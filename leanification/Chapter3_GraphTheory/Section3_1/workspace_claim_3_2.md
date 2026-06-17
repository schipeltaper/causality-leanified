# Workspace for claim_3_2 — AcyclicIffTopologicalOrder

## Context (refactor: `cdmg_typed_edges`, DEPENDENT row)

This row is pulled into the refactor because roots `def_3_1` (CDMG: `L` retyped
to `Finset (Sym2 Node)`, `hL_irrefl` simplified to `¬ s.IsDiag`, `hL_symm` and
`hE_subset`'s `e.2 ∈ V` clauses unchanged) and `def_3_4` (every walk-class
predicate rebuilt on a typed `refactor_WalkStep` inductive with three
constructors `.forwardE` / `.backwardE` / `.bidir`) changed upstream.

The **mathematics is unchanged** by this refactor. Both sides of the
biconditional are skeleton-level properties of the `(J, V, E)` shape only;
the `L` retyping does not enter, and the rebuilt walk-step inductive only
changes the *constructor names* the proof matches on, not the proof's
reasoning.

The bulk of this is a **mechanical port**. Strategy:

1. **Tex twin** (mathematical content unchanged): create
   `tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex` as a copy of
   the original with a "REFACTOR TWIN" header explaining the refactor context.
2. **Lean port**: wrap the existing original theorem + its proof-only helpers
   in `REFACTOR-BLOCK-ORIGINAL` markers (they all reference `Walk G u v` which
   will not survive Phase 7 — `Walk` becomes the new `refactor_Walk` after
   cleanup), and add a parallel `namespace refactor_CDMG` block containing
   `refactor_` twin helpers plus `refactor_acyclic_iff_topological_order`,
   each wrapped in `REFACTOR-BLOCK-REPLACEMENT` markers.

## Key upstream shape changes that touch the proof

| Original | Refactor twin |
|---|---|
| `CDMG Node` | `refactor_CDMG Node` |
| `G.IsAcyclic` | `G.refactor_IsAcyclic` (Acyclicity.lean) |
| `G.IsTopologicalOrder lt` | `G.refactor_IsTopologicalOrder lt` (TopologicalOrder.lean) |
| `Walk G u v` | `refactor_Walk G u v` |
| `Walk.nil v hv` | `refactor_Walk.nil v hv` |
| `Walk.cons v a h p` (a : Node × Node, h : WalkStep) | `refactor_Walk.cons v s p` (s : refactor_WalkStep) |
| `p.length` | `p.refactor_length` |
| `p.IsDirectedWalk` | `p.refactor_IsDirectedWalk` |
| `G.WalkStep u (u, v) v := Or.inl ⟨rfl, Or.inl huv⟩` (Prop) | `refactor_WalkStep.forwardE huv : refactor_WalkStep G u v` (typed inductive) |
| `obtain ⟨ha_eq, ha_E, hq_dir⟩ := hp` (on `IsDirectedWalk (cons _ a _ p)`) | After matching on `.forwardE h`, `refactor_IsDirectedWalk` unfolds to just `p.refactor_IsDirectedWalk`; the `(u,v) ∈ G.E` witness is `h` directly, no equation step |

`Pa` (`def_3_5`) → `refactor_Pa` (in `FamilyRelationships.lean`). Body
`{u | u ∈ G ∧ (u, w) ∈ G.E}` is unchanged.

## Plan (single phase — mechanical port)

1. Dispatch `spawn_agent_sub_task` with a refactor-port brief on the Lean file
   and the tex twin.
2. After worker returns: `verify_tex_statement_plus_proof` on the tex twin
   (structural).
3. `verify_tex_proof` on the tex twin (mathematical).
4. `review_design` on the refactor twin Lean theorem (full LN context).
5. `verify_equivalence` on the refactor twin (focused check that the Lean
   theorem matches LN+addition).
6. `add_design_choice_comments` on the refactor twin (port rationale +
   upstream-shift summary).
7. `solved` → final-gate verification.

## Notes on the proof helpers

The original file contains these `private` proof-only helpers (all `Walk`-
namespace, none statement-marked):

- `Walk.comp` — concatenate two walks.
- `Walk.length_comp` — length is additive under concat.
- `Walk.isDirectedWalk_comp` — directedness preserved under concat.
- `Walk.source_in_G_of_directedWalk_pos` — source ∈ G for non-trivial directed walks.
- `Walk.target_in_G_of_directedWalk_pos` — target ∈ G for non-trivial directed walks.
- `Walk.singleEdge_directedWalk` — a `(u, v) ∈ G.E` produces a length-1 directed walk.
- `Walk.lt_of_directedWalk_pos` — under transitivity + parent-precedes, lt holds source→target.

Each will need a refactor twin (`refactor_Walk.refactor_comp`, etc.) inside
`namespace refactor_CDMG`. The proofs port mechanically — every
`obtain ⟨ha_eq, ha_E, hq_dir⟩ := hp` becomes a match on the typed WalkStep
constructor (only `.forwardE h` survives for directed walks), and the
`(u, v) ∈ G.E` witness is reached via the constructor argument `h` rather
than the rewrite-with-`ha_eq` step.

All these helpers belong to the proof body (no `start statement` markers);
but since they reference `Walk` types that will be replaced at Phase 7
cleanup, they MUST be wrapped in `REFACTOR-BLOCK-ORIGINAL` markers (and the
twins in `REFACTOR-BLOCK-REPLACEMENT` markers) — otherwise the
post-cleanup file references a vanished `Walk` API and breaks the build.
