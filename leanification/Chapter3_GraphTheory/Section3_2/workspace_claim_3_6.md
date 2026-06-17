# Workspace for claim_3_6 — SplitTopologicalOrder (REFACTOR row)

## Context

- **Refactor:** `cdmg_typed_edges` (roots: `def_3_1`, `def_3_4`).
- **Role:** DEPENDENT — pulled in because `def_3_1` (CDMG) changed
  shape (`L : Finset (Sym2 Node)` + `hL_irrefl : ¬ s.IsDiag`, no
  `hL_symm` field).
- **Math content unchanged.** The claim is about acyclicity
  preservation under node-splitting + an explicit topological order
  on the split graph. Per the canonical tex spec's *"Role of the
  CADMG precondition"* closing paragraph: *"The bidirected-edge
  set $L$ plays no role in either sub-claim."* So the refactor of
  `def_3_1`'s `L`-field does not touch the math of this row.
- **`addition_to_the_LN` is empty** — no extra clauses to fold in.

## Upstream APIs (all post-refactor, available now)

| Original                          | Refactor twin                          |
|---|---|
| `CDMG Node`                       | `refactor_CDMG Node`                   |
| `SplitNode Node`                  | `refactor_SplitNode Node`              |
| `SplitNode.unsplit/copy0/copy1`   | `refactor_SplitNode.unsplit/copy0/copy1` |
| `toCopy0 W` / `toCopy1 W`         | `refactor_toCopy0 W` / `refactor_toCopy1 W` |
| `G.nodeSplittingOn W hW`          | `G.refactor_nodeSplittingOn W hW`      |
| `G.IsCADMG`                       | `G.refactor_IsCADMG`                   |
| `G.IsAcyclic`                     | `G.refactor_IsAcyclic`                 |
| `G.IsTopologicalOrder lt`         | `G.refactor_IsTopologicalOrder lt`     |
| `acyclic_iff_topological_order`   | `refactor_acyclic_iff_topological_order` |
| `G.Pa v`                          | `G.refactor_Pa v`                      |
| `G.hE_subset`                     | `G.hE_subset` (E-side unchanged)       |
| `instMembership` (`v ∈ G`)        | `refactor_instMembership`              |

## Existing original Lean structure (to port)

`SplitTopologicalOrder.lean` (lines 64–663) contains, inside
`namespace Causality / namespace CDMG`:

1. `variable {Node : Type*} [DecidableEq Node]` — claim_3_6 helper marker.
2. `def splOrder` — claim_3_6 helper marker. Case-analysis lex order on
   `SplitNode Node`.
3. `private def baseOf : SplitNode Node → Node`.
4. `private def tagOf : SplitNode Node → ℕ`.
5. `private lemma splOrder_iff` — lex characterisation.
6. `private lemma splitNode_ext`.
7. `private lemma baseOf_mem` — projects `x ∈ G.nodeSplittingOn` to
   `baseOf x ∈ G`.
8. `private lemma splOrder_lifted_edge` — uses `toCopy0`, `toCopy1`.
9. `private lemma splOrder_transfer_edge`.
10. `private lemma aux_splTopologicalOrder` — the workhorse, full
    `IsTopologicalOrder` content on the split graph.
11. `theorem splAcyclic` — claim_3_6 statement marker (sub-claim a).
12. `theorem splTopologicalOrder` — claim_3_6 statement marker (sub-claim b).

## REPLACEMENT block plan (refactor_* renames)

| Original name              | Refactor name                          |
|---|---|
| `splOrder`                 | `refactor_splOrder` (helper-marker)    |
| `baseOf`                   | `refactor_baseOf` (private, no markers)|
| `tagOf`                    | `refactor_tagOf` (private, no markers) |
| `splOrder_iff`             | `refactor_splOrder_iff` (private)      |
| `splitNode_ext`            | `refactor_splitNode_ext` (private)     |
| `baseOf_mem`               | `refactor_baseOf_mem` (private)        |
| `splOrder_lifted_edge`     | `refactor_splOrder_lifted_edge` (private)|
| `splOrder_transfer_edge`   | `refactor_splOrder_transfer_edge` (private)|
| `aux_splTopologicalOrder`  | `refactor_aux_splTopologicalOrder` (private)|
| `splAcyclic`               | `refactor_splAcyclic` (statement marker, REPLACEMENT)|
| `splTopologicalOrder`      | `refactor_splTopologicalOrder` (statement marker, REPLACEMENT)|

Helper marker for `variable` line: it doesn't reference any
refactored API symbol — pure typeclass binders — so it can be shared
between ORIGINAL and REPLACEMENT blocks (or duplicated; see how
sibling refactor files handled it).

The REPLACEMENT block lives in `namespace refactor_CDMG` (to match
the upstream `refactor_nodeSplittingOn` namespace), or wrap the
declarations in `namespace CDMG` with explicit `refactor_CDMG.` qualifications
on uses — pick whichever sibling files (`BifurcationAlternative`,
`HardInterventionsCommute`, `NodeSplittingOn`) settled on. The
pattern in `NodeSplittingOn.lean` is `namespace refactor_CDMG` inside
the REPLACEMENT block.

## Pipeline (Manager A → handoff → Manager B)

### Manager A (statement only)

1. `formalize_claim_in_tex` — verify the existing canonical tex
   statement reflects the (unchanged) LN + (empty) addition. Expected
   near-no-op for this refactor row.
2. `verify_tex_statement_only` — structural.
3. `verify_tex_statement_equivalence` — semantic.
4. `formalize_claim_in_lean` — wrap original in
   `REFACTOR-BLOCK-ORIGINAL-*` markers; write REPLACEMENT block with
   `refactor_*` renames throughout the *statements only* (the two
   theorems' signatures + the `refactor_splOrder` helper). Body
   placeholders with `sorry` (orchestrator builds; we'll fill bodies
   later — or, since this is a port, the leanifier should be able to
   write the full proof in one go because it has the original body as
   a guide; but worker prompt sequence is statement-first, proof-later).
5. `review_design` — full LN-context, should pass since math is
   unchanged and shape is LN-faithful (port).
6. `verify_equivalence` — should pass.
7. `add_design_choice_comments` — enrich comments on the REPLACEMENT
   block (mostly: explain the refactor port; reference the
   `refactor_cdmg_typed_edges.md` plan; preserve the original's
   design-choice rationale).
8. `new_manager` handoff to Manager B.

### Manager B (the proof)

9. `write_tex_proof` — write the twin `tex/refactor_claim_3_6_proof_SplitTopologicalOrder.tex`.
   Since math is unchanged, this is essentially a copy of the
   original tex proof, with the at-the-top statement block synced
   from the (unchanged) canonical statement tex.
10. `verify_tex_statement_plus_proof` — structural.
11. `verify_tex_proof` — semantic.
12. `prove_claim_in_lean` — fill the REPLACEMENT block's proof
    bodies, porting the original proofs to the refactored API
    (`refactor_CDMG`, `refactor_acyclic_iff_topological_order`,
    `refactor_toCopy0/1`, etc.).
13. `solved` → orchestrator runs verify_row_solved + sorry-check +
    strict-equivalence gate.

## Notes / hazards

- **Marker placement.** For the two main theorems, two-dash
  `-- claim_3_6 -- start/end statement` markers wrap only the
  *signature* (up to and including the type annotation `:
  (G.refactor_nodeSplittingOn W hW).refactor_IsAcyclic` /
  `... .refactor_IsTopologicalOrder (refactor_splOrder lt)`).
  The `:= by ...` proof body sits below the end marker. The
  `refactor_splOrder` helper uses three-dash `--- start/end helper`
  markers.
- **All `refactor_*` net-new declarations need REPLACEMENT markers.**
  Per the briefing: every `refactor_*` declaration the cleanup
  script encounters must be inside a REPLACEMENT block, or it
  REFUSES. So even the private helpers and the `refactor_splOrder`
  helper need their own REPLACEMENT marker pair. (Helper-marker is
  the website extractor; REPLACEMENT-marker is the cleanup script's
  rename target.)
- **`hCADMG : G.refactor_IsCADMG` unfolds to `G.refactor_IsAcyclic`**
  by the `def_3_7` REPLACEMENT (`refactor_IsCADMG :=
  refactor_IsAcyclic`). The `splAcyclic` proof body needs only
  `G.refactor_IsAcyclic` to invoke `refactor_acyclic_iff_topological_order`.
- **`baseOf_mem` proof.** The original uses `Finset.mem_union`
  destructuring of the four-piece carrier `G.J ⊍ (G.V \ W) ⊍ W^0 ⊍ W^1`.
  Post-refactor, `G.refactor_nodeSplittingOn W hW` has the SAME
  carrier-decomposition (only the `L`-field's typing changed), so
  this port is purely syntactic.
- **`splOrder_lifted_edge`.** The original calls `unfold toCopy0 toCopy1`.
  Port: `unfold refactor_toCopy0 refactor_toCopy1`.
