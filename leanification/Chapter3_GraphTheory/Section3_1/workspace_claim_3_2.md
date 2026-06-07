# Workspace for claim_3_2 — AcyclicIffTopologicalOrder (REFACTOR `total_order_helper`)

This file is the manager's scratchpad for this row.

## Refactor context

- This is a **dependent** row in refactor `total_order_helper`.
- `caused_by_roots: [def_3_8]`. The root `def_3_8` (TopologicalOrder) has already
  been refactored: `TopologicalOrder.lean` now hosts BOTH the original
  `IsTopologicalOrder` (flat 4-way `∧`, in `REFACTOR-BLOCK-ORIGINAL`) AND the
  REPLACEMENT `refactor_IsTopologicalOrder` (nested
  `G.refactor_IsTotalOrder lt ∧ (∀ v w, v ∈ G.Pa w → lt v w)`, in
  `REFACTOR-BLOCK-REPLACEMENT`), plus the new helper
  `refactor_IsTotalOrder` (irreflexive + transitive + trichotomous on `J ∪ V`).
- Cleanup will rename `refactor_*` → unprefixed.
- The other root `def_3_9` (Predecessors) is **not yet solved** in this
  refactor table. But `claim_3_2`'s proof does NOT reference `def_3_9` at all
  (the proof works with walks + `Pa^G` + the topological-order predicate
  directly), so we are independent of `def_3_9` here.

## What changes mechanically in the Lean proof

The theorem **statement** is unchanged in *shape*:
`G.IsAcyclic ↔ ∃ lt, G.IsTopologicalOrder lt`. The REPLACEMENT references
`refactor_IsTopologicalOrder` (cleanup will rename).

The **proof body** changes in exactly two pattern-matching sites:

1. **(⇒) direction**: the final `refine ⟨fun u v => s u v ∧ u ≠ v, ?_, ?_, ?_, ?_⟩`
   becomes `refine ⟨fun u v => s u v ∧ u ≠ v, ⟨?_, ?_, ?_⟩, ?_⟩` — the first
   three goals (irreflexive, transitive, trichotomous on `J ∪ V`) are packaged
   inside the `G.refactor_IsTotalOrder lt` conjunct, and the fourth (parent
   precedes) remains at the top level.

2. **(⇐) direction**: `rintro ⟨lt, hi, htr, htri, hp⟩` becomes
   `rintro ⟨lt, ⟨hi, htr, htri⟩, hp⟩`.

Everything else (the walk helpers, the Szpilrajn extension, the case analyses)
is unchanged.

## The tex proof

The mathematical proof is **unchanged** — the refactor is purely about the
Lean encoding of `IsTopologicalOrder`. The tex twin
`tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex` will be a
near-copy of the existing
`tex/claim_3_2_proof_AcyclicIffTopologicalOrder.tex`.

## Plan

1. **[worker]** Create the tex twin (near-copy of original; mathematical
   content unchanged).
2. **[worker]** Add `REFACTOR-BLOCK-ORIGINAL` markers around the existing
   `acyclic_iff_topological_order` theorem (including its design-choice
   comments + statement markers). Add `REFACTOR-BLOCK-REPLACEMENT` block
   below with `refactor_acyclic_iff_topological_order`, same proof strategy
   adapted to the nested 2-conjunct shape, referencing
   `G.refactor_IsTopologicalOrder lt`. Confirm `lake build` clean.
3. **[verify]** `verify_tex_statement_plus_proof` on the tex twin.
4. **[verify]** `verify_tex_proof` on the tex twin.
5. **[verify]** `review_design` on the REPLACEMENT block.
6. **[verify]** `verify_equivalence` on the REPLACEMENT block.
7. **[worker]** `add_design_choice_comments` — the existing comments mostly
   carry over; need to add a paragraph explaining the structural change
   (flat 4-tuple → nested 2-conjunct, mirroring `def_3_8`'s refactor).
8. **[solved]** Final-gate (verify_row_solved + sorry-check + strict-eq).

## Notes on what NOT to do

- Do NOT touch the existing `acyclic_iff_topological_order` theorem (other
  than wrapping it in the ORIGINAL markers). It must keep referencing the
  original `G.IsTopologicalOrder` so the build stays green.
- Do NOT touch the proof-only helpers (`Walk.comp`, `Walk.length_comp`,
  `Walk.isDirectedWalk_comp`, `Walk.source_in_G_of_directedWalk_pos`,
  `Walk.target_in_G_of_directedWalk_pos`, `Walk.singleEdge_directedWalk`,
  `Walk.lt_of_directedWalk_pos`). They are unchanged by the refactor —
  walk-level plumbing, used by BOTH original and replacement proofs.
- Do NOT touch the existing tex statement file
  (`tex/claim_3_2_statement_AcyclicIffTopologicalOrder.tex`) — the
  refactor briefing says only the proof file gets a twin for claim rows.
- Do NOT touch the `variable {Node : Type*} [DecidableEq Node]` line —
  shared between original and replacement.

## Running notes

- Turn 1 (spawn_agent_sub_task): tex twin created at `tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex`. Byte-identical to original except 7-line `% REFACTOR TWIN …` header prepended.
- Turn 2 (verify_tex_statement_plus_proof on twin): PASS.
- Turn 3 (verify_tex_proof on twin): PASS.
- Turn 4 (spawn_agent_sub_task): leanifier dispatched to wrap existing theorem in `REFACTOR-BLOCK-ORIGINAL` markers and add `refactor_acyclic_iff_topological_order` in `REFACTOR-BLOCK-REPLACEMENT` markers, referencing `G.refactor_IsTopologicalOrder lt` from the def_3_8 refactor.
