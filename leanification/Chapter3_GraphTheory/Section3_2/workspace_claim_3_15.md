# Workspace for claim_3_15 — AddingInterventionNodes (refactor `eqViaNodeMap_injective`)

## Context

This is a **DEPENDENT** row in refactor `eqViaNodeMap_injective`, pulled in
because root `claim_3_7` changed underneath it. The root change strengthens
`eqViaNodeMap` to `refactor_eqViaNodeMap` by adding a 1st conjunct
`Set.InjOn f (↑G.J ∪ ↑G.V)` on the carrier map. The four image-equality
conjuncts (J, V, E, L) are unchanged.

The existing Lean file `AddingInterventionNodesSwig.lean` (~772 lines)
contains the already-solved theorem `addInterventionNodes_comm_swig` using
the old `eqViaNodeMap`. The existing tex proof lives at
`tex/claim_3_15_proof_AddingInterventionNodes.tex`.

## Template: claim_3_14 (closest sibling, already solved)

`AddingInterventionNodes.lean` for claim_3_14 was solved by:
1. Wrapping original `addInterventionNodes_comm_disjoint` in
   `REFACTOR-BLOCK-ORIGINAL-BEGIN/END: addInterventionNodes_comm_disjoint` markers.
2. Adding `refactor_flattenIntExt_injOn_of_disjoint` (NEW helper) wrapped
   in `REFACTOR-BLOCK-REPLACEMENT` markers.
3. Adding `refactor_addInterventionNodes_comm_disjoint` (NEW theorem) wrapped
   in `REFACTOR-BLOCK-REPLACEMENT` markers — reuses the original via destructure
   `obtain ⟨⟨hJa, ...⟩, ⟨hJb, ...⟩⟩ := addInterventionNodes_comm_disjoint ...`,
   then `refine ⟨⟨?_, hJa, ...⟩, ⟨?_, hJb, ...⟩⟩` discharging only the new InjOn
   conjuncts via the helper.
4. Tex twin at `tex/refactor_claim_3_14_proof_AddingInterventionNodes.tex`
   with a new "Injectivity of the canonical flatten map" paragraph.

## Plan for claim_3_15

### Differences from claim_3_14

- **No conjunction.** claim_3_15's theorem is a single `eqViaNodeMap LHS RHS f`
  (not a conjunction of two directions like claim_3_14). So the new
  `refactor_addInterventionNodes_comm_swig` is also single, and uses one InjOn
  helper invocation.
- **LHS structure.** LHS = `(extendingCDMGsWith G W₂ hW₂).nodeSplittingHard hG' (W₁.image .unsplit) hW₁'`
  living in `CDMG (SplitNode (IntExtNode Node))`. RHS = `extendingCDMGsWith (G.nodeSplittingHard hG W₁ hW₁) (W₂.image .unsplit) hW₂'` living in `CDMG (IntExtNode (SplitNode Node))`. The carrier map is `flattenSwigDoit : SplitNode (IntExtNode Node) → IntExtNode (SplitNode Node)`.
- **InjOn is on the LHS carrier.** `refactor_eqViaNodeMap LHS RHS f` requires `Set.InjOn f (↑LHS.J ∪ ↑LHS.V)`.

### The four-cell partition of the LHS J ∪ V

LHS = `nodeSplittingHard (extendingCDMGsWith G W₂ hW₂) (W₁.image .unsplit)`.
Its J ∪ V decomposes as the disjoint union of four cells:
- Cell A: `.unsplit (.unsplit a)` for `a ∈ G.J ∨ (a ∈ G.V ∧ a ∉ W₁)` (merged inner J and (V \ W₁) since flatten and reasoning are identical)
- Cell B: `.unsplit (.intCopy w)` for `w ∈ W₂ \ G.J` (inner W₂-intCopy promoted through outer .unsplit)
- Cell C: `.copy0 (.unsplit w)` for `w ∈ W₁` (outer W₁^o tagged copy)
- Cell D: `.copy1 (.unsplit w)` for `w ∈ W₁` (outer W₁^i tagged copy)

### Outputs under flattenSwigDoit (four distinct constructor signatures)

- A: `IntExtNode.unsplit (SplitNode.unsplit a)`
- B: `IntExtNode.intCopy (SplitNode.unsplit w)`
- C: `IntExtNode.unsplit (SplitNode.copy0 w)`
- D: `IntExtNode.unsplit (SplitNode.copy1 w)`

### KEY OBSERVATION: Disjointness is NOT needed for the InjOn proof

All four output constructor patterns differ. Cross-cell collisions:
- A vs B: outer constructors differ (`.unsplit` vs `.intCopy`) → `cases heq`
- A vs C: same outer, but inner `.unsplit` vs `.copy0` → `cases heq` (after one injection)
- A vs D: similar, `.unsplit` vs `.copy1` → `cases heq`
- B vs C: outer constructors differ (`.intCopy` vs `.unsplit`) → `cases heq`
- B vs D: outer constructors differ → `cases heq`
- C vs D: same outer, inner `.copy0` vs `.copy1` → `cases heq` (after one injection)

Within-cell injectivity is structural: two-level constructor injection + within-W₁
or within-G.J/G.V uniqueness. The `hDisj` hypothesis is NOT consumed in the InjOn proof
(though it IS used elsewhere — e.g., to construct the RHS via `image_unsplit_subset_nodeSplittingHard_carrier`).

This contrasts with claim_3_14 (`flattenIntExt`) where cell-(3)-vs-(4) collides on `IntExtNode.intCopy w` and disjointness is load-bearing.

### Steps

1. **Tex twin**: write `tex/refactor_claim_3_15_proof_AddingInterventionNodes.tex`
   = existing tex proof + new "Injectivity of `flattenSwigDoit` on the LHS J ∪ V" paragraph
   inserted before the "Conclusion" block. Note that disjointness is *not* consumed
   in the InjOn paragraph (all six cross-cell collisions ruled out by constructor mismatch).
   Statement block should include the strengthened-componentwise paragraph.

2. **Structural check on tex twin**: `verify_tex_statement_plus_proof`.

3. **Math check on tex twin**: `verify_tex_proof`.

4. **Lean port**: modify `AddingInterventionNodesSwig.lean`:
   - Wrap existing `addInterventionNodes_comm_swig` (lines 506-768) in
     `REFACTOR-BLOCK-ORIGINAL-BEGIN/END: addInterventionNodes_comm_swig` markers.
   - Add NEW private helper `refactor_flattenSwigDoit_injOn_of_disjoint` wrapped in
     `REFACTOR-BLOCK-REPLACEMENT-BEGIN: flattenSwigDoit_injOn_of_disjoint (was: refactor_flattenSwigDoit_injOn_of_disjoint)` markers.
   - Add NEW theorem `refactor_addInterventionNodes_comm_swig` wrapped in
     `REFACTOR-BLOCK-REPLACEMENT-BEGIN: addInterventionNodes_comm_swig (was: refactor_addInterventionNodes_comm_swig)` markers.
     Reuses original via destructure: `obtain ⟨hJ, hV, hE, hL⟩ := addInterventionNodes_comm_swig ...`,
     then `refine ⟨?_, hJ, hV, hE, hL⟩` discharging only the InjOn.

5. **`add_design_choice_comments`** on the new declarations.

6. **`solved`** → orchestrator runs `verify_row_solved`, sorry-check, strict-equivalence gate.

## Notes

- The existing private helpers (`extendingCDMGsWith_isCADMG_of_isCADMG`, `image_unsplit_subset_extendingCDMGsWith_V`, `image_unsplit_subset_nodeSplittingHard_carrier`, `flattenSwigDoit`) are unchanged by this refactor; they do NOT need REFACTOR-BLOCK markers (claim_3_14's helpers stayed marker-less too).
- `addInterventionNodes_comm_hardIntervention`-style theorems don't exist for claim_3_15 (claim_3_15 is the pure SWIG variant of claim_3_14 (a), not (a)+(b)).
