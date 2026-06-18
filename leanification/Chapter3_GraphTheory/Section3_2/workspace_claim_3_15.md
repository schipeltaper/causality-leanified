# Workspace for claim_3_15 — AddingInterventionNodes (REFACTOR)

## Refactor context
- Refactor: `cdmg_typed_edges` (roots: `def_3_1`, `def_3_4`).
- This row is a DEPENDENT, pulled in by root `def_3_1` (CDMG structure).
- Root change on L channel:
  - OLD: `L : Finset (Node × Node)` + `hL_subset`, `hL_irrefl`, `hL_symm`.
  - NEW: `L : Finset (Sym2 Node)` + `hL_subset` (over `Sym2.Mem`), `hL_irrefl` (over `¬ s.IsDiag`); no symmetry field.
- The new structure is named `refactor_CDMG` and lives alongside the original; cleanup will rename `refactor_CDMG` → `CDMG` globally.
- Primary file: `AddingInterventionNodesSwig.lean` (claim_3_15) proves `addInterventionNodes_comm_swig` (J/V/E/L sub-goals via `eqViaNodeMap`).
- Sibling reference for porting pattern: `AddingInterventionNodes.lean` (claim_3_14) — just refactored in commit `87e6f9b`.

## Survey findings (from Explore agent)

### Sibling claim_3_14 pattern (`AddingInterventionNodes.lean`)
- REPLACEMENT theorem is `refactor_addInterventionNodes_comm_disjoint`, in `namespace refactor_CDMG`.
- L sub-goal uses `Sym2.map` instead of `Prod.map`.  Helper introduced inside the proof:
  ```lean
  have h_L_lift_uu_collapse : ∀ (S : Finset (Sym2 Node)),
      ((S.image (Sym2.map IntExtNode.unsplit)).image
          (Sym2.map IntExtNode.unsplit)).image
        (Sym2.map refactor_flattenIntExt)
      = S.image (Sym2.map IntExtNode.unsplit) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro s _
    change Sym2.map refactor_flattenIntExt
            (Sym2.map IntExtNode.unsplit (Sym2.map IntExtNode.unsplit s))
          = Sym2.map IntExtNode.unsplit s
    rw [Sym2.map_map, Sym2.map_map]
    refine Sym2.map_congr ?_
    intro a _
    rfl
  ```
- Pattern: `Sym2.map_map` (fusion) + `Sym2.map_congr` (pointwise on representatives) + `rfl` or pointwise identity.

### New API: `nodeSplittingHard` L channel
File: `Section3_2/NodeSplittingHard.lean` line 1212.
```lean
L := G.L.image (Sym2.map (refactor_toCopy0 W))
```
(Sym2.map of the same toCopy0 helper.)

### New API: `extendingCDMGsWith` L channel
File: `Section3_2/ExtendingCDMGsWith.lean` line 1075.
```lean
L := G.L.image (Sym2.map IntExtNode.unsplit)
```

### refactor_CDMG verified
File: `Section3_1/CDMG.lean` lines 383–392.

## Port plan for this row

5 declarations in `AddingInterventionNodesSwig.lean` to consider:
1. `extendingCDMGsWith_isCADMG_of_isCADMG` (private lemma) — depends on `CDMG` → needs `refactor_` variant.
2. `image_unsplit_subset_extendingCDMGsWith_V` (private lemma) — depends on `CDMG` → needs `refactor_` variant.
3. `image_unsplit_subset_nodeSplittingHard_carrier` (private lemma) — depends on `CDMG` → needs `refactor_` variant.
4. `flattenSwigDoit` (def) — pure `SplitNode (IntExtNode Node) → IntExtNode (SplitNode Node)`, no CDMG dependency → REUSE as-is (no markers needed).
5. `addInterventionNodes_comm_swig` (main theorem) — depends on `CDMG` → needs `refactor_` variant. The L sub-goal (lines 691–710) is the one that genuinely changes shape (Sym2.map instead of Prod.map).

For (1), (2), (3), (5): wrap original with `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: <name>` / `END`, add new `refactor_<name>` declaration wrapped with `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: <name> (was: refactor_<name>)` / `END` in `namespace refactor_CDMG`.

J, V, E sub-goals: mechanically identical (no Sym2 anywhere).  L sub-goal: rewrite using `Sym2.map flattenSwigDoit` + `Sym2.map_map` + `Sym2.map_congr` + reuse `h_flat_toCopy0_unsplit` (pointwise identity, unchanged).

Tex twin: copy `tex/claim_3_15_proof_AddingInterventionNodes.tex` → `tex/refactor_claim_3_15_proof_AddingInterventionNodes.tex`. Light edit to the "typing and axioms" paragraph at the top of the Lem block: drop the "L symmetric" axiom mention (now definitional via Sym2 quotient) and rephrase "L ⊆ V × V" to mention the quotient typing. The proof body itself (set-builder equalities) is unchanged.

## Action plan (turn-by-turn)
1. **Turn 1** (this turn) — `spawn_agent_sub_task`: port the Lean file (wrap + add `refactor_` variants) and create the tex twin; verify `lake build` clean.
2. **Turn 2** — `verify_tex_statement_plus_proof` on the tex twin (structural).
3. **Turn 3** — `verify_tex_proof` on the tex twin (mathematical; should be near-trivial since proof body is unchanged from the verified original).
4. **Turn 4** — `review_design` on the refactor variant Lean theorem.
5. **Turn 5** — `verify_equivalence` (Lean theorem ↔ LN block).
6. **Turn 6** — `add_design_choice_comments` (refactor variant comments explaining the Sym2 port choices).
7. **Turn 7** — `solved` (triggers strict-equivalence gate).

## History
_(this is turn 1 for claim_3_15 refactor row)_
