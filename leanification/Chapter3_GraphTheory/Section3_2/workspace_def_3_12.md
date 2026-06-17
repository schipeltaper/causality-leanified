# Workspace for def_3_12 — NodeSplittingHard

This file is the manager's scratchpad for this row. Use it for:

- The plan (output of `make_plan` worker)
- A running list of what has been tried and why it didn't work
- Notes for the next manager (if you `new_manager`-handoff or
  the run ends and a future invocation picks this row up again)

It is YAML-untyped markdown — feel free to add sections.

## Refactor port progress
- **Refactor:** `cdmg_typed_edges`. Role: DEPENDENT; pulled in because `def_3_1` (CDMG) refactored to `refactor_CDMG` with `L : Finset (Sym2 Node)` (no more `hL_symm`).
- **addition_to_the_LN:** empty. LN block is authoritative.
- Original `nodeSplittingHard` block (lines 65-624) wrapped in `REFACTOR-BLOCK-ORIGINAL-BEGIN/END: nodeSplittingHard` markers (inside `namespace CDMG`).
- Replacement `refactor_nodeSplittingHard` (lines 628-1045) added under `namespace refactor_CDMG`, includes:
  - `refactor_swig_toCopy0_inj` private helper (re-derived locally because `refactor_toCopy0_inj` is private to `NodeSplittingOn.lean`).
  - Four proof helpers: `refactor_nodeSplittingHard_h{JV_disj,E_subset,L_subset,L_irrefl}` (one fewer than the pre-refactor five — `hL_symm` is gone because Sym2 makes swap-symmetry definitional).
  - `hL_subset` ported from `e.1 ∈ V ∧ e.2 ∈ V` to `∀ v ∈ s, v ∈ V` over `Sym2.Mem`, mirroring the sibling `refactor_nodeSplittingOn_hL_subset` strategy.
  - `hL_irrefl` ported from `v₁ ≠ v₂` to `¬ s.IsDiag` via a single `Sym2.isDiag_map` lift (collapses the pre-refactor multi-step destructure).
  - L-side field: `G.L.image (Sym2.map (refactor_toCopy0 W))` — single `Sym2.map` lift; identical idiom to `refactor_nodeSplittingOn`.
  - J/V/E sides mechanically ported (only `refactor_` prefix changes on names).
- `lake build` clean (8287 jobs, all replays).

## Next steps
1. `review_design` on the replacement Lean (full-LN context) — validate Sym2.map idiom and removed hL_symm choice for a def-level shape.
2. `verify_equivalence` (focused, friendly) on the replacement against LN block.
3. `solved` — auto-chains the strict-equivalence gate.
