# Workspace for def_3_13 — ExtendingCDMGsWith

This file is the manager's scratchpad for this row.

## Refactor context
- DEPENDENT in refactor `cdmg_typed_edges`.
- Root `def_3_1` changed `CDMG.L` from `Finset (Node × Node)` (with explicit `hL_symm`) to `Finset (Sym2 Node)` (swap-symmetry definitional under the `Sym2` quotient; the `hL_symm` field is gone).
- Lean file: `ExtendingCDMGsWith.lean` contains BOTH the pre-refactor ORIGINAL block (lines 252–619, 5 helpers + main def) and the REPLACEMENT block (lines 655–1078, 4 helpers + main def — `_hL_symm` has no twin).

## Action trail (this run)
1. `spawn_agent_sub_task` → `formalize_definition_in_lean.md` — produced REPLACEMENT block: 4 helpers (`refactor_extendingCDMGsWith_hJV_disj`, `_hE_subset`, `_hL_subset`, `_hL_irrefl`) + main `refactor_extendingCDMGsWith` def. `L`-side uses `G.L.image (Sym2.map IntExtNode.unsplit)`; `_hL_subset` proof uses `Sym2.mem_map`; `_hL_irrefl` uses `Sym2.IsDiag.map_iff` (Mathlib API).
2. `review_design` — completed without re-dispatch; agent flagged the four Mathlib API choices (`Sym2.map`, `Sym2.mem_map`, `Sym2.IsDiag`, `Sym2.Mem`) as natural Mathlib idioms for the quotient encoding.
3. `verify_equivalence` — completed without re-dispatch; agent walked every clause of the rewritten tex spec against the REPLACEMENT block and found semantic equivalence.
4. `add_design_choice_comments` — completed; enriched the comment block above each REPLACEMENT-side declaration with refactor-specific rationale (mechanical port for `_hJV_disj` / `_hE_subset`; Sym2 quotient lift for `_hL_subset` / `_hL_irrefl` / main def). ORIGINAL block untouched.

## Next
Emit `solved` to trigger `verify_row_solved` + hard sorry-check + strict-equivalence gate.
