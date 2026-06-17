# Workspace for def_3_1 — CDMG (refactor ROOT in `cdmg_typed_edges`)

## Refactor context (see `leanification/refactors/refactor_cdmg_typed_edges.md`)

This row is a refactor ROOT. The original `structure CDMG` (current
`CDMG.lean` lines 174-185) stays in place wrapped in
`-- REFACTOR-BLOCK-ORIGINAL-BEGIN/END: CDMG` markers; a replacement
`refactor_CDMG` lives below in `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN/END:
CDMG (was: refactor_CDMG)` markers. Phase 7 cleanup will delete the
ORIGINAL block, rename `refactor_CDMG → CDMG` globally, and strip the
markers.

**The new shape (per the refactor plan):**

```lean
structure refactor_CDMG (Node : Type*) [DecidableEq Node] where
  J : Finset Node
  V : Finset Node
  hJV_disj : Disjoint J V
  E : Finset (Node × Node)
  hE_subset : ∀ ⦃e : Node × Node⦄, e ∈ E → e.1 ∈ J ∪ V ∧ e.2 ∈ V
  L : Finset (Sym2 Node)
  hL_subset : ∀ ⦃s : Sym2 Node⦄, s ∈ L → ∀ ⦃v : Node⦄, v ∈ s → v ∈ V
  hL_irrefl : ∀ ⦃s : Sym2 Node⦄, s ∈ L → ¬ s.IsDiag
  -- hL_symm removed — symmetry is built into Sym2 by construction
```

The math (LN + addition_to_the_LN) is unchanged. The Sym2 encoding is
the *quotient* encoding explicitly admitted by addition
`[l_quotient_vs_ordered_pair_typing_inconsistent]` ("may be encoded
either as a subset of the quotient... or as a subset of V × V subject
to symmetry"). We commit to the quotient encoding for the refactor.

The canonical statement tex (`tex/def_3_1_CDMG.tex`) is mathematically
unchanged under the refactor — both encodings remain admissible per
the addition. I'm leaving the tex untouched unless an equivalence
verifier flags a wording mismatch with the new Lean.

`addition_to_the_LN` is being left as-is: the new Sym2 shape doesn't
*contradict* any existing addition clause (it's one of the two
explicitly admitted encodings). If a strict-equivalence check flags
the existing addition's wording as misleading under the new encoding,
I'll revise on the next iteration.

## Plan

1. **Add REFACTOR-BLOCK markers + write `refactor_CDMG`** — single
   `spawn_agent_sub_task` dispatch. Worker:
   - Wraps the existing `structure CDMG` (lines 174-185) in
     `-- REFACTOR-BLOCK-ORIGINAL-BEGIN/END: CDMG` markers.
   - Appends below a `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: CDMG (was:
     refactor_CDMG)` block containing fresh design-choice comments,
     the `-- def_3_1 -- start statement` markers, the new
     `structure refactor_CDMG` with Sym2-based `L`, and the
     `-- def_3_1 -- end statement` + `-- REFACTOR-BLOCK-REPLACEMENT-END`
     closers.
   - The existing top-of-file `/-! ... -/` docstring and the
     pre-existing design-choice `--` block above the ORIGINAL
     statement stay where they are (they describe the original
     design; `polish_refactor_comments` will sort them at Phase 7
     cleanup).
   - Runs `lake build` to confirm clean.
2. `review_design` on the replacement.
3. `verify_equivalence` on the replacement against LN + addition.
4. `verify_equivalence_strict` (recommended — this introduces a new
   encoding/type for L). Auto-chains to `verify_with_examples` if it
   returns EXAMPLE_GENERATION.
5. `add_design_choice_comments` — polish the comment block above
   the REPLACEMENT to fully document the Sym2 commitment (why Sym2
   over ordered-pair-plus-symmetry, downstream implications for the
   ~35 dependents).
6. `solved` → strict-equivalence solved-gate (re-runs step 4) → mark
   solved.

## Carried-over tips

REFACTOR row. Original at same `main_lean_file` / `tex_file` paths.
Use same-file marker convention. Cleanup is atomic at Phase 7.

## Notes / history

_(first turn)_
