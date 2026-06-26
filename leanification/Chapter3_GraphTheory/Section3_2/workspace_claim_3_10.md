# Workspace for claim_3_10 — TwoDisjointNode (SWIG / `nodeSplittingHard` variant)

## Refactor context

This row is a **DEPENDENT** in refactor `eqViaNodeMap_injective`
(root: `claim_3_7`). The root provides the strengthened predicate
`refactor_eqViaNodeMap` (5 conjuncts: InjOn + 4 image equalities).

claim_3_7 is solved: its `TwoDisjointNode.lean` contains
- `refactor_eqViaNodeMap` (the new predicate, exported)
- `refactor_flattenSplit_injOn_of_disjoint` (helper for the
  iterated `nodeSplittingOn`'s J ∪ V)
- `refactor_twoDisjointNodeSplittingsCommute` (uses the new
  predicate, reuses original for J/V/E/L, adds InjOn)

claim_3_10's existing `TwoDisjointNodeSwig.lean` already contains
the post-`cdmg_typed_edges` SWIG analogue
`twoDisjointNodeSplittingHardCommute` using the OLD 4-conjunct
`eqViaNodeMap`. This refactor needs to add a 5-conjunct twin.

## Refactor plan (mirror claim_3_7's pattern)

The work is genuinely a "same shape, SWIG-adapted" port:

1. **Tex twin** `tex/refactor_claim_3_10_proof_TwoDisjointNode.tex`
   - Copy the existing `claim_3_10_proof_TwoDisjointNode.tex`
     (already a `cdmg_typed_edges` twin) as base.
   - Insert two new "Injectivity of the carrier bijection on the
     iterated graph's node set" paragraphs (one per sub-claim (a)/(b)),
     mirroring claim_3_7's refactor twin paragraphs but adapted to
     the SWIG's J/V partition.
   - Header preface explaining the refactor.

2. **Lean port** in `TwoDisjointNodeSwig.lean`
   - Wrap existing `twoDisjointNodeSplittingHardCommute` with
     `REFACTOR-BLOCK-ORIGINAL-BEGIN/END: twoDisjointNodeSplittingHardCommute`.
   - Add REPLACEMENT block: `refactor_flattenSplit_injOn_of_disjoint_swig`
     (private helper, net-new). Proves `Set.InjOn flattenSplit` on the
     iterated SWIG's J ∪ V. Structurally analogous to claim_3_7's
     `refactor_flattenSplit_injOn_of_disjoint` but with SWIG's J/V shape.
   - Add REPLACEMENT block: `refactor_twoDisjointNodeSplittingHardCommute`.
     Reuses original via `obtain ⟨⟨hJa, hVa, hEa, hLa⟩, ⟨hJb, hVb, hEb, hLb⟩⟩`
     then `refine ⟨⟨?_, hJa, ...⟩, ⟨?_, hJb, ...⟩⟩` and discharges the
     two InjOn goals with the new helper.

## SWIG iterated-graph carrier shape (for the InjOn helper)

`nodeSplittingHard` (`def_3_12` SWIG):
- `J_{swig(W)} := G.J.image .unsplit ∪ W.image .copy1`  (note: `.copy1` on the J-side, not V-side)
- `V_{swig(W)} := (G.V \ W).image .unsplit ∪ W.image .copy0`

So `((G_{swig(W₁)})_{swig(W₂.image .unsplit)}).J ∪ V` partitions into 5 cells:

1. **untagged**: `unsplit (unsplit a)` for `a ∈ G.J ∨ (a ∈ G.V ∧ a ∉ W₁ ∧ a ∉ W₂)`
2. **W₁^i (inner-SWIG J-side)**: `unsplit (copy1 w)` for `w ∈ W₁`
3. **W₁^o (inner-SWIG V-side)**: `unsplit (copy0 w)` for `w ∈ W₁`
4. **W₂^i (outer-SWIG J-side)**: `copy1 (unsplit w)` for `w ∈ W₂`
5. **W₂^o (outer-SWIG V-side)**: `copy0 (unsplit w)` for `w ∈ W₂`

(Compare to claim_3_7's `nodeSplittingOn` 5-cell partition:
`{untagged, W₁^{0₁}, W₁^{1₁}, W₂^{0₂}, W₂^{1₂}}`. Same count, same
flat structure, just the constructor sequencing differs.)

`flattenSplit` maps these to:
- untagged → unsplit-stripped element
- `unsplit (copy0 w)` → `copy0 w`
- `unsplit (copy1 w)` → `copy1 w`
- `copy0 (unsplit w)` → `copy0 w`
- `copy1 (unsplit w)` → `copy1 w`

Cross-collision patterns needing disjointness:
- W₁^o (cell 3, maps to `copy0 w₁`) vs W₂^o (cell 5, maps to `copy0 w₂`):
  `copy0 w₁ = copy0 w₂ ⟹ w₁ = w₂ ∈ W₁ ∩ W₂` — contradiction by `hDisj`.
- W₁^i (cell 2, maps to `copy1 w₁`) vs W₂^i (cell 4, maps to `copy1 w₂`):
  same argument with copy1.

All other cross-cell pairs close by constructor mismatch (no-confusion).

## Sources to read

- Existing `TwoDisjointNodeSwig.lean` (current SWIG theorem).
- `TwoDisjointNode.lean` lines 153-227 (`refactor_eqViaNodeMap`)
  and 799-1069 (helper + new theorem) — the pattern to mirror.
- `tex/refactor_claim_3_7_proof_TwoDisjointNode.tex` — the tex twin
  pattern, especially lines 253-271 (InjOn paragraph for (a)) and
  279-285 (InjOn paragraph for (b)).
- Existing `tex/claim_3_10_proof_TwoDisjointNode.tex` — the body
  to start from.

## Step-by-step

1. ✅ Explore.
2. Dispatch tex writer for the twin file.
3. Verify tex twin structurally + mathematically.
4. Dispatch Lean leanifier (statement + helper + theorem; reuse
   the original for J/V/E/L).
5. Review design + equivalence + design comments.
6. Solved + strict gate.
