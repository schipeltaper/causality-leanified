# Workspace for claim_3_10 — TwoDisjointNode (SWIG variant) — REFACTOR row

## Refactor context

This is a **dependent** row in the `cdmg_typed_edges` refactor (root: `def_3_1`).
The refactor changes the `CDMG.L` field from `Finset (Node × Node)` (with
`hL_symm`, `hL_irrefl` on ordered pairs) to `Finset (Sym2 Node)` (with
`hL_irrefl : ¬ s.IsDiag`, `hL_subset` quantifying via `Sym2.Mem`). The `hL_symm`
field is gone entirely — swap-symmetry is now definitional in the `Sym2`
quotient.

This row's mathematical content is **unchanged**; only its expression against
the refactored upstream shapes changes.

## Files to produce

1. **Tex twin proof**: `tex/refactor_claim_3_10_proof_TwoDisjointNode.tex` —
   essentially a verbatim copy of `tex/claim_3_10_proof_TwoDisjointNode.tex`,
   with **only** the L-axiom recitation reworded from
   "L \ins V \times V" + "L symmetric ((v_1,v_2) ∈ L ⇔ (v_2,v_1) ∈ L)"
   to "L consists of unordered pairs of distinct vertices in V".
   The proof body is mathematically identical (the LN-level argument about
   bidirected edges doesn't change between encodings).
   Model: `tex/refactor_claim_3_7_proof_TwoDisjointNode.tex` (the spl analogue's
   twin, which made exactly this rewording and otherwise kept the original
   proof verbatim).

2. **Lean replacement block**: add `REFACTOR-BLOCK-REPLACEMENT` markers around
   `refactor_twoDisjointNodeSplittingHardCommute` + its private helper
   `refactor_image_unsplit_subset_nodeSplittingHard_V`, both inside
   `TwoDisjointNodeSwig.lean`, alongside the existing ORIGINAL block.
   New names get the `refactor_` prefix; the cleanup script renames them
   back at Phase 7.

## Lean port — checklist of name changes

| Pre-refactor | Post-refactor |
| --- | --- |
| `CDMG` | `refactor_CDMG` |
| `SplitNode` | `refactor_SplitNode` |
| `SplitNode.unsplit` / `.copy0` / `.copy1` | `refactor_SplitNode.unsplit` / etc. |
| `nodeSplittingHard` | `refactor_nodeSplittingHard` |
| `IsCADMG` | `refactor_IsCADMG` |
| `swigAcyclic` | `refactor_swigAcyclic` |
| `flattenSplit` | `refactor_flattenSplit` |
| `eqViaNodeMap` | `refactor_eqViaNodeMap` |
| `toCopy0` / `toCopy1` | `refactor_toCopy0` / `refactor_toCopy1` |
| `image_unsplit_subset_nodeSplittingHard_V` (private) | `refactor_image_unsplit_subset_nodeSplittingHard_V` |
| `twoDisjointNodeSplittingHardCommute` | `refactor_twoDisjointNodeSplittingHardCommute` |

## Sub-goal port plan (8 sub-goals)

| Sub-goal | Pre-refactor | Post-refactor | Type of change |
|---|---|---|---|
| 1: J (a) | `Finset.image` fusion | Identical | Mechanical rename |
| 2: V (a) | Set membership chains | Identical | Mechanical rename |
| 3: E (a) | `Prod.map` + `Finset.image_image` | Identical | Mechanical rename |
| **4: L (a)** | `Prod.map flattenSplit flattenSplit` + `flatten_toCopy0_toCopy0` × 2 | `Sym2.map refactor_flattenSplit` + `Sym2.map_map` + `Sym2.map_congr` + `flatten_refactor_toCopy0_refactor_toCopy0` | **Structural rework** (Sym2-aware) |
| 5: J (b) | Same as 1 | Identical | Mechanical rename |
| 6: V (b) | Same as 2 | Identical | Mechanical rename |
| 7: E (b) | Same as 3 | Identical | Mechanical rename |
| **8: L (b)** | Same as 4 with W₁ ↔ W₂ | Same as 4 with W₁ ↔ W₂ | **Structural rework** |

## The Sym2 rework for L sub-goals (key delta vs old)

**Old (L sub-goal 4)** worked on `Finset (Node × Node)`:
```lean
· change ((G.L.image (fun e => (toCopy0 W₁ e.1, toCopy0 W₁ e.2))).image
            (fun e => (toCopy0 (W₂.image SplitNode.unsplit) e.1,
                       toCopy0 (W₂.image SplitNode.unsplit) e.2))).image
          (Prod.map flattenSplit flattenSplit)
        = G.L.image (fun e => (toCopy0 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
  rw [Finset.image_image, Finset.image_image]
  refine Finset.image_congr ?_
  intro e _
  change (flattenSplit (toCopy0 (W₂.image SplitNode.unsplit) (toCopy0 W₁ e.1)),
          flattenSplit (toCopy0 (W₂.image SplitNode.unsplit) (toCopy0 W₁ e.2)))
        = (toCopy0 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2)
  rw [flatten_toCopy0_toCopy0, flatten_toCopy0_toCopy0]
```

**New (L sub-goal 4)** works on `Finset (Sym2 Node)`:
```lean
· change ((G.L.image (Sym2.map (refactor_toCopy0 W₁))).image
            (Sym2.map (refactor_toCopy0 (W₂.image refactor_SplitNode.unsplit)))).image
          (Sym2.map refactor_flattenSplit)
        = G.L.image (Sym2.map (refactor_toCopy0 (W₁ ∪ W₂)))
  rw [Finset.image_image, Finset.image_image]
  refine Finset.image_congr ?_
  intro s _
  change Sym2.map refactor_flattenSplit
            (Sym2.map (refactor_toCopy0 (W₂.image refactor_SplitNode.unsplit))
              (Sym2.map (refactor_toCopy0 W₁) s))
        = Sym2.map (refactor_toCopy0 (W₁ ∪ W₂)) s
  rw [Sym2.map_map, Sym2.map_map]
  refine Sym2.map_congr ?_
  intro x _
  exact flatten_refactor_toCopy0_refactor_toCopy0 W₁ W₂ x
```

(Sub-goal 8 is the same with `W₁ ↔ W₂` and a `Finset.union_comm` flip on the RHS,
exactly like the existing version.)

The two `have` helpers (`flatten_refactor_toCopy0_refactor_toCopy0`,
`flatten_refactor_toCopy1_refactor_toCopy1`) get carried over verbatim from
`refactor_twoDisjointNodeSplittingsCommute`'s proof body (claim_3_7's twin) —
they are pure constructor-algebra facts on `refactor_SplitNode`, independent of
the Sym2 encoding.

## Plan

1. Dispatch `write_tex_proof.md` (REFACTOR mode) to produce
   `tex/refactor_claim_3_10_proof_TwoDisjointNode.tex` modelled on the spl
   analogue (`refactor_claim_3_7_proof_TwoDisjointNode.tex`).
2. `verify_tex_statement_plus_proof` (structural).
3. `verify_tex_proof` (mathematical).
4. Dispatch `prove_claim_in_lean.md` (REFACTOR mode) to insert the REPLACEMENT
   block into `TwoDisjointNodeSwig.lean`.
5. `solved`.
