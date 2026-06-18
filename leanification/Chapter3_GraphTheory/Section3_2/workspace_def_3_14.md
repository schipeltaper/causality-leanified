# Workspace for def_3_14 — MarginalizationAK (REFACTOR dependent)

This row is a DEPENDENT in refactor `cdmg_typed_edges`, pulled in by roots
`def_3_1` (CDMG: `L : Finset (Sym2 Node)`, no `hL_symm`) and `def_3_4`
(typed `refactor_Walk` / `refactor_WalkStep` with `.forwardE` /
`.backwardE` / `.bidir`).

## Plan (manager)

1. **Port the existing file** by adding `REFACTOR-BLOCK-ORIGINAL-*` markers
   around every original top-level declaration in `MarginalizationAK.lean`
   (variable_Node, MarginalizationΦE, MarginalizationΦL, two `instDecidableMarginalizationΦ*`,
   five private lemmas, the main `marginalize` def), AND
2. Append a `namespace refactor_CDMG` block holding
   `REFACTOR-BLOCK-REPLACEMENT-*` twins for each of the above
   *except* `marginalize_hL_symm` (the new `refactor_CDMG` has no
   `hL_symm` field), with the following mapping:

   | original                        | refactor twin                                |
   |--------------------------------|----------------------------------------------|
   | `Walk G u v`                    | `refactor_Walk G u v`                        |
   | `p.IsDirectedWalk`              | `p.refactor_IsDirectedWalk`                  |
   | `p.IsBifurcation`               | `p.refactor_IsBifurcation`                   |
   | `p.vertices`                    | `p.refactor_vertices`                        |
   | `p.length`                      | `p.refactor_length`                          |
   | `CDMG Node` (return)            | `refactor_CDMG Node`                         |
   | `Finset (Node × Node)` for `L`  | `Finset (Sym2 Node)` for `L`                 |

3. The `L` field becomes:
   ```
   L := (((G.V \ W) ×ˢ (G.V \ W)).filter
          (fun e => e.1 ≠ e.2 ∧ G.refactor_MarginalizationΦL W e.1 e.2)).image
         (fun e => s(e.1, e.2))
   ```
   — filter ordered-pair carrier first, then `Sym2.mk` via `Finset.image`.
   The `e.1 ≠ e.2` conjunct gives `hL_irrefl` directly; the product carrier
   gives `hL_subset` (via `Sym2.Mem` quantification).

4. Drop `marginalize_hL_symm`: the new `refactor_CDMG` has no `hL_symm`
   field — symmetry is *definitional* via `Sym2`.

5. `hL_subset` and `hL_irrefl` proofs need a small `Finset.mem_image` /
   `Sym2.IsDiag`-on-`Sym2.mk` unfolding step. Pattern: see
   `Sym2.IsDiag.elim`, `Sym2.mk_isDiag_iff`, or destructure via
   `Finset.mem_image.mp`.

6. Wrap each helper / private decl with the *helper* triple-dash markers,
   the main def with *statement* double-dash markers, per `manager.md`
   ## Lean statement markers section.

7. After porting → `verify_equivalence` (against the rewritten tex
   `tex/def_3_14_MarginalizationAK.tex`), then `add_design_choice_comments`
   (Sym2-encoding rationale), then `solved` → strict-equivalence gate.

## Sibling references

- `HardInterventionOn.lean` (def_3_10) — already refactored, shows the
  `Finset (Sym2 Node)` filter pattern for `L` (filtering an *existing*
  `G.L`, not constructing fresh `Sym2` values; but the proof idioms for
  `hL_subset` via `Sym2.Mem` and `hL_irrefl` via `Sym2.IsDiag` carry
  over).
- `AddingInterventionNodes.lean` (claim_3_14, just solved) — shows the
  `namespace refactor_CDMG` / `open CDMG` pattern for picking up the
  pre-refactor sibling declarations alongside the new ones.
