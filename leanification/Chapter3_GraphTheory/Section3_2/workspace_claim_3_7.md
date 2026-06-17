# Workspace for claim_3_7 — TwoDisjointNode (REFACTOR row)

## Context: refactor `cdmg_typed_edges`

This is a **DEPENDENT row** in the `cdmg_typed_edges` refactor. Root `def_3_1`
changed: `L : Finset (Node × Node)` (with `hL_symm`, `hL_irrefl` on ordered
pairs) → `L : Finset (Sym2 Node)` (with `hL_irrefl : ¬ s.IsDiag`, no `hL_symm`).

Downstream `def_3_11` (`nodeSplittingOn`) accordingly changed its L-side from
`G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2))` to
`G.L.image (Sym2.map (refactor_toCopy0 W))`. The V/J/E sides are structurally
unchanged.

## What this row's port needs

**Tex side**: write `tex/refactor_claim_3_7_proof_TwoDisjointNode.tex` (the
twin file). The mathematical proof is *encoding-agnostic* at the LN level —
the existing tex proof at `tex/claim_3_7_proof_TwoDisjointNode.tex` already
expresses L's symmetry/irreflexivity in LN-level "unordered-pair" form. So
the twin tex can be a **verbatim** copy (or near-verbatim, with the L axiom
recitation paraphrased to drop the explicit-ordered-pair form). The math
doesn't change.

**Lean side**: add a `REFACTOR-BLOCK-REPLACEMENT: TwoDisjointNode` block in
`Section3_2/TwoDisjointNode.lean` containing:

* `refactor_flattenSplit : refactor_SplitNode (refactor_SplitNode Node) → refactor_SplitNode Node`
   — structurally identical to original `flattenSplit`, only constructor names change.
* `refactor_eqViaNodeMap` — same 4-conjunct shape, but L conjunct uses
   `Sym2.map f` instead of `Prod.map f f`:
       `G.L.image (Sym2.map f) = G'.L`.
* `refactor_image_unsplit_subset_nodeSplittingOn_V` — structurally identical to original
   (uses `refactor_SplitNode.unsplit`, `refactor_CDMG`, `refactor_nodeSplittingOn`).
* `refactor_twoDisjointNodeSplittingsCommute` theorem — port of the main theorem.

**Proof port for the theorem**:

* Sub-goals 1, 2, 3, 5, 6, 7 (J, V, E for both directions) port mechanically:
   replace `SplitNode → refactor_SplitNode`, `toCopy0 → refactor_toCopy0`,
   `toCopy1 → refactor_toCopy1`, helpers
   `flatten_toCopy0_toCopy0 → flatten_refactor_toCopy0_refactor_toCopy0` etc.
* Sub-goals 4 and 8 (L for both directions) need a **Sym2.map rework**:
   - `(G.L.image (Sym2.map (refactor_toCopy0 W₁))).image (Sym2.map (refactor_toCopy0 (W₂.image .unsplit)))`
      → after `Finset.image_image` twice, becomes
      `G.L.image (Sym2.map (refactor_toCopy0 (W₂.image .unsplit)) ∘ Sym2.map (refactor_toCopy0 W₁))`
   - Apply `Sym2.map_map` (or its underlying lemma) to fuse:
      `Sym2.map f ∘ Sym2.map g = Sym2.map (f ∘ g)`.
   - Apply `flatten_refactor_toCopy0_refactor_toCopy0` pointwise via
      `Sym2.map_congr` (or `Finset.image_congr` + `Sym2.ind`).

## Plan / action sequence

1. `spawn_agent_sub_task` → `write_tex_proof` worker, briefed to produce the
    twin tex `tex/refactor_claim_3_7_proof_TwoDisjointNode.tex` (verbatim or
    near-verbatim copy of the existing tex; light prose touch on the L axiom
    recitation is optional).
2. `verify_tex_statement_plus_proof` on the twin (structural).
3. `verify_tex_proof` on the twin (mathematical) — should trivially pass since
    the math is identical.
4. `spawn_agent_sub_task` → `prove_claim_in_lean` worker, briefed to write
    the REFACTOR-BLOCK-REPLACEMENT in `TwoDisjointNode.lean`. Worker reads the
    original proof structure as template, ports mechanically for J/V/E
    sub-goals, reworks L sub-goals for `Sym2.map`.
5. `verify_equivalence` (refactor-mode aware via the briefing).
6. `add_design_choice_comments` on the REPLACEMENT block (mainly mirror the
    original's design comments + a refactor-context block explaining the
    `Sym2.map` route).
7. `solved` → strict-equivalence gate runs against the LN block.

## Notes for future managers

* The original proof is 880 lines; the refactor REPLACEMENT block will be
   of similar length. Encourage the leanifier to copy the original's proof
   structure verbatim where possible (J/V/E) and only rework L sub-goals.
* `Sym2.map_map` (Mathlib): `Sym2.map f (Sym2.map g s) = Sym2.map (f ∘ g) s`.
* `Sym2.map_congr` (or `Sym2.map_eq_map_of_funext`): if `∀ a, f a = g a`,
   then `Sym2.map f s = Sym2.map g s`.
* The flatten-fusion helpers `flatten_refactor_toCopy0_refactor_toCopy0` and
   `flatten_refactor_toCopy1_refactor_toCopy1` are pointwise statements over
   `Node`, so their proofs are structurally identical to the original
   `flatten_toCopy0_toCopy0` / `flatten_toCopy1_toCopy1` — only the prefix
   changes.
