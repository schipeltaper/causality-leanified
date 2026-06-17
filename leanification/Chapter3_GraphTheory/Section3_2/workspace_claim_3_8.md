# Workspace for claim_3_8 — DisjointHardInterventions (REFACTOR row)

## Context: refactor `cdmg_typed_edges`

This is a **DEPENDENT row** in the `cdmg_typed_edges` refactor. Root
`def_3_1` changed: `L : Finset (Node × Node)` (with `hL_symm`,
`hL_irrefl` on ordered pairs) → `L : Finset (Sym2 Node)` (with
`hL_irrefl : ¬ s.IsDiag`, no `hL_symm`).

Downstream `def_3_10` (`hardInterventionOn`) and `def_3_11`
(`nodeSplittingOn`) have already been refactored in the same table:

* `refactor_hardInterventionOn`'s L-side is
  `G.L.filter (fun s => ∀ v ∈ s, v ∉ W)` (single-sided "all
  endpoints outside W"; the pre-refactor two-sided-filter
  deviation `hard_intervention_l_symmetrized_removal` is
  structurally resolved by `Sym2`).
* `refactor_nodeSplittingOn`'s L-side is
  `G.L.image (Sym2.map (refactor_toCopy0 W))`.

J, V, E sides of both operations are structurally unchanged
modulo namespace prefix.

## What the port needs

**Tex twin** (`tex/refactor_claim_3_8_proof_DisjointHardInterventions.tex`):
* Math is unchanged at the LN level.
* Statement-restatement block: drop the explicit-ordered-pair
  L-axiom recitation (`L ⊆ V × V`, `L` irreflexive, `L`
  symmetric) and use the unordered-pair phrasing.
* Proof body's "Bidirected edges" section: the "Registered
  two-sided removal of L" paragraph is no longer needed — under
  the refactor the LN's literal one-sided filter agrees with
  the encoding by construction (no symmetrisation step
  required). Mark this as a refactor-context note in the prose
  rather than reasoning about the deviation.

**Lean REPLACEMENT block** in `DisjointHardInterventions.lean`,
containing three `refactor_`-prefixed declarations:

* `refactor_subset_V_of_hardInterventionOn` — helper 1, ports
  mechanically (no L-side changes, only the namespace
  `CDMG → refactor_CDMG`).
* `refactor_image_unsplit_subset_carrier_of_nodeSplittingOn` —
  helper 2, ports mechanically (J/V split-carrier reasoning
  unchanged; constructor names are `refactor_SplitNode.{unsplit,
  copy0, copy1}`).
* `refactor_disjointHardInterventionsAndNodeSplittingsCommute`
  — main theorem.

**Proof port of the main theorem:**

* `cdmgExt` helper now takes **8 fields** (not 9): the
  post-refactor `refactor_CDMG` drops `hL_symm`. Fields are
  `J, V, hJV_disj, E, hE_subset, L, hL_subset, hL_irrefl`.
* J sub-goal: identical (uses `Finset.image_union` on `.unsplit`).
* V sub-goal: identical (element-wise `ext`).
* E sub-goal: identical (uses `Finset.filter_union`,
  `Finset.filter_image`, `toCopy0_notMem_iff` for the head
  predicate).
* L sub-goal needs **`Sym2.map` rework**:
  - LHS: `(G.L.filter (fun s => ∀ v ∈ s, v ∉ W₁)).image
          (Sym2.map (refactor_toCopy0 W₂))`
  - RHS: `(G.L.image (Sym2.map (refactor_toCopy0 W₂))).filter
          (fun s => ∀ v ∈ s, v ∉ W₁.image .unsplit)`
  - Apply `Finset.filter_image` on the RHS to swap the filter
    inside the image.
  - Use `Finset.filter_congr` to align the predicates: for
    `s₀ ∈ G.L`, `(∀ v ∈ Sym2.map f s₀, v ∉ W₁.image .unsplit)`
    iff `(∀ v₀ ∈ s₀, v₀ ∉ W₁)` (via `Sym2.mem_map` and
    pointwise `toCopy0_notMem_iff`).

Note: the original Lean proof already has a `toCopy0_notMem_iff`
on ordered pairs; the refactor proof can reuse the same
identifier (`refactor_toCopy0_notMem_iff` or scope-shadowed) but
the underlying iff is the same statement applied to `Node` (not
to `Sym2 Node`).

## Plan / action sequence

1. `spawn_agent_sub_task` → `write_tex_proof` worker, briefed to
   produce the twin tex `tex/refactor_claim_3_8_proof_DisjointHardInterventions.tex`.
   Near-verbatim copy of the existing tex (with the
   L-axiom-recitation paraphrased and the deviation paragraph
   in the L-section dropped/restructured).
2. `verify_tex_statement_plus_proof` on the twin (structural).
3. `verify_tex_proof` on the twin (mathematical) — should
   trivially pass since the math is identical at the LN level.
4. `spawn_agent_sub_task` → `prove_claim_in_lean` worker,
   briefed to write the REFACTOR-BLOCK-REPLACEMENT in
   `DisjointHardInterventions.lean`.
5. `verify_equivalence` (statement equivalence, refactor-mode).
6. `add_design_choice_comments` on the REPLACEMENT block
   (mirror the original's design comments + a refactor-context
   note explaining the `Sym2.map` route and the deviation
   resolution).
7. `solved` → strict-equivalence gate runs against the LN block.

## Notes

* `Finset.filter_image` is the key Mathlib lemma:
  `(s.image f).filter p = (s.filter (p ∘ f)).image f` (or its
  contrapositive form). Confirmed in use at the original proof
  for the E sub-goal.
* `Sym2.mem_map`: `v ∈ Sym2.map f s ↔ ∃ v₀ ∈ s, f v₀ = v`. The
  pointwise `toCopy0_notMem_iff` step uses this.
* The "Notational reminder" paragraph in the original tex proof
  already explains `W_1` lifts as `.unsplit w` for `w ∈ W_1`
  using disjointness `W_1 ∩ W_2 = ∅` — this is unchanged.
* Confirmed via grep: the upstream refactor declarations
  `refactor_CDMG`, `refactor_hardInterventionOn`,
  `refactor_nodeSplittingOn`, `refactor_SplitNode`,
  `refactor_toCopy0`, `refactor_toCopy1` all live behind
  REFACTOR-BLOCK-REPLACEMENT markers in their respective files
  and are in scope under `namespace refactor_CDMG` /
  `namespace Causality.refactor_CDMG`.
