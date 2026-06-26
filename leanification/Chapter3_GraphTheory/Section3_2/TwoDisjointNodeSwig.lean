import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGTypes
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard
import Chapter3_GraphTheory.Section3_2.SwigAcyclic
import Chapter3_GraphTheory.Section3_2.TwoDisjointNode

namespace Causality

/-!
# Two disjoint node-splitting hard interventions commute (`claim_3_10`)

This file formalises the LN lemma `claim_3_10` (`TwoDisjointNode`, the
SWIG / node-splitting-hard-intervention variant) in section 3.2 of
`graphs.tex`:

> Let `G = (J, V, E, L)` be a CADMG and `W₁, W₂ ⊆ V` two disjoint
> subsets of the output nodes.  Then
> `(G_{swig(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{swig(W₁)}
>   = G_{swig(W₁ ⊍ W₂)}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_10_statement_TwoDisjointNode.tex`, verified equivalent to the
LN block by `verify_tex_statement_only` and
`verify_tex_statement_equivalence`.  The rewritten tex decomposes the
LN's triple equality into the conjunction of two binary equalities,
mirroring `claim_3_4` (`HardInterventionsCommute`) and the sibling
`claim_3_7` (`TwoDisjointNode`, the regular node-splitting variant):

* (a) `(G_{swig(W₁)})_{swig(W₂)} = G_{swig(W₁ ∪ W₂)}`
* (b) `(G_{swig(W₂)})_{swig(W₁)} = G_{swig(W₁ ∪ W₂)}`

Transitivity of equality recovers the LN's "swap symmetry" reading
from (a) ∧ (b).

## Reuse from `claim_3_7`'s solved file (`TwoDisjointNode.lean`)

This row is the SWIG analogue of `claim_3_7`; the same
constructor-algebra infrastructure applies, because `def_3_12` (SWIG)
and `def_3_11` (regular node-splitting) share the same `SplitNode`
tagged-sum carrier (with the convention
`copy0 ↔ ^o ↔ ^0`, `copy1 ↔ ^i ↔ ^1`, `unsplit` for the residual).
We therefore import — and reuse verbatim — the following symbols from
`TwoDisjointNode.lean`:

* `flattenSplit : SplitNode (SplitNode Node) → SplitNode Node` — the
  canonical flatten map collapsing nested `SplitNode (SplitNode Node)`
  onto `SplitNode Node`.  Reusable because the cases that actually
  inhabit the iterated SWIG carrier are the same constructor
  combinations as the iterated spl carrier (with the off-carrier
  pattern-match cases filled in identically for totality and
  irrelevant to the image-level equality this row asserts).
* `eqViaNodeMap` — the "two CDMGs are equal up to the canonical
  carrier bijection" predicate, four-conjunct `Finset` equality on
  the data fields under a node map.
* (No `flatten_toCopy0_toCopy0` / `flatten_toCopy1_toCopy1` import: those
  are hypothesis-free constructor-algebra helpers Manager B's proof
  body will need, but they live inside `claim_3_7`'s theorem proof
  block — Manager B will redo them locally if needed; they are not on
  the statement surface.)

## Carrier-mismatch wrinkle (load-bearing for this row's Lean signature)

`def_3_12`'s `nodeSplittingHard` changes the node carrier
(`CDMG α → CDMG (SplitNode α)`), so the iterated splitting
`(G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
    (swigAcyclic G hG W₁ hW₁) (W₂.image .unsplit) _`
lives in `CDMG (SplitNode (SplitNode Node))` — a formally distinct
type from the single splitting
`G.nodeSplittingHard hG (W₁ ∪ W₂) _ : CDMG (SplitNode Node)`.  The LN
identifies the two carriers set-theoretically via `def_3_12`'s
unsplit-injection convention `v^o := v^i := v` for
`v ∈ J ∪ (V ∖ W)`; the rewritten tex's "Equality up to the canonical
bijection of carriers" paragraph spells this out.  The Lean rendering
captures the identification via the imported `flattenSplit`; the LN's
"equality of CDMGs" reading becomes the imported `eqViaNodeMap`
applied with `flattenSplit` as the node map — the four `Finset` data
fields of the iterated splitting, after applying `flattenSplit`
field-wise, coincide with the four `Finset` data fields of the single
splitting.

## SWIG carrier vs. spl carrier — structural differences

The SWIG carrier is *smaller* on the `V` side than the
node-splitting carrier:

* SWIG `J_{swig(W)} := G.J.image .unsplit ∪ W.image .copy1`
* SWIG `V_{swig(W)} := (G.V ∖ W).image .unsplit ∪ W.image .copy0`
* spl  `J_{spl(W)}  := G.J.image .unsplit`
* spl  `V_{spl(W)}  := (G.V ∖ W).image .unsplit ∪ W.image .copy0 ∪
                          W.image .copy1`

The `^i` (= `.copy1`) copies sit in `J_{swig}` (input side), *not* in
`V_{swig}`.  This forces the local well-typedness helper
`image_unsplit_subset_nodeSplittingHard_V` below to be the
*two-piece-union* analogue of `claim_3_7`'s three-piece-union
`image_unsplit_subset_nodeSplittingOn_V`: a single
`Finset.mem_union_left` (into the `(G.V ∖ W₁).image .unsplit` piece)
rather than two nested `Finset.mem_union_left`s — the structural
difference traces back to `def_3_12` item ii vs. `def_3_11` item ii.

## Acyclicity requirement from `def_3_12`

Unlike `def_3_11`'s `nodeSplittingOn` (CDMG → CDMG, no acyclicity
binder), `def_3_12`'s `nodeSplittingHard` takes `(hG : G.IsCADMG)` on
its signature — see `NodeSplittingHard.lean`'s design block (d).  The
outer iterated call `(G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
?_ ...` therefore needs an `IsCADMG` witness on the inner SWIG; this
is exactly what `claim_3_9` `swigAcyclic` provides
(`(G.nodeSplittingHard hG W hW).IsAcyclic`, definitionally equal to
`.IsCADMG` by `def_3_7` item i: `IsCADMG := IsAcyclic`).  The theorem
signature below threads `swigAcyclic G hG W₁ hW₁` (and its `W₂`-swap)
through the inner-`hG` slot of each iterated SWIG call.

The body is filled in by `prove_claim_in_lean` (Manager B), following
the to-be-written tex proof at
`tex/claim_3_10_proof_TwoDisjointNode.tex`.
-/

namespace CDMG

-- ## Refactor port — REPLACEMENT blocks for the `cdmg_typed_edges` design
--
-- The two `REFACTOR-BLOCK-REPLACEMENT` blocks below port the
-- pre-refactor declarations in this file to the post-refactor
-- `def_3_1` / `def_3_12` shapes (`CDMG` with
-- `L : Finset (Sym2 Node)`; `nodeSplittingHard` with
-- `L := G.L.image (Sym2.map (toCopy0 W))`).  Each block
-- mirrors its ORIGINAL above with the prefix `refactor_` and the
-- type / operation substitutions:
--
--   * `CDMG → CDMG`
--   * `IsCADMG → IsCADMG`
--   * `SplitNode → SplitNode`
--   * `toCopy0 / toCopy1 → toCopy0 / toCopy1`
--   * `nodeSplittingHard → nodeSplittingHard`
--   * `swigAcyclic → swigAcyclic`
--   * `flattenSplit / eqViaNodeMap / image_unsplit_subset_…` →
--     same with the `refactor_` prefix (imported from
--     `TwoDisjointNode.lean`'s refactor twin for the first two)
--
-- The J/V/E sides of the main theorem port mechanically — same
-- tactics, just renames — because `nodeSplittingHard`'s
-- J/V/E fields are unchanged from `nodeSplittingHard`'s (the
-- refactor changes only the L side).  Only the L-side (sub-goals
-- 4 and 8) is structurally reworked: ordered-pair lifting via
-- `Prod.map flattenSplit flattenSplit` becomes `Sym2`-quotient
-- lifting via `Sym2.map flattenSplit`.  The rework uses
-- Mathlib's `Sym2.map_map` to fuse the two-stage tagged-sum lift
-- back into a single-stage one, then closes pointwise via
-- `Sym2.map_congr` and the inline
-- `flatten_refactor_toCopy0_refactor_toCopy0` helper (verbatim
-- port of the original `flatten_toCopy0_toCopy0`).

-- claim_3_10 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_10 --- end helper

-- ## Helper: well-typedness of the iterated SWIG splitting (refactor)
--
-- Refactor port of `image_unsplit_subset_nodeSplittingHard_V` for
-- the `cdmg_typed_edges` design.  Statement and proof are
-- structurally identical to the original; only the type carrier
-- (`CDMG → CDMG`), the splitting operation
-- (`nodeSplittingHard → nodeSplittingHard`), the
-- acyclicity predicate (`IsCADMG → IsCADMG`), and the
-- unsplit-injection constructor
-- (`SplitNode.unsplit → SplitNode.unsplit`) change.  The
-- proof body uses the same `Finset.mem_sdiff` /
-- `Finset.disjoint_right` machinery — the V-side of
-- `nodeSplittingHard` is structurally identical to the
-- pre-refactor `nodeSplittingHard`'s V-side (refactor changes
-- only the L-channel), so the lemma carries over verbatim with
-- only the rename pass.
-- claim_3_10 --- start helper
private lemma image_unsplit_subset_nodeSplittingHard_V
    {G : CDMG Node} {hG : G.IsCADMG}
    {W₁ W₂ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂.image SplitNode.unsplit ⊆
      (G.nodeSplittingHard hG W₁ hW₁).V
-- claim_3_10 --- end helper
:= by
  intro x hx
  obtain ⟨v, hvW₂, rfl⟩ := Finset.mem_image.mp hx
  -- `(G.nodeSplittingHard hG W₁ hW₁).V` unfolds to
  --   `(G.V ∖ W₁).image .unsplit ∪ W₁.image .copy0`.
  -- `v ∈ W₂` with `Disjoint W₁ W₂` gives `v ∈ G.V ∖ W₁`, hence
  -- `.unsplit v ∈ (G.V ∖ W₁).image .unsplit`.
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
  exact Finset.mem_sdiff.mpr ⟨hW₂ hvW₂, Finset.disjoint_right.mp hDisj hvW₂⟩

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: twoDisjointNodeSplittingHardCommute
-- ref: claim_3_10
--
-- Refactor port of `twoDisjointNodeSplittingHardCommute` for the
-- `cdmg_typed_edges` design.  Same statement structure as the
-- original — a conjunction `(a) ∧ (b)` of two
-- `eqViaNodeMap` equalities through the shared joint SWIG
-- `G_{swig(W₁ ∪ W₂)}` — and the same eight sub-goals (J, V, E, L
-- for each iteration order).
--
-- ## Refactor port — proof structure
--
-- * **J / V / E sub-goals (1, 2, 3, 5, 6, 7) port mechanically.**
--   The tactic blocks are verbatim from the original up to the
--   rename pass `SplitNode → SplitNode`,
--   `toCopy0 → toCopy0`, `toCopy1 → toCopy1`,
--   helper-name `flatten_toCopy0_toCopy0 →
--   flatten_refactor_toCopy0_refactor_toCopy0`, etc.  The
--   structural reason this works is that
--   `nodeSplittingHard`'s J / V / E fields are unchanged
--   from `nodeSplittingHard`'s (the refactor changes only the L
--   side); every `change`-target, every `Finset.image_image`
--   fusion, every `Finset.image_congr` pointwise check has the
--   same shape after the rename.
--
-- * **L sub-goals (4 and 8) are structurally reworked for
--   `Sym2.map`.**  The original L-side threaded the lift through
--   `Prod.map flattenSplit flattenSplit` on ordered pairs; the
--   refactor threads it through `Sym2.map flattenSplit`
--   on the `Sym2`-quotient.  The double-image fuses via
--   `Finset.image_image` exactly as before, but the inner
--   map-composition `Sym2.map f ∘ Sym2.map g` fuses (now) to
--   `Sym2.map (f ∘ g)` via Mathlib's `Sym2.map_map`.  The
--   pointwise close uses the inline helper
--   `flatten_refactor_toCopy0_refactor_toCopy0` (verbatim port of
--   `flatten_toCopy0_toCopy0`, all branches unchanged because the
--   tagged-sum carrier `SplitNode` is structurally the
--   same as the pre-refactor `SplitNode`).
--
-- * **Inline `have`-locals match the original's style.**  Per the
--   manager.md "Net-new helpers also need REPLACEMENT markers"
--   guidance: prefer inline `have`-locals over hoisted top-level
--   declarations.  The original `twoDisjointNodeSplittingHardCommute`
--   keeps `flatten_toCopy0_toCopy0` / `flatten_toCopy1_toCopy1`
--   inline; we do the same with the `refactor_`-prefixed twins.
-- claim_3_10 -- start statement
theorem twoDisjointNodeSplittingHardCommute (G : CDMG Node)
    (hG : G.IsCADMG) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    eqViaNodeMap
        ((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
            (swigAcyclic G hG W₁ hW₁)
            (W₂.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj))
        (G.nodeSplittingHard hG (W₁ ∪ W₂)
            (Finset.union_subset hW₁ hW₂))
        flattenSplit
      ∧
    eqViaNodeMap
        ((G.nodeSplittingHard hG W₂ hW₂).nodeSplittingHard
            (swigAcyclic G hG W₂ hW₂)
            (W₁.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingHard_V hW₂ hW₁ hDisj.symm))
        (G.nodeSplittingHard hG (W₁ ∪ W₂)
            (Finset.union_subset hW₁ hW₂))
        flattenSplit
-- claim_3_10 -- end statement
  := by
  -- Inline helpers: `flattenSplit` collapses the two-stage
  -- `toCopy0` chain to the single `toCopy0 (A ∪ B)`.
  -- Verbatim port of the original `flatten_toCopy0_toCopy0` with the
  -- refactor renames.
  have flatten_refactor_toCopy0_refactor_toCopy0 :
      ∀ (A B : Finset Node) (v : Node),
        flattenSplit
            (toCopy0 (B.image SplitNode.unsplit)
              (toCopy0 A v))
          = toCopy0 (A ∪ B) v := by
    intro A B v
    unfold toCopy0
    by_cases hA : v ∈ A
    · rw [if_pos hA]
      have h_notimg : SplitNode.copy0 v ∉ B.image SplitNode.unsplit := by
        intro h
        obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
        cases hweq
      rw [if_neg h_notimg]
      change SplitNode.copy0 v
          = (if v ∈ A ∪ B then SplitNode.copy0 v
              else SplitNode.unsplit v)
      rw [if_pos (Finset.mem_union_left _ hA)]
    · rw [if_neg hA]
      by_cases hB : v ∈ B
      · have h_img : SplitNode.unsplit v ∈ B.image SplitNode.unsplit :=
          Finset.mem_image.mpr ⟨v, hB, rfl⟩
        rw [if_pos h_img]
        change SplitNode.copy0 v
            = (if v ∈ A ∪ B then SplitNode.copy0 v
                else SplitNode.unsplit v)
        rw [if_pos (Finset.mem_union_right _ hB)]
      · have h_notimg : SplitNode.unsplit v ∉ B.image SplitNode.unsplit := by
          intro h
          obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
          cases hweq
          exact hB hw
        rw [if_neg h_notimg]
        change SplitNode.unsplit v
            = (if v ∈ A ∪ B then SplitNode.copy0 v
                else SplitNode.unsplit v)
        have hVU : v ∉ A ∪ B := fun h =>
          (Finset.mem_union.mp h).elim hA hB
        rw [if_neg hVU]
  -- Symmetric helper for `toCopy1`.
  have flatten_refactor_toCopy1_refactor_toCopy1 :
      ∀ (A B : Finset Node) (v : Node),
        flattenSplit
            (toCopy1 (B.image SplitNode.unsplit)
              (toCopy1 A v))
          = toCopy1 (A ∪ B) v := by
    intro A B v
    unfold toCopy1
    by_cases hA : v ∈ A
    · rw [if_pos hA]
      have h_notimg : SplitNode.copy1 v ∉ B.image SplitNode.unsplit := by
        intro h
        obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
        cases hweq
      rw [if_neg h_notimg]
      change SplitNode.copy1 v
          = (if v ∈ A ∪ B then SplitNode.copy1 v
              else SplitNode.unsplit v)
      rw [if_pos (Finset.mem_union_left _ hA)]
    · rw [if_neg hA]
      by_cases hB : v ∈ B
      · have h_img : SplitNode.unsplit v ∈ B.image SplitNode.unsplit :=
          Finset.mem_image.mpr ⟨v, hB, rfl⟩
        rw [if_pos h_img]
        change SplitNode.copy1 v
            = (if v ∈ A ∪ B then SplitNode.copy1 v
                else SplitNode.unsplit v)
        rw [if_pos (Finset.mem_union_right _ hB)]
      · have h_notimg : SplitNode.unsplit v ∉ B.image SplitNode.unsplit := by
          intro h
          obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
          cases hweq
          exact hB hw
        rw [if_neg h_notimg]
        change SplitNode.unsplit v
            = (if v ∈ A ∪ B then SplitNode.copy1 v
                else SplitNode.unsplit v)
        have hVU : v ∉ A ∪ B := fun h =>
          (Finset.mem_union.mp h).elim hA hB
        rw [if_neg hVU]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  -- ===== Sub-goal 1: J for (a) =====
  · change ((G.J.image SplitNode.unsplit
                ∪ W₁.image SplitNode.copy1).image SplitNode.unsplit
              ∪ (W₂.image SplitNode.unsplit).image SplitNode.copy1).image
            flattenSplit
          = G.J.image SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image SplitNode.copy1
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy1 | hy2
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy1
        rcases Finset.mem_union.mp hz with hz1 | hz2
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz1
          refine Finset.mem_union_left _ ?_
          exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz2
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
      · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy2
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx1
        refine Finset.mem_image.mpr
          ⟨SplitNode.unsplit (SplitNode.unsplit j), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit j, ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · refine Finset.mem_image.mpr
            ⟨SplitNode.unsplit (SplitNode.copy1 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.copy1 w, ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · refine Finset.mem_image.mpr
            ⟨SplitNode.copy1 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 2: V for (a) =====
  · change ((((G.V \ W₁).image SplitNode.unsplit
                ∪ W₁.image SplitNode.copy0) \
              (W₂.image SplitNode.unsplit)).image SplitNode.unsplit
            ∪ (W₂.image SplitNode.unsplit).image SplitNode.copy0).image
              flattenSplit
          = (G.V \ (W₁ ∪ W₂)).image SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image SplitNode.copy0
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy1 | hy2
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy1
        obtain ⟨hz_inner, hz_notW₂img⟩ := Finset.mem_sdiff.mp hz
        rcases Finset.mem_union.mp hz_inner with hz1 | hz2
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz1
          obtain ⟨hv_V, hv_notW₁⟩ := Finset.mem_sdiff.mp hv
          have hv_notW₂ : v ∉ W₂ := fun h =>
            hz_notW₂img (Finset.mem_image.mpr ⟨v, h, rfl⟩)
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨hv_V, ?_⟩
          intro hu
          exact (Finset.mem_union.mp hu).elim hv_notW₁ hv_notW₂
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz2
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
      · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy2
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨hv_V, hv_notW₁₂⟩ := Finset.mem_sdiff.mp hv
        have hv_notW₁ : v ∉ W₁ := fun h => hv_notW₁₂ (Finset.mem_union_left _ h)
        have hv_notW₂ : v ∉ W₂ := fun h => hv_notW₁₂ (Finset.mem_union_right _ h)
        refine Finset.mem_image.mpr
          ⟨SplitNode.unsplit (SplitNode.unsplit v), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit v, ?_, rfl⟩
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · refine Finset.mem_union_left _ ?_
          exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₁⟩, rfl⟩
        · intro h
          obtain ⟨v', hv'_mem, hv'_eq⟩ := Finset.mem_image.mp h
          cases hv'_eq
          exact hv_notW₂ hv'_mem
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · refine Finset.mem_image.mpr
            ⟨SplitNode.unsplit (SplitNode.copy0 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.copy0 w, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
          · intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
        · refine Finset.mem_image.mpr
            ⟨SplitNode.copy0 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 3: E for (a) =====
  · change ((G.E.image (fun e : Node × Node =>
                (toCopy1 W₁ e.1, toCopy0 W₁ e.2))).image
              (fun e => (toCopy1 (W₂.image SplitNode.unsplit) e.1,
                         toCopy0 (W₂.image SplitNode.unsplit) e.2))).image
            (Prod.map flattenSplit flattenSplit)
          = G.E.image (fun e : Node × Node =>
              (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro e _
    change (flattenSplit
                (toCopy1 (W₂.image SplitNode.unsplit)
                  (toCopy1 W₁ e.1)),
            flattenSplit
                (toCopy0 (W₂.image SplitNode.unsplit)
                  (toCopy0 W₁ e.2)))
          = (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2)
    rw [flatten_refactor_toCopy0_refactor_toCopy0,
        flatten_refactor_toCopy1_refactor_toCopy1]
  -- ===== Sub-goal 4: L for (a) — Sym2.map rework. =====
  · change ((G.L.image (Sym2.map (toCopy0 W₁))).image
                (Sym2.map (toCopy0 (W₂.image SplitNode.unsplit)))).image
              (Sym2.map flattenSplit)
          = G.L.image (Sym2.map (toCopy0 (W₁ ∪ W₂)))
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro s _
    change Sym2.map flattenSplit
              (Sym2.map (toCopy0 (W₂.image SplitNode.unsplit))
                (Sym2.map (toCopy0 W₁) s))
          = Sym2.map (toCopy0 (W₁ ∪ W₂)) s
    rw [Sym2.map_map, Sym2.map_map]
    refine Sym2.map_congr ?_
    intro x _
    exact flatten_refactor_toCopy0_refactor_toCopy0 W₁ W₂ x
  -- ===== Sub-goal 5: J for (b) — same shape as Sub-goal 1 with W₁ ↔ W₂. =====
  · change ((G.J.image SplitNode.unsplit
                ∪ W₂.image SplitNode.copy1).image SplitNode.unsplit
              ∪ (W₁.image SplitNode.unsplit).image SplitNode.copy1).image
            flattenSplit
          = G.J.image SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image SplitNode.copy1
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy1 | hy2
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy1
        rcases Finset.mem_union.mp hz with hz1 | hz2
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz1
          refine Finset.mem_union_left _ ?_
          exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz2
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
      · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy2
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx1
        refine Finset.mem_image.mpr
          ⟨SplitNode.unsplit (SplitNode.unsplit j), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit j, ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · refine Finset.mem_image.mpr
            ⟨SplitNode.copy1 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · refine Finset.mem_image.mpr
            ⟨SplitNode.unsplit (SplitNode.copy1 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.copy1 w, ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 6: V for (b) — same shape as Sub-goal 2 with W₁ ↔ W₂. =====
  · change ((((G.V \ W₂).image SplitNode.unsplit
                ∪ W₂.image SplitNode.copy0) \
              (W₁.image SplitNode.unsplit)).image SplitNode.unsplit
            ∪ (W₁.image SplitNode.unsplit).image SplitNode.copy0).image
              flattenSplit
          = (G.V \ (W₁ ∪ W₂)).image SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image SplitNode.copy0
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy1 | hy2
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy1
        obtain ⟨hz_inner, hz_notW₁img⟩ := Finset.mem_sdiff.mp hz
        rcases Finset.mem_union.mp hz_inner with hz1 | hz2
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz1
          obtain ⟨hv_V, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
          have hv_notW₁ : v ∉ W₁ := fun h =>
            hz_notW₁img (Finset.mem_image.mpr ⟨v, h, rfl⟩)
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨hv_V, ?_⟩
          intro hu
          exact (Finset.mem_union.mp hu).elim hv_notW₁ hv_notW₂
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz2
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
      · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy2
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨hv_V, hv_notW₁₂⟩ := Finset.mem_sdiff.mp hv
        have hv_notW₁ : v ∉ W₁ := fun h => hv_notW₁₂ (Finset.mem_union_left _ h)
        have hv_notW₂ : v ∉ W₂ := fun h => hv_notW₁₂ (Finset.mem_union_right _ h)
        refine Finset.mem_image.mpr
          ⟨SplitNode.unsplit (SplitNode.unsplit v), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit v, ?_, rfl⟩
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · refine Finset.mem_union_left _ ?_
          exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₂⟩, rfl⟩
        · intro h
          obtain ⟨v', hv'_mem, hv'_eq⟩ := Finset.mem_image.mp h
          cases hv'_eq
          exact hv_notW₁ hv'_mem
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · refine Finset.mem_image.mpr
            ⟨SplitNode.copy0 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · refine Finset.mem_image.mpr
            ⟨SplitNode.unsplit (SplitNode.copy0 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.copy0 w, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
          · intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
  -- ===== Sub-goal 7: E for (b) — same shape as Sub-goal 3 with W₁ ↔ W₂. =====
  · change ((G.E.image (fun e : Node × Node =>
                (toCopy1 W₂ e.1, toCopy0 W₂ e.2))).image
              (fun e => (toCopy1 (W₁.image SplitNode.unsplit) e.1,
                         toCopy0 (W₁.image SplitNode.unsplit) e.2))).image
            (Prod.map flattenSplit flattenSplit)
          = G.E.image (fun e : Node × Node =>
              (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
    rw [Finset.union_comm W₁ W₂]
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro e _
    change (flattenSplit
                (toCopy1 (W₁.image SplitNode.unsplit)
                  (toCopy1 W₂ e.1)),
            flattenSplit
                (toCopy0 (W₁.image SplitNode.unsplit)
                  (toCopy0 W₂ e.2)))
          = (toCopy1 (W₂ ∪ W₁) e.1, toCopy0 (W₂ ∪ W₁) e.2)
    rw [flatten_refactor_toCopy0_refactor_toCopy0,
        flatten_refactor_toCopy1_refactor_toCopy1]
  -- ===== Sub-goal 8: L for (b) — Sym2.map rework with W₁ ↔ W₂. =====
  · change ((G.L.image (Sym2.map (toCopy0 W₂))).image
                (Sym2.map (toCopy0 (W₁.image SplitNode.unsplit)))).image
              (Sym2.map flattenSplit)
          = G.L.image (Sym2.map (toCopy0 (W₁ ∪ W₂)))
    rw [Finset.union_comm W₁ W₂]
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro s _
    change Sym2.map flattenSplit
              (Sym2.map (toCopy0 (W₁.image SplitNode.unsplit))
                (Sym2.map (toCopy0 W₂) s))
          = Sym2.map (toCopy0 (W₂ ∪ W₁)) s
    rw [Sym2.map_map, Sym2.map_map]
    refine Sym2.map_congr ?_
    intro x _
    exact flatten_refactor_toCopy0_refactor_toCopy0 W₂ W₁ x
-- REFACTOR-BLOCK-ORIGINAL-END: twoDisjointNodeSplittingHardCommute

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: flattenSplit_injOnHard_of_disjoint (was: refactor_flattenSplit_injOnHard_of_disjoint)
-- ## Helper: `flattenSplit` is `InjOn` on the iterated SWIG's J ∪ V
--
-- Net-new helper introduced by refactor `eqViaNodeMap_injective`
-- to discharge the strengthened predicate's `Set.InjOn` conjunct
-- for the SWIG iterated graph (sibling of
-- `refactor_flattenSplit_injOn_of_disjoint` in
-- `TwoDisjointNode.lean`, which handles the regular node-splitting
-- iterated graph for `claim_3_7`).
--
-- ### Role
--
-- Establishes `Set.InjOn flattenSplit` on the carrier set of the
-- iterated SWIG CDMG
-- `(G_{swig(W₁)})_{swig(W₂)}`, under the disjointness hypothesis
-- `Disjoint W₁ W₂`.  Every existing image-equality conjunct of
-- the original `twoDisjointNodeSplittingHardCommute` ports verbatim
-- under the new predicate; only the new InjOn conjunct requires
-- a substantively new proof, and the whole of that work is
-- concentrated here.
--
-- ### Why a separate lemma (rather than inlined in the main theorem)?
--
-- Reused twice in `refactor_twoDisjointNodeSplittingHardCommute`
-- -- once for direction (a)
-- `(G_{swig W₁})_{swig W₂} = G_{swig(W₁ ∪ W₂)}`, once for direction
-- (b) `(G_{swig W₂})_{swig W₁} = G_{swig(W₁ ∪ W₂)}` via the
-- `(W₁ ↔ W₂)` swap of the helper's arguments.  Geometrically the
-- argument is a five-cell partition of the iterated SWIG's node
-- set (`J ∪ (V \ W₁ \ W₂)` plus the four tagged copies
-- `W₁^{i_1}, W₁^{o_1}, W₂^{i_2}, W₂^{o_2}`) followed by a
-- 5 × 5 = 25 case analysis, mirroring the verified tex twin's
-- "Injectivity of the carrier bijection on the iterated SWIG's
-- node set" paragraph one-to-one.
--
-- ### SWIG-specific shape vs. claim_3_7's regular-splitting variant
--
-- Two structural differences from
-- `refactor_flattenSplit_injOn_of_disjoint`:
--
--   * **Cell layout across J/V.** Under `def_3_12` (SWIG, items
--     i. and ii.), the input-side tagged copies `W_k^{i_k}` sit
--     in `J_{swig(W_k)}` (constructor `.copy1`) while the
--     output-side copies `W_k^{o_k}` sit in `V_{swig(W_k)}`
--     (constructor `.copy0`).  Under `def_3_11` (regular
--     node-splitting), both `W_k^{0_k}` and `W_k^{1_k}` sit in
--     `V_{spl(W_k)}`.  The 5-cell partition therefore distributes
--     cells 2/4 (`W₁^{i_1}, W₂^{i_2}`) on the J-side and cells
--     3/5 (`W₁^{o_1}, W₂^{o_2}`) on the V-side here, whereas
--     claim_3_7's regular-splitting partition keeps all four
--     tagged cells on the V-side.
--   * **Two-piece V-branch sdiff.** The inner SWIG's V-side has
--     just two image pieces (`(G.V \ W₁).image .unsplit` and
--     `W₁.image .copy0` -- `.copy1` lives on the J-side here),
--     one fewer than the regular splitting's three.  The
--     subsequent sdiff against `W₂.image .unsplit` acts on the
--     smaller piece, and the V-branch classification yields three
--     resulting forms (cell 1's V-part, `W₁^{o_1}`, `W₂^{o_2}`)
--     versus claim_3_7's four.
--
-- The closing `first | ... | ... | ... | cases heq` block is
-- structurally identical to claim_3_7's: the abstract pattern of
-- five same-form, four cross-W same-image, and sixteen
-- cross-constructor sub-cases is preserved (the cell shuffling
-- between J/V doesn't change which pairs collide under
-- `flattenSplit`'s image).
--
-- ### Why `Set.InjOn` on `↑(...).J ∪ ↑(...).V` (matching the predicate's carrier set verbatim)?
--
-- Pasted directly from `refactor_eqViaNodeMap`'s first-conjunct
-- shape so that the consumer call site in the main theorem can
-- plug this lemma in with no Set-arithmetic glue.  The
-- iterated-SWIG operand is the same one that appears on the
-- left of `refactor_eqViaNodeMap` in the main theorem statement,
-- so the carrier sets line up definitionally.
--
-- ### Why disjointness is load-bearing
--
-- `flattenSplit` is NOT globally injective on
-- `SplitNode (SplitNode Node)`.  The five-cell partition rules
-- out most would-be collisions structurally, but two cross-cell
-- patterns survive structural filtering and need the disjointness
-- hypothesis to close: the `^{i_1}`-vs-`^{i_2}` cross-collision
-- `W₁^{i_1}` vs. `W₂^{i_2}` (which would force
-- `w₁ = w₂ ∈ W₁ ∩ W₂`) and the symmetric `^{o_1}`-vs-`^{o_2}`
-- pattern.  The `Disjoint W₁ W₂` hypothesis is consumed exactly
-- in those two of the 25 subcases, matching the "load-bearing
-- use of the disjointness hypothesis `W₁ ∩ W₂ = ∅`" call-out in
-- the verified tex twin's across-cell injectivity paragraph.
private lemma refactor_flattenSplit_injOnHard_of_disjoint
    (G : CDMG Node) (hG : G.IsCADMG) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    Set.InjOn flattenSplit
        ((↑((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
              (swigAcyclic G hG W₁ hW₁)
              (W₂.image SplitNode.unsplit)
              (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj)).J :
            Set (SplitNode (SplitNode Node))) ∪
          ↑((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
              (swigAcyclic G hG W₁ hW₁)
              (W₂.image SplitNode.unsplit)
              (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj)).V) := by
  -- Classification: every element `z` of the iterated SWIG's
  -- `J ∪ V` (as Finsets) is in exactly one of 5 disjoint forms.
  -- Cells 2 (W₁^{i_1}) and 4 (W₂^{i_2}) sit on the J-side
  -- (the input-tagged copies); cells 3 (W₁^{o_1}) and 5
  -- (W₂^{o_2}) sit on the V-side (the output-tagged copies);
  -- cell 1 (untagged J ∪ (V \ W₁ \ W₂)) spans both J and V.
  have classify : ∀ z : SplitNode (SplitNode Node),
      z ∈ ((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
              (swigAcyclic G hG W₁ hW₁)
              (W₂.image SplitNode.unsplit)
              (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj)).J ∪
          ((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
              (swigAcyclic G hG W₁ hW₁)
              (W₂.image SplitNode.unsplit)
              (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj)).V →
      (∃ a : Node,
          ((a ∈ G.J) ∨ (a ∈ G.V ∧ a ∉ W₁ ∧ a ∉ W₂)) ∧
              z = SplitNode.unsplit (SplitNode.unsplit a))
        ∨ (∃ w : Node, w ∈ W₁ ∧
              z = SplitNode.unsplit (SplitNode.copy1 w))
        ∨ (∃ w : Node, w ∈ W₁ ∧
              z = SplitNode.unsplit (SplitNode.copy0 w))
        ∨ (∃ w : Node, w ∈ W₂ ∧
              z = SplitNode.copy1 (SplitNode.unsplit w))
        ∨ (∃ w : Node, w ∈ W₂ ∧
              z = SplitNode.copy0 (SplitNode.unsplit w)) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hJ | hV
    · -- z ∈ iterated SWIG's J = (inner.J).image .unsplit ∪
      --   (W₂.image .unsplit).image .copy1; inner.J unfolds to
      --   G.J.image .unsplit ∪ W₁.image .copy1.
      change z ∈ (G.J.image SplitNode.unsplit
                    ∪ W₁.image SplitNode.copy1).image SplitNode.unsplit ∪
                  (W₂.image SplitNode.unsplit).image SplitNode.copy1 at hJ
      rcases Finset.mem_union.mp hJ with hJ12 | hJ3
      · -- outer .unsplit piece: z = .unsplit y, y ∈ inner.J
        obtain ⟨y, hy_in, rfl⟩ := Finset.mem_image.mp hJ12
        rcases Finset.mem_union.mp hy_in with hJ1 | hJ2
        · -- y = .unsplit j, j ∈ G.J → cell 1 (J-part)
          obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hJ1
          exact Or.inl ⟨j, Or.inl hjJ, rfl⟩
        · -- y = .copy1 w, w ∈ W₁ → cell 2 (W₁^{i_1}, J-side)
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hJ2
          exact Or.inr (Or.inl ⟨w, hw, rfl⟩)
      · -- outer .copy1 piece: z = .copy1 (.unsplit w), w ∈ W₂
        -- → cell 4 (W₂^{i_2}, J-side)
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hJ3
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨w, hw, rfl⟩)))
    · -- z ∈ iterated SWIG's V
      change z ∈ (((G.V \ W₁).image SplitNode.unsplit ∪
                      W₁.image SplitNode.copy0) \
                    (W₂.image SplitNode.unsplit)).image SplitNode.unsplit ∪
                  (W₂.image SplitNode.unsplit).image SplitNode.copy0 at hV
      rcases Finset.mem_union.mp hV with hV12 | hV3
      · -- outer .unsplit branch
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hV12
        obtain ⟨hy_in, hy_notW₂img⟩ := Finset.mem_sdiff.mp hy
        rcases Finset.mem_union.mp hy_in with hV1 | hV2
        · -- y = .unsplit v, v ∈ G.V \ W₁, v ∉ W₂ → cell 1 (V-part)
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hV1
          obtain ⟨hv_V, hv_notW₁⟩ := Finset.mem_sdiff.mp hv
          have hv_notW₂ : v ∉ W₂ := fun h =>
            hy_notW₂img (Finset.mem_image.mpr ⟨v, h, rfl⟩)
          exact Or.inl ⟨v, Or.inr ⟨hv_V, hv_notW₁, hv_notW₂⟩, rfl⟩
        · -- y = .copy0 w, w ∈ W₁ → cell 3 (W₁^{o_1}, V-side)
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hV2
          exact Or.inr (Or.inr (Or.inl ⟨w, hw, rfl⟩))
      · -- outer .copy0 piece: z = .copy0 (.unsplit w), w ∈ W₂
        -- → cell 5 (W₂^{o_2}, V-side)
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hV3
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hw, rfl⟩)))
  -- Main InjOn argument.
  intro x hx y hy heq
  -- Convert hx, hy from Set membership to Finset disjunction-then-union.
  have hx' : x ∈ ((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
                    (swigAcyclic G hG W₁ hW₁)
                    (W₂.image SplitNode.unsplit)
                    (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj)).J ∪
              ((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
                    (swigAcyclic G hG W₁ hW₁)
                    (W₂.image SplitNode.unsplit)
                    (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj)).V := by
    rcases hx with h | h
    · exact Finset.mem_union_left _ (Finset.mem_coe.mp h)
    · exact Finset.mem_union_right _ (Finset.mem_coe.mp h)
  have hy' : y ∈ ((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
                    (swigAcyclic G hG W₁ hW₁)
                    (W₂.image SplitNode.unsplit)
                    (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj)).J ∪
              ((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
                    (swigAcyclic G hG W₁ hW₁)
                    (W₂.image SplitNode.unsplit)
                    (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj)).V := by
    rcases hy with h | h
    · exact Finset.mem_union_left _ (Finset.mem_coe.mp h)
    · exact Finset.mem_union_right _ (Finset.mem_coe.mp h)
  -- Classify x and y into one of 5 patterns each (5 × 5 = 25 subcases).
  rcases classify x hx' with
    ⟨xa, _, rfl⟩ | ⟨xw, hxw, rfl⟩ | ⟨xw, hxw, rfl⟩ | ⟨xw, hxw, rfl⟩ | ⟨xw, hxw, rfl⟩ <;>
  rcases classify y hy' with
    ⟨ya, _, rfl⟩ | ⟨yw, hyw, rfl⟩ | ⟨yw, hyw, rfl⟩ | ⟨yw, hyw, rfl⟩ | ⟨yw, hyw, rfl⟩ <;>
  -- Reduce flattenSplit applied to each specific pattern.  Each
  -- of the 25 cases now has heq of the form
  -- `<constructor> <var> = <constructor> <var>` after definitional
  -- unfolding; close by cases (constructor mismatch) or by
  -- injection-then-disjointness contradiction.
  first
  -- Same-form cases (5): (X1,Y1), (X2,Y2), (X3,Y3), (X4,Y4), (X5,Y5).
  -- Inject the underlying equality on the inner var, subst, rfl.
  | (injection heq with h; subst h; rfl)
  -- Cross-W cases where both flatten outputs use .copy1 or .copy0
  -- (4): (X2,Y4), (X4,Y2), (X3,Y5), (X5,Y3).
  -- After injection on .copy1 / .copy0, we get xw = yw.  But xw
  -- and yw straddle W₁ / W₂; disjointness gives the contradiction.
  | (injection heq with h; subst h;
     exact absurd hyw (Finset.disjoint_left.mp hDisj hxw))
  | (injection heq with h; subst h;
     exact absurd hxw (Finset.disjoint_left.mp hDisj hyw))
  -- Cross-constructor cases (16): heq is .C₁ _ = .C₂ _ with C₁ ≠ C₂.
  -- `cases heq` closes by no-confusion.
  | cases heq
-- REFACTOR-BLOCK-REPLACEMENT-END: flattenSplit_injOnHard_of_disjoint

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: twoDisjointNodeSplittingHardCommute (was: refactor_twoDisjointNodeSplittingHardCommute)
-- ref: claim_3_10
--
-- ## Refactor: `refactor_twoDisjointNodeSplittingHardCommute`
--
-- Refactor of `twoDisjointNodeSplittingHardCommute` for refactor
-- `eqViaNodeMap_injective`.  SWIG analogue of claim_3_7's
-- `refactor_twoDisjointNodeSplittingsCommute`.  Same conjunction
-- `(a) ∧ (b)` shape as the original (two `eqViaNodeMap` equalities
-- through the shared joint SWIG `G_{swig(W₁ ∪ W₂)}`), but the
-- predicate `eqViaNodeMap` is replaced by the strengthened
-- `refactor_eqViaNodeMap` (carrying a fifth `Set.InjOn` conjunct
-- on the carrier map `flattenSplit`).
--
-- ### What's reused from the original
--
-- The four image-equality conjuncts (`J`, `V`, `E`, `L`) come
-- straight from the existing (unchanged)
-- `twoDisjointNodeSplittingHardCommute` via the destructuring
-- binder in the opening `obtain ⟨⟨hJa, hVa, hEa, hLa⟩, ⟨hJb,
-- hVb, hEb, hLb⟩⟩ := ...` line.  The refactor does NOT redo the
-- ~450-line J/V/E/L bookkeeping -- it would produce a bit-for-bit
-- identical tactic block, so reusing the original keeps the
-- LN-to-Lean correspondence one-to-one and the file size
-- manageable.  The new content is purely the InjOn discharge
-- (the two `refine` underscores below the destructure).
--
-- ### Why the InjOn discharge is non-trivial
--
-- The carrier map `flattenSplit` is not globally injective: it
-- collapses off-iterated-graph constructor patterns (see the
-- comment block above
-- `refactor_flattenSplit_injOnHard_of_disjoint`).  The witnessing
-- InjOn property holds only on the iterated SWIG's `J ∪ V`, and
-- only because the disjointness hypothesis `Disjoint W₁ W₂` rules
-- out the two would-be cross-cell collisions (`W₁^{i_1}` vs.
-- `W₂^{i_2}` and `W₁^{o_1}` vs. `W₂^{o_2}`).  Without
-- disjointness the InjOn conjunct fails, and so does the LN's
-- claim "the iterated CDMG equals the single-step CDMG
-- `G_{swig(W₁ ∪ W₂)}`" -- two SWIG-copies of a node in
-- `W₁ ∩ W₂` would collide in the iterated graph in a way the
-- single-step graph cannot reproduce.
--
-- ### How disjointness flows in (both orderings)
--
-- The technical core is the helper
-- `refactor_flattenSplit_injOnHard_of_disjoint` above, invoked
-- twice:
--   * Direction (a)
--     `(G_{swig W₁})_{swig W₂} = G_{swig(W₁ ∪ W₂)}`: helper
--     applied with `(W₁, W₂, hDisj)` in the natural order.
--   * Direction (b)
--     `(G_{swig W₂})_{swig W₁} = G_{swig(W₁ ∪ W₂)}`: helper
--     applied with `(W₂, W₁, hDisj.symm)` -- the iterated SWIG
--     in the InjOn obligation swaps inner/outer roles of `W₁`
--     and `W₂`, and `Disjoint` is symmetric.
-- Both directions land at the same single-step right-hand side
-- `G_{swig(W₁ ∪ W₂)}`, recovering the LN's triple-equality
-- "swap-symmetry" reading via transitivity, exactly as in the
-- verified tex twin's "Recovery of the LN's triple equality"
-- closing paragraph.
-- claim_3_10 -- start statement
theorem refactor_twoDisjointNodeSplittingHardCommute (G : CDMG Node)
    (hG : G.IsCADMG) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    refactor_eqViaNodeMap
        ((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
            (swigAcyclic G hG W₁ hW₁)
            (W₂.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj))
        (G.nodeSplittingHard hG (W₁ ∪ W₂)
            (Finset.union_subset hW₁ hW₂))
        flattenSplit
      ∧
    refactor_eqViaNodeMap
        ((G.nodeSplittingHard hG W₂ hW₂).nodeSplittingHard
            (swigAcyclic G hG W₂ hW₂)
            (W₁.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingHard_V hW₂ hW₁ hDisj.symm))
        (G.nodeSplittingHard hG (W₁ ∪ W₂)
            (Finset.union_subset hW₁ hW₂))
        flattenSplit
-- claim_3_10 -- end statement
  := by
  -- Reuse the original theorem for the four image-equality
  -- conjuncts (J, V, E, L) in each of the two directions.
  obtain ⟨⟨hJa, hVa, hEa, hLa⟩, ⟨hJb, hVb, hEb, hLb⟩⟩ :=
    twoDisjointNodeSplittingHardCommute G hG W₁ W₂ hW₁ hW₂ hDisj
  refine ⟨⟨?_, hJa, hVa, hEa, hLa⟩, ⟨?_, hJb, hVb, hEb, hLb⟩⟩
  · -- InjOn for direction (a): iterated SWIG W₁ then W₂
    exact refactor_flattenSplit_injOnHard_of_disjoint G hG W₁ W₂ hW₁ hW₂ hDisj
  · -- InjOn for direction (b): iterated SWIG W₂ then W₁
    exact refactor_flattenSplit_injOnHard_of_disjoint G hG W₂ W₁ hW₂ hW₁ hDisj.symm
-- REFACTOR-BLOCK-REPLACEMENT-END: twoDisjointNodeSplittingHardCommute

end CDMG

end Causality
