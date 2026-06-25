import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn

namespace Causality

/-!
# Two disjoint node-splittings commute (`claim_3_7`)

This file formalises the LN lemma `claim_3_7` (`TwoDisjointNode`) in
section 3.2 of `graphs.tex`:

> Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ V` two disjoint subsets
> of the output nodes.  Then
> `(G_{spl(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{spl(W₁)} = G_{spl(W₁ ∪ W₂)}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_7_statement_TwoDisjointNode.tex`,
verified equivalent to the LN block plus the `cdmg_vs_cadmg_terminology_mismatch`
addition_to_the_LN (which corrects the LN's mid-sentence "CADMG" typo to
"CDMG": `nodeSplittingOn` is `CDMG → CDMG` and the asserted equality is
an equality of CDMGs).

The rewritten tex decomposes the LN's triple equality into the
conjunction of two binary equalities, matching the `claim_3_4`
(`HardInterventionsCommute`) pattern:

* (a) `(G_{spl(W₁)})_{spl(W₂)} = G_{spl(W₁ ∪ W₂)}`
* (b) `(G_{spl(W₂)})_{spl(W₁)} = G_{spl(W₁ ∪ W₂)}`

Transitivity of equality recovers the LN's "swap symmetry" reading
`(G_{spl(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{spl(W₁)}` from (a) ∧ (b).

## Carrier-mismatch wrinkle (load-bearing for this row's Lean signature)

`def_3_11`'s `nodeSplittingOn` changes the node carrier
(`CDMG α → CDMG (SplitNode α)`), so the iterated splitting
`(G.nodeSplittingOn W₁ _).nodeSplittingOn (W₂.image .unsplit) _` lives
in `CDMG (SplitNode (SplitNode Node))` — a formally distinct type from
the single splitting `G.nodeSplittingOn (W₁ ∪ W₂) _ : CDMG (SplitNode
Node)`.  The LN identifies the two carriers set-theoretically via
`def_3_11`'s unsplit-injection convention "`v⁰ := v¹ := v` for
`v ∈ J ∪ (V ∖ W)`"; the rewritten tex's "Equality up to the canonical
bijection of carriers" paragraph spells this out.  This Lean rendering
captures the identification via the canonical flatten function
`flattenSplit : SplitNode (SplitNode Node) → SplitNode Node` (defined
below); the LN's "equality of CDMGs" reading becomes "the four `Finset`
data fields of the iterated splitting, after applying `flattenSplit`
field-wise, coincide with the four `Finset` data fields of the single
splitting", packaged as the helper predicate `eqViaNodeMap`.

This row is the first in chapter 3 hitting the carrier-mismatch
wrinkle (`nodeSplittingOn` changing the node type from `α` to
`SplitNode α`).  The same `flattenSplit` / `eqViaNodeMap` encoding
pattern extends to any chapter row that iterates node-splitting or
composes node-splitting with hard intervention.

The body is filled in by `prove_claim_in_lean` (Manager B), following
the to-be-written tex proof at
`tex/claim_3_7_proof_TwoDisjointNode.tex`.
-/

namespace CDMG

-- ## Refactor port — REPLACEMENT blocks for the `cdmg_typed_edges` design
--
-- The five `REFACTOR-BLOCK-REPLACEMENT` blocks below port the
-- pre-refactor declarations in this file to the post-refactor
-- `def_3_1` / `def_3_11` shapes (`CDMG` with
-- `L : Finset (Sym2 Node)`; `nodeSplittingOn` with
-- `L := G.L.image (Sym2.map (toCopy0 W))`).  Each block
-- mirrors its ORIGINAL above with the prefix `refactor_` and the
-- type / operation substitutions:
--
--   * `CDMG → CDMG`
--   * `SplitNode → SplitNode`
--   * `toCopy0 / toCopy1 → toCopy0 / toCopy1`
--   * `nodeSplittingOn → nodeSplittingOn`
--   * `flattenSplit / eqViaNodeMap / image_unsplit_subset_…` →
--     same with the `refactor_` prefix
--
-- The J/V/E sides of the main theorem port mechanically — same
-- tactics, just renames.  Only the L-side (sub-goals 4 and 8) is
-- structurally reworked, because `L`'s storage changed from
-- ordered pairs (`Prod.map f f`) to `Sym2`-quotient
-- unordered pairs (`Sym2.map f`).  The rework uses Mathlib's
-- `Sym2.map_map` (`Sym2.map g (Sym2.map f x) = Sym2.map (g ∘ f) x`)
-- to fuse the two-stage tagged-sum lift back into a single-stage
-- one, then closes pointwise via `Sym2.map_congr` and the inline
-- `flatten_refactor_toCopy0_refactor_toCopy0` helper (verbatim port
-- of the original `flatten_toCopy0_toCopy0`).

-- claim_3_7 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_7 --- end helper

-- ## Helper: flatten map (refactor)
--
-- Refactor port of `flattenSplit` for the `cdmg_typed_edges`
-- design.  Structurally identical to the pre-refactor
-- `flattenSplit`; only the carrier `SplitNode` is replaced by
-- `SplitNode` throughout the pattern match.  The seven
-- case clauses are unchanged because `SplitNode`
-- (`def_3_11` post-refactor) has the same three named constructors
-- `unsplit / copy0 / copy1` as the pre-refactor `SplitNode` — the
-- refactor changes only the L-side of `def_3_1` / `def_3_11`, not
-- the tagged-sum carrier of the split-graph node universe.
-- See the design block above the original `flattenSplit` for the
-- substantive design rationale (function-not-`Equiv`, total
-- pattern match including off-carrier cases, symmetric in
-- `W₁` / `W₂` for both iteration orders).  Nothing about the
-- encoding choice changes under the refactor.
-- claim_3_7 --- start helper
def flattenSplit :
    SplitNode (SplitNode Node) → SplitNode Node
  | .unsplit x => x
  | .copy0 (.unsplit w) => SplitNode.copy0 w
  | .copy0 (.copy0 w) => SplitNode.copy0 w
  | .copy0 (.copy1 w) => SplitNode.copy1 w
  | .copy1 (.unsplit w) => SplitNode.copy1 w
  | .copy1 (.copy0 w) => SplitNode.copy0 w
  | .copy1 (.copy1 w) => SplitNode.copy1 w
-- claim_3_7 --- end helper

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: eqViaNodeMap
-- ## Helper: `eqViaNodeMap` (refactor)
--
-- Refactor port of `eqViaNodeMap` for the `cdmg_typed_edges`
-- design.  Same 4-conjunct shape, but the L-conjunct uses
-- `Sym2.map f` instead of `Prod.map f f`: under the post-refactor
-- `def_3_1` shape `L : Finset (Sym2 Node)`, the per-element lift
-- along `f : α → β` is `Sym2.map f : Sym2 α → Sym2 β` (the action
-- of `f` on the `Sym2`-quotient `(Node × Node) / swap`), not the
-- Cartesian `Prod.map f f`.
--
-- See the design block above the original `eqViaNodeMap` for the
-- substantive design rationale (`Prop`-valued helper, four
-- conjuncts mirroring `CDMG`'s four data fields, image-level
-- reading of the LN's "equality up to the canonical bijection of
-- carriers").  Only the L-conjunct's typing changes; the
-- conjunctive shape, the use of `Finset.image` over four data
-- fields, and the design choice against bundling a transported
-- CDMG are unchanged.
-- claim_3_7 --- start helper
def eqViaNodeMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : CDMG α) (G' : CDMG β) (f : α → β) : Prop :=
  G.J.image f = G'.J
    ∧ G.V.image f = G'.V
    ∧ G.E.image (Prod.map f f) = G'.E
    ∧ G.L.image (Sym2.map f) = G'.L
-- claim_3_7 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: eqViaNodeMap

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: eqViaNodeMap (was: refactor_eqViaNodeMap)
-- ## Helper: `refactor_eqViaNodeMap` -- strengthened with `Set.InjOn`
--
-- Refactor of `eqViaNodeMap` for refactor `eqViaNodeMap_injective`
-- (plan: `leanification/refactors/refactor_eqViaNodeMap_injective.md`).
--
-- ### Why a 5th conjunct?
--
-- The original 4-conjunct predicate (image equality on `J`, `V`,
-- `E`, `L`) is too weak: `f : α → β` is unconstrained, so a
-- many-to-one `f` that collapses distinct G-nodes onto the same
-- G'-node can satisfy all four image-equality conjuncts (the
-- images are *sets*, not multisets, so `Finset.image` drops
-- duplicates) -- and yet G and G' are NOT isomorphic as CDMGs.
-- A concrete counter-witness (refactor plan §"Concrete
-- counter-witness"): `G : CDMG (Fin 3)` with 3 nodes and a
-- 2-node-image-collapse `f`, against `G' : CDMG (Fin 2)` -- all
-- four image-equality conjuncts hold, but the CDMGs have
-- different node counts. Without the injectivity conjunct the
-- predicate "G and G' are equal up to the carrier bijection `f`"
-- silently degenerates to "G and G' are equal up to *some*
-- many-to-one `f`-image", which is a much weaker claim that
-- downstream consumers (`claim_3_8`, `claim_3_10/11/14/15/18/19`)
-- cannot reason about node-count preservation or fibre structure
-- from. The new InjOn conjunct rules out such collapsing and
-- restores the predicate's intended "equal up to renaming"
-- reading.
--
-- ### Why `Set.InjOn f (↑G.J ∪ ↑G.V)` and not `Function.Injective f`?
--
-- `f : α → β` may be arbitrary off the carrier set; the LN's
-- notion of "equivalence up to canonical carrier bijection" only
-- depends on what `f` does on the actual nodes of `G`. Several
-- consumer flatten maps (`flattenSplit` here, `flattenIntExt` in
-- `claim_3_14`, etc.) are NOT globally injective -- they collapse
-- off-graph constructor patterns -- but ARE injective on the
-- iterated graph's node set under the per-row disjointness side
-- condition. Requiring `Function.Injective f` would force every
-- consumer to prove a stronger (and false) global statement;
-- `Set.InjOn f (↑G.J ∪ ↑G.V)` is the *minimum* content needed:
-- distinct G-nodes (in `J` or `V`) map to distinct G'-nodes.
-- E and L endpoints are constrained to `J ∪ V` by `def_3_1`'s
-- subset axioms (`hE_subset : G.E ⊆ G.J ×ˢ G.V` and the
-- analogous `hL_subset` on `L`'s `Sym2`-quotient endpoints), so
-- injectivity on `J ∪ V` automatically preserves E and L
-- cardinalities and distinctness when transported via `f`. The
-- carrier set `↑G.J ∪ ↑G.V` is thus correct and minimal.
--
-- ### Why FIRST conjunct?
--
-- Logical priority: a future proof reading the predicate sees the
-- strong structural constraint up front; downstream extractors
-- (e.g. for `Set.InjOn`-on-subsets via `Set.InjOn.mono`) can
-- pattern-match `.1` instead of digging through the four
-- image-equality fields. This ordering also matches the verified
-- tex twin's narrative -- the "Injectivity of the carrier
-- bijection" paragraph in `tex/refactor_claim_3_7_proof_TwoDisjointNode.tex`
-- caps the componentwise verification before the "Combining ..."
-- closing -- so reading order in Lean tracks reading order in
-- the proof prose.
--
-- The four image-equality conjuncts are unchanged from the
-- original. The Set coercions `↑G.J` and `↑G.V` are `Finset.coe`
-- into `Set α`; `↑G.J ∪ ↑G.V` is the Set union (definitionally
-- equal to `↑(G.J ∪ G.V)` by `Finset.coe_union`).
-- claim_3_7 --- start helper
def refactor_eqViaNodeMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : CDMG α) (G' : CDMG β) (f : α → β) : Prop :=
  Set.InjOn f ((↑G.J : Set α) ∪ ↑G.V)
    ∧ G.J.image f = G'.J
    ∧ G.V.image f = G'.V
    ∧ G.E.image (Prod.map f f) = G'.E
    ∧ G.L.image (Sym2.map f) = G'.L
-- claim_3_7 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: eqViaNodeMap

-- ## Helper: well-typedness of the iterated splitting (refactor)
--
-- Refactor port of `image_unsplit_subset_nodeSplittingOn_V` for
-- the `cdmg_typed_edges` design.  Statement and proof are
-- structurally identical to the original; only the type carrier
-- (`CDMG → CDMG`), the splitting operation
-- (`nodeSplittingOn → nodeSplittingOn`), and the
-- unsplit-injection constructor
-- (`SplitNode.unsplit → SplitNode.unsplit`) change.  The
-- proof body uses the same `Finset.mem_sdiff` /
-- `Finset.disjoint_right` machinery — the V-side of
-- `nodeSplittingOn` is structurally identical to the
-- pre-refactor `nodeSplittingOn`'s V-side, so the lemma carries
-- over verbatim with only the rename pass.
-- claim_3_7 --- start helper
private lemma image_unsplit_subset_nodeSplittingOn_V
    {G : CDMG Node} {W₁ W₂ : Finset Node} (hW₁ : W₁ ⊆ G.V)
    (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂.image SplitNode.unsplit ⊆ (G.nodeSplittingOn W₁ hW₁).V
-- claim_3_7 --- end helper
:= by
  intro x hx
  obtain ⟨v, hvW₂, rfl⟩ := Finset.mem_image.mp hx
  -- `(G.nodeSplittingOn W₁ hW₁).V` unfolds to
  --   `(G.V ∖ W₁).image .unsplit ∪ W₁.image .copy0 ∪ W₁.image .copy1`.
  -- `v ∈ W₂` with `Disjoint W₁ W₂` gives `v ∈ G.V ∖ W₁`, hence
  -- `.unsplit v ∈ (G.V ∖ W₁).image .unsplit`.
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
  exact Finset.mem_sdiff.mpr ⟨hW₂ hvW₂, Finset.disjoint_right.mp hDisj hvW₂⟩

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: twoDisjointNodeSplittingsCommute
-- ref: claim_3_7
--
-- Refactor port of `twoDisjointNodeSplittingsCommute` for the
-- `cdmg_typed_edges` design.  Same statement structure as the
-- original — a conjunction `(a) ∧ (b)` of two
-- `eqViaNodeMap` equalities through the shared joint
-- intervention `G_{spl(W₁ ∪ W₂)}` — and the same eight
-- sub-goals (J, V, E, L for each iteration order).
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
--   `nodeSplittingOn`'s J / V / E fields are unchanged
--   from `nodeSplittingOn`'s (the refactor changes only the L
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
--   `Sym2.map (f ∘ g)` via Mathlib's `Sym2.map_map`
--   (`Sym2.map g (Sym2.map f x) = Sym2.map (g ∘ f) x`).  The
--   pointwise close uses the inline helper
--   `flatten_refactor_toCopy0_refactor_toCopy0` (verbatim port of
--   `flatten_toCopy0_toCopy0`, all branches unchanged because the
--   tagged-sum carrier `SplitNode` is structurally the
--   same as the pre-refactor `SplitNode`).
--
-- * **Inline `have`-locals match the original's style.**  Per the
--   manager.md "Net-new helpers also need REPLACEMENT markers"
--   guidance: prefer inline `have`-locals over hoisted top-level
--   declarations.  The original `twoDisjointNodeSplittingsCommute`
--   keeps `flatten_toCopy0_toCopy0` / `flatten_toCopy1_toCopy1`
--   inline; we do the same with the `refactor_`-prefixed twins.
-- claim_3_7 -- start statement
theorem twoDisjointNodeSplittingsCommute (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    eqViaNodeMap
        ((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
            (W₂.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj))
        (G.nodeSplittingOn (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenSplit
      ∧
    eqViaNodeMap
        ((G.nodeSplittingOn W₂ hW₂).nodeSplittingOn
            (W₁.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingOn_V hW₂ hW₁ hDisj.symm))
        (G.nodeSplittingOn (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenSplit
-- claim_3_7 -- end statement
  := by
  -- Inline helpers: `flattenSplit` collapses the two-stage
  -- `toCopy0` chain to the single `toCopy0 (A ∪ B)`.
  -- Verbatim port of the original `flatten_toCopy0_toCopy0` with the
  -- refactor renames; the proof case-splits on `v ∈ A` / `v ∈ B` and
  -- uses constructor mismatch to discharge each branch.
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
  -- ===== Sub-goal 1: J for (a) — port mechanically. =====
  · change ((G.J.image SplitNode.unsplit).image
                SplitNode.unsplit).image flattenSplit
          = G.J.image SplitNode.unsplit
    rw [Finset.image_image, Finset.image_image]
    rfl
  -- ===== Sub-goal 2: V for (a) — port mechanically. =====
  · change ((((G.V \ W₁).image SplitNode.unsplit
                ∪ W₁.image SplitNode.copy0 ∪ W₁.image SplitNode.copy1)
              \ (W₂.image SplitNode.unsplit)).image SplitNode.unsplit
            ∪ (W₂.image SplitNode.unsplit).image SplitNode.copy0
            ∪ (W₂.image SplitNode.unsplit).image SplitNode.copy1).image
              flattenSplit
          = (G.V \ (W₁ ∪ W₂)).image SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image SplitNode.copy0
            ∪ (W₁ ∪ W₂).image SplitNode.copy1
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy12 | hy3
      · rcases Finset.mem_union.mp hy12 with hy1 | hy2
        · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy1
          obtain ⟨hz_inner, hz_notW₂img⟩ := Finset.mem_sdiff.mp hz
          rcases Finset.mem_union.mp hz_inner with hz12 | hz3
          · rcases Finset.mem_union.mp hz12 with hz1 | hz2
            · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz1
              obtain ⟨hv_V, hv_notW₁⟩ := Finset.mem_sdiff.mp hv
              have hv_notW₂ : v ∉ W₂ := fun h =>
                hz_notW₂img (Finset.mem_image.mpr ⟨v, h, rfl⟩)
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
              refine Finset.mem_sdiff.mpr ⟨hv_V, ?_⟩
              intro hu
              exact (Finset.mem_union.mp hu).elim hv_notW₁ hv_notW₂
            · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz2
              refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
          · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz3
            refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
        · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy2
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
      · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy3
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hx12 | hx3
      · rcases Finset.mem_union.mp hx12 with hx1 | hx2
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
          obtain ⟨hv_V, hv_notW₁₂⟩ := Finset.mem_sdiff.mp hv
          have hv_notW₁ : v ∉ W₁ := fun h => hv_notW₁₂ (Finset.mem_union_left _ h)
          have hv_notW₂ : v ∉ W₂ := fun h => hv_notW₁₂ (Finset.mem_union_right _ h)
          refine Finset.mem_image.mpr
            ⟨SplitNode.unsplit (SplitNode.unsplit v), ?_, rfl⟩
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit v, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₁⟩, rfl⟩
          · intro h
            obtain ⟨v', hv'_mem, hv'_eq⟩ := Finset.mem_image.mp h
            cases hv'_eq
            exact hv_notW₂ hv'_mem
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
          rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
          · refine Finset.mem_image.mpr
              ⟨SplitNode.unsplit (SplitNode.copy0 w), ?_, rfl⟩
            refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            refine Finset.mem_image.mpr ⟨SplitNode.copy0 w, ?_, rfl⟩
            refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
            · intro h
              obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
              cases hweq
          · refine Finset.mem_image.mpr
              ⟨SplitNode.copy0 (SplitNode.unsplit w), ?_, rfl⟩
            refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
            exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx3
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · refine Finset.mem_image.mpr
            ⟨SplitNode.unsplit (SplitNode.copy1 w), ?_, rfl⟩
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          refine Finset.mem_image.mpr ⟨SplitNode.copy1 w, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
          · intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
        · refine Finset.mem_image.mpr
            ⟨SplitNode.copy1 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 3: E for (a) — port mechanically. =====
  · have hG_E :
        ((G.E.image (fun e : Node × Node =>
              (toCopy1 W₁ e.1, toCopy0 W₁ e.2))).image
            (fun e => (toCopy1 (W₂.image SplitNode.unsplit) e.1,
                       toCopy0 (W₂.image SplitNode.unsplit) e.2))).image
          (Prod.map flattenSplit flattenSplit)
        = G.E.image (fun e : Node × Node =>
            (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2)) := by
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
    have hW₁_tr :
        ((W₁.image (fun w : Node =>
              (SplitNode.copy0 w, SplitNode.copy1 w))).image
            (fun e => (toCopy1 (W₂.image SplitNode.unsplit) e.1,
                       toCopy0 (W₂.image SplitNode.unsplit) e.2))).image
          (Prod.map flattenSplit flattenSplit)
        = W₁.image (fun w : Node =>
            (SplitNode.copy0 w, SplitNode.copy1 w)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr ?_
      intro w _
      change (flattenSplit
                  (toCopy1 (W₂.image SplitNode.unsplit)
                    (SplitNode.copy0 w)),
              flattenSplit
                  (toCopy0 (W₂.image SplitNode.unsplit)
                    (SplitNode.copy1 w)))
            = (SplitNode.copy0 w, SplitNode.copy1 w)
      have h1 : SplitNode.copy0 w ∉ W₂.image SplitNode.unsplit := by
        intro h; obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h; cases hweq
      have h2 : SplitNode.copy1 w ∉ W₂.image SplitNode.unsplit := by
        intro h; obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h; cases hweq
      unfold toCopy0 toCopy1
      rw [if_neg h1, if_neg h2]
      rfl
    have hW₂_tr :
        ((W₂.image SplitNode.unsplit).image
            (fun w : SplitNode Node =>
              (SplitNode.copy0 w, SplitNode.copy1 w))).image
          (Prod.map flattenSplit flattenSplit)
        = W₂.image (fun w : Node =>
            (SplitNode.copy0 w, SplitNode.copy1 w)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr ?_
      intro w _
      rfl
    change ((G.E.image (fun e : Node × Node =>
                (toCopy1 W₁ e.1, toCopy0 W₁ e.2))
              ∪ W₁.image (fun w : Node =>
                  (SplitNode.copy0 w, SplitNode.copy1 w))).image
                (fun e => (toCopy1 (W₂.image SplitNode.unsplit) e.1,
                           toCopy0 (W₂.image SplitNode.unsplit) e.2))
            ∪ (W₂.image SplitNode.unsplit).image
                (fun w : SplitNode Node =>
                  (SplitNode.copy0 w, SplitNode.copy1 w))).image
              (Prod.map flattenSplit flattenSplit)
          = G.E.image (fun e : Node × Node =>
              (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
            ∪ (W₁ ∪ W₂).image (fun w : Node =>
                (SplitNode.copy0 w, SplitNode.copy1 w))
    simp only [Finset.image_union]
    rw [hG_E, hW₁_tr, hW₂_tr]
    rw [Finset.union_assoc]
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
  -- ===== Sub-goal 5: J for (b) — same shape as Sub-goal 1. =====
  · change ((G.J.image SplitNode.unsplit).image
                SplitNode.unsplit).image flattenSplit
          = G.J.image SplitNode.unsplit
    rw [Finset.image_image, Finset.image_image]
    rfl
  -- ===== Sub-goal 6: V for (b) — same shape as Sub-goal 2 with W₁ ↔ W₂. =====
  · change ((((G.V \ W₂).image SplitNode.unsplit
                ∪ W₂.image SplitNode.copy0 ∪ W₂.image SplitNode.copy1)
              \ (W₁.image SplitNode.unsplit)).image SplitNode.unsplit
            ∪ (W₁.image SplitNode.unsplit).image SplitNode.copy0
            ∪ (W₁.image SplitNode.unsplit).image SplitNode.copy1).image
              flattenSplit
          = (G.V \ (W₁ ∪ W₂)).image SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image SplitNode.copy0
            ∪ (W₁ ∪ W₂).image SplitNode.copy1
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy12 | hy3
      · rcases Finset.mem_union.mp hy12 with hy1 | hy2
        · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy1
          obtain ⟨hz_inner, hz_notW₁img⟩ := Finset.mem_sdiff.mp hz
          rcases Finset.mem_union.mp hz_inner with hz12 | hz3
          · rcases Finset.mem_union.mp hz12 with hz1 | hz2
            · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz1
              obtain ⟨hv_V, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
              have hv_notW₁ : v ∉ W₁ := fun h =>
                hz_notW₁img (Finset.mem_image.mpr ⟨v, h, rfl⟩)
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
              refine Finset.mem_sdiff.mpr ⟨hv_V, ?_⟩
              intro hu
              exact (Finset.mem_union.mp hu).elim hv_notW₁ hv_notW₂
            · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz2
              refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
          · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz3
            refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
        · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy2
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
      · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy3
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hx12 | hx3
      · rcases Finset.mem_union.mp hx12 with hx1 | hx2
        · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
          obtain ⟨hv_V, hv_notW₁₂⟩ := Finset.mem_sdiff.mp hv
          have hv_notW₁ : v ∉ W₁ := fun h => hv_notW₁₂ (Finset.mem_union_left _ h)
          have hv_notW₂ : v ∉ W₂ := fun h => hv_notW₁₂ (Finset.mem_union_right _ h)
          refine Finset.mem_image.mpr
            ⟨SplitNode.unsplit (SplitNode.unsplit v), ?_, rfl⟩
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit v, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₂⟩, rfl⟩
          · intro h
            obtain ⟨v', hv'_mem, hv'_eq⟩ := Finset.mem_image.mp h
            cases hv'_eq
            exact hv_notW₁ hv'_mem
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
          rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
          · refine Finset.mem_image.mpr
              ⟨SplitNode.copy0 (SplitNode.unsplit w), ?_, rfl⟩
            refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
            exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
          · refine Finset.mem_image.mpr
              ⟨SplitNode.unsplit (SplitNode.copy0 w), ?_, rfl⟩
            refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            refine Finset.mem_image.mpr ⟨SplitNode.copy0 w, ?_, rfl⟩
            refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
            · intro h
              obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
              cases hweq
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx3
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · refine Finset.mem_image.mpr
            ⟨SplitNode.copy1 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · refine Finset.mem_image.mpr
            ⟨SplitNode.unsplit (SplitNode.copy1 w), ?_, rfl⟩
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          refine Finset.mem_image.mpr ⟨SplitNode.copy1 w, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
          · intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
  -- ===== Sub-goal 7: E for (b) — same shape as Sub-goal 3 with W₁ ↔ W₂. =====
  · have hG_E :
        ((G.E.image (fun e : Node × Node =>
              (toCopy1 W₂ e.1, toCopy0 W₂ e.2))).image
            (fun e => (toCopy1 (W₁.image SplitNode.unsplit) e.1,
                       toCopy0 (W₁.image SplitNode.unsplit) e.2))).image
          (Prod.map flattenSplit flattenSplit)
        = G.E.image (fun e : Node × Node =>
            (toCopy1 (W₂ ∪ W₁) e.1, toCopy0 (W₂ ∪ W₁) e.2)) := by
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
    have hW₂_tr :
        ((W₂.image (fun w : Node =>
              (SplitNode.copy0 w, SplitNode.copy1 w))).image
            (fun e => (toCopy1 (W₁.image SplitNode.unsplit) e.1,
                       toCopy0 (W₁.image SplitNode.unsplit) e.2))).image
          (Prod.map flattenSplit flattenSplit)
        = W₂.image (fun w : Node =>
            (SplitNode.copy0 w, SplitNode.copy1 w)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr ?_
      intro w _
      change (flattenSplit
                  (toCopy1 (W₁.image SplitNode.unsplit)
                    (SplitNode.copy0 w)),
              flattenSplit
                  (toCopy0 (W₁.image SplitNode.unsplit)
                    (SplitNode.copy1 w)))
            = (SplitNode.copy0 w, SplitNode.copy1 w)
      have h1 : SplitNode.copy0 w ∉ W₁.image SplitNode.unsplit := by
        intro h; obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h; cases hweq
      have h2 : SplitNode.copy1 w ∉ W₁.image SplitNode.unsplit := by
        intro h; obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h; cases hweq
      unfold toCopy0 toCopy1
      rw [if_neg h1, if_neg h2]
      rfl
    have hW₁_tr :
        ((W₁.image SplitNode.unsplit).image
            (fun w : SplitNode Node =>
              (SplitNode.copy0 w, SplitNode.copy1 w))).image
          (Prod.map flattenSplit flattenSplit)
        = W₁.image (fun w : Node =>
            (SplitNode.copy0 w, SplitNode.copy1 w)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr ?_
      intro w _
      rfl
    change ((G.E.image (fun e : Node × Node =>
                (toCopy1 W₂ e.1, toCopy0 W₂ e.2))
              ∪ W₂.image (fun w : Node =>
                  (SplitNode.copy0 w, SplitNode.copy1 w))).image
                (fun e => (toCopy1 (W₁.image SplitNode.unsplit) e.1,
                           toCopy0 (W₁.image SplitNode.unsplit) e.2))
            ∪ (W₁.image SplitNode.unsplit).image
                (fun w : SplitNode Node =>
                  (SplitNode.copy0 w, SplitNode.copy1 w))).image
              (Prod.map flattenSplit flattenSplit)
          = G.E.image (fun e : Node × Node =>
              (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
            ∪ (W₁ ∪ W₂).image (fun w : Node =>
                (SplitNode.copy0 w, SplitNode.copy1 w))
    rw [Finset.union_comm W₁ W₂]
    simp only [Finset.image_union]
    rw [hG_E, hW₂_tr, hW₁_tr]
    rw [Finset.union_assoc]
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
-- REFACTOR-BLOCK-ORIGINAL-END: twoDisjointNodeSplittingsCommute

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: flattenSplit_injOn_of_disjoint (was: refactor_flattenSplit_injOn_of_disjoint)
-- ## Helper: `flattenSplit` is `InjOn` on the iterated graph's J ∪ V
--
-- Net-new helper introduced by refactor `eqViaNodeMap_injective`
-- to discharge the strengthened predicate's `Set.InjOn` conjunct.
--
-- ### Role
--
-- Establishes `Set.InjOn flattenSplit` on the carrier set of the
-- iterated CDMG `(G_{spl(W₁)})_{spl(W₂)}`, under the disjointness
-- hypothesis `Disjoint W₁ W₂`. This is the technical core of the
-- refactor: every existing image-equality conjunct of the original
-- `twoDisjointNodeSplittingsCommute` ports verbatim under the new
-- predicate; only the new InjOn conjunct requires a substantively
-- new proof, and the whole of that work is concentrated in this
-- lemma.
--
-- ### Why a separate lemma (rather than inlined in the main theorem)?
--
-- Reused twice in `refactor_twoDisjointNodeSplittingsCommute` --
-- once for direction (a) `(G_{spl W₁})_{spl W₂} = G_{spl(W₁ ∪ W₂)}`,
-- once for direction (b) `(G_{spl W₂})_{spl W₁} = G_{spl(W₁ ∪ W₂)}`
-- via the `(W₁ ↔ W₂)` swap of the helper's arguments. The proof
-- argument is also geometrically clean enough to deserve its own
-- name: a five-cell partition of the iterated graph's node set
-- (`J ∪ (V \ W₁ \ W₂)` plus the four tagged copies
-- `W₁^{0₁}, W₁^{1₁}, W₂^{0₂}, W₂^{1₂}`) followed by a
-- 5 × 5 = 25 case analysis with structural-equality / disjointness
-- closures, mirroring the verified tex twin's "Injectivity of the
-- carrier bijection on the iterated graph's node set" paragraph
-- one-to-one.
--
-- ### Why `Set.InjOn` on `↑(...).J ∪ ↑(...).V` (matching the predicate's carrier set verbatim)?
--
-- Pasted directly from `refactor_eqViaNodeMap`'s first-conjunct
-- shape so that the consumer call site in the main theorem can
-- plug this lemma in with no Set-arithmetic glue. The
-- iterated-graph operand is the same one that appears on the
-- left of `refactor_eqViaNodeMap` in the main theorem statement,
-- so the carrier sets line up definitionally.
--
-- ### Why disjointness is load-bearing
--
-- `flattenSplit` is NOT globally injective on
-- `SplitNode (SplitNode Node)`. For instance,
-- `flattenSplit (.copy0 (.unsplit w)) = .copy0 w` and
-- `flattenSplit (.copy0 (.copy0 w)) = .copy0 w` -- two distinct
-- input patterns collide off the iterated graph's `J ∪ V`. The
-- five-cell partition rules out most such would-be collisions
-- structurally, but two patterns survive structural filtering and
-- need the disjointness hypothesis to close: the `^0`-vs-`^0`
-- cross-collision `W₁^{0₁}` vs. `W₂^{0₂}` (which would force
-- `w₁ = w₂ ∈ W₁ ∩ W₂`) and the symmetric `^1`-vs-`^1` pattern.
-- The `Disjoint W₁ W₂` hypothesis is consumed exactly in those
-- two of the 25 subcases (the `(injection heq with h; subst h;
-- exact absurd ... (Finset.disjoint_left.mp hDisj _))` branches
-- in the closing `first | ... | ... | ...` block), matching the
-- "load-bearing use of the disjointness hypothesis
-- `W₁ ∩ W₂ = ∅`" call-out in the verified tex twin's
-- across-cell injectivity paragraph.
private lemma refactor_flattenSplit_injOn_of_disjoint
    (G : CDMG Node) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    Set.InjOn flattenSplit
        ((↑((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
              (W₂.image SplitNode.unsplit)
              (image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj)).J :
            Set (SplitNode (SplitNode Node))) ∪
          ↑((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
              (W₂.image SplitNode.unsplit)
              (image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj)).V) := by
  -- Classification: every element `z` of the iterated graph's
  -- `J ∪ V` (as Finsets) is in exactly one of 5 disjoint forms.
  -- This mirrors the 5-cell partition of the carrier in the
  -- verified tex twin's "Injectivity of the carrier bijection"
  -- paragraph.
  have classify : ∀ z : SplitNode (SplitNode Node),
      z ∈ ((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
              (W₂.image SplitNode.unsplit)
              (image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj)).J ∪
          ((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
              (W₂.image SplitNode.unsplit)
              (image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj)).V →
      (∃ a : Node,
          ((a ∈ G.J) ∨ (a ∈ G.V ∧ a ∉ W₁ ∧ a ∉ W₂)) ∧
              z = SplitNode.unsplit (SplitNode.unsplit a))
        ∨ (∃ w : Node, w ∈ W₁ ∧
              z = SplitNode.unsplit (SplitNode.copy0 w))
        ∨ (∃ w : Node, w ∈ W₁ ∧
              z = SplitNode.unsplit (SplitNode.copy1 w))
        ∨ (∃ w : Node, w ∈ W₂ ∧
              z = SplitNode.copy0 (SplitNode.unsplit w))
        ∨ (∃ w : Node, w ∈ W₂ ∧
              z = SplitNode.copy1 (SplitNode.unsplit w)) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hJ | hV
    · -- z ∈ iterated graph's J = (G.J.image .unsplit).image .unsplit
      change z ∈ (G.J.image SplitNode.unsplit).image
                  SplitNode.unsplit at hJ
      obtain ⟨y, hyG, rfl⟩ := Finset.mem_image.mp hJ
      obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hyG
      exact Or.inl ⟨j, Or.inl hjJ, rfl⟩
    · -- z ∈ iterated graph's V
      change z ∈
          ((((G.V \ W₁).image SplitNode.unsplit
                ∪ W₁.image SplitNode.copy0
                ∪ W₁.image SplitNode.copy1)
            \ (W₂.image SplitNode.unsplit)).image
                SplitNode.unsplit
          ∪ (W₂.image SplitNode.unsplit).image SplitNode.copy0
          ∪ (W₂.image SplitNode.unsplit).image SplitNode.copy1) at hV
      rcases Finset.mem_union.mp hV with hV12 | hV3
      · rcases Finset.mem_union.mp hV12 with hV1 | hV2
        · -- outer .unsplit branch
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hV1
          obtain ⟨hy_in, hy_notW₂img⟩ := Finset.mem_sdiff.mp hy
          rcases Finset.mem_union.mp hy_in with hy_in12 | hy_C1
          · rcases Finset.mem_union.mp hy_in12 with hy_Vuns | hy_C0
            · -- y = .unsplit v, v ∈ G.V \ W₁, v ∉ W₂
              obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy_Vuns
              obtain ⟨hv_V, hv_notW₁⟩ := Finset.mem_sdiff.mp hv
              have hv_notW₂ : v ∉ W₂ := fun h =>
                hy_notW₂img (Finset.mem_image.mpr ⟨v, h, rfl⟩)
              exact Or.inl ⟨v, Or.inr ⟨hv_V, hv_notW₁, hv_notW₂⟩, rfl⟩
            · -- y = .copy0 w, w ∈ W₁
              obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy_C0
              exact Or.inr (Or.inl ⟨w, hw, rfl⟩)
          · -- y = .copy1 w, w ∈ W₁
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy_C1
            exact Or.inr (Or.inr (Or.inl ⟨w, hw, rfl⟩))
        · -- outer .copy0 branch: z = .copy0 (.unsplit w), w ∈ W₂
          obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hV2
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨w, hw, rfl⟩)))
      · -- outer .copy1 branch: z = .copy1 (.unsplit w), w ∈ W₂
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hV3
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hw, rfl⟩)))
  -- Main InjOn argument.
  intro x hx y hy heq
  -- Convert hx, hy from Set membership to Finset disjunction-then-union.
  have hx' : x ∈ ((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
                    (W₂.image SplitNode.unsplit)
                    (image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj)).J ∪
              ((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
                    (W₂.image SplitNode.unsplit)
                    (image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj)).V := by
    rcases hx with h | h
    · exact Finset.mem_union_left _ (Finset.mem_coe.mp h)
    · exact Finset.mem_union_right _ (Finset.mem_coe.mp h)
  have hy' : y ∈ ((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
                    (W₂.image SplitNode.unsplit)
                    (image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj)).J ∪
              ((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
                    (W₂.image SplitNode.unsplit)
                    (image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj)).V := by
    rcases hy with h | h
    · exact Finset.mem_union_left _ (Finset.mem_coe.mp h)
    · exact Finset.mem_union_right _ (Finset.mem_coe.mp h)
  -- Classify x and y into one of 5 patterns each (5 × 5 = 25 subcases).
  rcases classify x hx' with
    ⟨xa, _, rfl⟩ | ⟨xw, hxw, rfl⟩ | ⟨xw, hxw, rfl⟩ | ⟨xw, hxw, rfl⟩ | ⟨xw, hxw, rfl⟩ <;>
  rcases classify y hy' with
    ⟨ya, _, rfl⟩ | ⟨yw, hyw, rfl⟩ | ⟨yw, hyw, rfl⟩ | ⟨yw, hyw, rfl⟩ | ⟨yw, hyw, rfl⟩ <;>
  -- Reduce flattenSplit applied to each specific pattern.  Each of
  -- the 25 cases now has heq of the form
  -- `<constructor> <var> = <constructor> <var>` after definitional
  -- unfolding; close by cases (constructor mismatch) or by
  -- injection-then-disjointness contradiction.
  first
  -- Same-form cases (5): (X1,Y1), (X2,Y2), (X3,Y3), (X4,Y4), (X5,Y5).
  -- Inject the underlying equality on the inner var, subst, rfl.
  | (injection heq with h; subst h; rfl)
  -- Cross-W cases where both flatten outputs use .copy0 or .copy1
  -- (4): (X2,Y4), (X4,Y2), (X3,Y5), (X5,Y3).
  -- After injection on .copy0 / .copy1, we get xw = yw.  But xw ∈ W₁
  -- and yw ∈ W₂ (or vice versa); disjointness gives the
  -- contradiction.
  | (injection heq with h; subst h;
     exact absurd hyw (Finset.disjoint_left.mp hDisj hxw))
  | (injection heq with h; subst h;
     exact absurd hxw (Finset.disjoint_left.mp hDisj hyw))
  -- Cross-constructor cases (16): heq is .C₁ _ = .C₂ _ with C₁ ≠ C₂.
  -- `cases heq` closes by no-confusion.
  | cases heq
-- REFACTOR-BLOCK-REPLACEMENT-END: flattenSplit_injOn_of_disjoint

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: twoDisjointNodeSplittingsCommute (was: refactor_twoDisjointNodeSplittingsCommute)
-- ref: claim_3_7
--
-- ## Refactor: `refactor_twoDisjointNodeSplittingsCommute`
--
-- Refactor of `twoDisjointNodeSplittingsCommute` for refactor
-- `eqViaNodeMap_injective`. Same conjunction `(a) ∧ (b)` shape
-- as the original (two `eqViaNodeMap` equalities through the
-- shared single splitting `G_{spl(W₁ ∪ W₂)}`), but the predicate
-- `eqViaNodeMap` is replaced by the strengthened
-- `refactor_eqViaNodeMap` (carrying a fifth `Set.InjOn` conjunct
-- on the carrier map `flattenSplit`).
--
-- ### What's reused from the original
--
-- The four image-equality conjuncts (`J`, `V`, `E`, `L`) come
-- straight from the existing (unchanged) `twoDisjointNodeSplittingsCommute`
-- via the destructuring binder in the opening `obtain ⟨⟨hJa, hVa,
-- hEa, hLa⟩, ⟨hJb, hVb, hEb, hLb⟩⟩ := ...` line. The refactor
-- does NOT redo the ~500-line J/V/E/L bookkeeping -- it would
-- produce a bit-for-bit identical tactic block, so reusing the
-- original keeps the LN-to-Lean correspondence one-to-one and
-- the file size manageable. The new content is purely the InjOn
-- discharge (the two `refine` underscores below the destructure).
--
-- ### Why the InjOn discharge is non-trivial
--
-- The carrier map `flattenSplit` is not globally injective: it
-- collapses off-iterated-graph constructor patterns (see the
-- comment block above `refactor_flattenSplit_injOn_of_disjoint`).
-- The witnessing InjOn property holds only on the iterated
-- graph's `J ∪ V`, and only because the disjointness hypothesis
-- `Disjoint W₁ W₂` rules out the two would-be cross-cell
-- collisions (`W₁^{0₁}` vs. `W₂^{0₂}` and `W₁^{1₁}` vs.
-- `W₂^{1₂}`). Without disjointness the InjOn conjunct fails,
-- and so does the LN's claim "the iterated CDMG equals the
-- single-step CDMG `G_{spl(W₁ ∪ W₂)}`" -- two split-copies of a
-- node in `W₁ ∩ W₂` would collide in the iterated graph in a way
-- the single-step graph cannot reproduce.
--
-- ### How disjointness flows in (both orderings)
--
-- The technical core is the helper
-- `refactor_flattenSplit_injOn_of_disjoint` above, invoked twice:
--   * Direction (a) `(G_{spl W₁})_{spl W₂} = G_{spl(W₁ ∪ W₂)}`:
--     helper applied with `(W₁, W₂, hDisj)` in the natural order.
--   * Direction (b) `(G_{spl W₂})_{spl W₁} = G_{spl(W₁ ∪ W₂)}`:
--     helper applied with `(W₂, W₁, hDisj.symm)` -- the iterated
--     graph in the InjOn obligation swaps inner/outer roles of
--     `W₁` and `W₂`, and `Disjoint` is symmetric.
-- Both directions land at the same single-step right-hand side
-- `G_{spl(W₁ ∪ W₂)}`, recovering the LN's triple-equality
-- "swap-symmetry" reading via transitivity, exactly as in the
-- verified tex twin's "Recovery of the LN's triple equality"
-- closing paragraph.
-- claim_3_7 -- start statement
theorem refactor_twoDisjointNodeSplittingsCommute (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    refactor_eqViaNodeMap
        ((G.nodeSplittingOn W₁ hW₁).nodeSplittingOn
            (W₂.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj))
        (G.nodeSplittingOn (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenSplit
      ∧
    refactor_eqViaNodeMap
        ((G.nodeSplittingOn W₂ hW₂).nodeSplittingOn
            (W₁.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingOn_V hW₂ hW₁ hDisj.symm))
        (G.nodeSplittingOn (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenSplit
-- claim_3_7 -- end statement
  := by
  -- Reuse the original theorem for the four image-equality
  -- conjuncts (J, V, E, L) in each of the two directions.
  obtain ⟨⟨hJa, hVa, hEa, hLa⟩, ⟨hJb, hVb, hEb, hLb⟩⟩ :=
    twoDisjointNodeSplittingsCommute G W₁ W₂ hW₁ hW₂ hDisj
  refine ⟨⟨?_, hJa, hVa, hEa, hLa⟩, ⟨?_, hJb, hVb, hEb, hLb⟩⟩
  · -- InjOn for direction (a): iterated split W₁ then W₂
    exact refactor_flattenSplit_injOn_of_disjoint G W₁ W₂ hW₁ hW₂ hDisj
  · -- InjOn for direction (b): iterated split W₂ then W₁
    exact refactor_flattenSplit_injOn_of_disjoint G W₂ W₁ hW₂ hW₁ hDisj.symm
-- REFACTOR-BLOCK-REPLACEMENT-END: twoDisjointNodeSplittingsCommute

end CDMG

end Causality
