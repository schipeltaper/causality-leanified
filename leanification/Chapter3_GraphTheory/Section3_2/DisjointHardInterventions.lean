import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn

namespace Causality

/-!
# Disjoint hard interventions and node-splittings commute (`claim_3_8`)

This file formalises the LN lemma `claim_3_8` (`DisjointHardInterventions`)
in section 3.2 of `graphs.tex`:

> Let `G = (J, V, E, L)` be a CDMG and `W₁ ⊆ J ∪ V`, `W₂ ⊆ V` two
> subsets of nodes of `G` with `W₁ ∩ W₂ = ∅`.  Then
> `(G_{doit(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{doit(W₁)}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_8_statement_DisjointHardInterventions.tex`, verified
equivalent to the LN block (`addition_to_the_LN` empty).

## Carrier reading (load-bearing for this row's Lean signature)

`def_3_10` (`hardInterventionOn`) preserves the node carrier (`Node → Node`)
while `def_3_11` (`nodeSplittingOn`) lifts the carrier
(`Node → SplitNode Node`).  Both sides of the asserted equality therefore
land in `CDMG (SplitNode Node)`:

* LHS `(G.hardInterventionOn W₁ hW₁).nodeSplittingOn W₂ _` — the inner
  hard intervention keeps the carrier as `Node`; the outer
  `nodeSplittingOn` lifts to `SplitNode Node`.
* RHS `(G.nodeSplittingOn W₂ hW₂).hardInterventionOn (W₁.image .unsplit) _`
  — the inner `nodeSplittingOn` lifts to `SplitNode Node`, and the outer
  hard intervention operates on the lifted carrier.  `W₁` is lifted to
  the split-graph carrier via `.image SplitNode.unsplit`, faithful to the
  tex spec's "carrier-reading" paragraph: every `w ∈ W₁` satisfies
  `w ∈ J ∪ V` (by `hW₁`) and `w ∉ W₂` (by disjointness), so `w` injects
  as its unsplit copy `.unsplit w` in the split-graph carrier.

Both sides have the same Lean type `CDMG (SplitNode Node)`, so the
equality is a *literal* `=` of CDMGs — NOT the
`eqViaNodeMap`/`flattenSplit` shape used by `claim_3_7`
(`TwoDisjointNode`), where iterating `nodeSplittingOn` twice produces
the nested carrier `SplitNode (SplitNode Node)` and required a
canonical-flatten relabelling.  Mirrors the literal-`=` pattern of
`claim_3_4` (`HardInterventionsCommute`).

The body is filled in by `prove_claim_in_lean` (Manager B), following
the to-be-written tex proof at
`tex/claim_3_8_proof_DisjointHardInterventions.tex` (the LN already
ships a worked proof at `graphs.tex` L504–534).
-/

namespace CDMG

-- ## Design choice — statement context (refactor twin)
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1`'s refactor twin `CDMG` (`CDMG.lean`).  The
--   signature references `CDMG Node`,
--   `G.hardInterventionOn` (`def_3_10` twin), and
--   `G.nodeSplittingOn` (`def_3_11` twin), each of which
--   depends on `[DecidableEq Node]` through `Finset`-backed membership
--   and image operations.  The split-graph carrier
--   `SplitNode Node` inherits `[DecidableEq (SplitNode
--   Node)]` automatically via the `deriving DecidableEq` clause on
--   `SplitNode` (`NodeSplittingOn.lean`).
-- claim_3_8 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_8 --- end helper

-- ## Local decidability instance for the L-filter predicate
--
-- Private polymorphic copy of the
-- `hardInterventionOn_decidable_bAll` instance declared in
-- `HardInterventionOn.lean`.  That instance is declared `private` at
-- the def-site, so it does not propagate by `import`.  We supply our
-- own local copy here so that the L-branch `change` step in the main
-- theorem below — which writes the L-component of the iterated
-- intervention as `… .filter (fun s : Sym2 _ => ∀ v ∈ s, v ∉ W)` —
-- elaborates without `DecidablePred` synthesis failure.  Polymorphic
-- over the ambient node type so that the *same* instance covers both
-- the LHS's inner `hardInterventionOn` on `Sym2 Node` *and*
-- the RHS's outer `hardInterventionOn` on the lifted carrier
-- `Sym2 (SplitNode Node)`.  Implementation is identical to
-- the def-site version: every `s : Sym2 α` is `s(a, b)` for some
-- `a, b`; `Sym2.ball` reduces `∀ v ∈ s(a, b), v ∉ W` to
-- `a ∉ W ∧ b ∉ W`; conjunction of decidable propositions is decidable.
set_option linter.style.longLine false in
private instance disjointHardInterventions_decidable_bAll
    {α : Type*} [DecidableEq α] (W : Finset α) :
    DecidablePred (fun s : Sym2 α => ∀ v ∈ s, v ∉ W) := fun s =>
  s.recOnSubsingleton fun _ _ => decidable_of_iff' _ Sym2.ball

-- ## Helper — `W₂` sits inside the carrier of the inner hard intervention (refactor twin)
--
-- Port of `subset_V_of_hardInterventionOn`.  Mechanical rename:
-- `CDMG → CDMG`, `hardInterventionOn →
-- hardInterventionOn`.  The V-side of the post-refactor
-- `hardInterventionOn` is structurally identical to the
-- pre-refactor `hardInterventionOn` (the refactor only touches `L`),
-- so the proof body carries over verbatim with the rename.
set_option linter.style.longLine false in
-- claim_3_8 --- start helper
private lemma subset_V_of_hardInterventionOn
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.J ∪ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂ ⊆ (G.hardInterventionOn W₁ hW₁).V
-- claim_3_8 --- end helper
:= by
  intro v hv
  change v ∈ G.V \ W₁
  exact Finset.mem_sdiff.mpr ⟨hW₂ hv, Finset.disjoint_right.mp hDisj hv⟩

-- ## Helper — `W₁.image .unsplit` sits inside the carrier of the
--   inner node-splitting (refactor twin)
--
-- Port of `image_unsplit_subset_carrier_of_nodeSplittingOn`.
-- Mechanical renames: `CDMG → CDMG`,
-- `SplitNode → SplitNode`, `nodeSplittingOn →
-- nodeSplittingOn`.  The J/V partition of
-- `nodeSplittingOn` is structurally identical to the
-- pre-refactor `nodeSplittingOn` (the refactor only touches `L`), so
-- the proof body carries over verbatim with the rename.
set_option linter.style.longLine false in
-- claim_3_8 --- start helper
private lemma image_unsplit_subset_carrier_of_nodeSplittingOn
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.J ∪ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₁.image SplitNode.unsplit ⊆
      (G.nodeSplittingOn W₂ hW₂).J ∪
        (G.nodeSplittingOn W₂ hW₂).V
-- claim_3_8 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  rcases Finset.mem_union.mp (hW₁ hv) with hJ | hV
  · -- `v ∈ G.J` → `.unsplit v ∈ G.J.image .unsplit = (split).J`.
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · -- `v ∈ G.V`: disjointness gives `v ∉ W₂`, so `v ∈ G.V \ W₂` and
    -- `.unsplit v` lands in the `(G.V \ W₂).image .unsplit` piece of
    -- `(split).V = (G.V \ W₂).image .unsplit ∪ W₂.image .copy0
    --   ∪ W₂.image .copy1`.
    have hv_notW₂ : v ∉ W₂ := Finset.disjoint_left.mp hDisj hv
    refine Finset.mem_union_right _ ?_
    refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hV, hv_notW₂⟩, rfl⟩

-- ref: claim_3_8 — refactor twin
--
-- For any `G : CDMG Node` and any two subsets
-- `W₁ ⊆ G.J ∪ G.V`, `W₂ ⊆ G.V` with `Disjoint W₁ W₂`, the LN equality
--   `(G_{doit(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{doit(W₁)}`
-- holds as a literal `=` of `CDMG`s over the split-graph
-- carrier `SplitNode Node`.
--
-- ## Refactor port — proof structure
--
-- * **J / V / E sub-goals port mechanically.**  The post-refactor
--   `hardInterventionOn` and `nodeSplittingOn`
--   leave J / V / E structurally unchanged (the refactor only
--   restructures `L`).  Each sub-goal is the pre-refactor tactic
--   block with the rename pass `CDMG → CDMG`,
--   `SplitNode → SplitNode`,
--   `toCopy0 → toCopy0`, `toCopy1 → toCopy1`.
--
-- * **L sub-goal is structurally reworked for `Sym2.map`.**  The
--   pre-refactor L-side threaded the lift through `Prod.map (toCopy0
--   W₂) (toCopy0 W₂)` on ordered pairs and used the *two-sided*
--   filter `fun e => e.1 ∉ W₁ ∧ e.2 ∉ W₁` (the
--   `hard_intervention_l_symmetrized_removal` deviation, structurally
--   resolved at the `def_3_10` row under `Sym2`).  Post-refactor the
--   lift is `Sym2.map (toCopy0 W₂)` on the `Sym2`-quotient,
--   and the filter is the endpoint-universal
--   `fun s => ∀ v ∈ s, v ∉ W₁` — no two-sided workaround needed
--   because swap-symmetry is definitional on `Sym2`.  The `change`
--   step writes the underlying form; `Finset.filter_image` then swaps
--   the filter inside the image; `Finset.filter_congr` reduces to a
--   per-element predicate equivalence
--     `(∀ v ∈ s, v ∉ W₁) ↔
--        (∀ v ∈ Sym2.map (toCopy0 W₂) s,
--           v ∉ W₁.image SplitNode.unsplit)`,
--   which closes via `Sym2.mem_map` (unfold `v ∈ Sym2.map f s` to
--   `∃ v₀ ∈ s, f v₀ = v`) plus the inline `toCopy0_notMem_iff` helper
--   (the same iff used by the original directed-edge sub-goal, now
--   applied to both endpoints of the unordered pair instead of just
--   the head of a directed edge).
--
-- * **`cdmgExt` destructures 8 fields, not 9.**  The post-refactor
--   `CDMG` has eight fields (`J`, `V`, `hJV_disj`, `E`,
--   `hE_subset`, `L`, `hL_subset`, `hL_irrefl`) — one fewer than the
--   pre-refactor nine, because `hL_symm` is gone (swap-symmetry is
--   definitional on `Sym2`).
--
-- * **Local `private instance disjointHardInterventions_decidable_bAll`
--   (declared above this comment block).**  The matching instance at
--   the `def_3_10`-twin site (`hardInterventionOn_decidable_bAll`)
--   is declared `private`, so it does not propagate to this file by
--   `import`.  We replicate the instance locally — polymorphic over
--   the underlying node type so it handles both the LHS's
--   `Sym2 Node`-filter and the RHS's `Sym2 (SplitNode
--   Node)`-filter at one declaration.  Same body as the def-site
--   instance (`Sym2.recOnSubsingleton` + `Sym2.ball`).  Mirrors the
--   pattern at `claim_3_4`'s refactor twin
--   (`hardInterventionsCommute_decidable_bAll`).
--
-- * **Literal `=` of `CDMG`s over `SplitNode Node`,
--   NOT `eqViaNodeMap` / `flattenSplit`.**  Both
--   sides take a *single* node-splitting on the same `W₂`, and
--   `hardInterventionOn` preserves the node carrier
--   (`CDMG α → CDMG α`), so both sides land in
--   `CDMG (SplitNode Node)` — no carrier mismatch
--   arises and the asserted equality is a literal `=` between two
--   terms of identical Lean type.  Contrast with `claim_3_7`'s
--   refactor twin where iterating `nodeSplittingOn` twice
--   produces `CDMG (SplitNode (SplitNode
--   Node))` on both sides with the constructor wrappings of the same
--   underlying graph node disagreeing between the two iteration
--   orders, forcing the `eqViaNodeMap` /
--   `flattenSplit` workaround.  Mirrors the literal-`=`
--   pattern of the pre-refactor `disjointHardInterventionsAndNodeSplittingsCommute`.
set_option linter.style.longLine false in
-- claim_3_8 -- start statement
theorem disjointHardInterventionsAndNodeSplittingsCommute
    (G : CDMG Node) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    (G.hardInterventionOn W₁ hW₁).nodeSplittingOn W₂
        (subset_V_of_hardInterventionOn hW₁ hW₂ hDisj)
      = (G.nodeSplittingOn W₂ hW₂).hardInterventionOn
          (W₁.image SplitNode.unsplit)
          (image_unsplit_subset_carrier_of_nodeSplittingOn hW₁ hW₂ hDisj)
-- claim_3_8 -- end statement
:= by
  -- `CDMG` extensionality: two `CDMG`s over the
  -- split-graph carrier are equal once their four data fields
  -- `(J, V, E, L)` agree.  Eight-field destructuring (the pre-
  -- refactor `hL_symm` field is gone — swap-symmetry is definitional
  -- on `Sym2`).
  have cdmgExt : ∀ {G₁ G₂ : CDMG (SplitNode Node)},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨J₁, V₁, hJV₁, E₁, hE₁, L₁, hL₁, hLi₁⟩
           ⟨J₂, V₂, hJV₂, E₂, hE₂, L₂, hL₂, hLi₂⟩ hJ hV hE hL
    obtain rfl := hJ
    obtain rfl := hV
    obtain rfl := hE
    obtain rfl := hL
    rfl
  -- Key membership lemma: under disjointness, the `toCopy0
  -- W₂`-lift of a `Node` lies outside `W₁.image .unsplit` iff the
  -- original `Node` lies outside `W₁`.  Implements the tex proof's
  -- "$v_k^0 \notin W_1 \Leftrightarrow v_k \notin W_1$" cross-check
  -- (used both in the *directed edges* section for the `e.2` head of
  -- each generator, and twice in the *bidirected edges* section for
  -- the two endpoints of each unordered-pair generator).
  --
  -- Case-split on `v ∈ W₂` mirrors the tex's case-split:
  --   * `v ∈ W₂`: `toCopy0 W₂ v = .copy0 v`, which is never
  --     in `W₁.image .unsplit` by constructor mismatch; on the other
  --     side `Disjoint W₁ W₂` rules out `v ∈ W₁`.  Both sides true.
  --   * `v ∉ W₂`: `toCopy0 W₂ v = .unsplit v`, which is in
  --     `W₁.image .unsplit` iff `v ∈ W₁` by injectivity of `.unsplit`.
  have toCopy0_notMem_iff : ∀ (v : Node),
      toCopy0 W₂ v ∉ W₁.image SplitNode.unsplit ↔
        v ∉ W₁ := by
    intro v
    unfold toCopy0
    by_cases hW₂ : v ∈ W₂
    · rw [if_pos hW₂]
      refine ⟨fun _ hW₁ => Finset.disjoint_left.mp hDisj hW₁ hW₂,
              fun _ hMem => ?_⟩
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hMem
      cases hweq
    · rw [if_neg hW₂]
      refine ⟨fun h hW₁ => h (Finset.mem_image.mpr ⟨v, hW₁, rfl⟩),
              fun h hMem => ?_⟩
      obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hMem
      cases hweq
      exact h hw
  refine cdmgExt ?_ ?_ ?_ ?_
  -- ===== Node sets: `J` =====
  -- LHS `J`: `(G.J ∪ W₁).image .unsplit`.
  -- RHS `J`: `G.J.image .unsplit ∪ W₁.image .unsplit`.
  -- Equal by `Finset.image_union`.
  · change (G.J ∪ W₁).image SplitNode.unsplit
          = G.J.image SplitNode.unsplit
              ∪ W₁.image SplitNode.unsplit
    exact Finset.image_union _ _
  -- ===== Node sets: `V` =====
  -- LHS `V`: `((G.V \ W₁) \ W₂).image .unsplit ∪ W₂.image .copy0
  --          ∪ W₂.image .copy1`.
  -- RHS `V`: `((G.V \ W₂).image .unsplit ∪ W₂.image .copy0
  --          ∪ W₂.image .copy1) \ W₁.image .unsplit`.
  -- Element-wise `ext` mirroring the tex's case-on-constructor reading.
  · change (((G.V \ W₁) \ W₂).image SplitNode.unsplit
              ∪ W₂.image SplitNode.copy0
              ∪ W₂.image SplitNode.copy1)
          = ((G.V \ W₂).image SplitNode.unsplit
              ∪ W₂.image SplitNode.copy0
              ∪ W₂.image SplitNode.copy1)
            \ W₁.image SplitNode.unsplit
    ext x
    constructor
    · -- LHS → RHS direction.
      intro hx
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · -- `x` is in the inner V (RHS-pre-sdiff).
        rcases Finset.mem_union.mp hx with hx12 | hx3
        · rcases Finset.mem_union.mp hx12 with hx1 | hx2
          · -- `x = .unsplit v`, `v ∈ (G.V \ W₁) \ W₂` ⊆ `G.V \ W₂`.
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
            obtain ⟨hv_VW₁, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
            obtain ⟨hv_V, _⟩ := Finset.mem_sdiff.mp hv_VW₁
            refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            exact Finset.mem_image.mpr
              ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₂⟩, rfl⟩
          · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            exact hx2
        · refine Finset.mem_union_right _ ?_
          exact hx3
      · -- `x ∉ W₁.image .unsplit`: case on which piece of LHS V holds x.
        rcases Finset.mem_union.mp hx with hx12 | hx3
        · rcases Finset.mem_union.mp hx12 with hx1 | hx2
          · -- `x = .unsplit v`, `v ∉ W₁` from `v ∈ G.V \ W₁`.
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
            obtain ⟨hv_VW₁, _⟩ := Finset.mem_sdiff.mp hv
            obtain ⟨_, hv_notW₁⟩ := Finset.mem_sdiff.mp hv_VW₁
            intro h
            obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
            cases hweq
            exact hv_notW₁ hw
          · -- `x = .copy0 w`: constructor mismatch with `.unsplit`.
            obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx2
            intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
        · -- `x = .copy1 w`: constructor mismatch with `.unsplit`.
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx3
          intro h
          obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
          cases hweq
    · -- RHS → LHS direction.
      intro hx
      obtain ⟨hx_inner, hx_notW₁'⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp hx_inner with hx12 | hx3
      · rcases Finset.mem_union.mp hx12 with hx1 | hx2
        · -- `x = .unsplit v`, `v ∈ G.V \ W₂`, and `v ∉ W₁` from
          -- `hx_notW₁'` (`.unsplit v ∉ W₁.image .unsplit` by injectivity).
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
          obtain ⟨hv_V, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
          have hv_notW₁ : v ∉ W₁ := fun h =>
            hx_notW₁' (Finset.mem_image.mpr ⟨v, h, rfl⟩)
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₁⟩, hv_notW₂⟩
        · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          exact hx2
      · refine Finset.mem_union_right _ ?_
        exact hx3
  -- ===== Directed edges: `E` =====
  -- LHS `E`: `(G.E.filter (e.2 ∉ W₁)).image (toCopy1 W₂ ·.1, toCopy0 W₂ ·.2)
  --          ∪ W₂.image (·.copy0, ·.copy1)`.
  -- RHS `E`: `(G.E.image (toCopy1 W₂ ·.1, toCopy0 W₂ ·.2)
  --          ∪ W₂.image (·.copy0, ·.copy1)).filter (e.2 ∉ W₁.image .unsplit)`.
  -- Same as the pre-refactor — E's filter / image / transfer-edge
  -- structure is untouched by the refactor.
  · change ((G.E.filter (fun e : Node × Node => e.2 ∉ W₁)).image
              (fun e : Node × Node =>
                (toCopy1 W₂ e.1, toCopy0 W₂ e.2))
            ∪ W₂.image (fun w : Node =>
                (SplitNode.copy0 w, SplitNode.copy1 w)))
          = (G.E.image
                (fun e : Node × Node =>
                  (toCopy1 W₂ e.1, toCopy0 W₂ e.2))
              ∪ W₂.image
                (fun w : Node =>
                  (SplitNode.copy0 w,
                    SplitNode.copy1 w))).filter
              (fun e : SplitNode Node × SplitNode Node =>
                e.2 ∉ W₁.image SplitNode.unsplit)
    rw [Finset.filter_union, Finset.filter_image]
    congr 1
    · -- Lifted-`G.E` piece: filter-pred agreement under `Finset.filter_congr`.
      congr 1
      refine Finset.filter_congr ?_
      intro e he
      exact (toCopy0_notMem_iff e.2).symm
    · -- Transfer-edge piece: filter is vacuous on
      -- `W₂.image (·.copy0, ·.copy1)`.
      symm
      refine Finset.filter_true_of_mem ?_
      intro x hx
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx
      intro h
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
      cases hweq
  -- ===== Bidirected edges: `L` =====
  -- LHS `L`: `(G.L.filter (∀ v ∈ s, v ∉ W₁)).image (Sym2.map (toCopy0 W₂))`.
  -- RHS `L`: `(G.L.image (Sym2.map (toCopy0 W₂))).filter
  --             (∀ v ∈ s, v ∉ W₁.image .unsplit)`.
  --
  -- Per the tex twin's "Bidirected edges" section: post-refactor, the
  -- LN's literal one-sided removal clause translates directly to the
  -- endpoint-universal form "every endpoint of the unordered pair lies
  -- outside `W₁`" — there is no ordered "second component" on a `Sym2`
  -- value to single out, and `Sym2`-swap-symmetry is definitional, so
  -- the pre-refactor `Registered two-sided removal of L` paragraph is
  -- no longer needed.  The L-side proof structurally reworks the
  -- pre-refactor calculation by swapping
  -- `Prod.map (toCopy0 W₂) (toCopy0 W₂)` for
  -- `Sym2.map (toCopy0 W₂)` and the conjunction
  -- `e.1 ∉ W₁ ∧ e.2 ∉ W₁` for the bounded universal `∀ v ∈ s, v ∉ W₁`.
  -- `Finset.filter_image` swaps the filter inside the image;
  -- `Finset.filter_congr` reduces to the per-endpoint predicate
  -- equivalence, which closes via `Sym2.mem_map` (unfolds
  -- `v ∈ Sym2.map f s` to `∃ v₀ ∈ s, f v₀ = v`) plus pointwise
  -- `toCopy0_notMem_iff`.
  · change (G.L.filter (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₁)).image
              (Sym2.map (toCopy0 W₂))
          = (G.L.image (Sym2.map (toCopy0 W₂))).filter
              (fun s : Sym2 (SplitNode Node) =>
                ∀ v ∈ s, v ∉ W₁.image SplitNode.unsplit)
    rw [Finset.filter_image]
    congr 1
    refine Finset.filter_congr ?_
    intro s hs
    constructor
    · -- `(∀ v ∈ s, v ∉ W₁) → ∀ v ∈ Sym2.map f s, v ∉ W₁.image .unsplit`.
      intro h v hv
      obtain ⟨v₀, hv₀, rfl⟩ := Sym2.mem_map.mp hv
      exact (toCopy0_notMem_iff v₀).mpr (h v₀ hv₀)
    · -- `(∀ v ∈ Sym2.map f s, v ∉ W₁.image .unsplit) → ∀ v ∈ s, v ∉ W₁`.
      intro h v hv
      exact (toCopy0_notMem_iff v).mp
        (h (toCopy0 W₂ v) (Sym2.mem_map.mpr ⟨v, hv, rfl⟩))

end CDMG

end Causality
