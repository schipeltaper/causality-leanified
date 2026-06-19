import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.ExtendingCDMGsWith
import Chapter3_GraphTheory.Section3_2.TwoDisjointNode

namespace Causality

/-!
# Adding intervention nodes commutes with disjoint hard interventions (`claim_3_14`)

This file formalises the LN lemma `claim_3_14`
(`AddingInterventionNodes` in `graphs.tex`, section 3.2):

> Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ J ∪ V` two disjoint
> subsets of nodes from `G`.  Then
>
> (a) `(G_{doit(I_{W₁})})_{doit(I_{W₂})} = (G_{doit(I_{W₂})})_{doit(I_{W₁})}
>       = G_{doit(I_{W₁ ∪ W₂})}`;
>
> (b) `(G_{doit(I_{W₁})})_{doit(W₂)} = (G_{doit(W₂)})_{doit(I_{W₁})}
>       = G_{doit(I_{W₁}, W₂)}`,
>
> where `G_{doit(I_{W₁}, W₂)} := (G_{doit(I_{W₁})})_{doit(W₂)}` is the
> mixed-notation CDMG introduced in this lemma.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_14_statement_AddingInterventionNodes.tex`, verified equivalent
to the LN block plus the `addition_to_the_LN` clarification
`[doit_overloaded_for_node_addition_vs_hard_intervention]` (the
disambiguation of the overloaded `\doit(·)` notation by the type of its
argument) by `verify_tex_statement_only` and
`verify_tex_statement_equivalence`.

## Carrier-mismatch wrinkle for sub-claim (a) (load-bearing for this row's Lean signature)

`def_3_13`'s `extendingCDMGsWith` changes the node carrier
(`CDMG α → CDMG (IntExtNode α)`), so the iterated extension
`(G.extendingCDMGsWith W₁ _).extendingCDMGsWith (W₂.image .unsplit) _`
lives in `CDMG (IntExtNode (IntExtNode Node))` — a formally distinct
type from the single extension
`G.extendingCDMGsWith (W₁ ∪ W₂) _ : CDMG (IntExtNode Node)`.  The LN
identifies the two carriers set-theoretically via the canonical
inclusion `ι : J ∪ V ↪ J_{doit(I_W)} ∪ V_{doit(I_W)}, v ↦ v` (i.e.\
`IntExtNode.unsplit`); the rewritten tex's "Well-typedness of the
iterated operations" paragraph spells this out (lines 39-43).  This
Lean rendering captures the identification via the canonical flatten
function `flattenIntExt : IntExtNode (IntExtNode Node) → IntExtNode
Node` (defined below); the LN's "componentwise equality of CDMGs"
reading is captured by `eqViaNodeMap` (defined in `claim_3_7`,
`TwoDisjointNode.lean`).

Sub-claim (b), by contrast, has no carrier-mismatch wrinkle: every one
of the three CDMGs `(G_{doit(I_{W₁})})_{doit(W₂)}`,
`(G_{doit(W₂)})_{doit(I_{W₁})}`, and `G_{doit(I_{W₁}, W₂)}` lives in
`CDMG (IntExtNode Node)` (since `hardInterventionOn` preserves the
node carrier, so applying it inside or outside `extendingCDMGsWith`
yields the same target carrier).  Hence sub-claim (b) is rendered as
literal `=` of CDMGs, matching the `claim_3_4`
(`HardInterventionsCommute`) pattern.

The body of each theorem is filled in by `prove_claim_in_lean`
(Manager B), following the to-be-written tex proof at
`tex/claim_3_14_proof_AddingInterventionNodes.tex`.
-/

-- ## `open CDMG` — bring `IntExtNode` and `extendingCDMGsWith`
-- into scope for the refactor twin
--
-- `def_3_13`'s `ExtendingCDMGsWith.lean` chose the single-namespace
-- pattern: the shared `inductive IntExtNode` and the refactor twin
-- `extendingCDMGsWith` both live inside `namespace CDMG`
-- alongside the pre-refactor `extendingCDMGsWith`.  Our refactor twin
-- below operates inside `namespace CDMG`, so we need to
-- bring those two identifiers into scope explicitly.  Dot notation
-- (`G.extendingCDMGsWith W hW`) would not work — it resolves
-- via the receiver's type namespace (`CDMG`), and
-- `extendingCDMGsWith` is registered under `CDMG`, not
-- `CDMG`.  Function-style calls (`extendingCDMGsWith
-- G W hW`) with `open CDMG` are the cleanest fix.  No name collisions
-- arise because every refactor-twin declaration below carries the
-- `refactor_` prefix.  `hardInterventionOn` and
-- `eqViaNodeMap` *are* in `namespace CDMG`, so dot
-- notation `G.hardInterventionOn` and function-style
-- `eqViaNodeMap` resolve directly without further imports.
namespace CDMG
open CDMG

-- claim_3_14 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_14 --- end helper

-- claim_3_14 --- start helper
private lemma image_unsplit_subset_extendingCDMGsWith_carrier
    {G : CDMG Node} {W : Finset Node} (hW : W ⊆ G.J ∪ G.V)
    {S : Finset Node} (hS : S ⊆ G.J ∪ G.V) :
    S.image IntExtNode.unsplit ⊆
      (extendingCDMGsWith G W hW).J ∪ (extendingCDMGsWith G W hW).V
-- claim_3_14 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change IntExtNode.unsplit v ∈
    (G.J.image IntExtNode.unsplit ∪ (W \ G.J).image IntExtNode.intCopy)
      ∪ G.V.image IntExtNode.unsplit
  rcases Finset.mem_union.mp (hS hv) with hJ | hV
  · refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · refine Finset.mem_union_right _ ?_
    exact Finset.mem_image.mpr ⟨v, hV, rfl⟩

-- claim_3_14 --- start helper
private lemma subset_carrier_of_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} (hW : W ⊆ G.J ∪ G.V)
    {S : Finset Node} (hS : S ⊆ G.J ∪ G.V) :
    S ⊆ (G.hardInterventionOn W hW).J ∪ (G.hardInterventionOn W hW).V
-- claim_3_14 --- end helper
:= by
  intro v hv
  change v ∈ (G.J ∪ W) ∪ (G.V \ W)
  rcases Finset.mem_union.mp (hS hv) with hJ | hV
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
  · by_cases hW' : v ∈ W
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hW')
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, hW'⟩)

-- claim_3_14 --- start helper
def flattenIntExt : IntExtNode (IntExtNode Node) → IntExtNode Node
  | .unsplit (.unsplit v) => IntExtNode.unsplit v
  | .unsplit (.intCopy w) => IntExtNode.intCopy w
  | .intCopy (.unsplit v) => IntExtNode.intCopy v
  | .intCopy (.intCopy w) => IntExtNode.intCopy w
-- claim_3_14 --- end helper

-- claim_3_14 --- start helper
def addInterventionNodesAndHardInterventionOn (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V) :
    CDMG (IntExtNode Node) :=
  (extendingCDMGsWith G W₁ hW₁).hardInterventionOn
      (W₂.image IntExtNode.unsplit)
      (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)
-- claim_3_14 --- end helper

set_option linter.unusedVariables false in
-- claim_3_14 -- start statement
theorem addInterventionNodes_comm_disjoint (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    eqViaNodeMap
        (extendingCDMGsWith
            (extendingCDMGsWith G W₁ hW₁)
            (W₂.image IntExtNode.unsplit)
            (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂))
        (extendingCDMGsWith G (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenIntExt
      ∧
    eqViaNodeMap
        (extendingCDMGsWith
            (extendingCDMGsWith G W₂ hW₂)
            (W₁.image IntExtNode.unsplit)
            (image_unsplit_subset_extendingCDMGsWith_carrier hW₂ hW₁))
        (extendingCDMGsWith G (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenIntExt
-- claim_3_14 -- end statement
:= by
  -- ## Flatten collapses for image-composition manipulation.
  --
  -- J/V flatten collapses (Node carrier) — port verbatim from the
  -- pre-refactor theorem, only `flattenIntExt → flattenIntExt`.
  have h_uu_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image IntExtNode.unsplit).image flattenIntExt
      = S.image IntExtNode.unsplit := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_iu_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image IntExtNode.intCopy).image flattenIntExt
      = S.image IntExtNode.intCopy := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_ui_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.intCopy).image IntExtNode.unsplit).image flattenIntExt
      = S.image IntExtNode.intCopy := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  -- E-pair collapses (Node × Node carrier; E field unchanged by refactor).
  have h_E_lift_uu_collapse : ∀ (S : Finset (Node × Node)),
      ((S.image (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
          (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
        (Prod.map flattenIntExt flattenIntExt)
      = S.image (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_W_transfer_inner_collapse : ∀ (S : Finset Node),
      ((S.image (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
          (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
        (Prod.map flattenIntExt flattenIntExt)
      = S.image (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_W_transfer_outer_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image
          (fun w : IntExtNode Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
        (Prod.map flattenIntExt flattenIntExt)
      = S.image (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  -- L-Sym2 lift collapse (Sym2 Node carrier; new under the refactor).
  --
  -- The pre-refactor `h_E_lift_uu_collapse` doubled for L because L was
  -- typed as `Finset (Node × Node)` (same as E).  Under the refactor L
  -- is `Finset (Sym2 Node)`, so we lift via `Sym2.map IntExtNode.unsplit`
  -- in place of `Prod.map .unsplit .unsplit`, and fuse the two-stage
  -- composition via Mathlib's `Sym2.map_map`
  -- (`Sym2.map g (Sym2.map f x) = Sym2.map (g ∘ f) x`).  The pointwise
  -- equality of `(flattenIntExt ∘ .unsplit) ∘ .unsplit` and
  -- `.unsplit` is by definitional pattern-match on
  -- `flattenIntExt (.unsplit (.unsplit v)) = .unsplit v`,
  -- hence `Sym2.map_congr` closes the goal via `rfl`.
  have h_L_lift_uu_collapse : ∀ (S : Finset (Sym2 Node)),
      ((S.image (Sym2.map IntExtNode.unsplit)).image
          (Sym2.map IntExtNode.unsplit)).image
        (Sym2.map flattenIntExt)
      = S.image (Sym2.map IntExtNode.unsplit) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro s _
    change Sym2.map flattenIntExt
            (Sym2.map IntExtNode.unsplit (Sym2.map IntExtNode.unsplit s))
          = Sym2.map IntExtNode.unsplit s
    rw [Sym2.map_map, Sym2.map_map]
    refine Sym2.map_congr ?_
    intro a _
    rfl
  -- ## The carrier-sdiff lift identity (tex proof's `W \ J₁ = W \ J` step).
  have h_sdiff : ∀ (W' W : Finset Node),
      W.image IntExtNode.unsplit \
        (G.J.image IntExtNode.unsplit ∪ (W' \ G.J).image IntExtNode.intCopy)
      = (W \ G.J).image IntExtNode.unsplit := by
    intro W' W
    ext x
    constructor
    · intro hx
      obtain ⟨hxW, hxNot⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨v, hvW, rfl⟩ := Finset.mem_image.mp hxW
      have hv_notJ : v ∉ G.J := by
        intro hjG
        apply hxNot
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hjG, rfl⟩)
      exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvW, hv_notJ⟩, rfl⟩
    · intro hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hvW, hv_notJ⟩ := Finset.mem_sdiff.mp hv
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨v, hvW, rfl⟩, ?_⟩
      intro h_in
      rcases Finset.mem_union.mp h_in with hL | hR
      · obtain ⟨j, hjJ, hjEq⟩ := Finset.mem_image.mp hL
        cases hjEq
        exact hv_notJ hjJ
      · obtain ⟨_, _, hwEq⟩ := Finset.mem_image.mp hR
        cases hwEq
  -- ## Disjoint-union-of-sdiff identity.
  have h_sdiff_union : (W₁ \ G.J) ∪ (W₂ \ G.J) = (W₁ ∪ W₂) \ G.J :=
    (Finset.union_sdiff_distrib W₁ W₂ G.J).symm
  have h_sdiff_union' : (W₂ \ G.J) ∪ (W₁ \ G.J) = (W₂ ∪ W₁) \ G.J :=
    (Finset.union_sdiff_distrib W₂ W₁ G.J).symm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  -- ===================== (a-1): iter₁₂ → joint =====================
  -- Sub-goal 1: J component for iter₁₂.
  · change ((G.J.image IntExtNode.unsplit ∪ (W₁ \ G.J).image IntExtNode.intCopy).image
              IntExtNode.unsplit
            ∪ (W₂.image IntExtNode.unsplit \
                (G.J.image IntExtNode.unsplit ∪
                  (W₁ \ G.J).image IntExtNode.intCopy)).image
              IntExtNode.intCopy).image flattenIntExt
          = G.J.image IntExtNode.unsplit ∪ ((W₁ ∪ W₂) \ G.J).image IntExtNode.intCopy
    rw [h_sdiff W₁ W₂]
    simp only [Finset.image_union]
    rw [h_uu_collapse, h_ui_collapse, h_iu_collapse]
    rw [Finset.union_assoc, ← Finset.image_union, h_sdiff_union]
  -- Sub-goal 2: V component for iter₁₂.
  · change ((G.V.image IntExtNode.unsplit).image IntExtNode.unsplit).image flattenIntExt
          = G.V.image IntExtNode.unsplit
    exact h_uu_collapse G.V
  -- Sub-goal 3: E component for iter₁₂.
  · change ((G.E.image
                (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
              ∪ (W₁ \ G.J).image
                (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
                (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
            ∪ (W₂.image IntExtNode.unsplit \
                (G.J.image IntExtNode.unsplit ∪
                  (W₁ \ G.J).image IntExtNode.intCopy)).image
              (fun w : IntExtNode Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
            (Prod.map flattenIntExt flattenIntExt)
          = G.E.image (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
            ∪ ((W₁ ∪ W₂) \ G.J).image
                (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))
    rw [h_sdiff W₁ W₂]
    simp only [Finset.image_union]
    rw [h_E_lift_uu_collapse, h_W_transfer_inner_collapse, h_W_transfer_outer_collapse]
    rw [Finset.union_assoc, ← Finset.image_union, h_sdiff_union]
  -- Sub-goal 4: L component for iter₁₂.
  · change ((G.L.image (Sym2.map IntExtNode.unsplit)).image
              (Sym2.map IntExtNode.unsplit)).image
            (Sym2.map flattenIntExt)
          = G.L.image (Sym2.map IntExtNode.unsplit)
    exact h_L_lift_uu_collapse G.L
  -- ===================== (a-2): iter₂₁ → joint =====================
  -- Sub-goal 5: J component for iter₂₁.
  · change ((G.J.image IntExtNode.unsplit ∪ (W₂ \ G.J).image IntExtNode.intCopy).image
              IntExtNode.unsplit
            ∪ (W₁.image IntExtNode.unsplit \
                (G.J.image IntExtNode.unsplit ∪
                  (W₂ \ G.J).image IntExtNode.intCopy)).image
              IntExtNode.intCopy).image flattenIntExt
          = G.J.image IntExtNode.unsplit ∪ ((W₁ ∪ W₂) \ G.J).image IntExtNode.intCopy
    rw [h_sdiff W₂ W₁]
    simp only [Finset.image_union]
    rw [h_uu_collapse, h_ui_collapse, h_iu_collapse]
    rw [Finset.union_assoc, ← Finset.image_union, h_sdiff_union', Finset.union_comm W₂ W₁]
  -- Sub-goal 6: V component for iter₂₁.
  · change ((G.V.image IntExtNode.unsplit).image IntExtNode.unsplit).image flattenIntExt
          = G.V.image IntExtNode.unsplit
    exact h_uu_collapse G.V
  -- Sub-goal 7: E component for iter₂₁.
  · change ((G.E.image
                (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
              ∪ (W₂ \ G.J).image
                (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
                (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
            ∪ (W₁.image IntExtNode.unsplit \
                (G.J.image IntExtNode.unsplit ∪
                  (W₂ \ G.J).image IntExtNode.intCopy)).image
              (fun w : IntExtNode Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
            (Prod.map flattenIntExt flattenIntExt)
          = G.E.image (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
            ∪ ((W₁ ∪ W₂) \ G.J).image
                (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))
    rw [h_sdiff W₂ W₁]
    simp only [Finset.image_union]
    rw [h_E_lift_uu_collapse, h_W_transfer_inner_collapse, h_W_transfer_outer_collapse]
    rw [Finset.union_assoc, ← Finset.image_union, h_sdiff_union', Finset.union_comm W₂ W₁]
  -- Sub-goal 8: L component for iter₂₁.
  · change ((G.L.image (Sym2.map IntExtNode.unsplit)).image
              (Sym2.map IntExtNode.unsplit)).image
            (Sym2.map flattenIntExt)
          = G.L.image (Sym2.map IntExtNode.unsplit)
    exact h_L_lift_uu_collapse G.L

-- claim_3_14 -- start statement
theorem addInterventionNodes_comm_hardIntervention (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (extendingCDMGsWith G W₁ hW₁).hardInterventionOn
        (W₂.image IntExtNode.unsplit)
        (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)
      = addInterventionNodesAndHardInterventionOn G W₁ W₂ hW₁ hW₂
      ∧
    extendingCDMGsWith (G.hardInterventionOn W₂ hW₂) W₁
        (subset_carrier_of_hardInterventionOn hW₂ hW₁)
      = addInterventionNodesAndHardInterventionOn G W₁ W₂ hW₁ hW₂
-- claim_3_14 -- end statement
:= by
  -- ## Inline CDMG extensionality on `CDMG (IntExtNode Node)`.
  --
  -- Two refactor_CDMGs are equal if their four data fields agree; the
  -- four propositional fields (`hJV_disj`, `hE_subset`, `hL_subset`,
  -- `hL_irrefl`) follow by proof irrelevance once the data fields are
  -- unified.  `CDMG` has 8 fields (one fewer than the
  -- pre-refactor `CDMG`'s 9 — `hL_symm` is gone under the Sym2
  -- encoding).
  have cdmgExt : ∀ {G₁' G₂' : CDMG (IntExtNode Node)},
      G₁'.J = G₂'.J → G₁'.V = G₂'.V → G₁'.E = G₂'.E → G₁'.L = G₂'.L → G₁' = G₂' := by
    rintro ⟨J₁, V₁, hJV₁, E₁, hE₁, L₁, hL₁, hLi₁⟩
           ⟨J₂, V₂, hJV₂, E₂, hE₂, L₂, hL₂, hLi₂⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL
    rfl
  -- ## Disjointness-consuming carrier identity: `W₁ \ (G.J ∪ W₂) = W₁ \ G.J`.
  have h_W₁_sdiff_collapse : W₁ \ (G.J ∪ W₂) = W₁ \ G.J := by
    ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · obtain ⟨hwW₁, hw_not⟩ := Finset.mem_sdiff.mp hw
      refine Finset.mem_sdiff.mpr ⟨hwW₁, ?_⟩
      intro hwJ
      exact hw_not (Finset.mem_union_left _ hwJ)
    · obtain ⟨hwW₁, hw_notJ⟩ := Finset.mem_sdiff.mp hw
      refine Finset.mem_sdiff.mpr ⟨hwW₁, ?_⟩
      intro h_in
      rcases Finset.mem_union.mp h_in with hJ' | hW₂'
      · exact hw_notJ hJ'
      · exact Finset.disjoint_left.mp hDisj hwW₁ hW₂'
  -- Conjunction split: (b-1) closes by `rfl`; (b-2) is the genuine content.
  refine ⟨rfl, ?_⟩
  -- ## (b-2): `middle = mixed` field-by-field.
  refine cdmgExt ?_ ?_ ?_ ?_
  -- ---------- J component ----------
  · change (G.J ∪ W₂).image IntExtNode.unsplit ∪ (W₁ \ (G.J ∪ W₂)).image IntExtNode.intCopy
          = G.J.image IntExtNode.unsplit ∪ (W₁ \ G.J).image IntExtNode.intCopy ∪
              W₂.image IntExtNode.unsplit
    rw [h_W₁_sdiff_collapse, Finset.image_union]
    rw [Finset.union_assoc, Finset.union_comm (W₂.image IntExtNode.unsplit) _,
        ← Finset.union_assoc]
  -- ---------- V component ----------
  · change (G.V \ W₂).image IntExtNode.unsplit
          = G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit
    ext x
    refine ⟨?_, ?_⟩
    · intro hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hvV, hv_notW⟩ := Finset.mem_sdiff.mp hv
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨v, hvV, rfl⟩, ?_⟩
      intro h
      obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
      injection hweq with hwv
      exact hv_notW (hwv ▸ hw)
    · intro hx
      obtain ⟨hxV, hx_notW⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hxV
      refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
      refine Finset.mem_sdiff.mpr ⟨hv, ?_⟩
      intro hvW
      exact hx_notW (Finset.mem_image.mpr ⟨v, hvW, rfl⟩)
  -- ---------- E component ----------
  -- E field is unchanged by the refactor (still `Finset (Node × Node)`),
  -- so this carries verbatim from the pre-refactor proof.
  · change (G.E.filter (fun e : Node × Node => e.2 ∉ W₂)).image
              (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
            ∪ (W₁ \ (G.J ∪ W₂)).image
                (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))
          = (G.E.image (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
              ∪ (W₁ \ G.J).image
                  (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))).filter
              (fun e : IntExtNode Node × IntExtNode Node =>
                e.2 ∉ W₂.image IntExtNode.unsplit)
    rw [h_W₁_sdiff_collapse, Finset.filter_union]
    congr 1
    · ext ⟨a, b⟩
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨e, ⟨heE, he2⟩, hab⟩
        refine ⟨⟨e, heE, hab⟩, ?_⟩
        rintro ⟨w, hwW₂, hweq⟩
        have hbe : b = IntExtNode.unsplit e.2 := by
          have := congrArg Prod.snd hab; simpa using this.symm
        rw [hbe] at hweq
        injection hweq with hwe
        exact he2 (hwe ▸ hwW₂)
      · rintro ⟨⟨e, heE, hab⟩, h_not⟩
        refine ⟨e, ⟨heE, ?_⟩, hab⟩
        intro he2
        apply h_not
        have hbe : b = IntExtNode.unsplit e.2 := by
          have := congrArg Prod.snd hab; simpa using this.symm
        rw [hbe]
        exact ⟨e.2, he2, rfl⟩
    · ext ⟨a, b⟩
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨w, hwW, hab⟩
        refine ⟨⟨w, hwW, hab⟩, ?_⟩
        rintro ⟨w', hwW₂, hweq⟩
        have hbw : b = IntExtNode.unsplit w := by
          have := congrArg Prod.snd hab; simpa using this.symm
        rw [hbw] at hweq
        injection hweq with hwweq
        cases hwweq
        exact Finset.disjoint_left.mp hDisj (Finset.mem_sdiff.mp hwW).1 hwW₂
      · rintro ⟨⟨w, hw, hab⟩, _⟩
        exact ⟨w, hw, hab⟩
  -- ---------- L component (refactor: Sym2 filter/image swap) ----------
  --   middle.L = (G.L.filter (fun s => ∀ v ∈ s, v ∉ W₂)).image
  --                (Sym2.map IntExtNode.unsplit)
  --   mixed.L  = (G.L.image (Sym2.map IntExtNode.unsplit)).filter
  --                (fun s => ∀ v ∈ s, v ∉ W₂.image IntExtNode.unsplit)
  -- Standard filter/image swap on the `Sym2` quotient, using
  -- `Sym2.mem_map` to unfold `v ∈ Sym2.map f s` to `∃ u ∈ s, f u = v`.
  -- The two endpoints of the unordered pair are handled by a single
  -- `Sym2.mem_map`-pull, instead of the original's two separate
  -- `.1`/`.2`-by-`.1`/`.2` argument under `Finset (Node × Node)`.
  · change (G.L.filter (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₂)).image
              (Sym2.map IntExtNode.unsplit)
          = (G.L.image (Sym2.map IntExtNode.unsplit)).filter
              (fun s : Sym2 (IntExtNode Node) => ∀ v ∈ s, v ∉ W₂.image IntExtNode.unsplit)
    ext s
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨s', ⟨hs'L, hs'W⟩, rfl⟩
      refine ⟨⟨s', hs'L, rfl⟩, ?_⟩
      intro v hv
      obtain ⟨u, huS', rfl⟩ := Sym2.mem_map.mp hv
      intro h_in
      obtain ⟨w, hwW₂, hwEq⟩ := h_in
      injection hwEq with hweq
      exact hs'W u huS' (hweq ▸ hwW₂)
    · rintro ⟨⟨s', hs'L, rfl⟩, hsW⟩
      refine ⟨s', ⟨hs'L, ?_⟩, rfl⟩
      intro u huS'
      have h_in : IntExtNode.unsplit u ∈ Sym2.map IntExtNode.unsplit s' :=
        Sym2.mem_map.mpr ⟨u, huS', rfl⟩
      intro huW₂
      exact hsW _ h_in ⟨u, huW₂, rfl⟩

end CDMG

end Causality
