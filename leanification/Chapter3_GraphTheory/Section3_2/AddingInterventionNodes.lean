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

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: addInterventionNodes_comm_disjoint
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
-- REFACTOR-BLOCK-ORIGINAL-END: addInterventionNodes_comm_disjoint

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: flattenIntExt_injOn_of_disjoint (was: refactor_flattenIntExt_injOn_of_disjoint)
-- ## Helper: `flattenIntExt` is `InjOn` on the iterated graph's J ∪ V
--
-- Net-new helper introduced by refactor `eqViaNodeMap_injective`
-- to discharge the strengthened predicate's `Set.InjOn` conjunct
-- for the carrier map `flattenIntExt` of sub-claim (a).
--
-- ### Role
--
-- Establishes `Set.InjOn flattenIntExt` on the carrier set of
-- the iterated CDMG `(G_{doit(I_{W₁})})_{doit(I_{W₂})}`, under
-- the disjointness hypothesis `Disjoint W₁ W₂`.  This is the
-- technical core of the refactor: every existing image-equality
-- conjunct (J, V, E, L) of the original
-- `addInterventionNodes_comm_disjoint` ports verbatim under the
-- new predicate; only the new InjOn conjunct requires a
-- substantively new proof, and the whole of that work is
-- concentrated in this lemma.
--
-- ### Why a separate lemma (rather than inlined in the main theorem)?
--
-- Reused twice in `refactor_addInterventionNodes_comm_disjoint`:
--   * Direction (a-1) `(G_{doit(I_{W₁})})_{doit(I_{W₂})} = G_{doit(I_{W₁ ∪ W₂})}`:
--     helper applied with `(W₁, W₂, hDisj)` in the natural order.
--   * Direction (a-2) `(G_{doit(I_{W₂})})_{doit(I_{W₁})} = G_{doit(I_{W₁ ∪ W₂})}`:
--     helper applied with `(W₂, W₁, hDisj.symm)` -- the iterated
--     graph in the InjOn obligation swaps inner/outer roles of
--     `W₁` and `W₂`, and `Disjoint` is symmetric.
-- The proof argument is also geometrically clean enough to
-- deserve its own name: a four-cell partition of the iterated
-- graph's `J ∪ V` followed by a 3 × 3 = 9 case analysis (cells
-- (1) `ι(ι(J))` and (2) `ι(ι(V))` of the tex twin merged into a
-- single `.unsplit (.unsplit a)` pattern with `a ∈ G.J ∨ a ∈ G.V`,
-- since the constructor chain and the within-cell injectivity
-- argument are identical; cells (3) `ι(I_{W₁})` and (4) `I_{W₂}`
-- kept separate as `.unsplit (.intCopy w)` and
-- `.intCopy (.unsplit w)` patterns), mirroring the verified tex
-- twin's "Injectivity of the canonical flatten map
-- `flattenIntExt` on the iterated extended graph's J ∪ V"
-- paragraph.
--
-- ### Why `Set.InjOn` on `↑(...).J ∪ ↑(...).V` (matching the predicate's carrier set verbatim)?
--
-- Pasted directly from `refactor_eqViaNodeMap`'s first-conjunct
-- shape so that the consumer call site in the main theorem can
-- plug this lemma in with no Set-arithmetic glue.  The
-- iterated-graph operand is the same one that appears on the
-- left of `refactor_eqViaNodeMap` in the main theorem statement,
-- so the carrier sets line up definitionally.
--
-- ### Why disjointness is load-bearing
--
-- `flattenIntExt` is NOT globally injective on
-- `IntExtNode (IntExtNode Node)`.  For instance,
-- `flattenIntExt (.unsplit (.intCopy w)) = .intCopy w` and
-- `flattenIntExt (.intCopy (.unsplit w)) = .intCopy w` -- two
-- distinct input patterns collide off the iterated graph's
-- `J ∪ V`.  The four-cell partition rules out most such
-- would-be collisions structurally, but one pattern survives
-- structural filtering and needs the disjointness hypothesis to
-- close: the cell-(3)-vs-cell-(4) collision
-- `.intCopy w₁` (image of an iterated `.unsplit (.intCopy w₁)`
-- with `w₁ ∈ W₁ \ G.J`) vs. `.intCopy w₂` (image of an iterated
-- `.intCopy (.unsplit w₂)` with `w₂ ∈ W₂ \ G.J`), which would
-- force `w₁ = w₂ ∈ W₁ ∩ W₂`.  The `Disjoint W₁ W₂` hypothesis
-- is consumed exactly in those two of the 9 subcases (the two
-- `(injection heq with h; subst h; exact absurd ...)` branches
-- in the closing `first | ... | ... | ...` block), matching the
-- "load-bearing use of the disjointness hypothesis
-- `W₁ ∩ W₂ = ∅`" call-out in the verified tex twin's
-- cell-(3)-vs-cell-(4) across-cell injectivity bullet.
private lemma refactor_flattenIntExt_injOn_of_disjoint
    (G : CDMG Node) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V) (hDisj : Disjoint W₁ W₂) :
    Set.InjOn flattenIntExt
        ((↑(extendingCDMGsWith
              (extendingCDMGsWith G W₁ hW₁)
              (W₂.image IntExtNode.unsplit)
              (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)).J :
            Set (IntExtNode (IntExtNode Node))) ∪
          ↑(extendingCDMGsWith
              (extendingCDMGsWith G W₁ hW₁)
              (W₂.image IntExtNode.unsplit)
              (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)).V) := by
  -- Classification: every element `z` of the iterated graph's
  -- `J ∪ V` (as Finsets) is in exactly one of 3 disjoint pattern
  -- families.  This compresses the verified tex twin's 4 cells:
  -- cells (1) `ι(ι(J))` and (2) `ι(ι(V))` are merged into a
  -- single `.unsplit (.unsplit a)` pattern (with
  -- `a ∈ G.J ∨ a ∈ G.V`), since the constructor chain and the
  -- injectivity proof are identical for both; cells (3) and (4)
  -- are kept separate as `.unsplit (.intCopy w)` and
  -- `.intCopy (.unsplit w)` patterns, indexed by `W₁ \ G.J` and
  -- `W₂ \ G.J` respectively.
  have classify : ∀ z : IntExtNode (IntExtNode Node),
      z ∈ (extendingCDMGsWith
              (extendingCDMGsWith G W₁ hW₁)
              (W₂.image IntExtNode.unsplit)
              (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)).J ∪
          (extendingCDMGsWith
              (extendingCDMGsWith G W₁ hW₁)
              (W₂.image IntExtNode.unsplit)
              (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)).V →
      (∃ a : Node, (a ∈ G.J ∨ a ∈ G.V) ∧
            z = IntExtNode.unsplit (IntExtNode.unsplit a))
        ∨ (∃ w : Node, w ∈ W₁ ∧ w ∉ G.J ∧
              z = IntExtNode.unsplit (IntExtNode.intCopy w))
        ∨ (∃ w : Node, w ∈ W₂ ∧ w ∉ G.J ∧
              z = IntExtNode.intCopy (IntExtNode.unsplit w)) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hJ | hV
    · -- z ∈ iterated graph's J
      change z ∈ (G.J.image IntExtNode.unsplit ∪
                    (W₁ \ G.J).image IntExtNode.intCopy).image
                  IntExtNode.unsplit ∪
                (W₂.image IntExtNode.unsplit \
                  (G.J.image IntExtNode.unsplit ∪
                    (W₁ \ G.J).image IntExtNode.intCopy)).image
                  IntExtNode.intCopy at hJ
      rcases Finset.mem_union.mp hJ with hJ1 | hJ2
      · -- outer `.unsplit` branch: z = .unsplit y, y ∈ inner J
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hJ1
        rcases Finset.mem_union.mp hy with hyJ | hyW
        · -- y = .unsplit j for j ∈ G.J → cell (1)
          obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hyJ
          exact Or.inl ⟨j, Or.inl hjJ, rfl⟩
        · -- y = .intCopy w for w ∈ W₁ \ G.J → cell (3)
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hyW
          obtain ⟨hwW, hwNJ⟩ := Finset.mem_sdiff.mp hw
          exact Or.inr (Or.inl ⟨w, hwW, hwNJ, rfl⟩)
      · -- outer `.intCopy` branch: z = .intCopy y,
        -- y ∈ W₂.image .unsplit \ inner J → cell (4)
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hJ2
        obtain ⟨hyW, hyNot⟩ := Finset.mem_sdiff.mp hy
        obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hyW
        have hwNJ : w ∉ G.J := by
          intro hjJ
          exact hyNot (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨w, hjJ, rfl⟩))
        exact Or.inr (Or.inr ⟨w, hwW, hwNJ, rfl⟩)
    · -- z ∈ iterated graph's V = (G.V.image .unsplit).image .unsplit → cell (2)
      change z ∈ (G.V.image IntExtNode.unsplit).image IntExtNode.unsplit at hV
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hV
      obtain ⟨v, hvV, rfl⟩ := Finset.mem_image.mp hy
      exact Or.inl ⟨v, Or.inr hvV, rfl⟩
  -- Main InjOn argument.
  intro x hx y hy heq
  -- Convert hx, hy from Set membership to Finset disjunction-then-union.
  have hx' : x ∈ (extendingCDMGsWith
                    (extendingCDMGsWith G W₁ hW₁)
                    (W₂.image IntExtNode.unsplit)
                    (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)).J ∪
              (extendingCDMGsWith
                    (extendingCDMGsWith G W₁ hW₁)
                    (W₂.image IntExtNode.unsplit)
                    (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)).V := by
    rcases hx with h | h
    · exact Finset.mem_union_left _ (Finset.mem_coe.mp h)
    · exact Finset.mem_union_right _ (Finset.mem_coe.mp h)
  have hy' : y ∈ (extendingCDMGsWith
                    (extendingCDMGsWith G W₁ hW₁)
                    (W₂.image IntExtNode.unsplit)
                    (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)).J ∪
              (extendingCDMGsWith
                    (extendingCDMGsWith G W₁ hW₁)
                    (W₂.image IntExtNode.unsplit)
                    (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)).V := by
    rcases hy with h | h
    · exact Finset.mem_union_left _ (Finset.mem_coe.mp h)
    · exact Finset.mem_union_right _ (Finset.mem_coe.mp h)
  -- Classify x and y into one of 3 patterns each (3 × 3 = 9 subcases).
  rcases classify x hx' with
    ⟨xa, _, rfl⟩ | ⟨xw, hxw, _, rfl⟩ | ⟨xw, hxw, _, rfl⟩ <;>
  rcases classify y hy' with
    ⟨ya, _, rfl⟩ | ⟨yw, hyw, _, rfl⟩ | ⟨yw, hyw, _, rfl⟩ <;>
  -- Each of the 9 cases has `heq` of the form
  -- `<constructor> <var> = <constructor> <var>` after definitional
  -- unfolding of `flattenIntExt`; close by structural
  -- injection-and-rfl, by injection-then-disjointness
  -- contradiction, or by constructor mismatch (`cases heq`).
  first
  -- Same-form cases (3): cells (1+2)-vs-(1+2), (3)-vs-(3), (4)-vs-(4).
  | (injection heq with h; subst h; rfl)
  -- Cross-W cases (2): cells (3)-vs-(4) and (4)-vs-(3) using disjointness.
  | (injection heq with h; subst h;
     exact absurd hyw (Finset.disjoint_left.mp hDisj hxw))
  | (injection heq with h; subst h;
     exact absurd hxw (Finset.disjoint_left.mp hDisj hyw))
  -- Cross-constructor cases (4): cells (1+2)-vs-(3), (3)-vs-(1+2),
  -- (1+2)-vs-(4), (4)-vs-(1+2).
  | cases heq
-- REFACTOR-BLOCK-REPLACEMENT-END: flattenIntExt_injOn_of_disjoint

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: addInterventionNodes_comm_disjoint (was: refactor_addInterventionNodes_comm_disjoint)
-- ref: claim_3_14
--
-- ## Refactor: `refactor_addInterventionNodes_comm_disjoint`
--
-- Refactor of `addInterventionNodes_comm_disjoint` for refactor
-- `eqViaNodeMap_injective`.  Same conjunction `(a-1) ∧ (a-2)`
-- shape as the original (two `eqViaNodeMap` equalities through
-- the shared single extension `G_{doit(I_{W₁ ∪ W₂})}`), but the
-- predicate `eqViaNodeMap` is replaced by the strengthened
-- `refactor_eqViaNodeMap` (carrying a fifth `Set.InjOn`
-- conjunct on the carrier map `flattenIntExt`).
--
-- ### What's reused from the original
--
-- The four image-equality conjuncts (`J`, `V`, `E`, `L`) come
-- straight from the existing (unchanged)
-- `addInterventionNodes_comm_disjoint` via the destructuring
-- binder in the opening `obtain ⟨⟨hJa, hVa, hEa, hLa⟩, ⟨hJb,
-- hVb, hEb, hLb⟩⟩ := ...` line.  The refactor does NOT redo the
-- ~200-line J/V/E/L bookkeeping -- it would produce a
-- bit-for-bit identical tactic block, so reusing the original
-- keeps the LN-to-Lean correspondence one-to-one and the file
-- size manageable.  The new content is purely the InjOn
-- discharge (the two `exact` lines below the destructure).
--
-- ### Why the InjOn discharge is non-trivial
--
-- The carrier map `flattenIntExt` is not globally injective: it
-- collapses off-iterated-graph constructor patterns (see the
-- comment block above
-- `refactor_flattenIntExt_injOn_of_disjoint`).  The witnessing
-- InjOn property holds only on the iterated graph's `J ∪ V`,
-- and only because the disjointness hypothesis
-- `Disjoint W₁ W₂` rules out the cell-(3)-vs-cell-(4)
-- cross-cell collision (an iterated `.unsplit (.intCopy w₁)` for
-- `w₁ ∈ W₁ \ G.J` vs. an iterated `.intCopy (.unsplit w₂)` for
-- `w₂ ∈ W₂ \ G.J`, both of which flatten to the single-step
-- `.intCopy` symbol).  Without disjointness the InjOn conjunct
-- fails, and so does the LN's claim "the iterated CDMG equals
-- the single-step CDMG `G_{doit(I_{W₁ ∪ W₂})}`" -- two
-- intervention nodes for a shared `w ∈ W₁ ∩ W₂` would collide
-- in the iterated graph in a way the single-step graph cannot
-- reproduce.
--
-- ### How disjointness flows in (both orderings)
--
-- The technical core is the helper
-- `refactor_flattenIntExt_injOn_of_disjoint` above, invoked
-- twice:
--   * Direction (a-1)
--     `(G_{doit(I_{W₁})})_{doit(I_{W₂})} = G_{doit(I_{W₁ ∪ W₂})}`:
--     helper applied with `(W₁, W₂, hDisj)` in the natural order.
--   * Direction (a-2)
--     `(G_{doit(I_{W₂})})_{doit(I_{W₁})} = G_{doit(I_{W₁ ∪ W₂})}`:
--     helper applied with `(W₂, W₁, hDisj.symm)` -- the iterated
--     graph in the InjOn obligation swaps inner/outer roles of
--     `W₁` and `W₂`, and `Disjoint` is symmetric.
-- Both directions land at the same single-step right-hand side
-- `G_{doit(I_{W₁ ∪ W₂})}`, recovering the LN's triple-equality
-- "swap-symmetry" reading via transitivity, exactly as in the
-- verified tex twin's "Swap-symmetry and recovery of the LN's
-- triple equality" closing paragraph.
--
-- ### Why this refactor does not touch `addInterventionNodes_comm_hardIntervention`
--
-- Sub-claim (b) of the LN (the second equation
-- `(G_{doit(I_{W₁})})_{doit(W₂)} = (G_{doit(W₂)})_{doit(I_{W₁})}
--      = G_{doit(I_{W₁}, W₂)}`) has no carrier mismatch: both
-- sides live on the same single-extension carrier
-- `J_{doit(I_{W₁})} ∪ V_{doit(I_{W₁})}` (the outer hard
-- intervention `doit(W₂)` preserves its argument CDMG's carrier
-- per `def_3_10`), so the sub-claim (b) theorem
-- `addInterventionNodes_comm_hardIntervention` uses literal
-- `=` of `CDMG (IntExtNode Node)` rather than `eqViaNodeMap`.
-- The refactor strengthens `eqViaNodeMap` only; it does not
-- touch literal-`=` theorems and the verified tex twin
-- (`tex/refactor_claim_3_14_proof_AddingInterventionNodes.tex`,
-- header comment) explicitly notes that sub-claim (b) "is *not*
-- touched" by `eqViaNodeMap_injective`.
-- claim_3_14 -- start statement
theorem refactor_addInterventionNodes_comm_disjoint (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    refactor_eqViaNodeMap
        (extendingCDMGsWith
            (extendingCDMGsWith G W₁ hW₁)
            (W₂.image IntExtNode.unsplit)
            (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂))
        (extendingCDMGsWith G (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenIntExt
      ∧
    refactor_eqViaNodeMap
        (extendingCDMGsWith
            (extendingCDMGsWith G W₂ hW₂)
            (W₁.image IntExtNode.unsplit)
            (image_unsplit_subset_extendingCDMGsWith_carrier hW₂ hW₁))
        (extendingCDMGsWith G (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenIntExt
-- claim_3_14 -- end statement
:= by
  -- Reuse the original theorem for the four image-equality
  -- conjuncts (J, V, E, L) in each of the two directions.
  obtain ⟨⟨hJa, hVa, hEa, hLa⟩, ⟨hJb, hVb, hEb, hLb⟩⟩ :=
    addInterventionNodes_comm_disjoint G W₁ W₂ hW₁ hW₂ hDisj
  refine ⟨⟨?_, hJa, hVa, hEa, hLa⟩, ⟨?_, hJb, hVb, hEb, hLb⟩⟩
  · -- InjOn for direction (a-1): iterated extension W₁ then W₂.
    exact refactor_flattenIntExt_injOn_of_disjoint G W₁ W₂ hW₁ hW₂ hDisj
  · -- InjOn for direction (a-2): iterated extension W₂ then W₁.
    exact refactor_flattenIntExt_injOn_of_disjoint G W₂ W₁ hW₂ hW₁ hDisj.symm
-- REFACTOR-BLOCK-REPLACEMENT-END: addInterventionNodes_comm_disjoint

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
