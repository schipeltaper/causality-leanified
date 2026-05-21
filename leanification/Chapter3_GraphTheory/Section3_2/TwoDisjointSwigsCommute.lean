import Chapter3_GraphTheory.Section3_2.NodeSplittingHard
import Chapter3_GraphTheory.Section3_2.TwoDisjointNodeSplittingsCommute

-- TeX statement: tex/claim_3_10_statement_TwoDisjointNode.tex
-- TeX proof:    tex/claim_3_10_proof_TwoDisjointNode.tex (Manager B)

/-!
# Two disjoint node-splitting hard interventions (SWIGs) commute (claim_3_10)

This file formalises the lecture notes' lemma "two disjoint node-splitting
hard interventions commute" -- `lecture-notes/lecture_notes/graphs.tex`
Lem at lines 627 -- 632 with proof at lines 635 -- 660. The LN states the
chained equality

  `(G_{swig(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{swig(W₁)} = G_{swig(W₁ ⊔ W₂)}`

under the precondition `W₁, W₂ ⊆ V` with `W₁ ∩ W₂ = ∅`. This is the SWIG
(`\swig`) mirror of `claim_3_7` (the `\spl` version proven in
`TwoDisjointNodeSplittingsCommute.lean`).

Like the `\spl` case, iterated SWIG is *type-changing*: the iterated SWIG
lives over `(α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)` while the merged SWIG lives over
`α ⊕ ↑(W₁ ∪ W₂)`. The two carriers are canonically *isomorphic* via the
same re-labeling bijection `fusionEquiv` used in the `\spl` case (the
SWIG carrier shape `α ⊕ ↑W` is inherited verbatim from `nodeSplittingOn`
-- the hard-intervention layer of `swig` does not touch the carrier).

This file delivers:

* `subset_swig_V_of_subset_V` -- bridging lemma so the inner
  `swig` call's precondition discharges cleanly. The proof is one
  line because `nodeSplittingHardInterventionOn_V` reduces
  `(G.swig W₁ hW₁).V` to `Sum.inl '' G.V` (the `range Sum.inr` piece
  has been killed by the HI), so a `W₂ ⊆ G.V` hypothesis lifts under
  `Set.image_subset`.
* `swig_swig_equiv` -- fusion lemma statement (body = `sorry`,
  Manager B fills it). Mirrors `nodeSplittingOn_nodeSplittingOn_equiv`
  with `swig` in place of `nodeSplittingOn`.
* `swig_comm_equiv` -- commute corollary statement (body = `sorry`,
  Manager B fills it via `.symm.trans` of the fusion lemma, same
  pattern as `nodeSplittingOn_comm_equiv`).

## Foundation reuse from `TwoDisjointNodeSplittingsCommute.lean`

`CDMGEquiv`, its groupoid laws (`refl` / `symm` / `trans`), and
`fusionEquiv` are imported verbatim from the sibling file rather than
redefined here. The `\spl` design decision (`CDMGEquiv` lives in the
claim_3_7 file rather than promoted to Section 3.1) explicitly named
this row as the second expected consumer (sibling file's docstring
lines 60 -- 65); we are that consumer.
-/

namespace Causality

namespace CDMG

universe u

variable {α β γ : Type u}

/-! ## Helper: `W₂ ⊆ V` lifts to `Sum.inl '' W₂ ⊆ V_swig` -/

/-- If `W₂ ⊆ G.V`, then `Sum.inl '' W₂` is contained in the vertex set of
the SWIG `G.swig W₁ hW₁`. Used to discharge the inner precondition of the
iterated SWIG in the fusion lemma below.

## Design choice

* **Why a named helper at all (not inline in the signature).** The
  fusion and commute statements below need to *type-check* the
  second-level `swig` application
  `(G.swig W₁ hW₁).swig (Sum.inl '' W₂) ?_`, whose hypothesis slot
  has the literal shape `Sum.inl '' W₂ ⊆ (G.swig W₁ hW₁).V`. We
  cannot just write `(Sum.inl '' W₂) ⊆ _` inline: the proof of that
  containment -- a single `rw` against
  `nodeSplittingHardInterventionOn_V` followed by `Set.image_mono
  hW₂` -- would otherwise have to sit in *every* signature that
  iterates SWIGs (the fusion lemma, the commute corollary, and any
  later consumer that wants the same iterate). Factoring it as
  `subset_swig_V_of_subset_V hW₂ hW₁` lets each call site discharge
  the precondition by name and keeps the iterated-SWIG type readable.
  Same factoring as `subset_nodeSplittingOn_V_of_subset_V` in the
  sibling claim_3_7 file (lines 242 -- 247 of
  `TwoDisjointNodeSplittingsCommute.lean`).

* **No `Disjoint W₁ W₂` hypothesis.** The SWIG's output layer is
  `Sum.inl '' G.V` (the `range Sum.inr` piece introduced by
  `nodeSplittingOn` is killed by the hard intervention on `W^i`),
  so any `W₂ ⊆ G.V` lifts under `Sum.inl` into the SWIG carrier
  regardless of how `W₁` and `W₂` overlap. Disjointness is only
  load-bearing for the *fusion* itself, not for this embedding
  step. Mirrors the same design call recorded for
  `subset_nodeSplittingOn_V_of_subset_V` in the sibling file
  (lines 242 -- 247 of `TwoDisjointNodeSplittingsCommute.lean`).

* **Simpler proof than the `\spl` analogue.** In the `\spl` case
  `subset_nodeSplittingOn_V_of_subset_V` had to land in
  `Sum.inl '' G.V ∪ Set.range Sum.inr` (the `nodeSplittingOn_V`
  shape) and pick the left disjunct. Here the
  `nodeSplittingHardInterventionOn_V` simp lemma
  (`NodeSplittingHard.lean` lines 253 -- 267) collapses the RHS to
  just `Sum.inl '' G.V`, so the conclusion follows by a single
  `Set.image_mono` step. -/
theorem subset_swig_V_of_subset_V
    {G : CDMG α} {W₁ W₂ : Set α} (hW₂ : W₂ ⊆ G.V) (hW₁ : W₁ ⊆ G.V) :
    Sum.inl '' W₂ ⊆ (G.swig W₁ hW₁).V := by
  rw [show (G.swig W₁ hW₁).V = _ from nodeSplittingHardInterventionOn_V _ _ _]
  exact Set.image_mono hW₂

/-! ## The fusion lemma and the commute corollary -/

-- claim_3_10 (part 1/2)
-- title: TwoDisjointNode -- SWIG fusion lemma
--
-- Iterating two disjoint SWIGs is equivalent (modulo the canonical
-- re-labeling `fusionEquiv`) to a single SWIG on the union. The LN
-- proves this as the first `=` of the chained equality
-- `(G_{swig(W₁)})_{swig(W₂)} = G_{swig(W₁ ⊔ W₂)}` -- the second `=`
-- (commute) follows by symmetry, formalised as `swig_comm_equiv`
-- below.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 627 -- 632)
-- linewrapped within the prose paragraph and within the displayed
-- equation; LaTeX whitespace collapses, so this is verbatim under
-- \LaTeX semantics:

\begin{claimmark}
\begin{Lem}[Two disjoint node-splitting hard interventions commute]
   Let $G=(J,V,E,L)$ be a CADMG and $W_1, W_2 \ins V$ two disjoint
   subsets of the output nodes from $G$.
   Then the CADMG obtained from first node-splitting on $W_1$ and
   then node-splitting on $W_2$ is the same CADMG that arises from
   first node-splitting on $W_2$ and then node-splitting on $W_1$:
   \[ \lp G_{\swig(W_1)} \rp_{\swig(W_2)} =  \lp G_{\swig(W_2)} \rp_{\swig(W_1)}
      =  G_{\swig(W_1 \dcup W_2)}.   \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_10 part 1/2 (SWIG fusion lemma): iterated SWIG is
`CDMGEquiv`-equivalent to a single SWIG on the union. Mirrors the first
half (`(G_{swig(W₁)})_{swig(W₂)} = G_{swig(W₁ ⊔ W₂)}`) of the chained
equality in the `\Lem` at `lecture-notes/lecture_notes/graphs.tex`
line 630. Body = `sorry`; the Lean proof is Manager B's job (the LN's
own proof at lines 635 -- 660 gives the four field-equality
arguments).

## Design choice

* **`CDMGEquiv` rather than literal `Eq`.** Same reasoning as the
  `\spl` fusion lemma: the two CDMGs live over *different* carrier
  types `(α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)` (iterated) and
  `α ⊕ ↑(W₁ ∪ W₂)` (merged), so literal `Eq` is not even
  type-correct. This is the *carrier-rewriting* regime, in
  explicit contrast with the *carrier-preserving* regime of the
  HI-only and HI-mixed-with-NS commute lemmas: in
  `HardInterventionsCommute.lean` (claim_3_4) both iterates live
  over the same `α`, and in `HardInterventionNodeSplittingCommute.lean`
  (claim_3_8) both sides live over `α ⊕ ↑W₂` because HI is
  carrier-preserving and the single NS is applied to the same
  `W₂` on each side -- *that* contrast is spelled out at
  `HardInterventionNodeSplittingCommute.lean` lines 20 -- 44 and is
  the load-bearing reason claim_3_4 / claim_3_8 ship literal `Eq`
  while claim_3_7 / this row ship `CDMGEquiv`. The SWIG carrier is
  inherited verbatim from `nodeSplittingOn` (the HI layer of `swig`
  does *not* touch the carrier -- see the four `@[simp]` lemmas
  `nodeSplittingHardInterventionOn_J/V` and
  `mem_nodeSplittingHardInterventionOn_E/L` in
  `NodeSplittingHard.lean` lines 237 -- 319, which all leave the
  carrier `α ⊕ ↑W` untouched), so the same `(α ⊕ ↑W₁) ⊕ ↑(Sum.inl
  '' W₂)` vs `α ⊕ ↑(W₁ ∪ W₂)` mismatch as the `\spl` case arises
  here.

* **Reuse `CDMGEquiv` / `fusionEquiv` from the sibling claim_3_7
  file, do not redefine.** The sibling
  `TwoDisjointNodeSplittingsCommute.lean` (docstring lines
  60 -- 65) explicitly anticipated this row as the second consumer
  of `CDMGEquiv`. Per its design notes, the `CDMGEquiv` structure
  stays *local* to that file until a *third* consumer triggers
  promotion to `Section3_1/`; two consumers is not enough.
  `fusionEquiv` works verbatim here because its codomain
  `(α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)` is exactly the SWIG iterate's
  carrier (the SWIG inherits `nodeSplittingOn`'s `α ⊕ ↑W` shape
  through the four `nodeSplittingHardInterventionOn_*` simp
  lemmas cited above). Concretely: changing the `CDMGEquiv` /
  `fusionEquiv` shape later means changing it in both the
  claim_3_7 site *and* this row -- the two are now joined
  consumers of the same API.

* **`W₁ ∪ W₂` plus `Disjoint W₁ W₂`, not `W₁ ⊔ W₂` / a
  `DisjUnion`-style type.** The LN writes `\dcup` (disjoint
  union) in the displayed equation, but Mathlib's standard idiom
  for "disjoint union of two `Set α`s" is `W₁ ∪ W₂` paired with a
  separate `Disjoint W₁ W₂` hypothesis -- this is what
  `Equiv.Set.union` (the Mathlib equivalence at the heart of
  `fusionEquiv`) consumes, and what `Set.union_subset` consumes to
  build the `W₁ ∪ W₂ ⊆ G.V` precondition for the merged
  `G.swig (W₁ ∪ W₂) _`. Encoding `\dcup` as `W₁ ∪ W₂` + `hdisj`
  keeps us inside Mathlib's set-API verbatim; a `DisjUnion`-style
  dedicated type would force every downstream consumer to chase a
  fresh `Sum`-versus-`Set` translation. The disjointness
  hypothesis appears here because `fusionEquiv`'s underlying
  `Equiv.Set.union` requires it.

* **Fusion + commute split mirrors the LN's own proof structure.**
  The LN proves only the fusion direction
  `(G_{swig(W₁)})_{swig(W₂)} = G_{swig(W₁ ⊔ W₂)}` and closes the
  other equality with "the other follows by symmetry"
  (`graphs.tex` line 635). We follow that factoring: fusion is the
  load-bearing lemma stated here, commute is the corollary
  `swig_comm_equiv` below. Mirrors the `\spl` row exactly. -/
noncomputable def swig_swig_equiv
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hdisj : Disjoint W₁ W₂) :
    CDMGEquiv
      ((G.swig W₁ hW₁).swig (Sum.inl '' W₂)
          (subset_swig_V_of_subset_V hW₂ hW₁))
      (G.swig (W₁ ∪ W₂) (Set.union_subset hW₁ hW₂)) := by
  letI : DecidablePred (· ∈ W₁) := Classical.decPred _
  -- `fusionEquiv` (forward direction) on each constructor case.
  have apply_inl : ∀ (a : α),
      fusionEquiv W₁ W₂ hdisj (Sum.inl a) = Sum.inl (Sum.inl a) := fun a => by
    simp [fusionEquiv]
  have apply_inr_left : ∀ (w : α) (hw₁ : w ∈ W₁) (hw : w ∈ W₁ ∪ W₂),
      fusionEquiv W₁ W₂ hdisj (Sum.inr ⟨w, hw⟩) =
        Sum.inl (Sum.inr ⟨w, hw₁⟩) := by
    intros w hw₁ hw
    have h_union : (Equiv.Set.union hdisj) ⟨w, hw⟩ = Sum.inl ⟨w, hw₁⟩ :=
      Equiv.Set.union_apply_left (a := ⟨w, hw⟩) hdisj hw₁
    simp [fusionEquiv, h_union]
  have apply_inr_right : ∀ (w : α) (hw₂ : w ∈ W₂) (hw : w ∈ W₁ ∪ W₂),
      fusionEquiv W₁ W₂ hdisj (Sum.inr ⟨w, hw⟩) =
        Sum.inr ⟨Sum.inl w, ⟨w, hw₂, rfl⟩⟩ := by
    intros w hw₂ hw
    have h_union : (Equiv.Set.union hdisj) ⟨w, hw⟩ = Sum.inr ⟨w, hw₂⟩ :=
      Equiv.Set.union_apply_right (a := ⟨w, hw⟩) hdisj hw₂
    simp [fusionEquiv, h_union]
  -- Derive the symm-direction by `e.symm (e x) = x`.
  have symm_inl_inl : ∀ (a : α),
      (fusionEquiv W₁ W₂ hdisj).symm (Sum.inl (Sum.inl a)) = Sum.inl a := fun a => by
    rw [← apply_inl a]; exact Equiv.symm_apply_apply _ _
  have symm_inl_inr : ∀ (w : α) (hw₁ : w ∈ W₁) (hw : w ∈ W₁ ∪ W₂),
      (fusionEquiv W₁ W₂ hdisj).symm (Sum.inl (Sum.inr ⟨w, hw₁⟩)) =
        Sum.inr ⟨w, hw⟩ := fun w hw₁ hw => by
    rw [← apply_inr_left w hw₁ hw]; exact Equiv.symm_apply_apply _ _
  have symm_inr : ∀ (w : α) (hw₂ : w ∈ W₂) (hw : w ∈ W₁ ∪ W₂),
      (fusionEquiv W₁ W₂ hdisj).symm (Sum.inr ⟨Sum.inl w, ⟨w, hw₂, rfl⟩⟩) =
        Sum.inr ⟨w, hw⟩ := fun w hw₂ hw => by
    rw [← apply_inr_right w hw₂ hw]; exact Equiv.symm_apply_apply _ _
  -- Key lemma for the E-field: `fusionEquiv` transports the source-side
  -- relabel of the merged SWIG to the iterated source-side relabel.
  -- Same statement as the `\spl` sibling: the SWIG carrier shape is
  -- inherited from `nodeSplittingOn`, so `split1` behaves identically.
  have key_e_source : ∀ (v : α),
      fusionEquiv W₁ W₂ hdisj (split1 (W₁ ∪ W₂) v) =
        split1 (Sum.inl '' W₂) (split1 W₁ v) := by
    intro v
    by_cases hv₁ : v ∈ W₁
    · -- v ∈ W₁: both sides land at `Sum.inl (Sum.inr ⟨v, hv₁⟩)`.
      have hv : v ∈ W₁ ∪ W₂ := Or.inl hv₁
      have hv_notin : (Sum.inr ⟨v, hv₁⟩ : α ⊕ ↑W₁) ∉ (Sum.inl '' W₂ : Set _) := by
        rintro ⟨_, _, h⟩; exact nomatch h
      rw [split1_of_mem hv, split1_of_mem hv₁, split1_of_not_mem hv_notin]
      exact apply_inr_left v hv₁ hv
    · by_cases hv₂ : v ∈ W₂
      · -- v ∈ W₂ (and v ∉ W₁): both sides land at `Sum.inr ⟨Sum.inl v, _⟩`.
        have hv : v ∈ W₁ ∪ W₂ := Or.inr hv₂
        have hv_mem : (Sum.inl v : α ⊕ ↑W₁) ∈ Sum.inl '' W₂ := ⟨v, hv₂, rfl⟩
        rw [split1_of_mem hv, split1_of_not_mem hv₁, split1_of_mem hv_mem]
        exact apply_inr_right v hv₂ hv
      · -- v ∉ W₁ ∪ W₂: both sides land at `Sum.inl (Sum.inl v)`.
        have hv : v ∉ W₁ ∪ W₂ := fun h => h.elim hv₁ hv₂
        have hv_notin : (Sum.inl v : α ⊕ ↑W₁) ∉ Sum.inl '' W₂ := by
          rintro ⟨w, hw, h⟩; exact hv₂ (Sum.inl_injective h ▸ hw)
        rw [split1_of_not_mem hv, split1_of_not_mem hv₁, split1_of_not_mem hv_notin]
        exact apply_inl v
  refine
    { toEquiv := (fusionEquiv W₁ W₂ hdisj).symm
      J_eq := ?_
      V_eq := ?_
      E_eq := ?_
      L_eq := ?_ }
  -- J_eq: SWIG.J has the `Sum.inl '' · ∪ Set.range Sum.inr` shape, so the
  -- proof mirrors the `\spl` sibling's V_eq (case-split on the two pieces).
  · simp only [nodeSplittingHardInterventionOn_J]
    ext y
    simp only [Set.mem_image, Set.mem_union, Set.mem_range]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩)
      · -- y = Sum.inl j, j ∈ G.J: lifted via double-Sum.inl in the iterated SWIG.
        refine ⟨Sum.inl (Sum.inl j),
          Or.inl ⟨Sum.inl j, Or.inl ⟨j, hj, rfl⟩, rfl⟩, ?_⟩
        exact symm_inl_inl j
      · rcases hw with hw₁ | hw₂
        · -- w ∈ W₁: lift via the outer Sum.inl of the iterated SWIG.
          refine ⟨Sum.inl (Sum.inr ⟨w, hw₁⟩),
            Or.inl ⟨Sum.inr ⟨w, hw₁⟩, Or.inr ⟨⟨w, hw₁⟩, rfl⟩, rfl⟩, ?_⟩
          exact symm_inl_inr w hw₁ (Or.inl hw₁)
        · -- w ∈ W₂: in the outer SWIG's range piece.
          refine ⟨Sum.inr ⟨Sum.inl w, ⟨w, hw₂, rfl⟩⟩,
            Or.inr ⟨⟨Sum.inl w, ⟨w, hw₂, rfl⟩⟩, rfl⟩, ?_⟩
          exact symm_inr w hw₂ (Or.inr hw₂)
    · rintro ⟨x, hx, rfl⟩
      rcases hx with (⟨z, hz, rfl⟩ | ⟨⟨w_val, hw_val⟩, rfl⟩)
      · rcases hz with (⟨j, hj, rfl⟩ | ⟨⟨w₁, hw₁⟩, rfl⟩)
        · -- x = Sum.inl (Sum.inl j) for j ∈ G.J
          refine Or.inl ⟨j, hj, ?_⟩
          exact (symm_inl_inl j).symm
        · -- x = Sum.inl (Sum.inr ⟨w₁, hw₁⟩) for hw₁ : w₁ ∈ W₁
          refine Or.inr ⟨⟨w₁, Or.inl hw₁⟩, ?_⟩
          exact (symm_inl_inr w₁ hw₁ (Or.inl hw₁)).symm
      · -- x = Sum.inr ⟨w_val, hw_val⟩ for hw_val : w_val ∈ Sum.inl '' W₂
        obtain ⟨w', hw'₂, rfl⟩ := hw_val
        refine Or.inr ⟨⟨w', Or.inr hw'₂⟩, ?_⟩
        exact (symm_inr w' hw'₂ (Or.inr hw'₂)).symm
  -- V_eq: SWIG.V is just `Sum.inl '' G.V` (HI deletes the `range Sum.inr`
  -- piece), so this is the simpler "double-inl" case mirroring `\spl`.J_eq.
  · simp only [nodeSplittingHardInterventionOn_V, Set.image_image]
    refine Set.image_congr (fun v _ => ?_)
    exact (symm_inl_inl v).symm
  -- E_eq: SWIG.E has only the LN's "v_1^i → v_2^o" piece (the inner
  -- split edges of the `\spl` sibling are killed by the HI layer). So the
  -- proof has only the "original-edge double-relabeled" branch.
  · ext y
    rw [Set.mem_image, mem_nodeSplittingHardInterventionOn_E]
    constructor
    · rintro ⟨v₁, v₂, hE, rfl⟩
      refine ⟨(split1 (Sum.inl '' W₂) (split1 W₁ v₁), Sum.inl (Sum.inl v₂)), ?_, ?_⟩
      · rw [mem_nodeSplittingHardInterventionOn_E]
        refine ⟨split1 W₁ v₁, Sum.inl v₂, ?_, rfl⟩
        rw [mem_nodeSplittingHardInterventionOn_E]
        exact ⟨v₁, v₂, hE, rfl⟩
      · refine Prod.ext ?_ ?_
        · change (fusionEquiv W₁ W₂ hdisj).symm
              (split1 (Sum.inl '' W₂) (split1 W₁ v₁))
            = split1 (W₁ ∪ W₂) v₁
          rw [← key_e_source]
          exact Equiv.symm_apply_apply _ _
        · exact symm_inl_inl v₂
    · rintro ⟨p, hp, rfl⟩
      rw [mem_nodeSplittingHardInterventionOn_E] at hp
      rcases hp with ⟨a₁, a₂, ha, rfl⟩
      rw [mem_nodeSplittingHardInterventionOn_E] at ha
      rcases ha with ⟨v₁, v₂, hE, h_eq⟩
      injection h_eq with h_eq1 h_eq2
      subst h_eq1; subst h_eq2
      refine ⟨v₁, v₂, hE, ?_⟩
      refine Prod.ext ?_ ?_
      · change (fusionEquiv W₁ W₂ hdisj).symm
            (split1 (Sum.inl '' W₂) (split1 W₁ v₁))
          = split1 (W₁ ∪ W₂) v₁
        rw [← key_e_source]
        exact Equiv.symm_apply_apply _ _
      · exact symm_inl_inl v₂
  -- L_eq: bidirected edges of any SWIG are the double-Sum.inl image of G.L
  -- (HI is a no-op on L because every L-endpoint is on the Sum.inl side).
  -- So both sides reduce to a double-`Sum.inl` image -- identical to `\spl`.
  · ext y
    rw [Set.mem_image, mem_nodeSplittingHardInterventionOn_L]
    constructor
    · rintro ⟨v₁, v₂, hL, rfl⟩
      refine ⟨(Sum.inl (Sum.inl v₁), Sum.inl (Sum.inl v₂)), ?_, ?_⟩
      · rw [mem_nodeSplittingHardInterventionOn_L]
        refine ⟨Sum.inl v₁, Sum.inl v₂, ?_, rfl⟩
        rw [mem_nodeSplittingHardInterventionOn_L]
        exact ⟨v₁, v₂, hL, rfl⟩
      · refine Prod.ext ?_ ?_
        · exact symm_inl_inl v₁
        · exact symm_inl_inl v₂
    · rintro ⟨p, hp, rfl⟩
      rw [mem_nodeSplittingHardInterventionOn_L] at hp
      obtain ⟨a, b, hab, rfl⟩ := hp
      rw [mem_nodeSplittingHardInterventionOn_L] at hab
      obtain ⟨v₁, v₂, hL, h_eq⟩ := hab
      injection h_eq with h_eq1 h_eq2
      subst h_eq1; subst h_eq2
      refine ⟨v₁, v₂, hL, ?_⟩
      refine Prod.ext ?_ ?_
      · exact symm_inl_inl v₁
      · exact symm_inl_inl v₂

-- claim_3_10 (part 2/2)
-- title: TwoDisjointNode -- SWIG commute corollary
--
-- The two iterations agree (modulo re-labeling): swapping `W₁` and
-- `W₂` in the iteration gives a `CDMGEquiv`-equivalent CDMG. Manager
-- B derives this by
-- `(swig_swig_equiv hW₁ hW₂ hdisj).trans
--    (bridge.trans (swig_swig_equiv hW₂ hW₁ hdisj.symm).symm)`
-- for some small `bridge` that absorbs `Set.union_comm`. Same
-- pattern as `nodeSplittingOn_comm_equiv`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 627 -- 632)
-- linewrapped within the prose paragraph and within the displayed
-- equation; LaTeX whitespace collapses, so this is verbatim under
-- \LaTeX semantics:

\begin{claimmark}
\begin{Lem}[Two disjoint node-splitting hard interventions commute]
   Let $G=(J,V,E,L)$ be a CADMG and $W_1, W_2 \ins V$ two disjoint
   subsets of the output nodes from $G$.
   Then the CADMG obtained from first node-splitting on $W_1$ and
   then node-splitting on $W_2$ is the same CADMG that arises from
   first node-splitting on $W_2$ and then node-splitting on $W_1$:
   \[ \lp G_{\swig(W_1)} \rp_{\swig(W_2)} =  \lp G_{\swig(W_2)} \rp_{\swig(W_1)}
      =  G_{\swig(W_1 \dcup W_2)}.   \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_10 part 2/2 (SWIG commute corollary): swapping `W₁` and
`W₂` in the iterated SWIG yields a `CDMGEquiv`-equivalent CDMG.
Mirrors the second half
(`(G_{swig(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{swig(W₁)}`) of the
chained equality in the `\Lem` at
`lecture-notes/lecture_notes/graphs.tex` line 630. Body = `sorry`;
Manager B derives this by composing the fusion lemma with its
`Disjoint.symm`-variant via `CDMGEquiv.trans` / `.symm`, with a
small `bridge` absorbing the `Set.union_comm` discrepancy on the
union-side carrier (same pattern as the `\spl` case at line 657 --
754 of `TwoDisjointNodeSplittingsCommute.lean`).

## Design choice

* **`CDMGEquiv` rather than literal `Eq`.** Inherited from the
  fusion lemma above -- the carriers of the two iterated SWIGs
  `(α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)` and `(α ⊕ ↑W₂) ⊕ ↑(Sum.inl '' W₁)`
  are different even before we ask whether the four data fields
  agree, so literal `Eq` is not type-correct. This is again the
  carrier-rewriting regime -- contrast with
  `HardInterventionNodeSplittingCommute.lean` lines 20 -- 44,
  which keeps the same carrier on both sides and so ships literal
  `Eq`. Notice that, unlike the fusion lemma above (whose right-
  hand carrier is the *merged* `α ⊕ ↑(W₁ ∪ W₂)`), the commute
  statement has carriers that are *symmetric* in `W₁` and `W₂` --
  swapping the two roles flips one carrier to the other. No `∪`
  appears in either side's carrier; disjointness is therefore
  *not* needed at the carrier-typing level here.

* **Derived from the fusion lemma, not re-proven from scratch.**
  Same payoff as the `\spl` case: shipping `CDMGEquiv.refl / symm /
  trans` lets Manager B express the LN's "the other follows by
  symmetry" close (`graphs.tex` line 635) as a one-line `.trans` /
  `.symm` composition of two `swig_swig_equiv` invocations
  (modulo a small `Set.union_comm` bridge on the union-side
  carrier). This is the entire reason `CDMGEquiv` carries
  groupoid laws.

* **Two independently consumable Lean facts for the LN's chained
  equality.** The LN writes a single three-way chain
  `(G_{swig(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{swig(W₁)} =
  G_{swig(W₁ ⊍ W₂)}`. We deliberately split it into fusion
  (`swig_swig_equiv`, the second `=`) and commute
  (`swig_comm_equiv`, the first `=`); composing them via
  `CDMGEquiv.trans` recovers the full chain, but a downstream
  consumer that wants only to *swap* the two iterates (without
  collapsing them to the union) reaches for the commute corollary
  directly, and a consumer that wants only to *collapse* the
  iterate reaches for the fusion lemma directly. Same factoring as
  `nodeSplittingOn_nodeSplittingOn_equiv` /
  `nodeSplittingOn_comm_equiv` in the `\spl` sibling, so a
  consumer that pattern-matches across `\spl` and `\swig` only has
  to learn one API shape.

* **Disjointness still appears as an explicit hypothesis even
  though carrier-typing does not need it.** `hdisj : Disjoint W₁
  W₂` is consumed inside the *proof* (not the type): Manager B's
  derivation composes two `swig_swig_equiv` invocations, one for
  `(W₁, W₂)` and one for `(W₂, W₁)`, each of which feeds
  `hdisj` / `hdisj.symm` into `fusionEquiv`'s underlying
  `Equiv.Set.union` (the Mathlib equivalence that *requires*
  disjointness to split a `Set` union into a `Sum`). The
  `Set.union_comm`-style bridge between the two union-side
  carriers (`↑(W₁ ∪ W₂)` vs `↑(W₂ ∪ W₁)`) is itself
  disjointness-free -- it factors through
  `Equiv.subtypeEquivRight (fun _ => Or.comm)`, a pure logical
  move on the subtype membership. Flagging both points so the
  proof-phase manager knows that disjointness threads through
  each fusion call but not through the gluing bridge.

* **Explicit `hW₁ hW₂ hdisj` ordering matches the fusion lemma and
  the `\spl` sibling.** Keeping hypothesis order consistent across
  the four declarations (`{spl,swig}_{swig,...}_equiv` and their
  commute corollaries) lets downstream consumers swap one
  construction for another by pattern with minimal call-site
  churn. -/
noncomputable def swig_comm_equiv
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hdisj : Disjoint W₁ W₂) :
    CDMGEquiv
      ((G.swig W₁ hW₁).swig (Sum.inl '' W₂)
          (subset_swig_V_of_subset_V hW₂ hW₁))
      ((G.swig W₂ hW₂).swig (Sum.inl '' W₁)
          (subset_swig_V_of_subset_V hW₁ hW₂)) := by
  -- Build the small bridge CDMGEquiv between the two merged SWIGs
  -- (over `W₁ ∪ W₂` and over `W₂ ∪ W₁` respectively). The two SWIGs are
  -- equal as Set α-valued data, but their carrier types differ since
  -- `↑(W₁ ∪ W₂) ≠ ↑(W₂ ∪ W₁)` def-equally. The bridge absorbs the
  -- `Set.union_comm` discrepancy via the subtype-relabel Equiv
  -- `Equiv.subtypeEquivRight (fun _ => Or.comm)`. Mirrors the `\spl`
  -- sibling's bridge construction exactly.
  let σ : ↑(W₁ ∪ W₂) ≃ ↑(W₂ ∪ W₁) := Equiv.subtypeEquivRight (fun _ => Or.comm)
  let toEq : (α ⊕ ↑(W₁ ∪ W₂)) ≃ (α ⊕ ↑(W₂ ∪ W₁)) :=
    Equiv.sumCongr (Equiv.refl α) σ
  have toEq_inl : ∀ (a : α),
      toEq (Sum.inl a) = Sum.inl a := fun a => rfl
  have toEq_inr : ∀ (a : α) (h : a ∈ W₁ ∪ W₂) (h' : a ∈ W₂ ∪ W₁),
      toEq (Sum.inr ⟨a, h⟩) = Sum.inr ⟨a, h'⟩ := fun _ _ _ => rfl
  have toEq_split1 : ∀ (v : α),
      toEq (split1 (W₁ ∪ W₂) v) = split1 (W₂ ∪ W₁) v := by
    intro v
    by_cases hv : v ∈ W₁ ∪ W₂
    · have hv' : v ∈ W₂ ∪ W₁ := hv.symm
      rw [split1_of_mem hv, split1_of_mem hv']
      exact toEq_inr v hv hv'
    · have hv' : v ∉ W₂ ∪ W₁ := fun h => hv h.symm
      rw [split1_of_not_mem hv, split1_of_not_mem hv']
      exact toEq_inl v
  let bridge : CDMGEquiv
      (G.swig (W₁ ∪ W₂) (Set.union_subset hW₁ hW₂))
      (G.swig (W₂ ∪ W₁) (Set.union_subset hW₂ hW₁)) :=
  { toEquiv := toEq
    J_eq := by
      -- SWIG.J has the `Sum.inl '' G.J ∪ Set.range Sum.inr` shape, so this
      -- mirrors the `\spl` bridge's V_eq (the union piece).
      simp only [nodeSplittingHardInterventionOn_J, Set.image_union]
      congr 1
      · rw [Set.image_image]
        refine Set.image_congr (fun j _ => ?_)
        exact (toEq_inl j).symm
      · ext y
        simp only [Set.mem_image, Set.mem_range]
        constructor
        · rintro ⟨w', rfl⟩
          refine ⟨Sum.inr (σ.symm w'), ⟨σ.symm w', rfl⟩, ?_⟩
          show toEq (Sum.inr (σ.symm w')) = Sum.inr w'
          simp [toEq, Equiv.sumCongr_apply, Equiv.apply_symm_apply]
        · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
          exact ⟨σ w, rfl⟩
    V_eq := by
      -- SWIG.V is just `Sum.inl '' G.V` (no range piece), so this is the
      -- simpler "double-inl" image case.
      simp only [nodeSplittingHardInterventionOn_V, Set.image_image]
      refine Set.image_congr (fun v _ => ?_)
      exact (toEq_inl v).symm
    E_eq := by
      ext y
      rw [Set.mem_image, mem_nodeSplittingHardInterventionOn_E]
      constructor
      · rintro ⟨v₁, v₂, hE, rfl⟩
        refine ⟨(split1 (W₁ ∪ W₂) v₁, Sum.inl v₂), ?_, ?_⟩
        · rw [mem_nodeSplittingHardInterventionOn_E]
          exact ⟨v₁, v₂, hE, rfl⟩
        · refine Prod.ext ?_ ?_
          · exact toEq_split1 v₁
          · exact toEq_inl v₂
      · rintro ⟨p, hp, rfl⟩
        rw [mem_nodeSplittingHardInterventionOn_E] at hp
        rcases hp with ⟨v₁, v₂, hE, h_eq⟩
        subst h_eq
        refine ⟨v₁, v₂, hE, ?_⟩
        refine Prod.ext ?_ ?_
        · exact toEq_split1 v₁
        · exact toEq_inl v₂
    L_eq := by
      ext y
      rw [Set.mem_image, mem_nodeSplittingHardInterventionOn_L]
      constructor
      · rintro ⟨v₁, v₂, hL, rfl⟩
        refine ⟨(Sum.inl v₁, Sum.inl v₂), ?_, ?_⟩
        · rw [mem_nodeSplittingHardInterventionOn_L]; exact ⟨v₁, v₂, hL, rfl⟩
        · refine Prod.ext ?_ ?_
          · exact toEq_inl v₁
          · exact toEq_inl v₂
      · rintro ⟨p, hp, rfl⟩
        rw [mem_nodeSplittingHardInterventionOn_L] at hp
        obtain ⟨v₁, v₂, hL, h_eq⟩ := hp
        subst h_eq
        refine ⟨v₁, v₂, hL, ?_⟩
        refine Prod.ext ?_ ?_
        · exact toEq_inl v₁
        · exact toEq_inl v₂ }
  exact (swig_swig_equiv hW₁ hW₂ hdisj).trans
    (bridge.trans (swig_swig_equiv hW₂ hW₁ hdisj.symm).symm)

end CDMG

end Causality
