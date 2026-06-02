import Chapter3_GraphTheory.Section3_2.ExtendingCDMGsWithInterventionNodes
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.TwoDisjointNodeSplittingsCommute

-- TeX statement: tex/claim_3_14_statement_AddingInterventionNodes.tex
-- TeX proof:    tex/claim_3_14_proof_AddingInterventionNodes.tex (Manager B)

/-!
# Adding intervention nodes commutes with disjoint hard interventions (claim_3_14)

This file formalises the lecture notes' lemma "Adding intervention nodes
commutes with disjoint hard interventions" --
`lecture-notes/lecture_notes/graphs.tex` Lem at lines 832 -- 843 with
`\Claude` proof at lines 845 -- 875. The LN bundles *two* chained
equalities under one `\Lem`, both with hypotheses
`W₁, W₂ ⊆ J ∪ V` and `Disjoint W₁ W₂`:

  * **Chain 1**:
    `(G_{do(I_{W₁})})_{do(I_{W₂})} = (G_{do(I_{W₂})})_{do(I_{W₁})}
        = G_{do(I_{W₁ ∪ W₂})}`.
  * **Chain 2**:
    `(G_{do(I_{W₁})})_{do(W₂)} = (G_{do(W₂)})_{do(I_{W₁})}
        = G_{do(I_{W₁}, W₂)}`.

Both chains are *carrier-changing* between sides (chain 1: nested
`Sum` vs. flat `Sum`; chain 2: subtype with extra `∉ W₂` clause vs.
without), so neither is type-correct as literal `Eq`. Both ship
`CDMGEquiv`, the carrier-rewriting bundle from claim_3_7
(`TwoDisjointNodeSplittingsCommute.lean`, imported here).

This file delivers:

* `subset_extendingCDMGWithInterventionNodes_J_union_V_of_subset`
  -- helper, fully proved: discharges chain-1's outer-`ext`
  precondition `Sum.inl '' W₂ ⊆ (G.ext W₁ _).J ∪ (G.ext W₁ _).V`.
* `subset_hardInterventionOn_J_union_V_of_disjoint`
  -- helper, fully proved: discharges chain-2's outer-`ext`
  precondition `W₁ ⊆ (G.hardInterventionOn W₂).J ∪ _.V`.
* `extFusionEquiv` -- carrier equiv for chain 1's fusion
  (`α ⊕ ↑((W₁ ∪ W₂) \ G.J) ≃ (α ⊕ ↑(W₁ \ G.J))
       ⊕ ↑(Sum.inl '' (W₂ \ G.J))`). Built from
  `Set.union_diff_distrib`, `Equiv.Set.union`, `Equiv.sumAssoc`,
  `Equiv.Set.image`. Fully proved.
* `extendingCDMGWithInterventionNodes_fusion_equiv`
  -- chain-1 fusion `CDMGEquiv`. Body = `sorry` (Manager B).
* `extendingCDMGWithInterventionNodes_comm_equiv`
  -- chain-1 commute corollary `CDMGEquiv`. Body = `sorry`
  (Manager B; one-line `.trans` of two fusion calls through a
  `Set.union_comm` bridge).
* `extHardCarrierEquiv` -- carrier equiv for chain 2
  (`α ⊕ ↑(W₁ \ G.J) ≃ α ⊕ ↑(W₁ \ (G.J ∪ W₂))`); subtype-relabel
  via `Equiv.subtypeEquivRight` consuming `Disjoint W₁ W₂` in both
  directions. Fully proved.
* `extendingCDMGWithInterventionNodes_hardInterventionOn_comm_equiv`
  -- chain-2 `CDMGEquiv`. Body = `sorry` (Manager B).

## Foundation reuse (workspace decision D5)

`CDMGEquiv` (with its `refl` / `symm` / `trans` groupoid laws) is
imported verbatim from `TwoDisjointNodeSplittingsCommute.lean` rather
than redefined here or promoted to a shared `Section3_1/` file. This
is the *third* consumer of the structure (after claim_3_7 in
`TwoDisjointNodeSplittingsCommute.lean` and claim_3_10 in
`TwoDisjointSwigsCommute.lean`). The original claim_3_7 design block
(`TwoDisjointNodeSplittingsCommute.lean` lines 48 -- 71) flagged a
*third* consumer as the natural promotion trigger, but the cost --
benefit still favours staying put:

* the import cost from this file is a single `import` line;
* promoting `CDMGEquiv` would touch the two prior consumers
  (claim_3_7, claim_3_10) for no measurable downstream payoff;
* no fourth consumer is queued in Section 3.2 (claim_3_15 is the
  next commute lemma but its Lean shape is not yet pinned, and a
  preemptive promotion risks locking in a `CDMGEquiv` API claim_3_15
  then has to refactor);
* the reverse move (merging a promoted file back) is cheap if the
  promotion turns out to be wrong, but inserting an extra file *now*
  fragments the design-choice narrative of this section.

Decision: keep local, `import` from this row. If claim_3_15 or a
chapter-4 CBN-side consumer arrives needing the same shape, run
`refactor_lean_code` then; workspace_claim_3_14.md D5 records the
trade-off in full.
-/

namespace Causality

namespace CDMG

universe u

variable {α : Type u}

/-! ## Helpers: outer-extension preconditions -/

/-- Chain-1 helper: if `W₂ ⊆ G.J ∪ G.V`, then `Sum.inl '' W₂` is
contained in the node-set union of `G.extendingCDMGWithInterventionNodes
W₁ hW₁`. Discharges the outer-`ext` precondition for
`((G.ext W₁ hW₁).ext (Sum.inl '' W₂) _)` in chain 1.

Proof: `(G.ext W₁ _).J = Sum.inl '' G.J ∪ Set.range Sum.inr` and
`_.V = Sum.inl '' G.V` (both by definition, see the four `@[simp]`
projection lemmas in `ExtendingCDMGsWithInterventionNodes.lean`), so a
`w ∈ W₂` with either `w ∈ G.J` or `w ∈ G.V` lifts under `Sum.inl` into
the left or right disjunct. The `Set.range Sum.inr` piece is never
needed — original outputs survive into the extension's vertex layer.

## Design choice (workspace decision D4)

* **Named helper, not inlined into the chain-1 statements.** The
  fusion and commute statements below need to *type-check* the
  outer-`ext` application
  `(G.ext W₁ hW₁).ext (Sum.inl '' W₂) ?_`, whose hypothesis slot has
  the literal shape `Sum.inl '' W₂ ⊆ (G.ext W₁ hW₁).J ∪ _.V`.
  Discharging this inline as a `by simp; ...` block in the headline
  signatures would (a) make every consumer re-prove the same subset
  fact under any goal-state perturbation, (b) drown the
  `CDMGEquiv`-valued conclusion in a precondition tactic block, and
  (c) duplicate the same containment in both `fusion_equiv` and
  `comm_equiv`. Factoring it as a named theorem mirrors the
  `subset_nodeSplittingOn_V_of_subset_V` helper in the sibling
  claim_3_7 file (`TwoDisjointNodeSplittingsCommute.lean` lines
  242 -- 247) and `subset_swig_V_of_subset_V` in claim_3_10
  (`TwoDisjointSwigsCommute.lean` lines 104 -- 108). Plan §4 in
  `workspace_claim_3_14.md` records the consistency choice.

* **No `Disjoint W₁ W₂` hypothesis -- contrast with the chain-2
  helper.** `extendingCDMGWithInterventionNodes` is *additive* on
  the input layer (the construction only mints fresh
  `Sum.inr`-labelled nodes; original `Sum.inl '' (G.J ∪ G.V)`
  survives untouched), so any `W₂ ⊆ G.J ∪ G.V` lifts under
  `Sum.inl` into the extension's node-set union regardless of how
  `W₁` and `W₂` overlap. Disjointness is only load-bearing for the
  fusion bijection (the `↑((W₁ ∪ W₂) \ G.J)` carrier needs an
  unambiguous dispatch in `Equiv.Set.union`); the embedding layer
  does not care. Mirrors the same design call recorded for
  `subset_nodeSplittingOn_V_of_subset_V` in the sibling file. The
  chain-2 analogue (next helper) *does* need disjointness because
  hard intervention is a *deletion* on the `V` side
  (`hardInterventionOn_V = G.V \ W₂`), which can strip out vertices
  of `W₁` if the disjointness is missing.

* **`Sum.inl '' W₂` rather than a bare `W₂`-like target set.** The
  outer-`ext` lives over the carrier `α ⊕ ↑(W₁ \ G.J)`, so its
  second argument must be a `Set (α ⊕ ↑(W₁ \ G.J))`, not a
  `Set α`. The natural and LN-faithful lift is `Sum.inl '' W₂` --
  under the convention `Sum.inl = original-α-side` (encoded
  carrier-level by `extendingCDMGWithInterventionNodes`, see its
  design block in `ExtendingCDMGsWithInterventionNodes.lean` lines
  82 -- 113), the LN's "the same `W₂`" *is* the `Sum.inl`-image of
  `W₂`. Same lift / same justification as
  `hardInterventionOn_swig_comm`
  (`HardInterventionSwigCommute.lean` lines 169 -- 206); without
  it, the outer `ext` would not be type-correct. The conclusion
  `Sum.inl '' W₂ ⊆ J_ext ∪ V_ext` is therefore forced by
  carrier-typing first, and only secondarily by faithfulness to LN
  intent.

* **The `Set.range Sum.inr` summand of `J_ext` is unused in the
  proof.** Constructor-disjointness of `Sum.inl` and `Sum.inr`
  means a `Sum.inl w` (image of `w ∈ W₂`) can never match the
  fresh-input layer; the case-split lands purely in the
  `Sum.inl '' G.J ∪ Sum.inl '' G.V` half. This is the "no
  collision with fresh intervention nodes" half of the LN's
  `W_2 \sm J_1 = W_2 \sm J` sub-argument (`graphs.tex` line 852),
  visible here as a typing fact rather than as a set-equation. -/
theorem subset_extendingCDMGWithInterventionNodes_J_union_V_of_subset
    {G : CDMG α} {W₁ W₂ : Set α} (hW₁ : W₁ ⊆ G.J ∪ G.V)
    (hW₂ : W₂ ⊆ G.J ∪ G.V) :
    Sum.inl '' W₂ ⊆
      (G.extendingCDMGWithInterventionNodes W₁ hW₁).J ∪
        (G.extendingCDMGWithInterventionNodes W₁ hW₁).V := by
  rintro _ ⟨w, hw, rfl⟩
  rcases hW₂ hw with hJ | hV
  · exact Or.inl (Or.inl ⟨w, hJ, rfl⟩)
  · exact Or.inr ⟨w, hV, rfl⟩

/-- Chain-2 helper: if `W₁ ⊆ G.J ∪ G.V` and `Disjoint W₁ W₂`, then
`W₁ ⊆ (G.hardInterventionOn W₂).J ∪ (G.hardInterventionOn W₂).V`.
Discharges the outer-`ext` precondition for
`((G.hardInterventionOn W₂).ext W₁ _)` in chain 2.

Proof: `(G.hardInterventionOn W₂).J = G.J ∪ W₂` and `_.V = G.V \ W₂`
(both `rfl`). A vertex `w ∈ W₁` with `w ∈ G.J` lifts directly; one with
`w ∈ G.V` needs `w ∉ W₂` to land in `G.V \ W₂`, which is exactly what
`Disjoint W₁ W₂` provides for `w ∈ W₁`.

## Design choice (workspace decision D4)

* **Named helper, not inlined into the chain-2 statement.** Exact
  same reasoning as the chain-1 helper above: discharging the
  outer-`ext` precondition inline would force the prover to re-do
  the disjointness-driven membership case-split inside the
  headline `CDMGEquiv`-valued statement, fragmenting the proof and
  obscuring the `CDMGEquiv` conclusion. Pulling it out as a named
  lemma also (a) makes the chain-2 statement readable at a glance
  and (b) isolates *the only* place in the precondition layer
  where `Disjoint W₁ W₂` does real work; any future row that
  wants to compose `hardInterventionOn W₂` with another operator
  on `W₁` under disjointness can re-use this helper verbatim.

* **`Disjoint W₁ W₂` is structurally load-bearing here -- contrast
  with the chain-1 helper.** Unlike `extendingCDMGWithInterventionNodes`
  (which is purely additive), `hardInterventionOn` is a
  *deletion* on the `V` side: `(G.hardInterventionOn W₂).V = G.V
  \ W₂` (`HardInterventionOn.lean` lines 275 -- 276). A vertex
  `w ∈ W₁ ∩ G.V` would *fall out* of `_.V` if `w ∈ W₂`, and
  *neither* of the two halves of the conclusion's union
  (`G.J ∪ W₂` on the `J` side, `G.V \ W₂` on the `V` side) would
  catch it. The disjointness hypothesis is what blocks this
  failure mode; dropping it makes the helper false. This is the
  Lean transcription of the LN's implicit
  `W₁ ∩ (V \ W₂) = W₁ ∩ V` lemma used silently in the `\Lem`'s
  chain-2 proof (`graphs.tex` lines 866 -- 873).

* **No `Sum.inl '' W₁` lift on the conclusion -- contrast with the
  chain-1 helper.** `hardInterventionOn` is *carrier-preserving*
  (the carrier stays `α`, not `α ⊕ ↑W₂` -- see
  `HardInterventionOn.lean` lines 232 -- 264), so the outer-`ext`
  in chain 2 acts on a `Set α` directly. `W₁` does not need a
  `Sum.inl '' ` lift to type-check, in contrast to chain 1 where
  the inner `extendingCDMGWithInterventionNodes` shifts to
  `α ⊕ ↑(W₁ \ G.J)` and forces `Sum.inl ''` on the outer-set
  argument. This carrier-preserving-vs-changing asymmetry between
  the chain-1 and chain-2 helpers is exactly the surface symptom
  of the deeper carrier asymmetry that makes chain 2 a
  `subtypeEquivRight`-mediated `CDMGEquiv` (see `extHardCarrierEquiv`
  below) rather than the `sumAssoc`-mediated `extFusionEquiv` of
  chain 1.

* **Conclusion form `W₁ ⊆ (G.HI W₂).J ∪ (G.HI W₂).V` literally,
  not unfolded to `G.J ∪ W₂ ∪ (G.V \ W₂)`.** Keeping the
  `(G.HI W₂).J ∪ (G.HI W₂).V` shape lets the conclusion plug
  directly into the second-`ext` precondition slot
  (`extendingCDMGWithInterventionNodes` takes precisely
  `W₁ ⊆ inner.J ∪ inner.V` as its hypothesis). Unfolding to the
  expanded set form would force every consumer to re-fold with
  `hardInterventionOn_J` / `_V`. Matches the same shape-keeping
  convention used for `subset_hardInterventionOn_V_of_disjoint`
  in `HardInterventionNodeSplittingCommute.lean` lines
  175 -- 182. -/
theorem subset_hardInterventionOn_J_union_V_of_disjoint
    {G : CDMG α} {W₁ W₂ : Set α} (hW₁ : W₁ ⊆ G.J ∪ G.V)
    (hdisj : Disjoint W₁ W₂) :
    W₁ ⊆ (G.hardInterventionOn W₂).J ∪ (G.hardInterventionOn W₂).V := by
  intro w hw
  rcases hW₁ hw with hJ | hV
  · exact Or.inl (Or.inl hJ)
  · exact Or.inr ⟨hV, fun hwW₂ => Set.disjoint_left.mp hdisj hw hwW₂⟩

/-! ## Chain 1: carrier equiv for the fusion lemma -/

/-- Carrier equivalence
`α ⊕ ↑((W₁ ∪ W₂) \ G.J) ≃ (α ⊕ ↑(W₁ \ G.J)) ⊕ ↑(Sum.inl '' (W₂ \ G.J))`
underlying chain-1's fusion. Built by composing:

* `Equiv.setCongr Set.union_diff_distrib` to rewrite the merged side's
  index set `(W₁ ∪ W₂) \ G.J` as the union `(W₁ \ G.J) ∪ (W₂ \ G.J)`;
* `Equiv.Set.union` on the derived disjointness
  `Disjoint (W₁ \ G.J) (W₂ \ G.J)` (deduced from `Disjoint W₁ W₂` by
  `.mono Set.diff_subset Set.diff_subset`), to split the union into a
  `Sum`;
* `Equiv.sumAssoc.symm` to reassociate `α ⊕ (A ⊕ B)` into `(α ⊕ A) ⊕ B`;
* `Equiv.Set.image (Sum.inl) (W₂ \ G.J) Sum.inl_injective` to transport
  the right summand under the canonical `Sum.inl` embedding.

`noncomputable` because `Equiv.Set.union` consumes a
`DecidablePred (· ∈ W₁ \ G.J)`, supplied here via `Classical.decPred`.
Analogue of claim_3_7's `fusionEquiv` (in
`TwoDisjointNodeSplittingsCommute.lean`); the only structural
difference is the extra `\ G.J` step (`union_diff_distrib`) needed
because `extendingCDMGWithInterventionNodes`'s carrier is
`α ⊕ ↑(W \ G.J)`, not `α ⊕ ↑W`.

## Design choice

* **Why a separately-named `Equiv`, not folded into the
  `CDMGEquiv`'s `toEquiv` field.** This bijection is reused in two
  consumers (the fusion lemma `extendingCDMGWithInterventionNodes_fusion_equiv`
  and the commute corollary `extendingCDMGWithInterventionNodes_comm_equiv`,
  with its `.symm` direction the load-bearing one for the
  fusion-lemma `CDMGEquiv`'s `toEquiv`). Naming it once and
  re-using lets Manager B's proofs of those `CDMGEquiv`'s
  field-equalities (`J_eq`, `V_eq`, `E_eq`, `L_eq`) all rewrite
  against the *same* set of constructor-case `apply_inl` /
  `apply_inr_left` / `apply_inr_right` simp lemmas (cf. the
  three `apply_*` helpers in
  `TwoDisjointNodeSplittingsCommute.lean` lines 395 -- 423). An
  inline anonymous `Equiv` in `toEquiv` would force the proof of
  each field-equality to re-derive the same case-dispatch from
  the raw `sumAssoc` / `Equiv.Set.union` composition every time.

* **Mathlib combinators (`Equiv.Set.union`, `Equiv.sumAssoc`,
  `Equiv.Set.image`, `Equiv.setCongr`), not a hand-rolled `dite`
  bijection.** A hand-rolled bijection on the four constructor
  cases (`Sum.inl a`, `Sum.inr ⟨w, hw⟩` with `w ∈ W₁ \ G.J` /
  `w ∈ W₂ \ G.J`) would require ~30 lines of `dite`-laden case
  analysis plus two round-trip proofs `left_inv` / `right_inv` --
  see the alternative walked through in
  `workspace_claim_3_14.md` (and the equivalent walkthrough in
  `workspace_claim_3_7.md` Plan §2.2). The Mathlib triple
  packages the same content with the round-trip proofs already
  discharged, and ships `_apply`-shaped simp lemmas
  (`Equiv.Set.union_apply_left` / `_right`,
  `Equiv.sumAssoc_apply`, `Equiv.Set.image_apply`,
  `Equiv.setCongr_apply`) that let the downstream `CDMGEquiv`
  proofs discharge field-equalities by `simp` rather than by
  unfolding hand-rolled match arms.

* **Structural difference from claim_3_7's `fusionEquiv`: one
  extra `Set.union_diff_distrib` step.** The `\spl` sibling
  `nodeSplittingOn` (def_3_11) restricts to `W ⊆ G.V` and
  subtypes the `Sum.inr` summand by `↑W` directly, so its
  fusion equiv has codomain `α ⊕ ↑(W₁ ∪ W₂)` -- no `\ G.J`
  bookkeeping needed. Here, `extendingCDMGWithInterventionNodes`
  subtypes by `↑(W \ G.J)` (carrier-level encoding of the LN's
  `I_j := j` convention; see
  `ExtendingCDMGsWithInterventionNodes.lean` lines 82 -- 113),
  so we must first rewrite `(W₁ ∪ W₂) \ G.J = (W₁ \ G.J) ∪ (W₂
  \ G.J)` via `Set.union_diff_distrib` before applying
  `Equiv.Set.union`. The derived disjointness
  `Disjoint (W₁ \ G.J) (W₂ \ G.J)` then follows from
  `Disjoint W₁ W₂` by `.mono Set.diff_subset Set.diff_subset`.
  This is the *only* structural difference from the `\spl`
  fusion equiv; everything downstream re-uses the same shape.

* **Alternative considered and rejected: factoring out a generic
  `fusionEquivWithDiff` shared with claim_3_7.** Would absorb the
  `\ G.J` step into a Mathlib-level lemma and let claim_3_7 +
  claim_3_10 + claim_3_14 all `import` from one place. Rejected:
  only one consumer needs the `\ J` form (this row); the `\spl`
  and `\swig` cases work without `\ J` because their `W ⊆ G.V`
  precondition makes `W \ J = W` (vacuously). A shared lemma
  would force claim_3_7 / claim_3_10 to thread a vacuous `G.J`
  argument that they don't need. Reconsider if a chapter-4 or
  later row introduces a *third* "extension with diff" use case;
  for now, code-duplication of a two-line bijection is cheaper
  than the API bloat.

* **Codomain ends in `↑(Sum.inl '' (W₂ \ G.J))`, not the cleaner
  `↑(W₂ \ G.J)`.** The iterated outer-extension
  `(G.ext W₁ _).ext (Sum.inl '' W₂) _` has carrier
  `(α ⊕ ↑(W₁ \ G.J)) ⊕ ↑((Sum.inl '' W₂) \ (G.ext W₁ _).J)`
  directly from the signature of
  `extendingCDMGWithInterventionNodes` -- its second argument is
  `Sum.inl '' W₂`. The `Equiv.Set.image` step lifts the right
  summand under `Sum.inl` so the codomain matches that
  signature's outer-subtype shape *as far as `Sum.inl '' (W₂ \
  G.J)` goes*. A `setCongr` bridge `↑(Sum.inl '' (W₂ \ G.J)) ≃
  ↑((Sum.inl '' W₂) \ (G.ext W₁ _).J)` then absorbs the remaining
  `\ G.J`-vs-`\ (Sum.inl '' G.J ∪ range Sum.inr)` mismatch
  inside the consumer (Manager B's job; cf. R2 in
  `workspace_claim_3_14.md`). Same asymmetric wrapping as
  claim_3_7's `fusionEquiv` (lines 291 -- 302 of
  `TwoDisjointNodeSplittingsCommute.lean`); avoiding it would
  require touching `ExtendingCDMGsWithInterventionNodes.lean` to
  factor out a carrier-lift helper, which is out of scope.

* **`noncomputable` -- inherited from `Equiv.Set.union`.** Same
  trade-off as the sibling `fusionEquiv` in claim_3_7
  (`TwoDisjointNodeSplittingsCommute.lean` lines 262 -- 277):
  `Equiv.Set.union` consumes a `DecidablePred`, we supply it via
  `Classical.decPred`, and `noncomputable` propagates. No
  observable cost since downstream usage is `Prop`-valued (in
  the type of `CDMGEquiv`-valued witnesses). Consistency across
  Section 3.2: `nodeSplittingOn` and friends are also
  `noncomputable`, so no `noncomputable`-vs-computable boundary
  is introduced here. -/
noncomputable def extFusionEquiv (G : CDMG α) (W₁ W₂ : Set α)
    (hdisj : Disjoint W₁ W₂) :
    α ⊕ ↑((W₁ ∪ W₂) \ G.J) ≃
      (α ⊕ ↑(W₁ \ G.J)) ⊕
        ↑((Sum.inl : α → α ⊕ ↑(W₁ \ G.J)) '' (W₂ \ G.J)) :=
  letI : DecidablePred (· ∈ (W₁ \ G.J)) := Classical.decPred _
  have hdisj_diff : Disjoint (W₁ \ G.J) (W₂ \ G.J) :=
    hdisj.mono Set.diff_subset Set.diff_subset
  (Equiv.sumCongr (Equiv.refl α)
        (Equiv.setCongr
          (Set.union_diff_distrib (s := W₁) (t := W₂) (u := G.J)))).trans <|
    (Equiv.sumCongr (Equiv.refl α) (Equiv.Set.union hdisj_diff)).trans <|
      (Equiv.sumAssoc α ↑(W₁ \ G.J) ↑(W₂ \ G.J)).symm.trans <|
        Equiv.sumCongr (Equiv.refl (α ⊕ ↑(W₁ \ G.J)))
          (Equiv.Set.image (Sum.inl : α → α ⊕ ↑(W₁ \ G.J)) (W₂ \ G.J)
            Sum.inl_injective)

/-! ## Chain 1: fusion lemma + commute corollary -/

-- claim_3_14 (chain 1, part 1/2)
-- title: AddingInterventionNodes -- chain 1 fusion lemma
--
-- Iterating two intervention-node extensions on disjoint sets collapses
-- (modulo the canonical re-labeling `extFusionEquiv`) into a single
-- extension on the union. Mirrors the LN's second `=` of chain 1:
-- `(G_{do(I_{W₁})})_{do(I_{W₂})} = G_{do(I_{W₁ ∪ W₂})}`. The commute
-- direction (first `=`) is `extendingCDMGWithInterventionNodes_comm_equiv`
-- below.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` Lem 832 -- 843
(both chain 1 and chain 2 are bundled in the same `\Lem`; this
declaration corresponds to the *second* `=` of chain 1):

\begin{claimmark}
\begin{Lem}[Adding intervention nodes commutes with disjoint hard interventions]
    Let $G=(J,V,E,L)$ be a CDMG and $W_1, W_2 \ins J \cup V$ two disjoint subsets of nodes from $G$.
      Then we have:
      \[ \lp G_{\doit(I_{W_1})} \rp_{\doit(I_{W_2})} = \lp G_{\doit(I_{W_2})} \rp_{\doit(I_{W_1})}
      =  G_{\doit(I_{W_1 \cup W_2})}. \]
      We also have:
      \[ \lp G_{\doit(I_{W_1})} \rp_{\doit(W_2)} = \lp G_{\doit(W_2)} \rp_{\doit(I_{W_1})}
      =  G_{\doit(I_{W_1}, W_2)}. \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_14 chain 1, part 1/2 (fusion lemma): iterating
`extendingCDMGWithInterventionNodes` on disjoint `W₁`, `W₂` is
`CDMGEquiv`-equivalent to a single extension on `W₁ ∪ W₂`. Mirrors
the second `=` of chain 1 in the LN's `\Lem` at
`lecture-notes/lecture_notes/graphs.tex` line 836:
`(G_{do(I_{W₁})})_{do(I_{W₂})} = G_{do(I_{W₁ ∪ W₂})}`.

Body = `sorry`; the LN's own proof at `graphs.tex` lines 847 -- 862
supplies the four field-equality arguments. The load-bearing
sub-argument is "$W_2 \sm J_1 = W_2 \sm J$" -- since the freshly added
`I_w` (for `w ∈ W₁ \ G.J`) do not belong to `W₂` (constructor
disjointness `Sum.inl ≠ Sum.inr`) and `Disjoint W₁ W₂` rules out
overlap with the original `W₁ \ G.J` piece.

## Design choice (workspace decisions D1, D2)

* **`CDMGEquiv` rather than literal `Eq` -- forced by typing, not
  stylistic (D1).** The LN's second `=` reads as set-equality at
  the CDMG-data level, but the two CDMGs in the conclusion live
  over *different* carrier types:
    * iterated side
      `(G.ext W₁ _).ext (Sum.inl '' W₂) _` :
      `CDMG ((α ⊕ ↑(W₁ \ G.J)) ⊕ ↑((Sum.inl '' W₂) \ (G.ext W₁ _).J))`
      -- the outer extension subtypes its `Sum.inr` summand by
      `(Sum.inl '' W₂) \ (G.ext W₁ _).J` directly, which after
      unfolding `(G.ext W₁ _).J` is *not* def-equal to a flat
      `Sum.inl '' (W₂ \ G.J)` (the LN's `W_2 \sm J_1 = W_2 \sm J`
      identity holds *as a set equation* under `Disjoint W₁ W₂`,
      but not as a *predicate* on `α ⊕ ↑(W₁ \ G.J)`);
    * merged side
      `G.ext (W₁ ∪ W₂) _` :
      `CDMG (α ⊕ ↑((W₁ ∪ W₂) \ G.J))` -- a *flat* `Sum`, not nested.

  These are not the same type, so literal `Eq` is not type-correct
  -- even with `Disjoint W₁ W₂` in scope. `CDMGEquiv` is the
  categorified version that captures "carrier-equal up to a
  canonical bijection plus four field-equalities", with the
  canonical bijection here being `(extFusionEquiv G W₁ W₂
  hdisj).symm` composed with a small `setCongr` bridge absorbing
  the `Sum.inl '' (W₂ \ G.J)` vs `(Sum.inl '' W₂) \ (G.ext W₁ _).J`
  set-equation. Same regime as claim_3_7's
  `nodeSplittingOn_nodeSplittingOn_equiv`
  (`TwoDisjointNodeSplittingsCommute.lean` lines 385 -- 392) and
  claim_3_10's `swig_swig_equiv` -- the three Section 3.2 rows that
  iterate a *carrier-changing* operator on two different sets all
  ship `CDMGEquiv`. Contrast with claim_3_4 / claim_3_8 / claim_3_11
  which iterate carrier-preserving operators (or apply only one
  carrier-changing step) and ship literal `Eq`.

* **Fusion + commute split mirrors the LN's own proof structure
  (D2).** The LN states a chained equality
  `(G_{do(I_{W₁})})_{do(I_{W₂})} = (G_{do(I_{W₂})})_{do(I_{W₁})}
  = G_{do(I_{W₁ ∪ W₂})}` and only proves the *fusion* direction
  (`graphs.tex` lines 847 -- 861); the commute direction is "by
  symmetry" (`graphs.tex` line 862). We follow that factoring:
  this declaration is the load-bearing fusion lemma, with the
  commute corollary `extendingCDMGWithInterventionNodes_comm_equiv`
  below derived by composing two fusion calls through a
  `Set.union_comm` bridge. Same factoring as claim_3_7
  (`nodeSplittingOn_nodeSplittingOn_equiv` + `nodeSplittingOn_comm_equiv`)
  and claim_3_10 (`swig_swig_equiv` + `swig_comm_equiv`). The
  consequence: callers who only want the fusion (collapsing two
  iterates into one) reach for *this* declaration; callers who
  only want commutation (swapping `W₁ ↔ W₂` while keeping two
  iterates) reach for the corollary. Both Lean names are
  load-bearing API; the LN's chained equality is exposed as two
  named facts the consumer can pick between by `rw`-shape.

* **Joint third term `G.ext (W₁ ∪ W₂) _` materialised as a
  *real* operator on the merged side (D3, chain-1 half).** The
  LN's third term `G_{do(I_{W₁ ∪ W₂})}` is a literal single
  extension on the union -- the same operator
  `extendingCDMGWithInterventionNodes` evaluated at `W₁ ∪ W₂`.
  We make this materialisation explicit: the RHS of the
  `CDMGEquiv` is `G.extendingCDMGWithInterventionNodes (W₁ ∪ W₂)
  (Set.union_subset hW₁ hW₂)`, *not* a fresh
  `extendingCDMGWithInterventionNodesJoint` operator. The
  precondition for the merged side is then
  `Set.union_subset hW₁ hW₂`, which composes the two prior
  preconditions verbatim. Contrast with chain 2 (decl-7
  below), where the LN's third term `G_{do(I_{W₁}, W₂)}` is
  *notation for the unambiguous composite*, not a single
  operator -- so we do *not* materialise it as a third Lean
  term there, and the chain-2 `CDMGEquiv` has only two
  iterates in its conclusion. This asymmetry in
  third-term-materialisation between chain 1 and chain 2 is
  intentional and mirrors the LN exactly.

* **`Sum.inl '' W₂` lift on the inner-set argument of the
  iterated side -- same justification as the chain-1 helper.**
  The outer-`ext` lives over `α ⊕ ↑(W₁ \ G.J)`; its second
  argument must be a `Set (α ⊕ ↑(W₁ \ G.J))`. The
  LN-faithful lift is `Sum.inl '' W₂` (canonical embedding of
  the original `W₂ : Set α` into the extension carrier;
  inherits the LN's implicit `α ≅ Sum.inl '' α`
  identification from the carrier-level convention recorded
  in `ExtendingCDMGsWithInterventionNodes.lean` lines 82 -- 113).
  Same lift / same justification as `hardInterventionOn_swig_comm`
  (`HardInterventionSwigCommute.lean` lines 169 -- 206) and the
  chain-1 helper above; without it, the outer `ext` is not
  type-correct.

* **Implicit `G`, `W₁`, `W₂` -- explicit `hW₁`, `hW₂`, `hdisj`.**
  The two sets pin themselves down via the conclusion (they
  appear on both sides of the `CDMGEquiv`), so making them
  implicit and the three hypotheses explicit mirrors the
  signature of `nodeSplittingOn_nodeSplittingOn_equiv`
  (`TwoDisjointNodeSplittingsCommute.lean` lines 385 -- 392) and
  keeps a uniform argument-order convention across the three
  iterated-carrier-changing fusion lemmas of Section 3.2. -/
noncomputable def extendingCDMGWithInterventionNodes_fusion_equiv
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hdisj : Disjoint W₁ W₂) :
    CDMGEquiv
      ((G.extendingCDMGWithInterventionNodes W₁ hW₁).extendingCDMGWithInterventionNodes
          (Sum.inl '' W₂)
          (subset_extendingCDMGWithInterventionNodes_J_union_V_of_subset hW₁ hW₂))
      (G.extendingCDMGWithInterventionNodes (W₁ ∪ W₂)
          (Set.union_subset hW₁ hW₂)) := by
  -- TeX: tex/claim_3_14_proof_AddingInterventionNodes.tex, chain 1.
  -- The carrier transport is `bridge.trans extFusionEquiv.symm` where
  -- `bridge` absorbs the `(Sum.inl '' W₂) \ (G.ext W₁ hW₁).J
  --  = Sum.inl '' (W₂ \ G.J)` set-equation (TeX preamble's "no collision
  -- with fresh intervention nodes", graphs.tex 852). The proof structure
  -- mirrors claim_3_7's `nodeSplittingOn_nodeSplittingOn_equiv`
  -- (`TwoDisjointNodeSplittingsCommute.lean`); the four field-equality
  -- fields correspond to TeX components (a)–(d) at graphs.tex 853–862.
  letI : DecidablePred (· ∈ W₁) := Classical.decPred _
  letI : DecidablePred (· ∈ W₁ \ G.J) := Classical.decPred _
  have hdisj_diff : Disjoint (W₁ \ G.J) (W₂ \ G.J) :=
    hdisj.mono Set.diff_subset Set.diff_subset
  -- Bridge equation between the two outer `Sum.inr` subtypes
  -- (TeX preamble's "no collision" bullet, graphs.tex 852).
  have h_bridge :
      ((Sum.inl : α → α ⊕ ↑(W₁ \ G.J)) '' W₂) \
        (G.extendingCDMGWithInterventionNodes W₁ hW₁).J
      = (Sum.inl : α → α ⊕ ↑(W₁ \ G.J)) '' (W₂ \ G.J) := by
    rw [extendingCDMGWithInterventionNodes_J]
    ext x
    simp only [Set.mem_diff, Set.mem_image, Set.mem_union, Set.mem_range]
    constructor
    · rintro ⟨⟨b, hbW₂, rfl⟩, hno⟩
      refine ⟨b, ⟨hbW₂, ?_⟩, rfl⟩
      intro hbJ
      exact hno (Or.inl ⟨b, hbJ, rfl⟩)
    · rintro ⟨b, ⟨hbW₂, hbJ⟩, rfl⟩
      refine ⟨⟨b, hbW₂, rfl⟩, ?_⟩
      rintro (⟨z, hzJ, hzeq⟩ | ⟨w, hwz⟩)
      · exact hbJ (Sum.inl_injective hzeq ▸ hzJ)
      · cases hwz
  -- Bridge between G_arg's outer Sum.inr subtype and extFusionEquiv's
  -- codomain Sum.inr subtype.
  let bridge :
      ((α ⊕ ↑(W₁ \ G.J)) ⊕
          ↑((Sum.inl '' W₂ : Set (α ⊕ ↑(W₁ \ G.J))) \
              (G.extendingCDMGWithInterventionNodes W₁ hW₁).J))
        ≃
      ((α ⊕ ↑(W₁ \ G.J)) ⊕
          ↑((Sum.inl : α → α ⊕ ↑(W₁ \ G.J)) '' (W₂ \ G.J))) :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.setCongr h_bridge)
  -- Forward applications of `extFusionEquiv` on each constructor case.
  have apply_inl_ext : ∀ (a : α),
      extFusionEquiv G W₁ W₂ hdisj (Sum.inl a) = Sum.inl (Sum.inl a) := fun a => by
    simp [extFusionEquiv]
  have apply_inr_left_ext : ∀ (w : α) (hwW₁ : w ∈ W₁ \ G.J)
      (hw : w ∈ (W₁ ∪ W₂) \ G.J),
      extFusionEquiv G W₁ W₂ hdisj (Sum.inr ⟨w, hw⟩) =
        Sum.inl (Sum.inr ⟨w, hwW₁⟩) := by
    intros w hwW₁ hw
    have h_diff : w ∈ (W₁ \ G.J) ∪ (W₂ \ G.J) := Or.inl hwW₁
    have h_union : (Equiv.Set.union hdisj_diff) ⟨w, h_diff⟩ =
        Sum.inl ⟨w, hwW₁⟩ :=
      Equiv.Set.union_apply_left (a := ⟨w, h_diff⟩) hdisj_diff hwW₁
    simp [extFusionEquiv, h_union]
  have apply_inr_right_ext : ∀ (w : α) (hwW₂ : w ∈ W₂ \ G.J)
      (hw : w ∈ (W₁ ∪ W₂) \ G.J),
      extFusionEquiv G W₁ W₂ hdisj (Sum.inr ⟨w, hw⟩) =
        Sum.inr ⟨Sum.inl w, ⟨w, hwW₂, rfl⟩⟩ := by
    intros w hwW₂ hw
    have h_diff : w ∈ (W₁ \ G.J) ∪ (W₂ \ G.J) := Or.inr hwW₂
    have h_union : (Equiv.Set.union hdisj_diff) ⟨w, h_diff⟩ =
        Sum.inr ⟨w, hwW₂⟩ :=
      Equiv.Set.union_apply_right (a := ⟨w, h_diff⟩) hdisj_diff hwW₂
    simp [extFusionEquiv, h_union]
  -- Derive the symm-direction by `e.symm (e x) = x`.
  have symm_inl_inl : ∀ (a : α),
      (extFusionEquiv G W₁ W₂ hdisj).symm (Sum.inl (Sum.inl a)) = Sum.inl a :=
    fun a => by rw [← apply_inl_ext a]; exact Equiv.symm_apply_apply _ _
  have symm_inl_inr : ∀ (w : α) (hwW₁ : w ∈ W₁ \ G.J)
      (hw : w ∈ (W₁ ∪ W₂) \ G.J),
      (extFusionEquiv G W₁ W₂ hdisj).symm (Sum.inl (Sum.inr ⟨w, hwW₁⟩)) =
        Sum.inr ⟨w, hw⟩ := fun w hwW₁ hw => by
    rw [← apply_inr_left_ext w hwW₁ hw]
    exact Equiv.symm_apply_apply _ _
  have symm_inr_right : ∀ (w : α) (hwW₂ : w ∈ W₂ \ G.J)
      (hw : w ∈ (W₁ ∪ W₂) \ G.J),
      (extFusionEquiv G W₁ W₂ hdisj).symm
          (Sum.inr ⟨Sum.inl w, ⟨w, hwW₂, rfl⟩⟩) = Sum.inr ⟨w, hw⟩ :=
    fun w hwW₂ hw => by
      rw [← apply_inr_right_ext w hwW₂ hw]
      exact Equiv.symm_apply_apply _ _
  -- Compose bridge with extFusionEquiv.symm to land in H_arg.carrier.
  -- The three nontrivial cases: Sum.inl (Sum.inl a), Sum.inl (Sum.inr w),
  -- Sum.inr ⟨Sum.inl b, _⟩ (constructor-mismatch rules out Sum.inr ⟨Sum.inr _, _⟩).
  have toEq_inl_inl : ∀ (a : α),
      bridge.trans (extFusionEquiv G W₁ W₂ hdisj).symm (Sum.inl (Sum.inl a)) =
        Sum.inl a := fun a => by
    change (extFusionEquiv G W₁ W₂ hdisj).symm (Sum.inl (Sum.inl a)) = Sum.inl a
    exact symm_inl_inl a
  have toEq_inl_inr : ∀ (w : α) (hwW₁ : w ∈ W₁ \ G.J)
      (hw : w ∈ (W₁ ∪ W₂) \ G.J),
      bridge.trans (extFusionEquiv G W₁ W₂ hdisj).symm
          (Sum.inl (Sum.inr ⟨w, hwW₁⟩)) = Sum.inr ⟨w, hw⟩ :=
    fun w hwW₁ hw => by
      change (extFusionEquiv G W₁ W₂ hdisj).symm
          (Sum.inl (Sum.inr ⟨w, hwW₁⟩)) = _
      exact symm_inl_inr w hwW₁ hw
  have toEq_inr_inl : ∀ (b : α) (hbW₂ : b ∈ W₂ \ G.J)
      (hb : Sum.inl b ∈
        ((Sum.inl '' W₂ : Set (α ⊕ ↑(W₁ \ G.J))) \
          (G.extendingCDMGWithInterventionNodes W₁ hW₁).J))
      (hw : b ∈ (W₁ ∪ W₂) \ G.J),
      bridge.trans (extFusionEquiv G W₁ W₂ hdisj).symm
          (Sum.inr ⟨Sum.inl b, hb⟩) = Sum.inr ⟨b, hw⟩ :=
    fun b hbW₂ hb hw => by
      change (extFusionEquiv G W₁ W₂ hdisj).symm
          (Sum.inr ⟨Sum.inl b, ⟨b, hbW₂, rfl⟩⟩) = Sum.inr ⟨b, hw⟩
      exact symm_inr_right b hbW₂ hw
  refine
    { toEquiv := bridge.trans (extFusionEquiv G W₁ W₂ hdisj).symm
      J_eq := ?_
      V_eq := ?_
      E_eq := ?_
      L_eq := ?_ }
  · -- (a) Input nodes (J), chain 1. TeX: graphs.tex 853 -- 858.
    -- H_arg.J = Sum.inl '' G.J ∪ Set.range Sum.inr (def-eq).
    -- G_arg.J = Sum.inl '' (Sum.inl '' G.J ∪ Set.range Sum.inr) ∪ Set.range Sum.inr.
    ext y
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨⟨v, hv⟩, rfl⟩)
      · -- y = Sum.inl j, j ∈ G.J. Source x = Sum.inl (Sum.inl j).
        refine ⟨Sum.inl (Sum.inl j),
          Or.inl ⟨Sum.inl j, Or.inl ⟨j, hj, rfl⟩, rfl⟩, ?_⟩
        exact toEq_inl_inl j
      · -- y = Sum.inr ⟨v, hv⟩, hv : v ∈ (W₁ ∪ W₂) \ G.J.
        rcases hv.1 with hvW₁ | hvW₂
        · -- v ∈ W₁ \ G.J: source via inner Sum.inr.
          have hwW₁ : v ∈ W₁ \ G.J := ⟨hvW₁, hv.2⟩
          refine ⟨Sum.inl (Sum.inr ⟨v, hwW₁⟩),
            Or.inl ⟨Sum.inr ⟨v, hwW₁⟩, Or.inr ⟨⟨v, hwW₁⟩, rfl⟩, rfl⟩, ?_⟩
          exact toEq_inl_inr v hwW₁ hv
        · -- v ∈ W₂ \ G.J: source via outer Sum.inr (across the bridge).
          have hbW₂ : v ∈ W₂ \ G.J := ⟨hvW₂, hv.2⟩
          have hb : Sum.inl v ∈
              (Sum.inl '' W₂ : Set (α ⊕ ↑(W₁ \ G.J))) \
                (G.extendingCDMGWithInterventionNodes W₁ hW₁).J := by
            refine ⟨⟨v, hvW₂, rfl⟩, ?_⟩
            rw [extendingCDMGWithInterventionNodes_J]
            rintro (⟨z, hzJ, hzeq⟩ | ⟨w, hw⟩)
            · exact hv.2 (Sum.inl_injective hzeq ▸ hzJ)
            · cases hw
          refine ⟨Sum.inr ⟨Sum.inl v, hb⟩, Or.inr ⟨⟨Sum.inl v, hb⟩, rfl⟩, ?_⟩
          exact toEq_inr_inl v hbW₂ hb hv
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨z, hz, rfl⟩ | ⟨⟨y_in, hy_in⟩, rfl⟩
      · -- x = Sum.inl z; z ∈ (G.ext W₁ hW₁).J.
        rcases hz with ⟨j, hj, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩
        · -- z = Sum.inl j, j ∈ G.J.
          rw [toEq_inl_inl j]
          exact Or.inl ⟨j, hj, rfl⟩
        · -- z = Sum.inr ⟨w, hw⟩, hw : w ∈ W₁ \ G.J.
          have hw_union : w ∈ (W₁ ∪ W₂) \ G.J := ⟨Or.inl hw.1, hw.2⟩
          rw [toEq_inl_inr w hw hw_union]
          exact Or.inr ⟨⟨w, hw_union⟩, rfl⟩
      · -- x = Sum.inr ⟨y_in, hy_in⟩.
        -- y_in = Sum.inl b for some b ∈ W₂ (from hy_in.1) and b ∉ G.J (from hy_in.2).
        obtain ⟨⟨b, hbW₂, rfl⟩, hno⟩ := hy_in
        have hbJ : b ∉ G.J := by
          intro hbJ
          rw [extendingCDMGWithInterventionNodes_J] at hno
          exact hno (Or.inl ⟨b, hbJ, rfl⟩)
        have hbW₂_diff : b ∈ W₂ \ G.J := ⟨hbW₂, hbJ⟩
        have hb_union : b ∈ (W₁ ∪ W₂) \ G.J := ⟨Or.inr hbW₂, hbJ⟩
        rw [toEq_inr_inl b hbW₂_diff _ hb_union]
        exact Or.inr ⟨⟨b, hb_union⟩, rfl⟩
  · -- (b) Output nodes (V), chain 1. TeX: graphs.tex 859.
    -- H_arg.V = Sum.inl '' G.V (def-eq).
    -- G_arg.V = Sum.inl '' (Sum.inl '' G.V) (def-eq).
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      -- y = Sum.inl v, v ∈ G.V. Source x = Sum.inl (Sum.inl v).
      refine ⟨Sum.inl (Sum.inl v), ⟨Sum.inl v, ⟨v, hv, rfl⟩, rfl⟩, ?_⟩
      exact toEq_inl_inl v
    · rintro ⟨x, ⟨z, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
      -- x = Sum.inl (Sum.inl v), v ∈ G.V.
      rw [toEq_inl_inl v]
      exact ⟨v, hv, rfl⟩
  · -- (c) Directed edges (E), chain 1. TeX: graphs.tex 860 -- 861.
    -- H_arg.E = (Sum.inl × Sum.inl) '' G.E ∪ Set.range (fresh edges).
    -- G_arg.E = (Sum.inl × Sum.inl) '' (G.ext W₁).E ∪ Set.range (outer fresh edges).
    ext p
    rw [Set.mem_image, mem_extendingCDMGWithInterventionNodes_E]
    constructor
    · rintro (⟨v₁, v₂, hE, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩)
      · -- Original edge case: p = (Sum.inl v₁, Sum.inl v₂), (v₁, v₂) ∈ G.E.
        -- Source q = (Sum.inl (Sum.inl v₁), Sum.inl (Sum.inl v₂)).
        refine ⟨(Sum.inl (Sum.inl v₁), Sum.inl (Sum.inl v₂)), ?_, ?_⟩
        · rw [mem_extendingCDMGWithInterventionNodes_E]
          refine Or.inl ⟨Sum.inl v₁, Sum.inl v₂, ?_, rfl⟩
          rw [mem_extendingCDMGWithInterventionNodes_E]
          exact Or.inl ⟨v₁, v₂, hE, rfl⟩
        · exact Prod.ext (toEq_inl_inl v₁) (toEq_inl_inl v₂)
      · -- Fresh-edge case: p = (Sum.inr ⟨w, hw⟩, Sum.inl w), hw : w ∈ (W₁ ∪ W₂) \ G.J.
        rcases hw.1 with hvW₁ | hvW₂
        · -- w ∈ W₁ \ G.J: source via inner fresh edge (lifted).
          have hwW₁ : w ∈ W₁ \ G.J := ⟨hvW₁, hw.2⟩
          refine ⟨(Sum.inl (Sum.inr ⟨w, hwW₁⟩), Sum.inl (Sum.inl w)), ?_, ?_⟩
          · rw [mem_extendingCDMGWithInterventionNodes_E]
            refine Or.inl ⟨Sum.inr ⟨w, hwW₁⟩, Sum.inl w, ?_, rfl⟩
            rw [mem_extendingCDMGWithInterventionNodes_E]
            exact Or.inr ⟨⟨w, hwW₁⟩, rfl⟩
          · exact Prod.ext (toEq_inl_inr w hwW₁ hw) (toEq_inl_inl w)
        · -- w ∈ W₂ \ G.J: source via outer fresh edge (across the bridge).
          have hbW₂ : w ∈ W₂ \ G.J := ⟨hvW₂, hw.2⟩
          have hb : Sum.inl w ∈
              (Sum.inl '' W₂ : Set (α ⊕ ↑(W₁ \ G.J))) \
                (G.extendingCDMGWithInterventionNodes W₁ hW₁).J := by
            refine ⟨⟨w, hvW₂, rfl⟩, ?_⟩
            rw [extendingCDMGWithInterventionNodes_J]
            rintro (⟨z, hzJ, hzeq⟩ | ⟨w', hw'⟩)
            · exact hw.2 (Sum.inl_injective hzeq ▸ hzJ)
            · cases hw'
          refine ⟨(Sum.inr ⟨Sum.inl w, hb⟩, Sum.inl (Sum.inl w)), ?_, ?_⟩
          · rw [mem_extendingCDMGWithInterventionNodes_E]
            exact Or.inr ⟨⟨Sum.inl w, hb⟩, rfl⟩
          · exact Prod.ext (toEq_inr_inl w hbW₂ hb hw) (toEq_inl_inl w)
    · rintro ⟨q, hq, rfl⟩
      rw [mem_extendingCDMGWithInterventionNodes_E] at hq
      rcases hq with ⟨a₁, a₂, ha, rfl⟩ | ⟨⟨y_in, hy_in⟩, rfl⟩
      · -- Original double-lift on the iterated side.
        rw [mem_extendingCDMGWithInterventionNodes_E] at ha
        rcases ha with ⟨v₁, v₂, hE, h_eq⟩ | ⟨⟨w, hw⟩, h_eq⟩
        · -- Inner original edge.
          injection h_eq with h_eq1 h_eq2
          subst h_eq1; subst h_eq2
          refine Or.inl ⟨v₁, v₂, hE, ?_⟩
          exact Prod.ext (toEq_inl_inl v₁) (toEq_inl_inl v₂)
        · -- Inner fresh edge (Sum.inr ⟨w, hw⟩, Sum.inl w).
          injection h_eq with h_eq1 h_eq2
          subst h_eq1; subst h_eq2
          have hw_union : w ∈ (W₁ ∪ W₂) \ G.J := ⟨Or.inl hw.1, hw.2⟩
          refine Or.inr ⟨⟨w, hw_union⟩, ?_⟩
          exact Prod.ext (toEq_inl_inr w hw hw_union) (toEq_inl_inl w)
      · -- Outer fresh edge.
        obtain ⟨⟨b, hbW₂, rfl⟩, hno⟩ := hy_in
        have hbJ : b ∉ G.J := by
          intro hbJ
          rw [extendingCDMGWithInterventionNodes_J] at hno
          exact hno (Or.inl ⟨b, hbJ, rfl⟩)
        have hbW₂_diff : b ∈ W₂ \ G.J := ⟨hbW₂, hbJ⟩
        have hb_union : b ∈ (W₁ ∪ W₂) \ G.J := ⟨Or.inr hbW₂, hbJ⟩
        refine Or.inr ⟨⟨b, hb_union⟩, ?_⟩
        exact Prod.ext (toEq_inr_inl b hbW₂_diff _ hb_union)
          (toEq_inl_inl b)
  · -- (d) Bidirected edges (L), chain 1. TeX: graphs.tex 862.
    -- H_arg.L = (Sum.inl × Sum.inl) '' G.L.
    -- G_arg.L = (Sum.inl × Sum.inl) '' (Sum.inl × Sum.inl) '' G.L.
    ext p
    rw [Set.mem_image, mem_extendingCDMGWithInterventionNodes_L]
    constructor
    · rintro ⟨v₁, v₂, hL, rfl⟩
      refine ⟨(Sum.inl (Sum.inl v₁), Sum.inl (Sum.inl v₂)), ?_, ?_⟩
      · rw [mem_extendingCDMGWithInterventionNodes_L]
        refine ⟨Sum.inl v₁, Sum.inl v₂, ?_, rfl⟩
        rw [mem_extendingCDMGWithInterventionNodes_L]
        exact ⟨v₁, v₂, hL, rfl⟩
      · exact Prod.ext (toEq_inl_inl v₁) (toEq_inl_inl v₂)
    · rintro ⟨q, hq, rfl⟩
      rw [mem_extendingCDMGWithInterventionNodes_L] at hq
      obtain ⟨a, b, hab, rfl⟩ := hq
      rw [mem_extendingCDMGWithInterventionNodes_L] at hab
      obtain ⟨v₁, v₂, hL, h_eq⟩ := hab
      injection h_eq with h_eq1 h_eq2
      subst h_eq1; subst h_eq2
      refine ⟨v₁, v₂, hL, ?_⟩
      exact Prod.ext (toEq_inl_inl v₁) (toEq_inl_inl v₂)

-- claim_3_14 (chain 1, part 2/2)
-- title: AddingInterventionNodes -- chain 1 commute corollary
--
-- Swapping `W₁` and `W₂` in the iterated extension gives a
-- `CDMGEquiv`-equivalent CDMG. The LN closes this direction with
-- "by symmetry" (`graphs.tex` line 862); the Lean transcription
-- composes two fusion-lemma invocations through a `Set.union_comm`
-- bridge.
/-
Verbatim LN block: same `\Lem` as the fusion lemma above (`graphs.tex`
lines 832 -- 843); this declaration corresponds to the *first* `=`
of chain 1.
-/
/-- claim_3_14 chain 1, part 2/2 (commute corollary): swapping `W₁` and
`W₂` in the iterated extension is `CDMGEquiv`-symmetric. Mirrors the
first `=` of chain 1:
`(G_{do(I_{W₁})})_{do(I_{W₂})} = (G_{do(I_{W₂})})_{do(I_{W₁})}`.

Body = `sorry`; Manager B derives this as
`(fusion W₁ W₂ hdisj).trans (bridge.trans (fusion W₂ W₁ hdisj.symm).symm)`,
where `bridge` is a small `CDMGEquiv` absorbing the
`Set.union_comm`-discrepancy between `↑((W₁ ∪ W₂) \ G.J)` and
`↑((W₂ ∪ W₁) \ G.J)` via `Equiv.subtypeEquivRight (fun _ => Or.comm)`.
Same construction as `nodeSplittingOn_comm_equiv` in
`TwoDisjointNodeSplittingsCommute.lean` lines 661 -- 752 (sibling
`bridge` device).

## Design choice (workspace decision D2)

* **Derived from the fusion lemma, not re-proven from scratch.**
  Once `extendingCDMGWithInterventionNodes_fusion_equiv` is in
  hand for both `(W₁, W₂, hdisj)` and `(W₂, W₁, hdisj.symm)`,
  Manager B's proof is a short composition through the
  `Set.union_comm`-bridge:
  `(fusion W₁ W₂ hdisj).trans (bridge.trans (fusion W₂ W₁
  hdisj.symm).symm)`. The bridge absorbs the difference between
  the joint third terms `G.ext (W₁ ∪ W₂) _` and `G.ext (W₂ ∪
  W₁) _`, which are equal as `Set α`-valued data but live over
  the def-distinct carrier subtypes `↑((W₁ ∪ W₂) \ G.J)` vs
  `↑((W₂ ∪ W₁) \ G.J)`. This is the entire payoff of shipping
  `CDMGEquiv.refl / symm / trans` with the structure (claim_3_7's
  groupoid laws at `TwoDisjointNodeSplittingsCommute.lean` lines
  165 -- 211), and is the Lean transcription of the LN's "by
  symmetry" close at `graphs.tex` line 862.

* **Stand-alone declaration, not folded into the fusion lemma's
  conclusion.** Downstream consumers that want to *swap* two
  intervention-node extensions (without collapsing them into a
  single joint extension) reach for this form directly. Folding
  it inside the fusion lemma would force every such consumer to
  chain two fusion calls themselves, an extra step every time,
  with the `Set.union_comm`-bridge re-derived at each call site.
  Same reasoning as `nodeSplittingOn_comm_equiv` vs
  `nodeSplittingOn_nodeSplittingOn_equiv` in
  `TwoDisjointNodeSplittingsCommute.lean` lines 613 -- 754, and
  `swig_comm_equiv` vs `swig_swig_equiv` in claim_3_10. The
  LN's chained equality is exposed as two named Lean facts a
  consumer can pick between by the `rw`-shape they need.

* **Same `CDMGEquiv` regime as the fusion lemma -- not literal
  `Eq` (D1).** Both iterates in the conclusion have *different*
  carriers: the LHS-iterate lives over
  `(α ⊕ ↑(W₁ \ G.J)) ⊕ ↑((Sum.inl '' W₂) \ (G.ext W₁ _).J)` and
  the RHS-iterate lives over `(α ⊕ ↑(W₂ \ G.J)) ⊕ ↑((Sum.inl
  '' W₁) \ (G.ext W₂ _).J)`. The two carriers are not even
  symmetric-looking (the outer `Sum.inl ''` lifts to different
  inner subtype types) -- the carrier-rewriting `CDMGEquiv`
  is what bridges them via the canonical composition described
  in the proof sketch above. Literal `Eq` would not type-check.

* **Mirror declaration `extendingCDMGWithInterventionNodes_comm_equiv
  (hW₂) (hW₁) hdisj.symm` is *not* exposed.** The reverse
  direction (with `W₁`/`W₂` swapped in the signature) is
  obtainable from this one via `.symm`. Following claim_3_7's
  convention (only `nodeSplittingOn_comm_equiv` in one
  orientation is exposed; consumers use `.symm` for the other),
  we expose one orientation. The LN's LHS-then-RHS reading order
  pins the choice.

* **`hdisj` not `hdisj.symm` on the second `fusion` call -- chosen
  by the bridge's parameter order.** Manager B's composition
  threads `hdisj.symm : Disjoint W₂ W₁` into the second fusion
  call, which is exactly the form Mathlib's `Disjoint.symm`
  produces. No special lemma is needed; cf. the identical pattern
  in claim_3_7's `nodeSplittingOn_comm_equiv` proof
  (`TwoDisjointNodeSplittingsCommute.lean` line 753). -/
noncomputable def extendingCDMGWithInterventionNodes_comm_equiv
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hdisj : Disjoint W₁ W₂) :
    CDMGEquiv
      ((G.extendingCDMGWithInterventionNodes W₁ hW₁).extendingCDMGWithInterventionNodes
          (Sum.inl '' W₂)
          (subset_extendingCDMGWithInterventionNodes_J_union_V_of_subset hW₁ hW₂))
      ((G.extendingCDMGWithInterventionNodes W₂ hW₂).extendingCDMGWithInterventionNodes
          (Sum.inl '' W₁)
          (subset_extendingCDMGWithInterventionNodes_J_union_V_of_subset hW₂ hW₁)) := by
  -- Build a small bridge CDMGEquiv between the two merged CDMGs (over
  -- W₁ ∪ W₂ vs W₂ ∪ W₁). Equal as Set α data, but def-distinct subtype
  -- carriers. Bridge absorbs the Set.union_comm discrepancy via
  -- Equiv.subtypeEquivRight (preserves underlying value). Mirrors the
  -- claim_3_7 sibling `nodeSplittingOn_comm_equiv`'s `bridge` device
  -- (TwoDisjointNodeSplittingsCommute.lean lines 661 -- 752); the only
  -- difference is the extra `\ G.J` in our subtype predicate.
  let σ : ↑((W₁ ∪ W₂) \ G.J) ≃ ↑((W₂ ∪ W₁) \ G.J) :=
    Equiv.subtypeEquivRight (fun _ =>
      ⟨fun ⟨hw, hwJ⟩ => ⟨hw.symm, hwJ⟩,
       fun ⟨hw, hwJ⟩ => ⟨hw.symm, hwJ⟩⟩)
  let toEq : (α ⊕ ↑((W₁ ∪ W₂) \ G.J)) ≃ (α ⊕ ↑((W₂ ∪ W₁) \ G.J)) :=
    Equiv.sumCongr (Equiv.refl α) σ
  have toEq_inl : ∀ (a : α),
      toEq (Sum.inl a) = Sum.inl a := fun _ => rfl
  have toEq_inr : ∀ (a : α) (h : a ∈ (W₁ ∪ W₂) \ G.J)
      (h' : a ∈ (W₂ ∪ W₁) \ G.J),
      toEq (Sum.inr ⟨a, h⟩) = Sum.inr ⟨a, h'⟩ := fun _ _ _ => rfl
  let bridge : CDMGEquiv
      (G.extendingCDMGWithInterventionNodes (W₁ ∪ W₂) (Set.union_subset hW₁ hW₂))
      (G.extendingCDMGWithInterventionNodes (W₂ ∪ W₁)
          (Set.union_subset hW₂ hW₁)) :=
  { toEquiv := toEq
    J_eq := by
      -- Both sides: Sum.inl '' G.J ∪ Set.range Sum.inr (range subtype differs).
      simp only [extendingCDMGWithInterventionNodes_J, Set.image_union]
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
      -- Both sides: Sum.inl '' G.V.
      simp only [extendingCDMGWithInterventionNodes_V, Set.image_image]
      refine Set.image_congr (fun v _ => ?_)
      exact (toEq_inl v).symm
    E_eq := by
      ext p
      rw [Set.mem_image, mem_extendingCDMGWithInterventionNodes_E]
      constructor
      · rintro (⟨v₁, v₂, hE, rfl⟩ | ⟨⟨w, hw'⟩, rfl⟩)
        · refine ⟨(Sum.inl v₁, Sum.inl v₂), ?_, ?_⟩
          · rw [mem_extendingCDMGWithInterventionNodes_E]
            exact Or.inl ⟨v₁, v₂, hE, rfl⟩
          · exact Prod.ext (toEq_inl v₁) (toEq_inl v₂)
        · have hw : w ∈ (W₁ ∪ W₂) \ G.J := ⟨hw'.1.symm, hw'.2⟩
          refine ⟨(Sum.inr ⟨w, hw⟩, Sum.inl w), ?_, ?_⟩
          · rw [mem_extendingCDMGWithInterventionNodes_E]
            exact Or.inr ⟨⟨w, hw⟩, rfl⟩
          · exact Prod.ext (toEq_inr w hw hw') (toEq_inl w)
      · rintro ⟨q, hq, rfl⟩
        rw [mem_extendingCDMGWithInterventionNodes_E] at hq
        rcases hq with ⟨v₁, v₂, hE, h_eq⟩ | ⟨⟨w, hw⟩, h_eq⟩
        · subst h_eq
          refine Or.inl ⟨v₁, v₂, hE, ?_⟩
          exact Prod.ext (toEq_inl v₁) (toEq_inl v₂)
        · subst h_eq
          have hw' : w ∈ (W₂ ∪ W₁) \ G.J := ⟨hw.1.symm, hw.2⟩
          refine Or.inr ⟨⟨w, hw'⟩, ?_⟩
          exact Prod.ext (toEq_inr w hw hw') (toEq_inl w)
    L_eq := by
      ext p
      rw [Set.mem_image, mem_extendingCDMGWithInterventionNodes_L]
      constructor
      · rintro ⟨v₁, v₂, hL, rfl⟩
        refine ⟨(Sum.inl v₁, Sum.inl v₂), ?_, ?_⟩
        · rw [mem_extendingCDMGWithInterventionNodes_L]
          exact ⟨v₁, v₂, hL, rfl⟩
        · exact Prod.ext (toEq_inl v₁) (toEq_inl v₂)
      · rintro ⟨q, hq, rfl⟩
        rw [mem_extendingCDMGWithInterventionNodes_L] at hq
        obtain ⟨v₁, v₂, hL, h_eq⟩ := hq
        subst h_eq
        refine ⟨v₁, v₂, hL, ?_⟩
        exact Prod.ext (toEq_inl v₁) (toEq_inl v₂) }
  exact (extendingCDMGWithInterventionNodes_fusion_equiv hW₁ hW₂ hdisj).trans
    (bridge.trans
      (extendingCDMGWithInterventionNodes_fusion_equiv hW₂ hW₁ hdisj.symm).symm)

/-! ## Chain 2: subtype-relabel carrier equiv -/

/-- Chain-2 carrier equivalence
`α ⊕ ↑(W₁ \ G.J) ≃ α ⊕ ↑(W₁ \ (G.J ∪ W₂))`.

The two subtypes are *set-equal* under `Disjoint W₁ W₂` -- a vertex
`w ∈ W₁` is automatically `∉ W₂` by disjointness, so the extra
`∉ W₂` cut in the RHS is vacuous -- but not definitionally equal.

Built as `Equiv.sumCongr (Equiv.refl α) (Equiv.subtypeEquivRight ...)`;
the prop witness uses `hdisj` in the forward direction (to add
the redundant `∉ W₂` clause) and is automatic in the backward
direction (weakening `∉ G.J ∪ W₂` to `∉ G.J`). One-line analog of the
`bridge` toEquiv pattern in claim_3_7's `nodeSplittingOn_comm_equiv`
(`TwoDisjointNodeSplittingsCommute.lean` lines 661 -- 665).

## Design choice (workspace decision D1, chain-2 half)

* **Why this carrier equiv exists at all -- chain 2's predicates
  are set-equal but not def-equal.** Chain 2's two iterates have
  carriers that look superficially identical -- `α ⊕ ↑(W₁ \ ?)`
  on both sides -- but the `?` differs:
    * LHS iterate `(G.ext W₁ hW₁).hardInterventionOn (Sum.inl ''
      W₂)`: hard intervention is carrier-preserving
      (`HardInterventionOn.lean` lines 232 -- 264), so the carrier
      stays `α ⊕ ↑(W₁ \ G.J)` -- inherited from the inner `ext`'s
      subtyping by `W \ G.J`.
    * RHS iterate `(G.hardInterventionOn W₂).extendingCDMGWithInterventionNodes
      W₁ _`: the inner hard intervention promotes `W₂` into `J`
      (`hardInterventionOn_J = G.J ∪ W₂`), so the outer `ext`'s
      subtyping `W \ (inner).J` reads as `W₁ \ (G.J ∪ W₂)`.

  Under `Disjoint W₁ W₂` the two predicates `(· ∈ W₁ \ G.J)` and
  `(· ∈ W₁ \ (G.J ∪ W₂))` denote the *same set*: a `w ∈ W₁` is
  automatically `∉ W₂` by disjointness, so the extra `∉ W₂` cut
  is vacuous. But Lean's subtype constructor cares about the
  predicate, not the underlying set -- the two `↑`-subtypes are
  *not* definitionally equal even when their carriers are
  set-equal. This is the chain-2 analogue of chain-1's
  nested-vs-flat `Sum` mismatch: a transport via an `Equiv` is
  required, hence the `CDMGEquiv` regime (not literal `Eq`) on the
  chain-2 commute identity below.

* **`Equiv.subtypeEquivRight` over a hand-rolled `Subtype`
  bijection.** Mathlib's `Equiv.subtypeEquivRight` is the
  canonical API for "two subtypes whose predicates are
  pointwise iff": it ships `_apply` / `_symm_apply` simp lemmas
  that fire automatically in downstream `image`-equality goals,
  and its definition uses `fun ⟨x, h⟩ => ⟨x, hpred x h⟩` which
  preserves the underlying value -- so the `image` of the
  carrier equiv on the original-α layer is *literally* the
  identity. A hand-rolled `Subtype`-bijection would have to
  re-prove these facts every time. Same combinator as the
  `bridge` device in claim_3_7's `nodeSplittingOn_comm_equiv`
  proof (`TwoDisjointNodeSplittingsCommute.lean` line 663).

* **Built on `Equiv.refl α` for the `Sum.inl` side; only the
  `Sum.inr` side is transported.** `Equiv.sumCongr (Equiv.refl
  α) (Equiv.subtypeEquivRight ...)` leaves the original-α
  layer pointwise-identity. This matches the LN's chain-2
  proof exactly: the proof at `graphs.tex` lines 866 -- 873 does
  not relabel any original `v ∈ G.J ∪ G.V`; only the
  intervention-input subtype gets the relabel
  (`W₁ \ J` becomes `W₁ \ (J ∪ W₂)`). Identity on `α` keeps the
  four `image`-equality fields of the chain-2 `CDMGEquiv`
  reducing to `Set.image (Sum.inl) ...` rewrites on the
  original layer -- no spurious `Sum.inl` chasing.

* **Standalone `Equiv`, not folded into the `CDMGEquiv`'s
  `toEquiv` field.** Same reasoning as `extFusionEquiv`:
  the proof of the chain-2 `CDMGEquiv` (decl 7 below) needs to
  rewrite against this bijection's `_apply` form in all four
  field-equalities; naming it lets Manager B's proof discharge
  those via `simp [extHardCarrierEquiv]` rather than by
  unfolding an anonymous composition each time.

* **`hdisj` consumed in the forward direction only.** The
  forward implication `(w ∈ W₁ ∧ w ∉ G.J) → (w ∈ W₁ ∧ w ∉
  G.J ∪ W₂)` needs to rule out `w ∈ W₂`, which is exactly
  what `Set.disjoint_left.mp hdisj hwW₁` provides. The
  backward implication is automatic: `w ∉ G.J ∪ W₂` weakens to
  `w ∉ G.J` because the union dominates each summand. So
  `hdisj` is load-bearing only in one direction; we do not
  thread it elsewhere in the construction.

* **`noncomputable` -- inherited from the surrounding combinators.**
  `Equiv.sumCongr` and `Equiv.subtypeEquivRight` are themselves
  computable, but consistency with `extFusionEquiv` (which is
  `noncomputable` due to `Equiv.Set.union`) means we keep the
  `noncomputable` annotation uniform across both chain-1 and
  chain-2 carrier equivs in this file. No observable cost since
  downstream consumers are `Prop`-valued. -/
noncomputable def extHardCarrierEquiv (G : CDMG α) (W₁ W₂ : Set α)
    (hdisj : Disjoint W₁ W₂) :
    α ⊕ ↑(W₁ \ G.J) ≃ α ⊕ ↑(W₁ \ (G.J ∪ W₂)) :=
  Equiv.sumCongr (Equiv.refl α)
    (Equiv.subtypeEquivRight fun w => by
      refine ⟨?_, ?_⟩
      · rintro ⟨hwW₁, hwJ⟩
        refine ⟨hwW₁, fun h => ?_⟩
        rcases h with hJ | hW₂
        · exact hwJ hJ
        · exact Set.disjoint_left.mp hdisj hwW₁ hW₂
      · rintro ⟨hwW₁, hwJW₂⟩
        exact ⟨hwW₁, fun hJ => hwJW₂ (Or.inl hJ)⟩)

/-! ## Chain 2: commute `CDMGEquiv` -/

-- claim_3_14 (chain 2)
-- title: AddingInterventionNodes -- chain 2 commute
--
-- Hard intervention on `W₂` and extension by intervention nodes on `W₁`
-- commute when `Disjoint W₁ W₂`. The LN's "third term"
-- `G_{do(I_{W₁}, W₂)}` (RHS of chain 2) is *notation* for the
-- unambiguous value, not a separate Lean construction -- the commute
-- identity itself is the content (workspace D2).
/-
Verbatim LN block: same `\Lem` as chain 1 (`graphs.tex`
lines 832 -- 843); this declaration corresponds to the *first* `=`
of chain 2.
-/
/-- claim_3_14 chain 2: hard intervention on `W₂` and extension by
intervention nodes on `W₁` commute when `Disjoint W₁ W₂`. Mirrors the
first `=` of chain 2 in the LN's `\Lem` at
`lecture-notes/lecture_notes/graphs.tex` line 839:
`(G_{do(I_{W₁})})_{do(W₂)} = (G_{do(W₂)})_{do(I_{W₁})}`.

Body = `sorry`; the LN proof at `graphs.tex` lines 864 -- 873
computes both sides componentwise. The only carrier-level step is the
subtype-relabel `W₁ \ G.J ↔ W₁ \ (G.J ∪ W₂)` (under `Disjoint W₁ W₂`),
which is exactly what `extHardCarrierEquiv` provides as `toEquiv`.

The LN's RHS-of-chain `G_{do(I_{W₁}, W₂)}` is notation for the
unambiguous value of either side, not a separate Lean term (workspace
decision D3). Same `Sum.inl ''`-lift pattern on the chain-2 LHS's
hard-intervention target set as in `hardInterventionOn_swig_comm`
(`HardInterventionSwigCommute.lean` lines 277 -- 282).

## Design choice (workspace decisions D1, D3)

* **`CDMGEquiv` rather than literal `Eq` -- forced by typing, not
  stylistic (D1).** The two iterates look superficially same-carrier
  but actually live over the def-distinct subtypes
  `α ⊕ ↑(W₁ \ G.J)` (LHS) and `α ⊕ ↑(W₁ \ (G.J ∪ W₂))` (RHS) --
  see the `extHardCarrierEquiv` design block above for the full
  derivation. Under `Disjoint W₁ W₂` the two predicates denote the
  *same set*, but they are not def-equal as predicates, so literal
  `Eq` is not type-correct. `CDMGEquiv` with `toEquiv =
  extHardCarrierEquiv G W₁ W₂ hdisj` (or its `.symm`, depending on
  the direction Manager B picks) is the categorified version that
  bridges the subtype mismatch. Once the carrier-level transport
  is discharged the four `image`-equality fields reduce to literal
  componentwise simp work (the LN's
  `(\spl)`-style J / V / E / L checks at `graphs.tex` lines
  866 -- 873).

* **Carrier-level work is *only one step*, hence "much shorter
  proof than chain 1's fusion lemma".** Both sides of chain 2's
  identity apply the carrier-changing operator
  `extendingCDMGWithInterventionNodes` *only once* (on `W₁`); the
  partner operation `hardInterventionOn` is carrier-preserving
  (`HardInterventionOn.lean` lines 232 -- 264). So unlike chain 1,
  which iterates *two* carrier-changing extensions and needs the
  `extFusionEquiv` (`Equiv.Set.union` + `sumAssoc` +
  `Equiv.Set.image`) reassociation, chain 2 only needs the
  `subtypeEquivRight`-mediated `extHardCarrierEquiv`. Plan §3
  Risk R3 in `workspace_claim_3_14.md` records the expected
  proof-length contrast (~30 -- 50 lines for chain 2 vs ~80 -- 120
  for chain 1).

* **No joint third term -- `G_{do(I_{W₁}, W₂)}` is *notation*,
  not a separate Lean construction (D3).** The LN's chain 2
  closes with `(G_{do(I_{W₁})})_{do(W₂)} = (G_{do(W₂)})_{do(I_{W₁})}
  = G_{do(I_{W₁}, W₂)}`, but as the commented-out lines at
  `graphs.tex` 840 -- 842 make explicit, `G_{do(I_{W₁}, W₂)}` is
  the LN's *notation for the unambiguous value of either side*,
  not a third standalone operator like the chain-1 joint
  extension `G.ext (W₁ ∪ W₂) _`. Inventing a `do(I_·, ·)`
  joint operator just for chain 2 would mean:
    * minting a fresh CDMG definition that takes *two* subset
      arguments and is computationally identical to the
      composite, with its own four `@[simp]` characterisations;
    * threading the new operator through downstream rows
      (chapter 4 CBN-intervention semantics, etc.) that
      currently chain `hardInterventionOn` and
      `extendingCDMGWithInterventionNodes` directly;
    * absorbing the carrier-relabel into the new operator's
      definition, which then has to ship its own `CDMGEquiv` to
      the LHS *and* RHS of chain 2 -- doubling the API for no
      payoff.

  Rejected. The chain-2 `CDMGEquiv`'s conclusion has only *two*
  iterates (LHS and RHS), and any consumer who wants to invoke
  "the joint $do(I_{W₁}, W₂)$ value" picks one of the two
  iterates by `.symm` if needed. This asymmetry with chain 1
  (which *does* materialise its joint third term as a real
  Lean operator) is intentional and mirrors the LN exactly.

* **`Sum.inl '' W₂` lift on the LHS's outer hard-intervention
  target -- same justification as `hardInterventionOn_swig_comm`.**
  The outer `hardInterventionOn` on the LHS acts on
  `G.ext W₁ hW₁`, whose carrier is `α ⊕ ↑(W₁ \ G.J)`. Its target
  set must therefore be a `Set (α ⊕ ↑(W₁ \ G.J))`, not a `Set
  α`. The LN-faithful lift is `Sum.inl '' W₂` -- the canonical
  embedding of the original `W₂ : Set α` into the extension's
  carrier, under the convention `Sum.inl = original-α-side`
  established by `extendingCDMGWithInterventionNodes`. Same lift
  / same justification as `hardInterventionOn_swig_comm`
  (`HardInterventionSwigCommute.lean` lines 169 -- 206); without
  it, the outer hard intervention is not type-correct. The LN's
  "the same `W₂`" *is* the `Sum.inl`-image, inherited from the
  same LN-implicit `α ≅ Sum.inl '' α` identification that
  pervades def_3_11 / def_3_12 / def_3_13.

* **RHS uses the chain-2 helper
  `subset_hardInterventionOn_J_union_V_of_disjoint` to discharge
  the outer `ext`'s precondition (D4).** The named helper is
  load-bearing here: the outer `extendingCDMGWithInterventionNodes`
  takes `W₁ ⊆ (G.hardInterventionOn W₂).J ∪ _.V` as its
  precondition slot, and that containment is *exactly* the
  helper's conclusion. Discharging it inline would force every
  consumer (and Manager B's proof) to re-derive the
  `Disjoint`-driven case-split at the type-check level. Same
  factoring as the chain-1 outer-`ext` precondition.

* **Argument order `hW₁` then `hdisj`; `hW₂` not exposed.** The
  LHS of chain 2 only needs `hW₁ : W₁ ⊆ G.J ∪ G.V` (for the
  inner `extendingCDMGWithInterventionNodes`); the RHS uses the
  same `hW₁` plus `hdisj` (threaded through the helper). The LN
  also requires `W₂ ⊆ J ∪ V` in its prose, but
  `hardInterventionOn` is well-defined for *any*
  `W₂ : Set α` (`HardInterventionOn.lean` lines 217 -- 231 records
  the dropped LN precondition with its full justification --
  vertices in `W₂ \ (G.J ∪ G.V)` are inert under
  `hardInterventionOn`). So we drop `hW₂` from the signature,
  matching the same drop in
  `HardInterventionSwigCommute.lean`'s
  `hardInterventionOn_swig_comm` (line 277 -- 282). The
  consequence: this row's chain-2 lemma is strictly more general
  than the LN statement, in a way that is invisible to LN-faithful
  consumers and frees down-stream callers from carrying a
  vacuous `W₂ ⊆ J ∪ V` proof.

* **Implicit `G`, `W₁`, `W₂` -- explicit `hW₁`, `hdisj`.** Same
  convention as the chain-1 lemmas and as the sibling commute
  lemmas across Section 3.2; the two sets pin themselves down via
  the conclusion. -/
noncomputable def extendingCDMGWithInterventionNodes_hardInterventionOn_comm_equiv
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hdisj : Disjoint W₁ W₂) :
    CDMGEquiv
      ((G.extendingCDMGWithInterventionNodes W₁ hW₁).hardInterventionOn
          (Sum.inl '' W₂))
      ((G.hardInterventionOn W₂).extendingCDMGWithInterventionNodes W₁
          (subset_hardInterventionOn_J_union_V_of_disjoint hW₁ hdisj)) := by
  -- TeX: tex/claim_3_14_proof_AddingInterventionNodes.tex, chain 2.
  -- The carrier-level transport is `extHardCarrierEquiv G W₁ W₂ hdisj`;
  -- it absorbs the subtype mismatch `↑(W₁ \ G.J) ↔ ↑(W₁ \ (G.J ∪ W₂))`
  -- (set-equal under `Disjoint W₁ W₂`; vacuous `∉ W₂` cut). Each of the
  -- four `image`-equality fields chases the TeX proof's componentwise
  -- check (a)–(d) at `graphs.tex` 866 -- 873.
  --
  -- The two `toEq_*` lemmas are local `rfl`s: `extHardCarrierEquiv` is
  -- `Equiv.sumCongr (Equiv.refl α) (Equiv.subtypeEquivRight _)`, so each
  -- constructor case is preserved verbatim (modulo the subtype's prop
  -- witness, which is irrelevant up to def-eq under proof irrelevance).
  have toEq_inl : ∀ (a : α),
      extHardCarrierEquiv G W₁ W₂ hdisj (Sum.inl a) = Sum.inl a := fun _ => rfl
  have toEq_inr : ∀ (w : α) (hw : w ∈ W₁ \ G.J) (hw' : w ∈ W₁ \ (G.J ∪ W₂)),
      extHardCarrierEquiv G W₁ W₂ hdisj (Sum.inr ⟨w, hw⟩) =
        Sum.inr ⟨w, hw'⟩ := fun _ _ _ => rfl
  -- TeX preamble's "no fresh edges into W₂" bullet, Lean form. The
  -- forward implication uses `Disjoint W₁ W₂`; the backward implication
  -- is automatic since `G.J ∪ W₂` dominates `G.J`.
  have diff_iff : ∀ w : α, w ∈ W₁ \ G.J ↔ w ∈ W₁ \ (G.J ∪ W₂) := fun w =>
    ⟨fun ⟨hwW₁, hwJ⟩ =>
        ⟨hwW₁, fun h => h.elim hwJ (fun hW₂ =>
          Set.disjoint_left.mp hdisj hwW₁ hW₂)⟩,
     fun ⟨hwW₁, hwJW₂⟩ =>
        ⟨hwW₁, fun hJ => hwJW₂ (Or.inl hJ)⟩⟩
  refine
    { toEquiv := extHardCarrierEquiv G W₁ W₂ hdisj
      J_eq := ?_
      V_eq := ?_
      E_eq := ?_
      L_eq := ?_ }
  · -- (a) Input nodes (J), chain 2. TeX: graphs.tex 866 -- 867.
    -- H_arg.J = Sum.inl '' (G.J ∪ W₂) ∪ Set.range Sum.inr (def-eq).
    -- G_arg.J = (Sum.inl '' G.J ∪ Set.range Sum.inr) ∪ Sum.inl '' W₂ (def-eq).
    -- Prove componentwise by `ext` + case-split on `y`. We rely on the
    -- `rfl`-truth of `toEq_inl` / `toEq_inr` (Lean's def-eq + proof
    -- irrelevance on the subtype's prop witness): `rfl`-equation witnesses
    -- carry through the existential pairs in `Set.mem_image` / `_range`.
    ext y
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨⟨w, hw'⟩, rfl⟩)
      · refine ⟨Sum.inl a, ?_, rfl⟩
        rcases ha with hJ | hW₂
        · exact Or.inl (Or.inl ⟨a, hJ, rfl⟩)
        · exact Or.inr ⟨a, hW₂, rfl⟩
      · have hw : w ∈ W₁ \ G.J := (diff_iff w).mpr hw'
        exact ⟨Sum.inr ⟨w, hw⟩, Or.inl (Or.inr ⟨⟨w, hw⟩, rfl⟩), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rcases hx with (⟨a, hJ, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩) | ⟨a, hW₂, rfl⟩
      · exact Or.inl ⟨a, Or.inl hJ, rfl⟩
      · have hw' : w ∈ W₁ \ (G.J ∪ W₂) := (diff_iff w).mp hw
        exact Or.inr ⟨⟨w, hw'⟩, rfl⟩
      · exact Or.inl ⟨a, Or.inr hW₂, rfl⟩
  · -- (b) Output nodes (V), chain 2. TeX: graphs.tex 868.
    -- H_arg.V = Sum.inl '' (G.V \ W₂) (def-eq).
    -- G_arg.V = Sum.inl '' G.V \ Sum.inl '' W₂ (def-eq).
    -- Prove componentwise; the carrier-level `toEq` is identity on `inl`.
    ext y
    constructor
    · rintro ⟨v, ⟨hvV, hvW⟩, rfl⟩
      refine ⟨Sum.inl v, ⟨⟨v, hvV, rfl⟩, ?_⟩, rfl⟩
      rintro ⟨z, hzW, hzeq⟩
      exact hvW (Sum.inl_injective hzeq ▸ hzW)
    · rintro ⟨x, ⟨⟨v, hvV, rfl⟩, hxno⟩, rfl⟩
      refine ⟨v, ⟨hvV, ?_⟩, rfl⟩
      intro hvW
      exact hxno ⟨v, hvW, rfl⟩
  · -- (c) Directed edges (E), chain 2. TeX: graphs.tex 869 -- 872. Load-bearing.
    -- Forward original: (v₁, v₂) ∈ G.E ∧ v₂ ∉ W₂ → LHS witness
    --   (Sum.inl v₁, Sum.inl v₂); outer HI keeps it (Sum.inl v₂ ∉ Sum.inl '' W₂).
    -- Forward fresh: w ∈ W₁ \ (G.J ∪ W₂) → LHS witness fresh edge at the
    --   pre-relabel subtype; outer HI keeps it (Disjoint W₁ W₂).
    ext p
    simp only [mem_extendingCDMGWithInterventionNodes_E,
      mem_hardInterventionOn_E, Set.mem_image]
    constructor
    · rintro (⟨v₁, v₂, ⟨hE, hv₂W₂⟩, rfl⟩ | ⟨⟨w, hw'⟩, rfl⟩)
      · refine ⟨(Sum.inl v₁, Sum.inl v₂),
          ⟨Or.inl ⟨v₁, v₂, hE, rfl⟩, ?_⟩, ?_⟩
        · rintro ⟨z, hzW₂, hzeq⟩
          exact hv₂W₂ (Sum.inl_injective hzeq ▸ hzW₂)
        · exact Prod.ext (toEq_inl v₁) (toEq_inl v₂)
      · have hw : w ∈ W₁ \ G.J := (diff_iff w).mpr hw'
        refine ⟨(Sum.inr ⟨w, hw⟩, Sum.inl w),
          ⟨Or.inr ⟨⟨w, hw⟩, rfl⟩, ?_⟩, ?_⟩
        · rintro ⟨z, hzW₂, hzeq⟩
          have hwW₂ : w ∈ W₂ := Sum.inl_injective hzeq ▸ hzW₂
          exact Set.disjoint_left.mp hdisj hw.1 hwW₂
        · exact Prod.ext (toEq_inr w hw hw') (toEq_inl w)
    · rintro ⟨⟨a, b⟩, ⟨hab, hbW₂⟩, hp⟩
      rcases hab with ⟨v₁, v₂, hE, h_eq⟩ | ⟨⟨w, hw⟩, h_eq⟩
      · injection h_eq with h_eq1 h_eq2
        subst h_eq1; subst h_eq2
        have hp' : p = (Sum.inl v₁, Sum.inl v₂) := by
          rw [← hp]; exact Prod.ext (toEq_inl v₁) (toEq_inl v₂)
        rw [hp']
        refine Or.inl ⟨v₁, v₂, ⟨hE, ?_⟩, rfl⟩
        intro hv₂W₂
        exact hbW₂ ⟨v₂, hv₂W₂, rfl⟩
      · injection h_eq with h_eq1 h_eq2
        subst h_eq1; subst h_eq2
        have hw' : w ∈ W₁ \ (G.J ∪ W₂) := (diff_iff w).mp hw
        have hp' : p = (Sum.inr ⟨w, hw'⟩, Sum.inl w) := by
          rw [← hp]; exact Prod.ext (toEq_inr w hw hw') (toEq_inl w)
        rw [hp']
        exact Or.inr ⟨⟨w, hw'⟩, rfl⟩
  · -- (d) Bidirected edges (L), chain 2. TeX: graphs.tex 873.
    -- Both endpoints become `Sum.inl vₖ`, so the exclusion conditions
    -- transport via `Sum.inl_injective` symmetrically.
    ext p
    simp only [mem_extendingCDMGWithInterventionNodes_L,
      mem_hardInterventionOn_L, Set.mem_image]
    constructor
    · rintro ⟨v₁, v₂, ⟨hL, hv₁W₂, hv₂W₂⟩, rfl⟩
      refine ⟨(Sum.inl v₁, Sum.inl v₂),
        ⟨⟨v₁, v₂, hL, rfl⟩, ?_, ?_⟩, ?_⟩
      · rintro ⟨z, hzW₂, hzeq⟩
        exact hv₁W₂ (Sum.inl_injective hzeq ▸ hzW₂)
      · rintro ⟨z, hzW₂, hzeq⟩
        exact hv₂W₂ (Sum.inl_injective hzeq ▸ hzW₂)
      · exact Prod.ext (toEq_inl v₁) (toEq_inl v₂)
    · rintro ⟨⟨a, b⟩, ⟨⟨v₁, v₂, hL, h_eq⟩, hno₁, hno₂⟩, hp⟩
      injection h_eq with h_eq1 h_eq2
      subst h_eq1; subst h_eq2
      have hp' : p = (Sum.inl v₁, Sum.inl v₂) := by
        rw [← hp]; exact Prod.ext (toEq_inl v₁) (toEq_inl v₂)
      rw [hp']
      refine ⟨v₁, v₂, ⟨hL, ?_, ?_⟩, rfl⟩
      · intro h₁W₂; exact hno₁ ⟨v₁, h₁W₂, rfl⟩
      · intro h₂W₂; exact hno₂ ⟨v₂, h₂W₂, rfl⟩

end CDMG

end Causality
