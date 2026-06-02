import Chapter3_GraphTheory.Section3_2.ExtendingCDMGsWithInterventionNodes
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard
import Chapter3_GraphTheory.Section3_2.TwoDisjointNodeSplittingsCommute

-- TeX statement: tex/claim_3_15_statement_AddingInterventionNodes.tex
-- TeX proof:    tex/claim_3_15_proof_AddingInterventionNodes.tex (Manager B)

/-!
# Adding intervention nodes commutes with disjoint node-splitting hard interventions (claim_3_15)

This file formalises the lecture notes' lemma "Adding intervention nodes
commutes with disjoint node-splitting hard interventions" --
`lecture-notes/lecture_notes/graphs.tex` Lem at lines 877 -- 886 with
`\Claude` proof at lines 887 -- 930. The LN states the single equality

  `(G_{swig(W₁)})_{do(I_{W₂})} = (G_{do(I_{W₂})})_{swig(W₁)}`

under the hypotheses `W₁ ⊆ V`, `W₂ ⊆ J ∪ V`, and `Disjoint W₁ W₂`.
Unlike `claim_3_14`, which bundles *two* chained equalities under one
`\Lem` (`do(I_·)` ∘ `do(I_·)` fusion + commute, and `do(I_·)` ∘
`do(·)` commute), claim_3_15 is a *single* commute identity between
two *different* operators: SWIG (`\swig`, def_3_12) and intervention-
node extension (`\doit(I_·)`, def_3_13). Both operators are
carrier-changing, so the conclusion ships `CDMGEquiv` (not literal
`Eq`); the carrier-rewriting bundle from claim_3_7
(`TwoDisjointNodeSplittingsCommute.lean`) is imported here.

The LN proof's load-bearing fact is the identity
`W₂ \ Ĵ = W₂ \ J` (graphs.tex line 916), where `Ĵ = J ∪ W₁^i` is the
inner SWIG's input set: because `W₁^i` lives in `Set.range Sum.inr`
and the `Sum.inl ''` lift of `W₂` lives in `Set.range Sum.inl`,
constructor-disjointness rules out any overlap, and the "with `Ĵ`"
vs "with `J`" diff sets coincide. This is exactly the
set-equation Manager B's proof has to verify at the carrier-subtype
level (see the design block on the headline lemma below).

This file delivers:

* `subset_extendingCDMGWithInterventionNodes_J_union_V_of_subset_swig`
  -- helper, fully proved: discharges the outer-`ext` precondition
  `Sum.inl '' W₂ ⊆ (G.swig W₁ _).J ∪ (G.swig W₁ _).V` on the LHS
  iterate.
* `subset_swig_V_of_subset_V_of_ext`
  -- helper, fully proved: discharges the outer-`swig` precondition
  `Sum.inl '' W₁ ⊆ (G.ext W₂ _).V` on the RHS iterate.
* `swig_extendingCDMGWithInterventionNodes_comm_equiv`
  -- the commute `CDMGEquiv`, fully proved: a 5-step carrier equiv
  (`swigExtCarrierEquiv`) composed with a local `setCongr` bridge,
  plus componentwise J/V/E/L extensionality mirroring the LN's
  four field-equality arguments.

## Foundation reuse

`CDMGEquiv` (with its `refl` / `symm` / `trans` groupoid laws) is
imported verbatim from `TwoDisjointNodeSplittingsCommute.lean`. This
row is the *fourth* in-Section-3.2 consumer (after claim_3_7,
claim_3_10, claim_3_14). Per the claim_3_14 design notes
(`AddingInterventionNodesCommute.lean` lines 57 -- 84), a *fourth*
consumer is still not a strong enough promotion trigger -- this row
adds a single `import` line, no API churn -- so `CDMGEquiv` stays in
its claim_3_7 home for now. If a chapter-4 CBN-side row demands the
same shape, that becomes the natural promotion trigger.
-/

namespace Causality

namespace CDMG

universe u

variable {α : Type u}

/-! ## Helpers: outer-operator preconditions -/

/-- LHS-iterate helper: if `W₂ ⊆ G.J ∪ G.V`, then `Sum.inl '' W₂` is
contained in the node-set union of `G.swig W₁ hW₁`. Discharges the
outer-`ext` precondition for
`((G.swig W₁ hW₁).extendingCDMGWithInterventionNodes (Sum.inl '' W₂) _)`
on the LHS of claim_3_15.

Proof: `(G.swig W₁ hW₁).J = Sum.inl '' G.J ∪ Set.range Sum.inr` and
`(G.swig W₁ hW₁).V = Sum.inl '' G.V` (by the `@[simp]` lemmas
`nodeSplittingHardInterventionOn_J/V` in `NodeSplittingHard.lean`,
which fire on `G.swig W hW` by `abbrev`-reducibility). A `w ∈ W₂`
with `w ∈ G.J` lifts under `Sum.inl` into the swig's `J` (the
`Sum.inl '' G.J` summand); a `w ∈ W₂` with `w ∈ G.V` lifts into
`(G.swig W₁ hW₁).V = Sum.inl '' G.V`. The `Set.range Sum.inr` piece
of the swig's `J` is never needed -- original `G.J ∪ G.V` elements
survive into the swig's `inl`-image layer.

## Design choice

* **Named helper, not inlined into the headline lemma's signature.**
  The headline statement below needs to type-check the outer-`ext`
  application `(G.swig W₁ hW₁).ext (Sum.inl '' W₂) ?_`, whose
  hypothesis slot has the literal shape `Sum.inl '' W₂ ⊆ (G.swig W₁
  hW₁).J ∪ _.V`. Discharging this inline as a `by simp; ...` block in
  the headline signature would (a) drown the `CDMGEquiv`-valued
  conclusion in a precondition tactic block and (b) force every
  consumer to re-prove the same subset fact under any goal-state
  perturbation. Factoring it as a named theorem mirrors
  `subset_extendingCDMGWithInterventionNodes_J_union_V_of_subset`
  in the sibling claim_3_14 (`AddingInterventionNodesCommute.lean`
  lines 167 -- 176), `subset_nodeSplittingOn_V_of_subset_V` in
  claim_3_7 (`TwoDisjointNodeSplittingsCommute.lean` lines
  242 -- 247), and `subset_swig_V_of_subset_V` in claim_3_10
  (`TwoDisjointSwigsCommute.lean` lines 104 -- 108).

* **No `Disjoint W₁ W₂` hypothesis -- contrast with the chain-2
  helper of claim_3_14.** The SWIG is *additive* on the input layer
  (`Set.range Sum.inr` is fresh-mint) and *image-preserving* on the
  vertex layer (the inner HI's deletion target `Set.range Sum.inr`
  is disjoint from `Sum.inl '' G.V` by constructor mismatch, so the
  output set collapses to `Sum.inl '' G.V` -- see
  `nodeSplittingHardInterventionOn_V` in `NodeSplittingHard.lean`
  lines 253 -- 267). So any `W₂ ⊆ G.J ∪ G.V` lifts under `Sum.inl`
  into the SWIG's `J ∪ V` regardless of how `W₁` and `W₂` overlap.
  Disjointness is only load-bearing for the carrier-level bridge
  inside the headline `CDMGEquiv` (the LN's `W₂ \ Ĵ = W₂ \ J`
  identity); the embedding layer here does not care. Same design
  call as the claim_3_14 chain-1 helper and the claim_3_10 helper.

* **`Sum.inl '' W₂` rather than a bare `W₂`-like target set.** The
  outer-`ext` lives over the carrier `α ⊕ ↑W₁`, so its second
  argument must be a `Set (α ⊕ ↑W₁)`, not a `Set α`. The natural
  and LN-faithful lift is `Sum.inl '' W₂` -- under the convention
  `Sum.inl = original-α-side = w^o` established in
  `NodeSplittingOn.lean` and inherited by `NodeSplittingHard.lean`,
  the LN's "the same `W₂`" *is* the `Sum.inl`-image of `W₂` in the
  SWIG carrier. Same lift / same justification as
  `hardInterventionOn_swig_comm`
  (`HardInterventionSwigCommute.lean` lines 169 -- 206) and the
  claim_3_14 chain-1 / chain-2 lifts. Without it, the outer `ext`
  is not type-correct.

* **The `Set.range Sum.inr` summand of the SWIG's `J` is unused in
  the proof.** Constructor-disjointness of `Sum.inl` and `Sum.inr`
  means a `Sum.inl w` (image of `w ∈ W₂ ∩ G.J`) can never match the
  fresh-input layer; the case-split lands purely in the
  `Sum.inl '' G.J` summand. This is the same "no collision with
  fresh intervention nodes" structural fact as in the claim_3_14
  chain-1 helper, but materialising at a different operator: there
  it is `extendingCDMGWithInterventionNodes`'s `Set.range Sum.inr`,
  here it is the SWIG's `Set.range Sum.inr`. -/
theorem subset_extendingCDMGWithInterventionNodes_J_union_V_of_subset_swig
    {G : CDMG α} {W₁ W₂ : Set α} (hW₁ : W₁ ⊆ G.V)
    (hW₂ : W₂ ⊆ G.J ∪ G.V) :
    Sum.inl '' W₂ ⊆
      (G.swig W₁ hW₁).J ∪ (G.swig W₁ hW₁).V := by
  rintro _ ⟨w, hw, rfl⟩
  rcases hW₂ hw with hJ | hV
  · refine Or.inl ?_
    rw [nodeSplittingHardInterventionOn_J]
    exact Or.inl ⟨w, hJ, rfl⟩
  · refine Or.inr ?_
    rw [nodeSplittingHardInterventionOn_V]
    exact ⟨w, hV, rfl⟩

/-- RHS-iterate helper: if `W₁ ⊆ G.V`, then `Sum.inl '' W₁` is
contained in the vertex set of
`G.extendingCDMGWithInterventionNodes W₂ hW₂`. Discharges the outer-
`swig` precondition for
`((G.extendingCDMGWithInterventionNodes W₂ hW₂).swig (Sum.inl '' W₁) _)`
on the RHS of claim_3_15.

Proof: `(G.extendingCDMGWithInterventionNodes W₂ hW₂).V = Sum.inl ''
G.V` by the `@[simp]` lemma `extendingCDMGWithInterventionNodes_V`
(`ExtendingCDMGsWithInterventionNodes.lean` lines 334 -- 336), so a
`W₁ ⊆ G.V` hypothesis lifts under `Set.image_mono`.

## Design choice

* **Named helper, not inlined.** Same reasoning as the LHS-iterate
  helper above: factoring out the precondition discharge keeps the
  headline `CDMGEquiv`'s signature readable and consolidates the
  `Sum.inl`-image bookkeeping in one place. Mirrors
  `subset_swig_V_of_subset_V` in claim_3_10
  (`TwoDisjointSwigsCommute.lean` lines 104 -- 108), which has the
  same `Sum.inl '' W₂ ⊆ V_post-swig` shape but with the inner
  operator being SWIG itself (not extension).

* **One-line proof via `extendingCDMGWithInterventionNodes_V` +
  `Set.image_mono`.** The extension's `V` is *just* `Sum.inl ''
  G.V` (the extension only adds inputs, never vertices --
  `ExtendingCDMGsWithInterventionNodes.lean` lines 325 -- 336), so
  there is no extra summand to manage. Contrast with the LHS-iterate
  helper above, where the SWIG's `J` carries a `Set.range Sum.inr`
  summand that has to be sidestepped by case-splitting on
  `w ∈ G.J ∪ G.V`.

* **No `Disjoint W₁ W₂` hypothesis.** Extension is *additive* on the
  input layer (fresh `Sum.inr ⟨w, _⟩` for each `w ∈ W₂ \ G.J`) and
  *identity* on the vertex layer (`V_ext = Sum.inl '' G.V`); the
  outer-`swig` only consumes the latter. So this helper is
  insensitive to how `W₁` and `W₂` overlap. Disjointness is
  load-bearing inside the headline `CDMGEquiv`'s carrier transport,
  not at this precondition layer. Same design call as the
  claim_3_10 `subset_swig_V_of_subset_V` helper. -/
theorem subset_swig_V_of_subset_V_of_ext
    {G : CDMG α} {W₁ W₂ : Set α} (hW₁ : W₁ ⊆ G.V)
    (hW₂ : W₂ ⊆ G.J ∪ G.V) :
    Sum.inl '' W₁ ⊆ (G.extendingCDMGWithInterventionNodes W₂ hW₂).V := by
  rw [extendingCDMGWithInterventionNodes_V]
  exact Set.image_mono hW₁

/-! ## Carrier-level transport equiv -/

/-- Post-bridge carrier equiv for `claim_3_15`: the LN's `Sum.inl '' (W₂ \ G.J)`
form of the outer ext's fresh-index set on the LHS-iterate maps canonically to
the RHS-iterate's carrier. Composes the 5 Mathlib combinators sketched in the
design block on the headline lemma (steps 2 -- 6 of the 6-step transport; step 1
-- the `setCongr` bridge over `W_2 \ Ĵ = W_2 \ J` -- is consumed locally inside
the headline proof, where the bridge's domain naturally appears).

`Equiv.Set.image.symm` strips the inner `Sum.inl`-image wrapper to expose the
bare `W₂ \ G.J` subtype; `Equiv.sumAssoc` + `Equiv.sumComm` swap the roles of
`↑W₁` and `↑(W₂ \ G.J)` inside the nested sum; `Equiv.Set.image` re-wraps the
remaining `↑W₁` factor under the RHS-iterate's outer `Sum.inl`-image. -/
private noncomputable def swigExtCarrierEquiv
    (G : CDMG α) (W₁ W₂ : Set α) :
    (α ⊕ ↑W₁) ⊕ ↑((Sum.inl : α → α ⊕ ↑W₁) '' (W₂ \ G.J))
      ≃ (α ⊕ ↑(W₂ \ G.J)) ⊕
          ↑((Sum.inl : α → α ⊕ ↑(W₂ \ G.J)) '' W₁) :=
  (Equiv.sumCongr (Equiv.refl (α ⊕ ↑W₁))
        (Equiv.Set.image (Sum.inl : α → α ⊕ ↑W₁) (W₂ \ G.J)
          Sum.inl_injective).symm).trans <|
    (Equiv.sumAssoc α ↑W₁ ↑(W₂ \ G.J)).trans <|
      (Equiv.sumCongr (Equiv.refl α) (Equiv.sumComm ↑W₁ ↑(W₂ \ G.J))).trans <|
        (Equiv.sumAssoc α ↑(W₂ \ G.J) ↑W₁).symm.trans <|
          Equiv.sumCongr (Equiv.refl (α ⊕ ↑(W₂ \ G.J)))
            (Equiv.Set.image (Sum.inl : α → α ⊕ ↑(W₂ \ G.J)) W₁
              Sum.inl_injective)

/-! ## The commute `CDMGEquiv` -/

-- claim_3_15
-- title: AddingInterventionNodes
--
-- Node-splitting on `W₁ ⊆ G.V` and intervention-node extension on
-- `W₂ ⊆ G.J ∪ G.V` commute when `Disjoint W₁ W₂`. Both operators
-- are carrier-changing, so the LN's `=` lifts to a `CDMGEquiv`, with
-- the carrier-level bridge absorbing the LN's `W₂ \ Ĵ = W₂ \ J`
-- identity (graphs.tex line 916).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 877 -- 886)
-- the prose paragraph and displayed equation are reflowed for the
-- 100-character line limit (linewrap only; LaTeX whitespace
-- collapses between tokens, so this is verbatim under \LaTeX
-- semantics):

\begin{claimmark}
\begin{Lem}[Adding intervention nodes commutes with disjoint node-splitting hard
            interventions]
  Let $G=(J,V,E,L)$ be a CADMG and $W_1 \ins V$ and $W_2 \ins J \cup V$ two
    disjoint subsets of nodes from $G$.
    Then the CADMG that arises from first introducing intervention nodes
    $I_{W_2}$ and then splitting the nodes from $W_1$ is the same as the CADMG
    that arises from first splitting the nodes from $W_1$ and then introducing
    the intervention nodes $I_{W_2}$:
    \[  \lp G_{\swig(W_1)} \rp_{\doit(I_{W_2})} = \lp G_{\doit(I_{W_2})} \rp_{\swig(W_1)}. \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_15 (`AddingInterventionNodes`): for a CDMG `G : CDMG α`
and disjoint subsets `W₁ ⊆ G.V`, `W₂ ⊆ G.J ∪ G.V`, the SWIG on `W₁`
and the intervention-node extension on `W₂` commute. Mirrors the
displayed equation in the `\Lem` at
`lecture-notes/lecture_notes/graphs.tex` line 881.

The body composes a 5-step carrier equiv (`swigExtCarrierEquiv`) with
a local `setCongr` bridge, then closes J/V/E/L componentwise --
mirroring the LN's four field-equality arguments at `graphs.tex`
lines 887 -- 930. The carrier transport rests on the LN's identity
`W₂ \ Ĵ = W₂ \ J` (line 916) -- because the inner SWIG's "extra"
input layer `W₁^i = Set.range Sum.inr` is constructor-disjoint from
`Sum.inl '' W₂`, the diff-from-`Ĵ` and diff-from-`J` versions of the
fresh-extension index set coincide.

## Design choice (workspace decisions; see `workspace_claim_3_15.md`)

* **`CDMGEquiv` rather than literal `Eq` -- forced by typing, not
  stylistic.** Both operators are carrier-changing, and the two
  iterates in the conclusion live over *different* carrier types:
    * LHS iterate
      `(G.swig W₁ hW₁).extendingCDMGWithInterventionNodes
          (Sum.inl '' W₂) _` :
      `CDMG ((α ⊕ ↑W₁) ⊕ ↑((Sum.inl '' W₂) \ (G.swig W₁ hW₁).J))`
      -- swig contributes `α ⊕ ↑W₁`; the outer extension subtypes
      its `Sum.inr` summand by `(Sum.inl '' W₂) \ (G.swig W₁ hW₁).J`
      directly. After unfolding `(G.swig W₁ hW₁).J = Sum.inl '' G.J
      ∪ Set.range Sum.inr`, this subtype is *not* def-equal to a
      flat `Sum.inl '' (W₂ \ G.J)`. The LN's `W_2 \sm \hat{J} = W_2
      \sm J` identity (graphs.tex line 916) holds *as a set
      equation* in the post-swig carrier under
      constructor-disjointness, but not as a *predicate* on
      `α ⊕ ↑W₁`.
    * RHS iterate
      `(G.extendingCDMGWithInterventionNodes W₂ hW₂).swig
          (Sum.inl '' W₁) _` :
      `CDMG ((α ⊕ ↑(W₂ \ G.J)) ⊕ ↑(Sum.inl '' W₁))` -- extension
      contributes `α ⊕ ↑(W₂ \ G.J)`; the outer swig subtypes its
      `Sum.inr` summand by `Sum.inl '' W₁` (no further `\ ·` cut
      because `swig` has no `J`-style index subtraction in its
      carrier signature -- `nodeSplittingOn`'s carrier is `α ⊕ ↑W`,
      *not* `α ⊕ ↑(W \ ·)`).

  These two carrier types are not def-equal -- they are not even
  symmetric-looking (the LHS outer subtype carries a `\ J`-style
  diff, the RHS outer does not; the inner subtypes are `↑W₁`
  vs `↑(W₂ \ G.J)`, etc.) -- so literal `Eq` is *not type-correct*,
  even with `Disjoint W₁ W₂` in scope. `CDMGEquiv` is the
  categorified version that captures "carrier-equal up to a
  canonical bijection plus four field-equalities".

  Contrast with claim_3_11 (`HardInterventionSwigCommute.lean`
  lines 99 -- 127), which iterates `do(·)` and `swig` -- the *hard
  intervention* leg is carrier-preserving, so both iterates land
  over the same `α ⊕ ↑W₂` and claim_3_11 ships *literal `Eq`*.
  Distinguish carefully: claim_3_11 has one carrier-changing leg
  (`swig`) applied to the *same set* on both sides; claim_3_15 has
  *two* carrier-changing legs applied to *different sets* on each
  side, so the carriers themselves disagree.

  Contrast also with claim_3_14 chain 2
  (`AddingInterventionNodesCommute.lean` lines 1234 -- 1241),
  which has one carrier-preserving leg (`hardInterventionOn`, on
  `W₂`) and one carrier-changing leg (`extendingCDMGWithInterventionNodes`,
  on `W₁`). That row still ships `CDMGEquiv` because the
  carrier-changing leg sees *different inner graphs* on the two
  sides (one sees `G.ext W₁`, the other sees `G.HI W₂`), and the
  outer subtype indexing differs (`W₁ \ G.J` vs `W₁ \ (G.J ∪ W₂)`).
  Here the same carrier-mismatch logic applies but with both legs
  carrier-changing, so the two iterates' carriers disagree on *every*
  factor of the nested `Sum`. This row is therefore strictly the
  most carrier-asymmetric commute identity in Section 3.2.

* **`Sum.inl ''` lifts on the inner-set arguments of both sides --
  forced by carrier-typing on each iterate's outer operator.** Each
  side's outer operator acts on the carrier of its inner CDMG:
    * LHS: the outer `extendingCDMGWithInterventionNodes` acts on
      `G.swig W₁ hW₁`, whose carrier is `α ⊕ ↑W₁`. Its second
      argument must therefore be a `Set (α ⊕ ↑W₁)`, not `Set α`.
      The LN-faithful lift is `Sum.inl '' W₂`.
    * RHS: the outer `swig` acts on `G.extendingCDMGWithInterventionNodes
      W₂ hW₂`, whose carrier is `α ⊕ ↑(W₂ \ G.J)`. Its second
      argument must therefore be a `Set (α ⊕ ↑(W₂ \ G.J))`, not
      `Set α`. The LN-faithful lift is `Sum.inl '' W₁`.

  In both cases the convention is the same: `Sum.inl = original-α-
  side` (from `NodeSplittingOn.lean` and `ExtendingCDMGsWithInterventionNodes.lean`),
  so the LN's "the same `W₂`" / "the same `W₁`" *is* the `Sum.inl`-
  image. Same lift / same justification as `hardInterventionOn_swig_comm`
  (`HardInterventionSwigCommute.lean` lines 169 -- 206), the
  claim_3_14 chain-1 / chain-2 lifts, and the claim_3_10 inner
  lift. Inherits the LN's implicit `α ≅ Sum.inl '' α`
  identification.

* **Why `(Sum.inl '' W₂) \ (G.swig W₁ hW₁).J = Sum.inl '' (W₂ \
  G.J)` -- the carrier-level transcription of the LN's
  `W_2 \sm \hat{J} = W_2 \sm J`.** The outer LHS iterate's `Sum.inr`
  subtype is indexed by `(Sum.inl '' W₂) \ (G.swig W₁ hW₁).J`.
  Unfolding `(G.swig W₁ hW₁).J = Sum.inl '' G.J ∪ Set.range
  Sum.inr` (the `@[simp]` lemma `nodeSplittingHardInterventionOn_J`),
  the diff splits componentwise:
    * `Sum.inl x ∈ Sum.inl '' G.J` iff `x ∈ G.J` (by `Sum.inl`
      injectivity);
    * `Sum.inl x ∈ Set.range Sum.inr` is *false* by constructor
      mismatch -- `Sum.inl ≠ Sum.inr`.

  The second bullet is the load-bearing structural fact: it
  collapses the LN's "extra" diff against `W₁^i ⊂ \hat J` to
  vacuous, leaving only the diff against `G.J`. So
  `(Sum.inl '' W₂) \ (G.swig W₁ hW₁).J = Sum.inl '' (W₂ \ G.J)` as
  a set equation (over `α ⊕ ↑W₁`). Manager B's proof exposes this
  via an `h_bridge`-style local lemma -- the same shape as the
  bridge used in `extendingCDMGWithInterventionNodes_fusion_equiv`
  (`AddingInterventionNodesCommute.lean` lines 548 -- 564), but
  with the inner operator being SWIG instead of `ext`.

  This is the Lean transcription of the LN's `W_2 \sm \hat J = W_2
  \sm J` identity at graphs.tex line 916: in the LN, `\hat J = J
  \cup W_1^i` is the SWIG's input set, and the proof argues that
  for `w ∈ W_2`, "`w ∈ W_1^i`" is impossible because `W_1^i` is a
  set of fresh labels disjoint from any original vertex. In Lean,
  that "impossible" is `Sum.inl ≠ Sum.inr`. Same fact, two
  phrasings.

* **No "fusion + commute" split -- claim_3_15 is one declaration,
  not two.** Unlike claim_3_10 / claim_3_14 chain 1, which iterate
  the *same* carrier-changing operator on two different sets and
  expose both a fusion lemma (collapsing the iterate into a single
  operator-call on `W₁ ∪ W₂`) and a commute corollary (swapping
  `W₁ ↔ W₂` in the iterate), claim_3_15 iterates *two different*
  carrier-changing operators (SWIG and `ext`) on *two different*
  sets (`W₁` and `W₂`). There is no "joint third term" -- no single
  operator on `α` that the iterated SWIG-then-`ext` or `ext`-then-
  SWIG would both reduce to -- so the LN states only the commute
  identity and we expose only `_comm_equiv`. The closest LN sibling
  is claim_3_14 chain 2, which has the same one-statement structure
  for the same reason (one of its legs is *also* carrier-preserving,
  but the LN explicitly comments out a hypothetical "joint third
  term"; here both legs are carrier-changing so the joint-third-
  term option does not even arise).

* **Argument order `hW₁ hW₂ _hdisj` -- mirrors the claim_3_14 chain 2
  signature and the LN prose.** The LN states the precondition as
  "`W_1 \ins V`, `W_2 \ins J \cup V`, disjoint" in that order;
  claim_3_14 chain 2 has
  `(hW₁ : W₁ ⊆ G.J ∪ G.V) (hdisj : Disjoint W₁ W₂)`
  (`AddingInterventionNodesCommute.lean` lines 1235 -- 1236), but
  drops `hW₂` because `hardInterventionOn` does not need it. Here
  *both* hypotheses are structurally required (the SWIG demands
  `W₁ ⊆ G.V`, the extension demands `W₂ ⊆ G.J ∪ G.V`), so both
  appear. The disjointness comes last, matching the LN's writing
  order and the chain-2 sibling. Implicit `G`, `W₁`, `W₂`; explicit
  `hW₁`, `hW₂`, `_hdisj`.

* **Hypothesis `W₁ ⊆ G.V` is *stricter* than chain-2's `W₁ ⊆ G.J ∪
  G.V` -- the LN says so.** SWIG (`def_3_12`) is restricted to
  `W ⊆ V` in the LN (and in `NodeSplittingHard.lean` lines
  205 -- 207: `swig` takes `hW : W ⊆ G.V`), whereas `ext`
  (`def_3_13`) accepts `W ⊆ J ∪ V`. The hypothesis split `W₁ ⊆ V`
  for the swig-leg and `W₂ ⊆ J ∪ V` for the ext-leg is the LN's
  own asymmetry, not a Lean-only restriction. Keeping the
  hypotheses LN-tight (rather than weakening `hW₁` to `W₁ ⊆ G.J ∪
  G.V` and adding a sidecondition) lets `subset_swig_V_of_subset_V_of_ext`
  close by a one-line `Set.image_mono` and matches the LN
  hypothesis shape verbatim.

* **Inner-`swig` precondition via the new helper
  `subset_swig_V_of_subset_V_of_ext hW₁ hW₂` (RHS).** The outer
  `swig` on the RHS demands `Sum.inl '' W₁ ⊆ (G.ext W₂ hW₂).V`,
  which is exactly the helper's conclusion. Discharging it inline
  would force every consumer (and Manager B's proof) to re-derive
  the `Set.image_mono hW₁` step at the type-check level. Same
  factoring as the claim_3_14 chain-2 outer-`ext` precondition
  helper.

* **Outer-`ext` precondition via the new helper
  `subset_extendingCDMGWithInterventionNodes_J_union_V_of_subset_swig
  hW₁ hW₂` (LHS).** Symmetrically, the outer `ext` on the LHS
  demands `Sum.inl '' W₂ ⊆ (G.swig W₁ hW₁).J ∪ (G.swig W₁ hW₁).V`,
  again the helper's conclusion. Helper-named for the same
  readability + reuse reasons as the chain-1 helper of claim_3_14.

* **`noncomputable def` (not `theorem`) -- inherited from the
  `CDMGEquiv` regime.** Every commute declaration that lands in
  `CDMGEquiv` is a `noncomputable def` because (i) `CDMGEquiv`
  carries data (`toEquiv : α ≃ β`), not just a `Prop`, and (ii)
  the underlying carrier equivalences (`Equiv.Set.union`,
  `Equiv.Set.image`, `Equiv.setCongr`) inherit `noncomputable`
  via `Classical.decPred`. Same regime as `swig_swig_equiv`
  (`TwoDisjointSwigsCommute.lean` line 211),
  `extendingCDMGWithInterventionNodes_fusion_equiv` (claim_3_14
  chain 1; `AddingInterventionNodesCommute.lean` line 524), and
  `extendingCDMGWithInterventionNodes_hardInterventionOn_comm_equiv`
  (claim_3_14 chain 2; line 1234).

* **Naming `swig_extendingCDMGWithInterventionNodes_comm_equiv`.**
  Follows the Section 3.2 commute-lemma convention:
    * `_comm` suffix for literal-`Eq` rows (`hardInterventionOn_comm`,
      `hardInterventionOn_nodeSplittingOn_comm`,
      `hardInterventionOn_swig_comm`);
    * `_comm_equiv` suffix for `CDMGEquiv` rows
      (`nodeSplittingOn_comm_equiv`, `swig_comm_equiv`,
      `extendingCDMGWithInterventionNodes_comm_equiv` chain-1,
      `extendingCDMGWithInterventionNodes_hardInterventionOn_comm_equiv`
      chain-2);
  and lists operators left-to-right matching the LHS of the
  conclusion (`swig` first, `ext` second). The mirror name
  `extendingCDMGWithInterventionNodes_swig_comm_equiv` (operators
  reversed) is technically equivalent via `.symm` but not exposed.

* **Optional carrier-equiv `def` left to Manager B.** The natural
  carrier transport (workspace sketch) composes ~6 Mathlib
  combinators:
    `(α ⊕ ↑W₁) ⊕ ↑((Sum.inl '' W₂) \ (G.swig W₁ hW₁).J)`
       ≃ `(α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' (W₂ \ G.J))`   [`setCongr` bridge]
       ≃ `(α ⊕ ↑W₁) ⊕ ↑(W₂ \ G.J)`                [`Equiv.Set.image.symm`]
       ≃ `α ⊕ (↑W₁ ⊕ ↑(W₂ \ G.J))`                [`sumAssoc`]
       ≃ `α ⊕ (↑(W₂ \ G.J) ⊕ ↑W₁)`                [inner `sumComm`]
       ≃ `(α ⊕ ↑(W₂ \ G.J)) ⊕ ↑W₁`                [`sumAssoc.symm`]
       ≃ `(α ⊕ ↑(W₂ \ G.J)) ⊕ ↑(Sum.inl '' W₁)`   [`Equiv.Set.image`].
  Whether to materialise this as a separately named
  `swigExtCarrierEquiv` `def` (à la `extFusionEquiv` in
  `AddingInterventionNodesCommute.lean`) or inline it inside the
  headline body is left as a proof-phase choice; either is fine
  for the LN-faithfulness contract. The cost of inlining is one
  larger proof block; the cost of naming is one extra `def` and
  its 4-projection `_apply` simp lemmas. The headline statement
  itself does not depend on the choice.

## Constraints / known limitations

* **`Sum.inl`-image lifts persist in the public API.** Every
  downstream consumer of either iterate must work with the explicit
  `Sum.inl '' W₁` / `Sum.inl '' W₂` outer-operator arguments, not
  the bare `W₁` / `W₂`. The LN paragraph implicitly identifies `α`
  with its `Sum.inl`-image after the inner operator runs ("the same
  $W_2$" in graphs.tex line 880 is post-swig under our convention,
  not the original `W_2 ⊆ α`); Lean cannot make that identification
  silently, so the lift appears in every consumer's signature.
  Manager B's proof body inherits the same lift on each of the four
  field-equalities.

* **`CDMGEquiv` is structure-valued, not propositional.** The LN
  conclusion is a literal `=`; Lean's stronger typing forces it
  into a data-carrying bundle (`toEquiv : α ≃ β` plus the four
  field-equality fields). Downstream rows can `.trans` / `.symm` /
  `.refl` this with other `CDMGEquiv`s (groupoid laws from
  claim_3_7) but cannot directly `rw` with it as if it were `Eq`.
  A rewrite-style consumer must invoke `toEquiv` plus the four
  field-equalities explicitly. The LN never has to compose this
  with another such "equality", so the gap is invisible there but
  load-bearing in Lean.

* **No exposed mirror (`extendingCDMGWithInterventionNodes_swig_comm_equiv`).**
  The reverse-direction declaration is reachable as
  `(swig_extendingCDMGWithInterventionNodes_comm_equiv hW₁ hW₂
  _hdisj).symm` but is not named separately. Consumers wanting the
  opposite orientation must write `.symm` at call site -- the same
  convention as `nodeSplittingOn_comm_equiv`,
  `swig_comm_equiv`, and the chain-2 sibling in
  `AddingInterventionNodesCommute.lean`.

* **Carrier transport is non-unique.** Several Mathlib-combinator
  chains land on the same `(α ⊕ ↑(W₂ \ G.J)) ⊕ ↑(Sum.inl '' W₁)`
  carrier (e.g. re-ordering the `sumAssoc` / `sumComm` steps), and
  the resulting `Equiv`s are propositionally equal but not
  definitionally equal. The `_apply` simp lemmas of any one chain
  do not auto-fire on another. If a downstream row composes this
  commute with another `CDMGEquiv`, the specific carrier-equiv
  choice has to be surfaced at the composition site. The
  workspace-sketched chain mirrors `extFusionEquiv`'s shape for
  cross-commute composability.

* **Disjointness enters only via `Sum.inl` / `Sum.inr` constructor
  mismatch, not via subtype-relabel.** Contrast with claim_3_14
  chain 2's `extHardCarrierEquiv`, which uses
  `Equiv.subtypeEquivRight` to consume `Disjoint W₁ W₂` *as a
  subtype-membership condition* (because `hardInterventionOn`
  deletes `W₂` from the carrier). Here `Disjoint W₁ W₂` is used
  *only* to argue the impossible `Sum.inl w ∈ Set.range Sum.inr`
  case during the `setCongr` bridge -- both `W₁` and `W₂` survive
  on the `Sum.inl` side, just sitting in different `Sum`
  factors. The bookkeeping is mechanically lighter; the LN
  paragraph blurs the two by quoting the same `W_1 ∩ W_2 = ∅`
  twice. -/
noncomputable def swig_extendingCDMGWithInterventionNodes_comm_equiv
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V) (_hdisj : Disjoint W₁ W₂) :
    CDMGEquiv
      ((G.swig W₁ hW₁).extendingCDMGWithInterventionNodes
          (Sum.inl '' W₂)
          (subset_extendingCDMGWithInterventionNodes_J_union_V_of_subset_swig hW₁ hW₂))
      ((G.extendingCDMGWithInterventionNodes W₂ hW₂).swig
          (Sum.inl '' W₁)
          (subset_swig_V_of_subset_V_of_ext hW₁ hW₂)) := by
  -- TeX: tex/claim_3_15_proof_AddingInterventionNodes.tex (Manager B).
  -- Carrier-level transport: 6-step Mathlib combinator chain (the
  -- `setCongr` bridge absorbing the LN's `W_2 \sm \hat J = W_2 \sm J`
  -- identity, then `swigExtCarrierEquiv`'s 5 steps). Field equalities
  -- follow the TeX componentwise check (a)–(d) at graphs.tex 866–873.
  --
  -- Step 1: the bridge set-equation (the LN's `W_2 \sm \hat J = W_2 \sm J`,
  -- graphs.tex line 916). Constructor disjointness `Sum.inl ≠ Sum.inr`
  -- collapses the extra `\ W₁^i` cut to vacuous.
  have h_bridge : (Sum.inl '' W₂ : Set (α ⊕ ↑W₁)) \ (G.swig W₁ hW₁).J
      = Sum.inl '' (W₂ \ G.J) := by
    rw [nodeSplittingHardInterventionOn_J]
    ext x
    simp only [Set.mem_diff, Set.mem_image, Set.mem_union, Set.mem_range]
    constructor
    · rintro ⟨⟨w, hwW₂, rfl⟩, hno⟩
      refine ⟨w, ⟨hwW₂, ?_⟩, rfl⟩
      intro hwJ
      exact hno (Or.inl ⟨w, hwJ, rfl⟩)
    · rintro ⟨w, ⟨hwW₂, hwJ⟩, rfl⟩
      refine ⟨⟨w, hwW₂, rfl⟩, ?_⟩
      rintro (⟨z, hzJ, hzeq⟩ | ⟨z, hzeq⟩)
      · exact hwJ (Sum.inl_injective hzeq ▸ hzJ)
      · exact nomatch hzeq
  -- Step 2: the bridge equiv (proof-relabel on the outer subtype).
  let bridge :
      ((α ⊕ ↑W₁) ⊕
        ↑((Sum.inl '' W₂ : Set (α ⊕ ↑W₁)) \ (G.swig W₁ hW₁).J))
        ≃ ((α ⊕ ↑W₁) ⊕
            ↑((Sum.inl : α → α ⊕ ↑W₁) '' (W₂ \ G.J))) :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.setCongr h_bridge)
  -- Step 3: total carrier equiv.
  let toEq := bridge.trans (swigExtCarrierEquiv G W₁ W₂)
  -- Forward applications of `swigExtCarrierEquiv` on each constructor case.
  have apply_inl_inl_chain : ∀ (a : α),
      swigExtCarrierEquiv G W₁ W₂ (Sum.inl (Sum.inl a)) =
        Sum.inl (Sum.inl a) := fun a => by simp [swigExtCarrierEquiv]
  have apply_inl_inr_chain : ∀ (w : α) (hw : w ∈ W₁),
      swigExtCarrierEquiv G W₁ W₂ (Sum.inl (Sum.inr ⟨w, hw⟩)) =
        Sum.inr ⟨Sum.inl w, ⟨w, hw, rfl⟩⟩ := fun w hw => by
    simp [swigExtCarrierEquiv]
  -- The `Sum.inr` case: input `Sum.inr ⟨Sum.inl wo, hxB⟩` where the
  -- subtype witness comes from `Sum.inl wo ∈ Sum.inl '' (W₂ \ G.J)`.
  -- Result is `Sum.inl (Sum.inr ⟨wo, hwo⟩)` (LN's "the fresh I_wo").
  have apply_inr_chain : ∀ (wo : α) (hwo : wo ∈ W₂ \ G.J)
      (hxB : (Sum.inl wo : α ⊕ ↑W₁) ∈
        (Sum.inl : α → α ⊕ ↑W₁) '' (W₂ \ G.J)),
      swigExtCarrierEquiv G W₁ W₂ (Sum.inr ⟨Sum.inl wo, hxB⟩) =
        Sum.inl (Sum.inr ⟨wo, hwo⟩) := fun wo hwo hxB => by
    simp [swigExtCarrierEquiv, Equiv.Set.image_symm_apply]
  -- Three `toEq` apply lemmas (the `Sum.inl _` cases pass through
  -- `bridge` as a no-op on the left summand; the `Sum.inr _` case
  -- consumes the `setCongr` bridge via proof irrelevance).
  have toEq_inl_inl : ∀ (a : α),
      toEq (Sum.inl (Sum.inl a)) = Sum.inl (Sum.inl a) := fun a => by
    change swigExtCarrierEquiv G W₁ W₂ (Sum.inl (Sum.inl a)) = _
    exact apply_inl_inl_chain a
  have toEq_inl_inr : ∀ (w : α) (hw : w ∈ W₁),
      toEq (Sum.inl (Sum.inr ⟨w, hw⟩)) =
        Sum.inr ⟨Sum.inl w, ⟨w, hw, rfl⟩⟩ := fun w hw => by
    change swigExtCarrierEquiv G W₁ W₂ (Sum.inl (Sum.inr ⟨w, hw⟩)) = _
    exact apply_inl_inr_chain w hw
  have toEq_inr : ∀ (wo : α) (hwoW₂ : wo ∈ W₂) (hwoJ : wo ∉ G.J)
      (hxR : (Sum.inl wo : α ⊕ ↑W₁) ∈
        (Sum.inl '' W₂ : Set (α ⊕ ↑W₁)) \ (G.swig W₁ hW₁).J),
      toEq (Sum.inr ⟨Sum.inl wo, hxR⟩) =
        Sum.inl (Sum.inr ⟨wo, ⟨hwoW₂, hwoJ⟩⟩) :=
    fun wo hwoW₂ hwoJ hxR => by
      have hwo : wo ∈ W₂ \ G.J := ⟨hwoW₂, hwoJ⟩
      have hxB : (Sum.inl wo : α ⊕ ↑W₁) ∈
          (Sum.inl : α → α ⊕ ↑W₁) '' (W₂ \ G.J) := ⟨wo, hwo, rfl⟩
      change swigExtCarrierEquiv G W₁ W₂ (Sum.inr ⟨Sum.inl wo, hxB⟩) = _
      exact apply_inr_chain wo hwo hxB
  -- Key `split1`-source transport lemma for the E-field. The LHS-iterate's
  -- inner SWIG relabels sources via `split1 W₁`, the RHS-iterate's outer
  -- SWIG relabels via `split1 (Sum.inl '' W₁)`; the two split-points are
  -- `Sum.inl`-image conjugates, so `toEq` carries one to the other.
  have key_e_source : ∀ (v : α),
      toEq (Sum.inl (split1 W₁ v)) = split1 (Sum.inl '' W₁) (Sum.inl v) := by
    intro v
    by_cases hv : v ∈ W₁
    · have hvSI : (Sum.inl v : α ⊕ ↑(W₂ \ G.J)) ∈ Sum.inl '' W₁ :=
        ⟨v, hv, rfl⟩
      rw [split1_of_mem hv, split1_of_mem hvSI]
      exact toEq_inl_inr v hv
    · have hvSI : (Sum.inl v : α ⊕ ↑(W₂ \ G.J)) ∉ Sum.inl '' W₁ := by
        rintro ⟨z, hz, hzeq⟩
        exact hv (Sum.inl_injective hzeq ▸ hz)
      rw [split1_of_not_mem hv, split1_of_not_mem hvSI]
      exact toEq_inl_inl v
  refine
    { toEquiv := toEq
      J_eq := ?_
      V_eq := ?_
      E_eq := ?_
      L_eq := ?_ }
  · -- (a) Input nodes (J). TeX: graphs.tex 866 -- 867.
    -- RHS.J = `Sum.inl '' (G.ext W₂ hW₂).J ∪ Set.range (Sum.inr : ↑(Sum.inl '' W₁) → _)`.
    -- LHS.J = `Sum.inl '' (G.swig W₁ hW₁).J ∪ Set.range (Sum.inr : outer subtype → _)`.
    -- Three pieces on each side; case-split on which piece y lies in.
    rw [show ((G.extendingCDMGWithInterventionNodes W₂ hW₂).swig
        (Sum.inl '' W₁) _).J =
        Sum.inl '' (G.extendingCDMGWithInterventionNodes W₂ hW₂).J ∪
          Set.range (Sum.inr :
            ↑((Sum.inl : α → α ⊕ ↑(W₂ \ G.J)) '' W₁) → _)
        from nodeSplittingHardInterventionOn_J _ _ _]
    ext y
    constructor
    · rintro (⟨z, hz, rfl⟩ | ⟨⟨w, hwSI⟩, rfl⟩)
      · -- y = Sum.inl z, z ∈ (G.ext W₂ hW₂).J.
        rcases hz with ⟨j, hj, rfl⟩ | ⟨⟨wo, hwo⟩, rfl⟩
        · -- z = Sum.inl j, j ∈ G.J. Source x = Sum.inl (Sum.inl j).
          refine ⟨Sum.inl (Sum.inl j),
            Or.inl ⟨Sum.inl j, ?_, rfl⟩, toEq_inl_inl j⟩
          rw [nodeSplittingHardInterventionOn_J]
          exact Or.inl ⟨j, hj, rfl⟩
        · -- z = Sum.inr ⟨wo, hwo⟩, hwo : wo ∈ W₂ \ G.J.
          -- Source x = Sum.inr ⟨Sum.inl wo, hxR⟩.
          have hxR : (Sum.inl wo : α ⊕ ↑W₁) ∈
              (Sum.inl '' W₂ : Set (α ⊕ ↑W₁)) \ (G.swig W₁ hW₁).J := by
            refine ⟨⟨wo, hwo.1, rfl⟩, ?_⟩
            rw [nodeSplittingHardInterventionOn_J]
            rintro (⟨z, hzJ, hzeq⟩ | ⟨z, hzeq⟩)
            · exact hwo.2 (Sum.inl_injective hzeq ▸ hzJ)
            · exact nomatch hzeq
          refine ⟨Sum.inr ⟨Sum.inl wo, hxR⟩,
            Or.inr ⟨⟨Sum.inl wo, hxR⟩, rfl⟩, ?_⟩
          exact toEq_inr wo hwo.1 hwo.2 hxR
      · -- y = Sum.inr ⟨w, hwSI⟩, hwSI : w ∈ Sum.inl '' W₁.
        obtain ⟨w', hw'W₁, rfl⟩ := hwSI
        -- Source x = Sum.inl (Sum.inr ⟨w', hw'W₁⟩).
        refine ⟨Sum.inl (Sum.inr ⟨w', hw'W₁⟩),
          Or.inl ⟨Sum.inr ⟨w', hw'W₁⟩, ?_, rfl⟩, ?_⟩
        · rw [nodeSplittingHardInterventionOn_J]
          exact Or.inr ⟨⟨w', hw'W₁⟩, rfl⟩
        · exact toEq_inl_inr w' hw'W₁
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨z, hz, rfl⟩ | ⟨⟨y_in, hy_in⟩, rfl⟩
      · -- x = Sum.inl z, z ∈ (G.swig W₁ hW₁).J.
        rw [nodeSplittingHardInterventionOn_J] at hz
        rcases hz with ⟨j, hj, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩
        · -- z = Sum.inl j, j ∈ G.J.
          rw [toEq_inl_inl j]
          refine Or.inl ⟨Sum.inl j, ?_, rfl⟩
          exact Or.inl ⟨j, hj, rfl⟩
        · -- z = Sum.inr ⟨w, hw⟩, hw : w ∈ W₁.
          rw [toEq_inl_inr w hw]
          exact Or.inr ⟨⟨Sum.inl w, ⟨w, hw, rfl⟩⟩, rfl⟩
      · -- x = Sum.inr ⟨y_in, hy_in⟩. y_in must be Sum.inl wo for some wo ∈ W₂\G.J.
        obtain ⟨⟨wo, hwoW₂, rfl⟩, hno⟩ := hy_in
        have hwoJ : wo ∉ G.J := by
          intro hwoJ
          apply hno
          rw [nodeSplittingHardInterventionOn_J]
          exact Or.inl ⟨wo, hwoJ, rfl⟩
        have hxR : (Sum.inl wo : α ⊕ ↑W₁) ∈
            (Sum.inl '' W₂ : Set (α ⊕ ↑W₁)) \ (G.swig W₁ hW₁).J :=
          ⟨⟨wo, hwoW₂, rfl⟩, hno⟩
        rw [toEq_inr wo hwoW₂ hwoJ hxR]
        refine Or.inl ⟨Sum.inr ⟨wo, ⟨hwoW₂, hwoJ⟩⟩, ?_, rfl⟩
        exact Or.inr ⟨⟨wo, ⟨hwoW₂, hwoJ⟩⟩, rfl⟩
  · -- (b) Output nodes (V). TeX: graphs.tex 868.
    -- Both LHS.V and RHS.V reduce to `Sum.inl '' (Sum.inl '' G.V)`; toEq
    -- is identity on `Sum.inl (Sum.inl _)`. The swig's V needs the
    -- `nodeSplittingHardInterventionOn_V` simp lemma to flatten to
    -- `Sum.inl '' G.V` -- inner-image witnesses are constructed via that.
    rw [show ((G.extendingCDMGWithInterventionNodes W₂ hW₂).swig
        (Sum.inl '' W₁) _).V =
        Sum.inl '' (G.extendingCDMGWithInterventionNodes W₂ hW₂).V
        from nodeSplittingHardInterventionOn_V _ _ _]
    ext y
    constructor
    · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨Sum.inl (Sum.inl v), ?_, toEq_inl_inl v⟩
      refine ⟨Sum.inl v, ?_, rfl⟩
      rw [nodeSplittingHardInterventionOn_V]
      exact ⟨v, hv, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hx
      rw [nodeSplittingHardInterventionOn_V] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      rw [toEq_inl_inl v]
      exact ⟨Sum.inl v, ⟨v, hv, rfl⟩, rfl⟩
  · -- (c) Directed edges (E). TeX: graphs.tex 869 -- 872.
    -- LHS.E has two pieces: original edges (via inner-swig + outer-ext relabel)
    -- and outer-ext fresh edges. RHS.E has two pieces: original edges and
    -- outer-swig edges (which subsume both inner-ext-fresh and inner-original).
    ext p
    rw [Set.mem_image, mem_nodeSplittingHardInterventionOn_E]
    constructor
    · -- y ∈ RHS.E → ∃ q ∈ LHS.E, (Prod.map toEq toEq) q = y.
      rintro ⟨u₁, u₂, hu, rfl⟩
      rw [mem_extendingCDMGWithInterventionNodes_E] at hu
      rcases hu with ⟨v₁, v₂, hE, h_eq⟩ | ⟨⟨wo, hwo⟩, h_eq⟩
      · -- original-edge case: (u₁, u₂) = (Sum.inl v₁, Sum.inl v₂), (v₁,v₂) ∈ G.E.
        injection h_eq with h_eq1 h_eq2
        subst h_eq1; subst h_eq2
        refine ⟨(Sum.inl (split1 W₁ v₁), Sum.inl (Sum.inl v₂)), ?_, ?_⟩
        · rw [mem_extendingCDMGWithInterventionNodes_E]
          refine Or.inl ⟨split1 W₁ v₁, Sum.inl v₂, ?_, rfl⟩
          rw [mem_nodeSplittingHardInterventionOn_E]
          exact ⟨v₁, v₂, hE, rfl⟩
        · refine Prod.ext ?_ (toEq_inl_inl v₂)
          exact key_e_source v₁
      · -- fresh-edge case: (u₁, u₂) = (Sum.inr ⟨wo, hwo⟩, Sum.inl wo), hwo : wo ∈ W₂\G.J.
        injection h_eq with h_eq1 h_eq2
        subst h_eq1; subst h_eq2
        -- Source q = (Sum.inr ⟨Sum.inl wo, hxR⟩, Sum.inl (Sum.inl wo)).
        have hxR : (Sum.inl wo : α ⊕ ↑W₁) ∈
            (Sum.inl '' W₂ : Set (α ⊕ ↑W₁)) \ (G.swig W₁ hW₁).J := by
          refine ⟨⟨wo, hwo.1, rfl⟩, ?_⟩
          rw [nodeSplittingHardInterventionOn_J]
          rintro (⟨z, hzJ, hzeq⟩ | ⟨z, hzeq⟩)
          · exact hwo.2 (Sum.inl_injective hzeq ▸ hzJ)
          · exact nomatch hzeq
        refine ⟨(Sum.inr ⟨Sum.inl wo, hxR⟩, Sum.inl (Sum.inl wo)), ?_, ?_⟩
        · rw [mem_extendingCDMGWithInterventionNodes_E]
          exact Or.inr ⟨⟨Sum.inl wo, hxR⟩, rfl⟩
        · -- Goal: Prod.map toEq toEq (Sum.inr ⟨Sum.inl wo, hxR⟩, Sum.inl (Sum.inl wo))
          --     = (split1 (Sum.inl '' W₁) (Sum.inr ⟨wo, hwo⟩), Sum.inl (Sum.inl wo)).
          -- Reduce RHS first via constructor disjointness, then close by Prod.ext.
          have hnotin : (Sum.inr ⟨wo, hwo⟩ : α ⊕ ↑(W₂ \ G.J)) ∉
              (Sum.inl : α → α ⊕ ↑(W₂ \ G.J)) '' W₁ := by
            rintro ⟨z, _, hzeq⟩
            exact nomatch hzeq
          rw [split1_of_not_mem hnotin]
          exact Prod.ext (toEq_inr wo hwo.1 hwo.2 hxR) (toEq_inl_inl wo)
    · rintro ⟨q, hq, rfl⟩
      rw [mem_extendingCDMGWithInterventionNodes_E] at hq
      rcases hq with ⟨a₁, a₂, ha, rfl⟩ | ⟨⟨y_in, hy_in⟩, rfl⟩
      · -- LHS original-edge piece, q = (Sum.inl a₁, Sum.inl a₂).
        rw [mem_nodeSplittingHardInterventionOn_E] at ha
        rcases ha with ⟨v₁, v₂, hE, h_eq'⟩
        injection h_eq' with h_eq'1 h_eq'2
        subst h_eq'1; subst h_eq'2
        refine ⟨Sum.inl v₁, Sum.inl v₂, ?_, ?_⟩
        · rw [mem_extendingCDMGWithInterventionNodes_E]
          exact Or.inl ⟨v₁, v₂, hE, rfl⟩
        · refine Prod.ext ?_ (toEq_inl_inl v₂)
          exact key_e_source v₁
      · -- LHS fresh-edge piece, q = (Sum.inr ⟨y_in, hy_in⟩, Sum.inl y_in).
        obtain ⟨⟨wo, hwoW₂, rfl⟩, hno⟩ := hy_in
        have hwoJ : wo ∉ G.J := by
          intro hwoJ
          apply hno
          rw [nodeSplittingHardInterventionOn_J]
          exact Or.inl ⟨wo, hwoJ, rfl⟩
        have hwo : wo ∈ W₂ \ G.J := ⟨hwoW₂, hwoJ⟩
        refine ⟨Sum.inr ⟨wo, hwo⟩, Sum.inl wo, ?_, ?_⟩
        · rw [mem_extendingCDMGWithInterventionNodes_E]
          exact Or.inr ⟨⟨wo, hwo⟩, rfl⟩
        · -- Prod.map toEq toEq (Sum.inr ⟨Sum.inl wo, _⟩, Sum.inl (Sum.inl wo))
          -- = (split1 (Sum.inl '' W₁) (Sum.inr ⟨wo, hwo⟩), Sum.inl (Sum.inl wo)).
          have hnotin : (Sum.inr ⟨wo, hwo⟩ : α ⊕ ↑(W₂ \ G.J)) ∉
              (Sum.inl : α → α ⊕ ↑(W₂ \ G.J)) '' W₁ := by
            rintro ⟨z, _, hzeq⟩
            exact nomatch hzeq
          rw [split1_of_not_mem hnotin]
          refine Prod.ext ?_ (toEq_inl_inl wo)
          exact toEq_inr wo hwoW₂ hwoJ _
  · -- (d) Bidirected edges (L). TeX: graphs.tex 873.
    -- Both sides reduce to `(Prod.map (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inl)) '' G.L`.
    ext p
    rw [Set.mem_image, mem_nodeSplittingHardInterventionOn_L]
    constructor
    · rintro ⟨v₁, v₂, hL, rfl⟩
      -- v₁, v₂ : α ⊕ ↑(W₂ \ G.J); destructure hL to get the original α-endpoints.
      rw [mem_extendingCDMGWithInterventionNodes_L] at hL
      obtain ⟨v₁', v₂', hL', h_eq⟩ := hL
      injection h_eq with h_eq1 h_eq2
      subst h_eq1; subst h_eq2
      refine ⟨(Sum.inl (Sum.inl v₁'), Sum.inl (Sum.inl v₂')), ?_, ?_⟩
      · rw [mem_extendingCDMGWithInterventionNodes_L]
        refine ⟨Sum.inl v₁', Sum.inl v₂', ?_, rfl⟩
        rw [mem_nodeSplittingHardInterventionOn_L]
        exact ⟨v₁', v₂', hL', rfl⟩
      · exact Prod.ext (toEq_inl_inl v₁') (toEq_inl_inl v₂')
    · rintro ⟨q, hq, rfl⟩
      rw [mem_extendingCDMGWithInterventionNodes_L] at hq
      obtain ⟨a₁, a₂, hab, rfl⟩ := hq
      rw [mem_nodeSplittingHardInterventionOn_L] at hab
      obtain ⟨v₁, v₂, hL, h_eq⟩ := hab
      injection h_eq with h_eq1 h_eq2
      subst h_eq1; subst h_eq2
      refine ⟨Sum.inl v₁, Sum.inl v₂, ?_, ?_⟩
      · rw [mem_extendingCDMGWithInterventionNodes_L]
        exact ⟨v₁, v₂, hL, rfl⟩
      · exact Prod.ext (toEq_inl_inl v₁) (toEq_inl_inl v₂)

end CDMG

end Causality
