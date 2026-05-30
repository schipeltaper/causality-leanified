import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard

-- TeX statement: tex/claim_3_12_statement_HardInterventionNodeSplitOrder.tex
-- TeX proof: tex/claim_3_12_proof_HardInterventionNodeSplitOrder.tex (Manager B)

/-!
# Why disjointness is essential in claim_3_11 (claim_3_12)

This file formalises the *remark* (LN type `Rem`) immediately
following claim_3_11 (`hardInterventionOn_swig_comm` in
`HardInterventionSwigCommute.lean`). The remark explains **why
the disjointness hypothesis in claim_3_11 is essential**: when
`W₁ ∩ W₂ ⊆ V` is non-empty, the order/setup of `do(W₁)` and
`swig(W₂)` matters, and the LN walks through three distinct
outcomes to make the point.

LN source: `lecture-notes/lecture_notes/graphs.tex` lines
702 -- 709 (the Remark following the claim_3_11 proof at lines
672 -- 700).

## Why this is *four* observations, not one `Eq`

The LN block is a Remark -- a discussion of *non-commutativity*
-- not a clean equality. To formalise the Remark faithfully we
produce *four observations*, mapping one-to-one onto the LN's
three scenarios (A, B1, B2) plus the punchline corollary:

* **Scenario A**
  (`swig_precondition_fails_on_intersection`): first HI on `w`,
  then SWIG -- in our Lean framework the LHS of claim_3_11's
  identity is *ill-typed* because the SWIG precondition
  `W₂ ⊆ V` fails after `w` is removed from `V` by
  `hardInterventionOn`. (The LN's parenthetical "a
  node-splitting hard intervention (if we would define it for
  input nodes) would not change `w^i`" is informal exploration
  of a hypothetical extension; the formal content here is that
  the LHS *type-check* fails.)
* **Scenario B1**
  (`swig_hardInterventionOn_inputs_eq_self`): first SWIG, then
  HI on input copies (`Sum.inr` half) -- the SWIG is unchanged
  ("A hard intervention on `w^i` would not do anything").
* **Scenario B2** (`swig_hardInterventionOn_outputs_V`):
  first SWIG, then HI on output copies (`Sum.inl` half) --
  the SWIG's `V` shrinks ("hard intervening on `w^o` would
  turn `w^o` into an additional input node").
* **Punchline corollary**
  (`swig_then_hardInterventionOn_depends_on_copy_choice`):
  combining B1 and B2, for any `w ∈ G.V` the two natural copy
  choices (input vs output) yield non-equal graphs --
  exhibiting the order-dependence the Remark warns about.

Together these four formalise the Remark's argument that the
order/setup is essential when `W₁ ∩ W₂ ⊆ V` is non-empty. The
disjointness hypothesis in claim_3_11 is therefore
load-bearing, not a convenience.

## Relationship to claim_3_11

`HardInterventionSwigCommute.lean` proves the commute identity
`(G_{do(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{do(W₁)}` under the
disjointness premise; this row explains what goes wrong when
that premise fails. The two rows together capture the LN's
full treatment of "HI ∘ SWIG", with this row providing the
*non-commutativity warning* that the disjointness premise of
claim_3_11 is essential.

## Imports

* `HardInterventionOn.lean` -- `hardInterventionOn` and its
  four `@[simp]` projection lemmas (`hardInterventionOn_J/V`,
  `mem_hardInterventionOn_E/L`), used to characterise the
  result of the outer HI in every scenario.
* `NodeSplittingHard.lean` -- `swig` / the long-form
  `nodeSplittingHardInterventionOn`, plus the four `@[simp]`
  projections (`nodeSplittingHardInterventionOn_J/V`,
  `mem_nodeSplittingHardInterventionOn_E/L`), used to
  characterise the SWIG's components in scenarios B1, B2, and
  the punchline.

We do *not* import `HardInterventionSwigCommute.lean`
(claim_3_11) -- this row is *about* the precondition of that
claim, not built atop it; the four observations below stand
on their own and would not be made easier by claim_3_11's
existence.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

/-! ## Local CDMG-extensionality helper -/

/-- Local CDMG-extensionality helper: two CDMGs over the same carrier
are equal as soon as their four data fields `J / V / E / L` agree. The
six prop fields close by proof irrelevance after the data fields are
pinned down. Re-declared verbatim from
`HardInterventionSwigCommute.lean` lines 50 -- 59 (the claim_3_11
sibling) rather than imported: `CDMG` is intentionally not
`@[ext]`-tagged, so each row that needs componentwise extensionality
re-declares this `private` ten-line helper -- the duplication is
cheaper than wiring a build-graph dependency on the sibling. -/
private theorem mk_eq_of_data {G H : CDMG α}
    (hJ : G.J = H.J) (hV : G.V = H.V) (hE : G.E = H.E) (hL : G.L = H.L) :
    G = H := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := G
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := H
  subst hJ
  subst hV
  subst hE
  subst hL
  rfl

/-! ## Scenario A: HI on `W₁` removes `w` from `V`, breaking the SWIG precondition -/

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: swig_precondition_fails_on_intersection
-- claim_3_12 (Scenario A)
-- title: HardInterventionNodeSplitOrder
--
-- When `w ∈ W₁ ∩ W₂ ⊆ G.V`, hard-intervening on `W₁` first
-- removes `w` from `V`, so `W₂` no longer satisfies the SWIG
-- precondition `W₂ ⊆ V_{do(W₁)}`. In our Lean framework the
-- LHS of claim_3_11's identity becomes *ill-typed* (the inner
-- `swig W₂` call cannot be constructed at all). The LN's
-- speculative "a node-splitting hard intervention (if we
-- would define it for input nodes) would not change `w^i`" is
-- a hypothetical extension that our `swig` does not implement
-- -- the formal observation is just that the precondition
-- fails.
/-
LN source -- the *first* sentence of the Remark, verbatim from
`lecture-notes/lecture_notes/graphs.tex` lines 705 -- 706
(reflowed for the 100-character line limit; LaTeX whitespace
collapses between tokens, so this is verbatim under \LaTeX
semantics):

\begin{claimmark}
\begin{Rem}
    Note that if $W_1$ and $W_2$ are not disjoint and
    $w \in W_1 \cap W_2 \ins V$ then first hard intervening on
    $w$ turns $w$ into an input node, for now indicated as
    $w^i$, and a node-splitting hard intervention (if we would
    define it for input nodes) would not change $w^i$.
\end{Rem}
\end{claimmark}
-/
/-- claim_3_12 (Scenario A): when `w ∈ W₁ ∩ W₂` (and the LN
states this happens in `G.V`), the SWIG precondition
`W₂ ⊆ (G.hardInterventionOn W₁).V` fails. Hence the LHS of
claim_3_11's identity `(G_{do(W₁)})_{swig(W₂)}` cannot even
be formed in our Lean framework -- so the "HI then SWIG" order
is *strictly worse* than "SWIG then HI" when `W₁ ∩ W₂` meets
`G.V`.

## Design choice

* **Why a *precondition-failure* statement, not an `Eq` or
  `Ne` of CDMGs (and why this row is one of *four*
  observations).** The LN block is a Remark walking through
  *three operational scenarios* (A here; B1, B2 in the next
  two theorems) plus a punchline corollary -- not a single
  equation. A single `Eq` or `Ne` of CDMGs would force a
  choice of *which* scenario to formalise and silently drop
  the other two; decomposing into *four observations*, one
  per LN clause, is the only honest translation of a
  narrative `Rem`. The four together reconstruct the LN's
  argument that the disjointness premise of claim_3_11
  (`HardInterventionSwigCommute.lean`) is load-bearing.
  Scenario A is *this* theorem; its specific shape
  ("precondition fails") comes from the LN's clause "first
  hard intervening on `w` turns `w` into an input node ... a
  node-splitting hard intervention (if we would define it
  for input nodes) would not change `w^i`" (`graphs.tex`
  line 706). The parenthetical "if we would define it for
  input nodes" flags that the LN's own `swig` is *not*
  defined on input nodes, and our `swig`
  (`NodeSplittingHard.lean` lines 205 -- 207, with
  precondition `W ⊆ G.V`) inherits exactly this limitation.
  The formal content of Scenario A is therefore the *typing
  obstruction*, not a hypothetical "extended" SWIG that
  neither the LN nor we actually formalise.

* **Conclusion shape `¬ (W₂ ⊆ (G.hardInterventionOn W₁).V)`.**
  This is the literal SWIG precondition (`swig` is defined in
  `NodeSplittingHard.lean` lines 205 -- 207 to require
  `W ⊆ G.V`). Stating the *negation* of the precondition is
  the cleanest way to record "the LHS cannot be formed", since
  Lean does not let us write `¬ (∃ proof of ill-formed term)`
  directly -- the LHS literally fails to elaborate, and what
  we can prove is that the discharge required by `swig`
  on `(G.hardInterventionOn W₁)` is unavailable. A reader
  who tries to write `(G.hardInterventionOn W₁).swig W₂ ?_`
  with `?_ : W₂ ⊆ (G.hardInterventionOn W₁).V` will be unable
  to fill the hole when `W₁ ∩ W₂ ≠ ∅` meets `G.V` --
  precisely the obstruction this theorem records. The
  `@[simp]` projection `hardInterventionOn_V`
  (`HardInterventionOn.lean` lines 275 -- 276) unfolds the
  RHS to `G.V \ W₁`, so the proof reduces to the elementary
  set fact "`w ∈ W₂` and `w ∈ W₁` together force `w ∉ G.V \ W₁`".

* **LN's `W₁ ∩ W₂ ⊆ V` (a *set-level* statement, vacuously
  true when the intersection is empty) is operationally
  translated to the *point-level* `w ∈ W₁ ∩ W₂` with
  `w ∈ G.V`.** The two are equivalent in spirit when the
  intersection is non-empty, but the point-level form is the
  one our conclusion actually consumes -- the obstruction to
  `W₂ ⊆ (G.hardInterventionOn W₁).V` is witnessed by a
  *single* `w`, not by a property of the whole intersection
  set. Recording the obstruction per-witness keeps the
  hypothesis minimal (we never need to assume
  `W₁ ∩ W₂ ⊆ G.V` as a set-containment) and aligns with how
  consumers will discharge it (typically: from a concrete
  `w ∈ W₁ ∩ W₂` exhibited by the scenario at hand).

* **`hwV : w ∈ G.V` is included for LN-faithfulness but not
  strictly load-bearing.** The conclusion `W₂ ⊄
  (G.hardInterventionOn W₁).V` (where the RHS unfolds to
  `G.V \ W₁` via `hardInterventionOn_V`) follows from `w ∈ W₂`
  and `w ∈ W₁` alone: `w ∈ W₂ ⊆ G.V \ W₁` would force
  `w ∉ W₁`, contradicting `w ∈ W₁`. The LN's `w ∈ V`
  qualifier is what places the scenario in the regime where
  the original `swig(W₂)` would have been applicable (i.e.,
  `W₂ ⊆ G.V` to start with); we keep `hwV` in the signature
  to mirror the LN's "$w \in W_1 \cap W_2 \ins V$" exactly.
  Documenting this rather than dropping `hwV` keeps a
  downstream reader aware that the *operational* obstruction
  is `w ∈ W₁ ∩ W₂`, with the `w ∈ V` qualifier serving as
  context that this is the LN's scenario A and not a vacuous
  case (`W₁ ∩ W₂ ⊆ G.V` non-empty is *required* for
  claim_3_11's hypothesis `W₂ ⊆ G.V` to be meaningful while
  also having `W₁ ∩ W₂ ≠ ∅`).

* **`G : CDMG α` implicit; `w`, `W₁`, `W₂` implicit;
  `hw`, `hwV` explicit.** Mirrors the sibling claim_3_11's
  `hardInterventionOn_swig_comm` convention
  (`HardInterventionSwigCommute.lean` lines 277 -- 282), which
  has `G`, `W₁`, `W₂` implicit and the hypotheses explicit.
  Here `w` is also implicit because every call site will have
  a concrete `w` already in scope.

* **Naming: `swig_precondition_fails_on_intersection`.** The
  name emphasises *what* fails (the SWIG precondition) and
  *why* (the `W₁ ∩ W₂` intersection meets `V`). An alternative
  `not_subset_hardInterventionOn_V_of_inter` would mirror the
  helper `subset_hardInterventionOn_V_of_disjoint` from the
  sibling (`HardInterventionNodeSplittingCommute.lean` line
  175) by negation; we prefer the semantic name because this
  theorem is consumed by *humans* (a reader trying to
  understand why claim_3_11 needs disjointness), not by
  another proof. -/
theorem swig_precondition_fails_on_intersection
    {G : CDMG α} {w : α} {W₁ W₂ : Set α}
    (hw : w ∈ W₁ ∩ W₂) (hwV : w ∈ G.V) :
    ¬ (W₂ ⊆ (G.hardInterventionOn W₁).V) := by
  -- Mirrors TeX Scenario A (lines 54 -- 77): `w ∈ W₂` plus
  -- `W₂ ⊆ V \ W₁` forces `w ∈ V \ W₁`, whose second component
  -- contradicts `w ∈ W₁`. `hwV` is documented as LN-faithful but not
  -- strictly load-bearing -- it is not consumed below.
  intro hsub
  have hwHI : w ∈ (G.hardInterventionOn W₁).V := hsub hw.2
  rw [hardInterventionOn_V] at hwHI
  exact hwHI.2 hw.1
-- REFACTOR-BLOCK-ORIGINAL-END: swig_precondition_fails_on_intersection

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: swig_precondition_fails_on_intersection (was: refactor_swig_hardInterventionOn_inputs_J)
/-- claim_3_12 (Scenario A, LN-faithful replacement): when
`w ∈ W₁ ∩ W₂` (and the LN states this happens in `G.V`), the first
hard intervention `G.hardInterventionOn W₁` *promotes `w` into the
input set* -- i.e. `w ∈ (G.hardInterventionOn W₁).J`. Formalises the
LN's literal "first hard intervening on `w` turns `w` into an input
node, for now indicated as `w^i`" (`graphs.tex` line 706) as a
positive J-membership claim.

## What changed from the original

The original `swig_precondition_fails_on_intersection` stated only the
*consequence* `¬ (W₂ ⊆ (G.hardInterventionOn W₁).V)` -- a
typing/precondition-failure observation downstream of the LN's primary
content but not the same statement. The strict-equivalence gate flagged
that as a CONTENT deviation: the LN's primary content is the positive
J-membership of `w`, not the consequent SWIG-precondition failure.
This replacement records the LN-faithful J-membership directly; the
original's consequence still follows because `hardInterventionOn_V`
reduces `(G.hardInterventionOn W₁).V` to `G.V \ W₁`, which `w` cannot
inhabit since `w ∈ W₁` -- so a downstream caller who needs the
typing-obstruction form can still derive it in one line.

## Design choice

* **Positive J-membership, not a downstream consequence.** The LN
  literally writes "turns `w` into an input node `w^i`" -- i.e. `w`
  is now in `J`. The positive form is the LN-faithful translation.
  Stating only the precondition failure (the original's `¬ ⊆`) was
  the strict-gate's CONTENT-level complaint.
* **Same `{G, w, W₁, W₂}` implicit and `hw, hwV` explicit signature
  as the original**, so any future caller adapting between the two
  only has to swap the name. `hwV` remains documented (in the
  original's block above) as LN-faithful but not strictly load-bearing
  -- it is still not consumed in the proof.
* **Naming `swig_hardInterventionOn_inputs_J`.** Parallels Scenario
  B2's T3 replacement `swig_hardInterventionOn_outputs_J`: both are
  J-membership statements about HI of the Scenario-A input candidates
  (T1) or the Scenario-B2 output candidates (T3). The `swig_` prefix
  marks the file/scenario context even though the SWIG does not
  actually appear in T1's statement -- Scenario A is "HI without the
  later SWIG step", since the SWIG precondition fails. -/
theorem refactor_swig_hardInterventionOn_inputs_J
    {G : CDMG α} {w : α} {W₁ W₂ : Set α}
    (hw : w ∈ W₁ ∩ W₂) (hwV : w ∈ G.V) :
    w ∈ (G.hardInterventionOn W₁).J := by
  -- `hardInterventionOn_J` unfolds the LHS to `G.J ∪ W₁`; `hw.1` gives
  -- `w ∈ W₁`. `hwV` is documented as LN-faithful but not consumed.
  rw [hardInterventionOn_J]
  exact Or.inr hw.1
-- REFACTOR-BLOCK-REPLACEMENT-END: swig_precondition_fails_on_intersection

/-! ## Scenario B1: HI on input copies (`Sum.inr` half) is a no-op on the SWIG -/

-- claim_3_12 (Scenario B1)
--
-- After `G.swig W hW`, the `Sum.inr` half of the carrier is
-- exactly the fresh `W^i` set: `Set.range Sum.inr ⊆
-- (G.swig W hW).J`, no edge of the SWIG has an endpoint of
-- the form `Sum.inr _` (directed edges target `Sum.inl _`;
-- bidirected edges have both endpoints of the form
-- `Sum.inl _`), and `Sum.inr _ ∉ (G.swig W hW).V`. Hence
-- hard-intervening on any `Sum.inr '' I ⊆ Set.range Sum.inr`
-- adds nothing to `J` (the new copies are already in `J`),
-- removes nothing from `V` (the targets are not in `V`),
-- removes no directed edges (none have target in `W^i`), and
-- removes no bidirected edges (none have either endpoint in
-- `W^i`). The result is bit-for-bit `G.swig W hW`.
/-
LN source -- the *third* sentence of the Remark (the first
clause), verbatim from `graphs.tex` line 707 (reflowed for the
100-character line limit; LaTeX whitespace collapses between
tokens):

A hard intervention on $w^i$ would not do anything, but would
leave the additional output node $w^o$ in the graph
-/
/-- claim_3_12 (Scenario B1): for any subset `I` of the
input-copy indices, hard-intervening on `Sum.inr '' I` is a
*no-op* on `G.swig W hW`. Formalises the LN's "A hard
intervention on `w^i` would not do anything" -- the `Sum.inr`
half of the SWIG carrier is the `W^i` set, which is already
in `J` of the SWIG (so the HI's J-promotion adds nothing) and
not in `V`, with no edges incident to it (so the HI's edge
deletions are vacuous).

## Design choice

* **General `Sum.inr '' I` form, not the LN's singleton
  `{Sum.inr ⟨w, _⟩}`.** The LN narrates the singleton case
  (a single `w ∈ W₁ ∩ W₂`), but the underlying no-op property
  holds uniformly for *any* subset of the input-copy half:
  none of the SWIG's data fields are sensitive to which
  `Sum.inr` labels the HI is asked to "promote", because every
  such label is already in `J` (and not in `V`, and not an
  endpoint of any edge). Stating the theorem in the general
  form does three things:
    * it correctly identifies the *reason* the no-op holds
      (a global property of `Sum.inr`'s position in the SWIG
      carrier, not a special property of the single LN
      vertex `w`);
    * it gives a stronger downstream lemma at zero proof
      cost -- the singleton case is an immediate corollary
      `swig_hardInterventionOn_inputs_eq_self
        (I := {⟨w, hw⟩})` after observing
      `Sum.inr '' {⟨w, hw⟩} = {Sum.inr ⟨w, hw⟩}`;
    * it sidesteps the awkward subtype-construction
      `⟨w, hw⟩ : ↑W` that the singleton form would force at
      every call site.
  The LN-faithfulness "cost" is small: the LN's scenario is
  literally a single `w`, but the LN itself indicates the
  point is a no-op *property* (not a specific-`w` fact),
  via the phrasing "would not do anything" (no edges, no
  vertex change, no input change). Our general statement
  is the same property quantified universally.

* **`I : Set ↑W` typing rather than `T : Set (α ⊕ ↑W)` with
  `T ⊆ Set.range Sum.inr`.** Both encode the same no-op
  region, but `I : Set ↑W` is the *natural* parameterisation
  -- `Sum.inr : ↑W → α ⊕ ↑W` is the inclusion of the
  intervention-input labels, so subsets of `↑W` are the right
  domain. The `T ⊆ Set.range Sum.inr` encoding would require
  every call site to discharge the containment hypothesis;
  the `I`-parameterisation makes that containment
  *structural* (every `Sum.inr '' I` is in `Set.range Sum.inr`
  by definition of image).

* **Conclusion is a literal `Eq`, not a `CDMGEquiv` or a
  componentwise statement.** Both sides have carrier
  `α ⊕ ↑W` (HI is carrier-preserving), and the four data
  fields agree on the nose: J adds no new elements, V loses
  none, E loses no edges, L loses no edges. So the bare
  `Eq` typechecks. Manager B's proof will discharge it via
  the local `mk_eq_of_data` helper (the same pattern used in
  `HardInterventionSwigCommute.lean` lines 50 -- 59 and
  `HardInterventionNodeSplittingCommute.lean`), with each
  data-field check a one-line consequence of one of the four
  `@[simp]` SWIG projections plus one of the four `@[simp]`
  outer-HI projections, namely:
    * J-field -- `nodeSplittingHardInterventionOn_J` plus
      `hardInterventionOn_J`. The SWIG's `J` is
      `Sum.inl '' G.J ∪ Set.range Sum.inr`; the outer HI's
      `J` is that union together with `Sum.inr '' I`; and
      `Sum.inr '' I ⊆ Set.range Sum.inr` collapses the
      addition. (NSH projection at
      `NodeSplittingHard.lean` lines 237 -- 243; HI
      projection at `HardInterventionOn.lean`
      lines 269 -- 270.)
    * V-field -- `nodeSplittingHardInterventionOn_V` plus
      `hardInterventionOn_V`. The SWIG's `V` is
      `Sum.inl '' G.V`, which is disjoint from `Sum.inr ''
      I` by constructor mismatch, so the outer HI's `V`
      (`Sum.inl '' G.V \ Sum.inr '' I`) equals `Sum.inl ''
      G.V` itself. (NSH projection at
      `NodeSplittingHard.lean` lines 253 -- 267; HI
      projection at `HardInterventionOn.lean`
      lines 275 -- 276.)
    * E-field -- `mem_nodeSplittingHardInterventionOn_E`
      plus `mem_hardInterventionOn_E`. Every directed edge
      of the SWIG ends at `Sum.inl v₂`, which is never of
      the form `Sum.inr _`, so the outer HI's "target not in
      `Sum.inr '' I`" filter is vacuous. (NSH projection at
      `NodeSplittingHard.lean` lines 278 -- 294; HI
      projection at `HardInterventionOn.lean`
      lines 284 -- 286.)
    * L-field -- `mem_nodeSplittingHardInterventionOn_L`
      plus `mem_hardInterventionOn_L`. Every bidirected
      edge of the SWIG has both endpoints of the form
      `Sum.inl _`, so neither endpoint lies in
      `Sum.inr '' I`. (NSH projection at
      `NodeSplittingHard.lean` lines 305 -- 319; HI
      projection at `HardInterventionOn.lean`
      lines 296 -- 300.)
  Each line of the four-line discharge is a constructor
  mismatch (`Sum.inl _ ∉ Sum.inr '' I` and its symmetric
  partner) -- the *reason* the no-op holds at all. The LN's
  `w^i = Sum.inr ⟨w, hw⟩` convention (recorded in
  `NodeSplittingHard.lean` lines 22 and 57) is precisely
  what places every LN `w^i` outside the four "natural"
  components of `(G.swig W hW)` *except* for `J`, which is
  why a HI on the input-copy half is a no-op.

* **Surface API `G.swig W hW` rather than the long-form
  `nodeSplittingHardInterventionOn`.** Same reasoning as the
  sibling claim_3_11 (`HardInterventionSwigCommute.lean`
  lines 208 -- 220): the four `@[simp]` characterisation
  lemmas fire on `G.swig W hW` terms by `abbrev`-reducibility,
  and the surface name reads like the LN's `G_{\swig(W)}`
  prose.

* **`G` implicit; `W` implicit; `hW` and `I` explicit.**
  Both `G` and `W` are recoverable from `hW` (its type pins
  them down); `hW` is explicit because it's a structural
  precondition that the elaborator cannot synthesise from
  context; `I` is explicit because it parameterises the
  conclusion non-trivially and call sites will want to
  specify it. Mirrors the sibling claim_3_11's argument
  ordering. -/
theorem swig_hardInterventionOn_inputs_eq_self
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.V) (I : Set ↑W) :
    (G.swig W hW).hardInterventionOn (Sum.inr '' I) = G.swig W hW := by
  -- Mirrors TeX Scenario B1 (lines 79 -- 134): four-field check via
  -- `mk_eq_of_data`. Each field's no-op witness is the same
  -- constructor mismatch `Sum.inl _ ≠ Sum.inr _`.
  refine mk_eq_of_data ?_ ?_ ?_ ?_
  · -- J: `Sum.inr '' I ⊆ Set.range Sum.inr` absorbs the HI's
    -- J-promotion (TeX "Input set", lines 103 -- 106).
    simp only [hardInterventionOn_J, nodeSplittingHardInterventionOn_J]
    rw [Set.union_assoc,
      Set.union_eq_left.mpr (Set.image_subset_range Sum.inr I)]
  · -- V: `Sum.inl '' G.V` is disjoint from `Sum.inr '' I` by
    -- constructor mismatch (TeX "Output set", lines 108 -- 111).
    simp only [hardInterventionOn_V, nodeSplittingHardInterventionOn_V]
    ext x
    constructor
    · intro h
      exact h.1
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨v, hv, rfl⟩, ?_⟩
      rintro ⟨z, _, hh⟩
      cases hh
  · -- E: every directed edge of the SWIG has target `Sum.inl v₂`,
    -- never in `Sum.inr '' I` (TeX "Directed edges", lines 113 -- 117).
    ext p
    simp only [mem_hardInterventionOn_E, mem_nodeSplittingHardInterventionOn_E]
    constructor
    · rintro ⟨⟨v₁, v₂, hE, rfl⟩, _⟩
      exact ⟨v₁, v₂, hE, rfl⟩
    · rintro ⟨v₁, v₂, hE, rfl⟩
      refine ⟨⟨v₁, v₂, hE, rfl⟩, ?_⟩
      rintro ⟨z, _, hh⟩
      cases hh
  · -- L: every bidirected edge of the SWIG has both endpoints
    -- `Sum.inl _`, neither in `Sum.inr '' I` (TeX "Bidirected edges",
    -- lines 119 -- 123).
    ext p
    simp only [mem_hardInterventionOn_L, mem_nodeSplittingHardInterventionOn_L]
    constructor
    · rintro ⟨⟨v₁, v₂, hL, rfl⟩, _, _⟩
      exact ⟨v₁, v₂, hL, rfl⟩
    · rintro ⟨v₁, v₂, hL, rfl⟩
      refine ⟨⟨v₁, v₂, hL, rfl⟩, ?_, ?_⟩
      · rintro ⟨z, _, hh⟩
        cases hh
      · rintro ⟨z, _, hh⟩
        cases hh

/-! ## Scenario B2: HI on output copies (`Sum.inl` half) shrinks `V` -/

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: swig_hardInterventionOn_outputs_V
-- claim_3_12 (Scenario B2)
--
-- After `G.swig W hW`, the `Sum.inl` half of the carrier
-- contains the output copies: `(G.swig W hW).V = Sum.inl ''
-- G.V` (`nodeSplittingHardInterventionOn_V`, NodeSplittingHard
-- lines 253 -- 267). Hard-intervening on `Sum.inl '' S`
-- (for `S ⊆ W`) removes exactly `Sum.inl '' S` from `V`,
-- adds it to `J`, and removes incoming edges to it -- this
-- is *not* a no-op, contrasting with Scenario B1. We record
-- the `V`-shrinkage as the cleanest witness of the change.
/-
LN source -- the *third* sentence of the Remark (the second
clause), verbatim from `graphs.tex` line 707 (reflowed for the
100-character line limit; LaTeX whitespace collapses between
tokens):

while hard intervening on $w^o$ would turn $w^o$ into an
additional input node, for now indicated as $(w^o)^i$.

(The LN continues to describe the final state -- "two input
nodes `(w^o)^i` and `w^i`" -- but the *operational* observation
for our purposes is just that `V` shrinks, which is the
direct opposite of Scenario B1.)
-/
/-- claim_3_12 (Scenario B2): hard-intervening on
`Sum.inl '' S` removes exactly `Sum.inl '' S` from the SWIG's
`V`. Formalises the LN's "hard intervening on `w^o` would
turn `w^o` into an additional input node" -- the
`Sum.inl`-half is the canonical observation half, and HI
genuinely promotes those vertices out of `V`.

## Design choice

* **`V`-component-only conclusion, not a full CDMG equality
  or a componentwise tuple.** Three reasons.
    * The point of this theorem is to *contrast* with
      Scenario B1 (the no-op). B1 said *nothing changes*;
      B2 says *`V` changes*. Witnessing the change on the
      single `V` component is enough to refute equality
      with B1 -- which is exactly what the punchline
      corollary will use.
    * Stating the full CDMG-equality (with the new `J`
      `Sum.inl '' G.J ∪ Set.range Sum.inr ∪ Sum.inl '' S`,
      new `E` `... ∖ {(_, Sum.inl s) | s ∈ S}`, etc.) would
      add four times the complexity for zero downstream
      payoff -- claim_3_11's analogue does that work
      already (it really is a full `Eq`), but our purpose
      here is just to *exhibit* one component-level
      disagreement to underpin the punchline.
    * The `V`-component is the *cleanest* witness: it
      shrinks by exactly `Sum.inl '' S`, no more, no less,
      with no constructor case-split.

* **Closed form `Sum.inl '' (G.V \ S)`, not
  `(G.swig W hW).V \ Sum.inl '' S`.** Both are correct (and
  equal by `Set.image_diff Sum.inl_injective`); we prefer
  the closed form because (i) it eliminates the explicit
  `Sum.inl ''` re-application a downstream consumer would
  have to do to combine with `nodeSplittingHardInterventionOn_V`,
  and (ii) it makes the *visible shape* of the result a
  single `Sum.inl ''` image, lining up with the LN's mental
  model `V_{swig(W)} = V` (under the identification
  `α ≅ inl '' α`) minus the intervened set. Manager B's
  proof rewrites against two `@[simp]` projections: the
  outer `hardInterventionOn_V` (`HardInterventionOn.lean`
  lines 275 -- 276) reduces the LHS to
  `(G.swig W hW).V \ Sum.inl '' S`; the inner
  `nodeSplittingHardInterventionOn_V`
  (`NodeSplittingHard.lean` lines 253 -- 267) rewrites
  `(G.swig W hW).V` to `Sum.inl '' G.V`; and then
  `Set.image_diff Sum.inl_injective` combines the two into
  `Sum.inl '' (G.V \ S)`.

* **LN's `w^o = Sum.inl w` identification.** The LN's
  Scenario B2 clause "hard intervening on `w^o` would turn
  `w^o` into an additional input node" (`graphs.tex`
  line 707) names the *output copy* of `w` after splitting.
  Our `NodeSplittingHard.lean` (lines 22 and 57) records
  the convention `Sum.inl = 0-copy = w^o = canonical
  observation copy`, established in `NodeSplittingOn.lean`
  (lines 244 -- 269) and inherited by the SWIG. The
  intervention target `Sum.inl '' S` of this theorem is
  therefore exactly the LN's `(W^o)_S = {w^o : w ∈ S}` for
  any `S ⊆ W`, and `Sum.inl w` instantiates to the LN's
  `w^o` per-witness. Spelling this out keeps a downstream
  reader from second-guessing whether `Sum.inl` is the
  "observation" copy or the "intervention" copy -- the
  convention is global to the chapter, but every theorem
  that talks about `Sum.inl '' _` benefits from re-stating
  it for self-containment.

* **`hS : S ⊆ W` precondition: LN-faithful but mathematically
  optional.** The conclusion holds for *any* `S : Set α`,
  not just `S ⊆ W` -- the proof goes through `Set.image_diff
  Sum.inl_injective`, which is unconditional in `S`. We keep
  `hS` because the LN's Scenario B2 is exactly the case
  `S = {w}` with `w ∈ W` (the output copies of vertices that
  were split). Documenting this rather than dropping `hS`:
    * preserves call-site clarity (a reader instantiating
      with their own `S` immediately sees the LN-intended
      scope);
    * costs nothing -- the proof never *consumes* `hS`, so
      Manager B can simply ignore it.
  An alternative encoding is to drop `hS` entirely and treat
  the LN-faithful scope as a downstream lemma; we judged the
  inline `hS` more readable and less likely to mislead a
  future user into thinking the theorem applies to arbitrary
  `Sum.inl '' S` when the LN scenario does not.

* **`S : Set α`, not `S : Set ↑W`.** The LN's `w^o` is the
  `Sum.inl` of an element of `α` -- we read `Sum.inl '' S`
  as "the canonical observation copies of `S`", with `S` as
  an arbitrary subset of `α` (constrained by `hS` to land in
  `W`). Using `S : Set ↑W` would force an extra layer of
  subtype-coercion at every call site for no payoff.

* **`G` implicit; `W` implicit; `hW`, `S`, `hS` explicit.**
  Same convention as Scenario B1; mirrors the sibling
  claim_3_11. -/
theorem swig_hardInterventionOn_outputs_V
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.V) (S : Set α) (hS : S ⊆ W) :
    ((G.swig W hW).hardInterventionOn (Sum.inl '' S)).V
      = Sum.inl '' (G.V \ S) := by
  -- Mirrors TeX Scenario B2 (lines 136 -- 171): `hardInterventionOn_V`
  -- reduces the LHS to `(G.swig W hW).V \ Sum.inl '' S`;
  -- `nodeSplittingHardInterventionOn_V` rewrites the inner
  -- `(G.swig W hW).V` to `Sum.inl '' G.V`; and `Set.image_diff
  -- Sum.inl_injective` consolidates `Sum.inl '' G.V \ Sum.inl '' S`
  -- back to `Sum.inl '' (G.V \ S)`. `hS` is documented as
  -- LN-faithful but unused (the conclusion holds for any
  -- `S : Set α`).
  rw [hardInterventionOn_V, nodeSplittingHardInterventionOn_V]
  exact (Set.image_diff Sum.inl_injective G.V S).symm
-- REFACTOR-BLOCK-ORIGINAL-END: swig_hardInterventionOn_outputs_V

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: swig_hardInterventionOn_outputs_V (was: refactor_swig_hardInterventionOn_outputs_J)
/-- claim_3_12 (Scenario B2, LN-faithful replacement): hard-intervening
on `Sum.inl '' S` (the output copies of `S ⊆ W`) *promotes those output
copies into the SWIG's input set* --
`Sum.inl '' S ⊆ ((G.swig W hW).hardInterventionOn (Sum.inl '' S)).J`.
Formalises the LN's literal "hard intervening on `w^o` would turn `w^o`
into an additional input node" (`graphs.tex` line 707) as a positive
J-subset claim about the output copies.

## What changed from the original

The original `swig_hardInterventionOn_outputs_V` stated only the
*V-shrinkage*
`((G.swig W hW).hardInterventionOn (Sum.inl '' S)).V = Sum.inl '' (G.V \ S)`
-- a consequence of the LN's clause, but not its primary content. The
strict-equivalence gate flagged that as a CONTENT deviation: the LN's
primary content is the *positive* J-membership ("turns `w^o` into an
*input* node"), not the V-shrinkage. This replacement states the
J-subset directly; the V-shrinkage still follows from the original's
two-step rewrite `hardInterventionOn_V` then
`nodeSplittingHardInterventionOn_V` plus `Set.image_diff`, but is now
demoted to a downstream consequence rather than the headline.

## Design choice

* **Positive J-subset, not V-shrinkage.** The LN literally writes
  "turn `w^o` into an additional *input* node" -- a J-membership claim
  about the output copies. V-shrinkage is the downstream consequence
  (an output-promoted-to-input is no longer an output). The J-subset
  form is the LN-faithful translation; the original's V-equality was
  the strict-gate's CONTENT-level complaint.
* **`Sum.inl '' S ⊆ ... .J` rather than equality.** The HI's full
  J-promotion result is `(G.swig W hW).J ∪ Sum.inl '' S` (by
  `hardInterventionOn_J`); the LN-faithful statement is that
  `Sum.inl '' S` lands *inside* the post-HI J, which is the cleaner
  subset form. (The full equality would itself be a near-triviality
  given the `@[simp]` projection, and would not be the LN's content.)
* **Same `(hW, S, hS)` explicit signature as the original**, keeping
  caller compatibility. `hS : S ⊆ W` remains LN-faithful but
  mathematically optional -- the conclusion holds for any `S : Set α`,
  and the proof never consumes `hS`.
* **Naming `swig_hardInterventionOn_outputs_J`.** Parallels Scenario
  A's T1 replacement (`swig_hardInterventionOn_inputs_J`) and matches
  the pattern "J-membership lemma about the post-SWIG HI target". -/
theorem refactor_swig_hardInterventionOn_outputs_J
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.V) (S : Set α) (hS : S ⊆ W) :
    Sum.inl '' S ⊆ ((G.swig W hW).hardInterventionOn (Sum.inl '' S)).J := by
  -- `hardInterventionOn_J` unfolds the RHS to `(G.swig W hW).J ∪ Sum.inl '' S`;
  -- `Set.subset_union_right` then identifies the LHS as the second summand.
  -- `hS` is documented as LN-faithful but unused.
  rw [hardInterventionOn_J]
  exact Set.subset_union_right
-- REFACTOR-BLOCK-REPLACEMENT-END: swig_hardInterventionOn_outputs_V

/-! ## Punchline corollary: B1 ≠ B2, so the SWIG order is ambiguous -/

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: swig_then_hardInterventionOn_depends_on_copy_choice
-- claim_3_12 (Punchline)
--
-- Combining B1 and B2 for the LN's specific scenario
-- `W = {w}` with `w ∈ G.V`: the input-copy HI gives back
-- `G.swig {w} hW` unchanged (B1), while the output-copy HI
-- shrinks `V` by `Sum.inl '' {w} = {Sum.inl w}` (B2). Since
-- `w ∈ G.V`, `Sum.inl w ∈ Sum.inl '' G.V = (G.swig {w} hW).V`,
-- so the post-B1 `V` *contains* `Sum.inl w` while the post-B2
-- `V` *does not*. Hence the two graphs disagree on `V`, and
-- so disagree as CDMGs.
/-
LN source -- the *fourth* sentence of the Remark (the
final clause), verbatim from `graphs.tex` lines 707 -- 708
(reflowed for the 100-character line limit; LaTeX whitespace
collapses between tokens):

So in the latter case we are left with two input node
$(w^o)^i$, which does not have any edges, and $w^i$, which
might have outgoing edges.
-/
/-- claim_3_12 (Punchline corollary): for `w ∈ G.V`, hard
intervention on `{Sum.inl w}` (the output copy, "`w^o`") gives
a *different* graph from hard intervention on
`{Sum.inr ⟨w, _⟩}` (the input copy, "`w^i`"). This formalises
the Remark's punchline that, under our `Sum.inl = w^o`,
`Sum.inr = w^i` convention, the LN's "ambiguity on which of
those two the hard intervention should be applied" yields
genuinely non-equal graphs -- so "SWIG then HI on `w`" is
*not* a well-defined operation when `w ∈ W`; one must commit
to a copy.

## Design choice

* **Singleton `W = {w}` form rather than a general
  `Sum.inl '' S₁ ≠ Sum.inr '' S₂` statement.** The LN's
  Remark is a *narrative* about a single `w ∈ W₁ ∩ W₂`,
  walking through "what would happen if we picked `w^i`"
  vs. "what would happen if we picked `w^o`". The
  singleton form is therefore the most LN-faithful: it
  matches the prose one-to-one and serves as a concrete
  refutation of any naive "post-SWIG HI on `w`" claim. A
  general `Sum.inl '' S` vs. `Sum.inr '' S` non-equality
  for `S ⊆ W` non-empty would be marginally more
  generality at the cost of significant LN-distance.

* **Hypothesis `hwV : w ∈ G.V`, not a separate `hwW : w ∈ W`
  for some external `W`.** The Remark *constructs* the
  witnessing `W` from `w` (the singleton `{w}`). Pinning
  `W = {w}` inside the conclusion removes the external `W`
  parameter and lines up with the LN's scenario, where the
  single shared vertex `w` is the entire object of
  attention. The `Set.singleton_subset_iff.mpr hwV`
  discharge of the SWIG's `W ⊆ G.V` precondition is the
  unique mathematically meaningful choice given `hwV`.

* **`hardInterventionOn` on both sides, with the singleton
  targets differing only in the constructor.** The two
  CDMGs being compared have *the same underlying SWIG*
  (`G.swig {w} _`) and the same outer operation
  (`hardInterventionOn`); only the *target set* differs:
  `{Sum.inl w}` for the output-copy branch (Scenario B2),
  `{Sum.inr ⟨w, _⟩}` for the input-copy branch (Scenario
  B1). This makes the disagreement maximally crisp: any
  one component-level disagreement (here `V`) suffices,
  and the proof can use Scenario B1's `_eq_self` plus
  Scenario B2's `_outputs_V` directly.

* **`{Sum.inr ⟨w, rfl⟩}` for the input-copy singleton.**
  `Sum.inr` takes an element of `↑({w} : Set α)`, which is
  the subtype `{x : α // x ∈ ({w} : Set α)}`. To exhibit
  `w` as such an element we need a proof of
  `w ∈ ({w} : Set α)`, and `rfl` discharges it by reduction
  through Lean 4's `Set` / `setOf` / singleton encoding
  (`({w} : Set α) = {x | x = w}`, so `w ∈ {w}` reduces to
  `w = w`). Should the reduction fail in some
  configuration, the equivalent
  `Set.mem_singleton_iff.mpr rfl` works as a drop-in
  replacement; we use `rfl` here for syntactic minimalism.

* **Conclusion is `≠` (i.e., `¬ Eq`), not a specific
  component disagreement.** The LN's punchline -- "left with
  two input nodes `(w^o)^i` and `w^i`" (`graphs.tex` line
  708) -- is *non-equality of graphs*, which our `≠`
  formalises exactly. Manager B's proof will derive `≠` via
  the chain:
    1. Apply `swig_hardInterventionOn_inputs_eq_self`
       (Scenario B1) on the RHS with `I = {⟨w, rfl⟩}`,
       reducing `(G.swig {w} _).hardInterventionOn
       {Sum.inr ⟨w, rfl⟩}` to `G.swig {w} _`.
    2. Apply `swig_hardInterventionOn_outputs_V`
       (Scenario B2) on the LHS's `V` projection with
       `S = {w}`, reducing
       `((G.swig {w} _).hardInterventionOn {Sum.inl w}).V`
       to `Sum.inl '' (G.V \ {w})`.
    3. Note `Sum.inl w ∉ Sum.inl '' (G.V \ {w})` (since
       `w ∉ G.V \ {w}`) while `Sum.inl w ∈ Sum.inl '' G.V
       = (G.swig {w} _).V` (since `w ∈ G.V` by `hwV`, using
       `nodeSplittingHardInterventionOn_V`,
       `NodeSplittingHard.lean` lines 253 -- 267).
    4. The two `V`s differ on the element `Sum.inl w`, so
       the CDMGs differ.
  The disagreement element `Sum.inl w` -- the LN's `w^o`
  -- is therefore the concrete *witness* of the LN's
  punchline `w^o ≠ w^i`, and the proof traces the LN's
  prose one step at a time.

* **Mathlib re-use: just `Set.singleton_subset_iff` plus
  the four-element `Sum.inl` / `Sum.inr` constructor
  toolkit.** This row does not invent any new mathlib-style
  combinator; it composes claim_3_12 Scenarios B1 and B2
  with three off-the-shelf facts: `Sum.inl ≠ Sum.inr`
  (constructor disjointness), `Set.singleton_subset_iff`
  (for the SWIG-precondition discharge), and
  `Set.image_singleton` / membership unfolding. Building a
  bespoke `CDMG` non-equality combinator would be premature
  generalisation -- the sibling-theorem chain handles every
  proof step.

* **`G : CDMG α` implicit; `w` implicit; `hwV` explicit.**
  As elsewhere in this row; the only "data" parameter the
  user supplies is `hwV`, and `w` is recovered from it. -/
theorem swig_then_hardInterventionOn_depends_on_copy_choice
    {G : CDMG α} {w : α} (hwV : w ∈ G.V) :
    (G.swig ({w} : Set α) (Set.singleton_subset_iff.mpr hwV)).hardInterventionOn
        ({Sum.inl w} : Set (α ⊕ ↑({w} : Set α)))
      ≠ (G.swig ({w} : Set α) (Set.singleton_subset_iff.mpr hwV)).hardInterventionOn
        ({Sum.inr ⟨w, rfl⟩} : Set (α ⊕ ↑({w} : Set α))) := by
  -- Mirrors TeX Punchline (lines 173 -- 221): compute V-projections of
  -- both sides via Scenarios B1 and B2, then exhibit `Sum.inl w` in
  -- exactly one. The two V's then differ, so the CDMGs differ.
  -- LHS.V = Sum.inl '' (G.V \ {w}) via theorem 3 (with S = {w}).
  have hLHS : ((G.swig ({w} : Set α) (Set.singleton_subset_iff.mpr hwV)).hardInterventionOn
                ({Sum.inl w} : Set (α ⊕ ↑({w} : Set α)))).V
              = Sum.inl '' (G.V \ ({w} : Set α)) := by
    have h1 : ({Sum.inl w} : Set (α ⊕ ↑({w} : Set α))) = Sum.inl '' ({w} : Set α) :=
      Set.image_singleton.symm
    rw [h1]
    exact swig_hardInterventionOn_outputs_V _ _ (Set.Subset.refl _)
  -- RHS.V = Sum.inl '' G.V via theorem 2 (with I = {⟨w, rfl⟩}) then
  -- `nodeSplittingHardInterventionOn_V`.
  have hRHS : ((G.swig ({w} : Set α) (Set.singleton_subset_iff.mpr hwV)).hardInterventionOn
                ({Sum.inr ⟨w, rfl⟩} : Set (α ⊕ ↑({w} : Set α)))).V
              = Sum.inl '' G.V := by
    have h2 : ({Sum.inr (⟨w, rfl⟩ : ↑({w} : Set α))} : Set (α ⊕ ↑({w} : Set α)))
              = Sum.inr '' ({⟨w, rfl⟩} : Set ↑({w} : Set α)) :=
      Set.image_singleton.symm
    rw [h2, swig_hardInterventionOn_inputs_eq_self, nodeSplittingHardInterventionOn_V]
  intro hEq
  have hVEq := congrArg CDMG.V hEq
  rw [hLHS, hRHS] at hVEq
  -- hVEq : Sum.inl '' (G.V \ {w}) = Sum.inl '' G.V
  -- Sum.inl w ∈ Sum.inl '' G.V (witness w ∈ G.V) but ∉ Sum.inl ''
  -- (G.V \ {w}) (since w ∈ {w}).
  have hMem : (Sum.inl w : α ⊕ ↑({w} : Set α)) ∈ (Sum.inl '' G.V : Set _) :=
    ⟨w, hwV, rfl⟩
  rw [← hVEq] at hMem
  obtain ⟨v, ⟨_, hvNe⟩, hveq⟩ := hMem
  have hvw : v = w := Sum.inl_injective hveq
  subst hvw
  exact hvNe rfl
-- REFACTOR-BLOCK-ORIGINAL-END: swig_then_hardInterventionOn_depends_on_copy_choice

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: swig_then_hardInterventionOn_depends_on_copy_choice (was: refactor_swig_then_hardInterventionOn_two_input_nodes)
/-- claim_3_12 (Punchline, LN-faithful replacement): for `w ∈ G.V`,
after first SWIG-ing on `{w}` and then hard-intervening on the output
copy `{Sum.inl w}` (i.e. `w^o`), the resulting CDMG has **two input
nodes**: the freshly promoted `Sum.inl w` (the LN's `(w^o)^i`) **and**
the original split-input copy `Sum.inr ⟨w, rfl⟩` (the LN's `w^i`).
Both lie in `J` of the post-HI graph. Formalises the LN punchline
literally: "we are left with two input node `(w^o)^i`, which does not
have any edges, and `w^i`, which might have outgoing edges"
(`graphs.tex` line 708) -- the existence of both inputs in `J` is the
LN's primary content.

## What changed from the original

The original `swig_then_hardInterventionOn_depends_on_copy_choice`
stated a *non-equality* of the two candidate "SWIG-then-HI on a copy
of `w`" CDMGs -- a consequence of B1+B2 that captured the LN's
"ambiguity on which copy to apply" framing but *not* the LN's literal
punchline. The strict-equivalence gate flagged that as a CONTENT
deviation: the LN's punchline is the *positive* statement "two input
nodes", not the abstract non-equality of two candidate CDMGs. This
replacement states the LN-faithful "two input nodes" claim as a
conjunction of two J-memberships; the original's non-equality remains
a downstream consequence (the two candidate CDMGs disagree precisely
because their J-sets disagree at `Sum.inl w` -- the B1 branch lacks
it, the B2 branch contains it).

## Design choice

* **Positive joint J-membership, not non-equality.** The LN literally
  enumerates the two input nodes after the "HI on `w^o`" branch -- a
  positive statement about the post-HI J-set. Stating non-equality of
  the two candidate CDMGs (the original) is one possible *consequence*
  of the LN punchline, but obscures the LN's actual content. The
  joint J-membership form is the strict-gate-aligned LN-faithful
  translation.
* **Conjunction `∧`, not two separate lemmas.** The LN itself
  enumerates the two input nodes in one breath ("two input node
  `(w^o)^i` ... and `w^i`"); the conjunction matches the LN's
  syntactic shape one-to-one. Splitting into two lemmas would invent
  an artificial decomposition the LN does not make.
* **`Sum.inl w` and `Sum.inr ⟨w, rfl⟩` as the two witnesses.** Under
  the `NodeSplittingHard.lean` convention `Sum.inl = w^o`,
  `Sum.inr = w^i`, the LN's `(w^o)^i` is the freshly HI-promoted
  output copy `Sum.inl w` (in `J` thanks to the HI's J-extension via
  `hardInterventionOn_J`), and the LN's `w^i` is the original
  split-input `Sum.inr ⟨w, rfl⟩` (in `J` thanks to
  `nodeSplittingHardInterventionOn_J` placing every `Sum.inr` in the
  SWIG's `J` via `Set.range Sum.inr`). The HI does not remove
  anything from `J`, so the SWIG's pre-existing
  `Sum.inr ⟨w, rfl⟩ ∈ J` survives.
* **Singleton `{w}` SWIG, mirroring the original.** Same LN-faithful
  scope as the original (and same `Set.singleton_subset_iff.mpr hwV`
  SWIG-precondition discharge). The Punchline is narrated for a
  single shared `w ∈ W₁ ∩ W₂`; the singleton form is the most
  LN-faithful.
* **Naming `swig_then_hardInterventionOn_two_input_nodes`.** Mirrors
  the LN's prose "two input nodes" directly. The original's
  `_depends_on_copy_choice` framing was a derived interpretation, not
  the LN's literal punchline. -/
theorem refactor_swig_then_hardInterventionOn_two_input_nodes
    {G : CDMG α} {w : α} (hwV : w ∈ G.V) :
    Sum.inl w ∈ ((G.swig ({w} : Set α)
        (Set.singleton_subset_iff.mpr hwV)).hardInterventionOn
        ({Sum.inl w} : Set (α ⊕ ↑({w} : Set α)))).J ∧
    Sum.inr (⟨w, rfl⟩ : ↑({w} : Set α)) ∈
      ((G.swig ({w} : Set α)
        (Set.singleton_subset_iff.mpr hwV)).hardInterventionOn
        ({Sum.inl w} : Set (α ⊕ ↑({w} : Set α)))).J := by
  -- `hardInterventionOn_J` unfolds `(... HI {Sum.inl w}).J` to
  -- `(G.swig {w} _).J ∪ {Sum.inl w}`; `nodeSplittingHardInterventionOn_J`
  -- unfolds the SWIG's J to `Sum.inl '' G.J ∪ Set.range Sum.inr`. The
  -- LN's `(w^o)^i = Sum.inl w` is the right summand; the LN's
  -- `w^i = Sum.inr ⟨w, rfl⟩` sits in `Set.range Sum.inr` of the SWIG.
  rw [hardInterventionOn_J, nodeSplittingHardInterventionOn_J]
  refine ⟨?_, ?_⟩
  · -- `Sum.inl w ∈ (Sum.inl '' G.J ∪ Set.range Sum.inr) ∪ {Sum.inl w}`:
    -- the right summand by singleton-membership.
    exact Or.inr rfl
  · -- `Sum.inr ⟨w, rfl⟩ ∈ (Sum.inl '' G.J ∪ Set.range Sum.inr) ∪ {Sum.inl w}`:
    -- left summand, then right summand (`Set.range Sum.inr`), with
    -- witness `⟨w, rfl⟩`.
    exact Or.inl (Or.inr ⟨⟨w, rfl⟩, rfl⟩)
-- REFACTOR-BLOCK-REPLACEMENT-END: swig_then_hardInterventionOn_depends_on_copy_choice

end CDMG

end Causality
