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

-- ## Design choice — statement context
--
-- `Node : Type*` with `[DecidableEq Node]`.  Inherited from `def_3_1`
-- (`CDMG.lean`); load-bearing because the statement constructs
-- `W₁ ∪ W₂` (needs `Finset.union`), `W₂.image SplitNode.unsplit`
-- (needs `Finset.image`), and four `Finset.image f` equalities
-- inside `eqViaNodeMap` — every one of which requires decidable
-- equality on `Node` (and, via the auto-derived
-- `DecidableEq (SplitNode Node)` and
-- `DecidableEq (SplitNode (SplitNode Node))` instances from
-- `def_3_11`, on the iterated and single-step carriers as well).
-- Stronger instances (`Fintype`, `LinearOrder`) are not needed at the
-- statement level and are deferred to the proof body's use sites.
-- claim_3_7 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_7 --- end helper

-- ## Helper: the canonical flatten map `SplitNode (SplitNode Node) → SplitNode Node`
--
-- Realises the LN's "canonical bijection of carriers" induced by
-- `def_3_11`'s unsplit-injection convention `v⁰ := v¹ := v` for
-- `v ∈ J ∪ (V ∖ W)`.  On the *iterated* carrier (the elements that
-- actually inhabit `(G_{spl(W₁)})_{spl(W₂)}.V`):
--
--   .unsplit (.unsplit v) ↦ .unsplit v   (v ∈ J ∪ (V ∖ (W₁ ∪ W₂)))
--   .unsplit (.copy0 w)   ↦ .copy0 w     (w ∈ W₁; inner-split copy)
--   .unsplit (.copy1 w)   ↦ .copy1 w     (w ∈ W₁; inner-split copy)
--   .copy0 (.unsplit w)   ↦ .copy0 w     (w ∈ W₂; outer-split copy)
--   .copy1 (.unsplit w)   ↦ .copy1 w     (w ∈ W₂; outer-split copy)
--
-- The off-carrier cases (`.copy0 (.copy0 _)`, etc.) never appear in the
-- iterated carrier when `Disjoint W₁ W₂`; the values below are filled
-- in for totality of the pattern match and do not affect the equality
-- this row asserts.
--
-- ## Design choice
--
-- *Function, not `Equiv` of types.*  A type-level `SplitNode (SplitNode
--   Node) ≃ SplitNode Node` does not exist: when `Node` is non-empty
--   the source has nine reachable constructor combinations per node
--   and the target only three, so no bijection on the underlying
--   types is possible.  `flattenSplit` is instead injective only when
--   restricted to the *iterated carrier*
--   `((G.V ∖ W₁) ⊍ W₁⁰ ⊍ W₁¹) ⊍ ((W₂ image .unsplit)⁰) ⊍ …`,
--   and the disjointness hypothesis `Disjoint W₁ W₂` is precisely
--   what makes that restricted injection well-defined (without it,
--   `.copy0 (.unsplit w)` and `.copy0 (.copy0 w)` could both lie in
--   the carrier and would both map to `.copy0 w`).  Image-level
--   reasoning via `Finset.image flattenSplit` is enough for the
--   statement; the proof of the main theorem will only ever apply
--   `flattenSplit` to elements actually in the iterated carrier.
--
-- *Total pattern match on `SplitNode (SplitNode Node)`.*  Lean requires
--   total functions; the off-carrier cases (`.copy0 (.copy0 _)`,
--   `.copy0 (.copy1 _)`, `.copy1 (.copy0 _)`, `.copy1 (.copy1 _)`)
--   are filled in with the simplest value that keeps the pattern
--   match exhaustive.  Their values do not affect the equality this
--   row asserts, because `Finset.image` over the iterated carrier
--   never reaches them.  An alternative — partial functions over
--   `Subtype` of the iterated carrier — was rejected because every
--   downstream `Finset.image` call would then need a subtype-respecting
--   wrapper, ballooning the four field-equalities in `eqViaNodeMap`.
--
-- *Same `flattenSplit` for the (a) and (b) directions.*  The
--   case-analysis above is symmetric in `W₁` / `W₂`: the constructors
--   `unsplit` / `copy0` / `copy1` are blind to which `Wᵢ` the
--   underlying node belongs to, so the same flatten map handles both
--   iteration orders.  This is the reason a single
--   `flattenSplit` (rather than an asymmetric pair `flattenSplit₁₂` /
--   `flattenSplit₂₁`) is enough; without this symmetry the statement
--   would need two distinct flatten maps and the conjunction shape
--   `(a) ∧ (b)` would not be symmetric in its proof witnesses.
--
-- *Mathlib re-use.*  Rolled our own — Mathlib carries no general
--   "flatten nested tagged sum" map specific to the `unsplit / copy0 /
--   copy1` triple of `def_3_11`.  A `Sum`-based encoding of `SplitNode`
--   would let us reuse `Sum.elim`, but the case-analysis would not
--   shorten; only the names of the constructors would change.
-- claim_3_7 --- start helper
def flattenSplit : SplitNode (SplitNode Node) → SplitNode Node
  | .unsplit x => x
  | .copy0 (.unsplit w) => SplitNode.copy0 w
  | .copy0 (.copy0 w) => SplitNode.copy0 w
  | .copy0 (.copy1 w) => SplitNode.copy1 w
  | .copy1 (.unsplit w) => SplitNode.copy1 w
  | .copy1 (.copy0 w) => SplitNode.copy0 w
  | .copy1 (.copy1 w) => SplitNode.copy1 w
-- claim_3_7 --- end helper

-- ## Helper: equality of two CDMGs (over possibly different carriers) via a node map
--
-- The four data fields `(J, V, E, L)` of a CDMG are `Finset`s.  Given
-- a node map `f : α → β`, `eqViaNodeMap G G' f` asserts that the image
-- of `G`'s four data fields under `f` (with `Prod.map f f` on the edge
-- sets) coincides with `G'`'s four data fields.  This captures the
-- LN's "equality of CDMGs read up to the canonical bijection of
-- carriers": when `f` is the canonical bijection on the carriers
-- (here `flattenSplit`), the predicate holds iff the two CDMGs
-- describe the same graph after identifying nodes via `f`.
--
-- ## Design choice
--
-- *Strongest Lean reading of "equality of CDMGs up to a canonical
--   carrier relabelling" without quotient types.*  Literal `=` between
--   `G` and `G'` is not type-correct when their carriers differ; an
--   `Equiv`-of-CDMGs / `CDMG.Iso` layer would require the carrier map
--   to be a type-level bijection, which `flattenSplit` is not (see the
--   `flattenSplit` block above).  Quotienting both carriers by a
--   common identification would discharge the type-mismatch but is
--   overkill for an equality read componentwise on `Finset`s; the LN
--   never invokes such a quotient.  `eqViaNodeMap` instead asserts the
--   image-level equality of the four data fields under `f`, which is
--   the literal componentwise reading the LN's "the same CDMG" intends
--   (the `def_3_11` notational shorthand `v⁰ := v¹ := v` is precisely
--   the carrier-level identification that `flattenSplit` realises).
--
-- *`Prop`-valued helper, not a `def CDMG.mapNodes` returning `CDMG β`.*
--   A data-valued transport would require discharging the five
--   propositional CDMG axioms (`hJV_disj`, `hE_subset`, `hL_subset`,
--   `hL_irrefl`, `hL_symm`) under the image, with an
--   injectivity-on-the-carrier hypothesis on `f` to lift `Disjoint J
--   V` and `hL_irrefl` through.  The `Prop`-valued form sidesteps both
--   costs: the four field equalities are plain `Finset` equalities,
--   and well-formedness of `G'` is automatic (it is supplied as
--   input, not constructed from `G` and `f`).  Trade-off:
--   `eqViaNodeMap` does not bundle a "mapped" CDMG, so downstream
--   consumers wanting to apply further constructions to the
--   transported graph would need to either prove well-formedness ad
--   hoc or upgrade to a data-valued `mapNodes`.  The current row only
--   needs the equality reading.
--
-- *Four conjuncts, mirroring `CDMG`'s four data fields.*  Consumers
--   destructure via `.1` / `.2.1` / `.2.2.1` / `.2.2.2`.  A bundled
--   `structure` would add a layer of named-field projection without
--   changing content; the four `Finset` equalities are exactly the
--   data part of `def_3_1`, so the conjunctive shape is the natural
--   "componentwise" reading.
--
-- *Mathlib re-use.*  Rolled our own.  Mathlib's `Equiv` / `Iso`
--   abstractions assume a two-sided invertible carrier map (or a
--   morphism-and-inverse pair); neither shape fits a one-directional
--   image equality under a non-bijective carrier function.
-- claim_3_7 --- start helper
def eqViaNodeMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : CDMG α) (G' : CDMG β) (f : α → β) : Prop :=
  G.J.image f = G'.J
    ∧ G.V.image f = G'.V
    ∧ G.E.image (Prod.map f f) = G'.E
    ∧ G.L.image (Prod.map f f) = G'.L
-- claim_3_7 --- end helper

-- ## Helper: well-typedness of the iterated splitting
--
-- For `W₁ ⊆ G.V`, `W₂ ⊆ G.V` disjoint, `W₂.image .unsplit` sits inside
-- the output-node set of `G.nodeSplittingOn W₁ hW₁` — specifically,
-- inside the `(G.V ∖ W₁).image .unsplit` piece, by disjointness.  This
-- discharges the `hW` precondition of `def_3_11`'s `nodeSplittingOn`
-- for the *outer* splitting in `(G_{spl(W₁)})_{spl(W₂)}`.
--
-- ## Design choice
--
-- *Lift via `Finset.image SplitNode.unsplit`, not via a fresh `Finset`
--   on the iterated carrier.*  The `unsplit` constructor of
--   `def_3_11`'s `SplitNode` is the type-level realisation of the LN's
--   "$v \in J \cup (V \sm W)$ stays in the carrier as itself" — so
--   `.image SplitNode.unsplit` *tags each `w ∈ W₂` as a node that the
--   inner splitting on `W₁` left alone*.  The disjointness
--   `Disjoint W₁ W₂` is exactly what guarantees that this tagging is
--   compatible with `def_3_11`'s output: `nodeSplittingOn` of `W₁`
--   removes `W₁` from the output carrier (`(V ∖ W₁).image .unsplit`)
--   and creates the new `W₁⁰`, `W₁¹` copies separately, so a `w ∈ W₂`
--   with `w ∉ W₁` lands in the `(V ∖ W₁).image .unsplit` piece via
--   `.unsplit w`.
--
-- *Disjointness `Disjoint W₁ W₂`, not the weaker `W₂ ⊆ G.V ∖ W₁` or
--   the stronger `W₁ ∩ W₂ = ∅` rewritten as `Finset.inter_eq_empty`.*
--   `Disjoint W₁ W₂` is the canonical Mathlib `Finset` shape
--   (intersection-empty) and lets the helper consume / produce
--   `Finset.disjoint_right` (and similar) directly; the LN's
--   "$W_1 \cap W_2 = \emptyset$" reads as exactly this `Disjoint`.
--   `W₂ ⊆ G.V ∖ W₁` would force the consumer to derive disjointness
--   from a subset, an extra rewrite at every call site.
--
-- *`private`, with helper markers.*  Mirrors the
--   `subset_carrier_of_hardInterventionOn` pattern in
--   `HardInterventionsCommute.lean` (`claim_3_4`).  The helper is
--   load-bearing for the statement to type-check (it supplies the
--   inner `hW` argument of `nodeSplittingOn`), so it carries helper
--   markers; the website builder pulls it out alongside the rendered
--   statement.  `private` localises it to this file; downstream
--   carrier-mismatch rows can re-introduce the same pattern locally
--   rather than reaching across files.
--
-- *Symmetric in `W₁` / `W₂`: applied as
--   `image_unsplit_subset_nodeSplittingOn_V hW₁ hW₂ hDisj` for the (a)
--   direction and as
--   `image_unsplit_subset_nodeSplittingOn_V hW₂ hW₁ hDisj.symm`
--   for the (b) direction.*  A single helper covers both; splitting
--   into two named lemmas would duplicate the proof.
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

-- ref: claim_3_7
--
-- For any CDMG `G` and any two disjoint subsets `W₁, W₂ ⊆ G.V`, the
-- LN's triple equality `(G_{spl(W₁)})_{spl(W₂)} =
-- (G_{spl(W₂)})_{spl(W₁)} = G_{spl(W₁ ∪ W₂)}` decomposes (per the
-- rewritten tex's (a)/(b) split) into two CDMG equalities read up to
-- the canonical flatten map `flattenSplit`:
--   (a) `(G_{spl(W₁)})_{spl(W₂)} = G_{spl(W₁ ∪ W₂)}`,
--   (b) `(G_{spl(W₂)})_{spl(W₁)} = G_{spl(W₁ ∪ W₂)}`.
-- Transitivity of equality recovers the LN's "swap symmetry" reading
-- from (a) ∧ (b).
/-
LN tex (rewritten canonical statement for `claim_3_7`):

  Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ V` two subsets of
  the output-node set of `G`, with `W₁ ∩ W₂ = ∅`.  Then
    (a) `(G_{spl(W₁)})_{spl(W₂)} = G_{spl(W₁ ∪ W₂)}`,
    (b) `(G_{spl(W₂)})_{spl(W₁)} = G_{spl(W₁ ∪ W₂)}`,
  read up to the canonical bijection of carriers induced by
  `def_3_11`'s unsplit-injection convention.

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CDMG and `W_1, W_2 ⊆ V` two disjoint
  subsets of the output nodes of `G`.  Then the CDMG obtained from
  first node-splitting `W_1` and then node-splitting `W_2` is the
  same CADMG that arises from first node-splitting `W_2` and then
  node-splitting `W_1`:
    `(G_{spl(W_1)})_{spl(W_2)} = (G_{spl(W_2)})_{spl(W_1)}
       = G_{spl(W_1 ∪ W_2)}`.

(The mid-sentence "CADMG" is a typo for "CDMG" per the
`cdmg_vs_cadmg_terminology_mismatch` addition_to_the_LN; the
equality is an equality of CDMGs.)
-/
-- ## Design choice
--
-- *One theorem returning a conjunction `(a) ∧ (b)`, with the
--   joint-intervention `G_{spl(W₁ ∪ W₂)}` as the shared right-hand
--   side.*  Lean has no native triple equality; the rewritten tex's
--   `enumerate[label=(\alph*)]` block makes the two-binary-equality
--   decomposition load-bearing.  The same conjunction shape appears
--   in `HardInterventionsCommute` (claim_3_4); reusing the pattern
--   here keeps the two "commute" rows callable at parallel `.1` /
--   `.2` projections.  The LN's swap-symmetry reading
--   `(G_{spl(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{spl(W₁)}` is recovered
--   from (a) ∧ (b) via transitivity through the shared right-hand
--   side.
--
-- *Why the LHS-equals-RHS form `eqViaNodeMap iter single flattenSplit`,
--   not `eqViaNodeMap iter₁₂ iter₂₁ (refl)` or any other "direct"
--   equality between the two iterated forms.*  At the Lean level,
--   `iter₁₂ := (G.nodeSplittingOn W₁ _).nodeSplittingOn (W₂.image
--   .unsplit) _` and `iter₂₁ := (G.nodeSplittingOn W₂ _).nodeSplittingOn
--   (W₁.image .unsplit) _` have the same carrier type
--   `SplitNode (SplitNode Node)`, but the *constructor wrappings* of
--   the same underlying graph node disagree: a node `w₁ ∈ W₁`
--   appears as `.unsplit (.copy0 w₁)` in `iter₁₂`'s carrier (since
--   `W₁` is split first, producing `.copy0 w₁ : SplitNode Node`, then
--   wrapped under `.unsplit` by the outer splitting on
--   `W₂.image .unsplit`) but as `.copy0 (.unsplit w₁)` in `iter₂₁`'s
--   carrier (since `W₁` is now split *second*, after `W₂` produced
--   a `SplitNode Node` carrier in which `w₁` was tagged `.unsplit`).
--   A literal `iter₁₂ = iter₂₁` is therefore *false* as a Lean
--   proposition — the four `Finset` fields contain different
--   constructor combinations even though they describe the same
--   abstract graph.  Routing both sides through the canonical
--   single-step `G_{spl(W₁ ∪ W₂)}` via the *same* `flattenSplit`
--   image-level relabelling is the mathematically faithful encoding;
--   "swap symmetry" between `iter₁₂` and `iter₂₁` is then recovered
--   as the transitive composite `eqViaNodeMap iter₁₂ single
--   flattenSplit ∧ eqViaNodeMap iter₂₁ single flattenSplit`, not as a
--   raw `=`.
--
-- *Disjoint-union encoding: `W₁ ∪ W₂` together with `Disjoint W₁ W₂`,
--   not `Sum`-based `⊔`.*  Matches `def_3_11`'s `nodeSplittingOn` API,
--   which takes `W : Finset Node` and `hW : W ⊆ G.V` — so the natural
--   right-hand side is `G.nodeSplittingOn (W₁ ∪ W₂) (Finset.union_subset
--   hW₁ hW₂)`.  The `Disjoint W₁ W₂` hypothesis (Mathlib's
--   `Finset.Disjoint`, i.e.\ intersection-empty on `Finset`) is
--   load-bearing for the well-typedness of the iterated splitting
--   (the inner-`hW` proof `image_unsplit_subset_nodeSplittingOn_V`
--   consumes it), per the rewritten tex's "Well-typedness of the
--   iterated splitting" paragraph.  It plays well with
--   `Finset.union_subset` for the right-hand side hypothesis
--   `W₁ ∪ W₂ ⊆ V`, with no `Finset.disjUnion` coercion gymnastics
--   needed.  Encoding the LN's "$W_1 \cap W_2 = \emptyset$" as the raw
--   `W₁ ∩ W₂ = ∅` was an alternative; the `Disjoint`-formulation is
--   chosen because `def_3_11`-driven side conditions (which this
--   helper discharges by case-splitting via `Finset.disjoint_right`)
--   live more naturally in the `Disjoint` API.
--
-- *Result is a CDMG, not a CADMG.*  Per the `addition_to_the_LN`
--   `cdmg_vs_cadmg_terminology_mismatch`: the LN's mid-sentence drift
--   "the CDMG\ldots is the same CADMG\ldots" is a typographical
--   inconsistency, not a genuine change of category.
--   `nodeSplittingOn` is `CDMG → CDMG` (it can introduce 2-cycles
--   when `G` has self-loops on `W`, so the result is in general not
--   acyclic).  Both sides of the asserted equality live in
--   `CDMG (SplitNode _)`; no `CADMG` wrapper appears anywhere in the
--   signature.
--
-- *Carrier-mismatch wrinkle handled via `eqViaNodeMap` + `flattenSplit`.*
--   See the module-level docstring and the helper blocks above.  The
--   LN's "equality of CDMGs read up to the canonical bijection of
--   carriers" is rendered as `eqViaNodeMap iterated single
--   flattenSplit`: the four `Finset` data fields of the iterated
--   splitting, after applying `flattenSplit` field-wise, coincide
--   with the four data fields of the single splitting.  This is the
--   strongest equality form available without introducing quotient
--   types or a `CDMG.Iso` layer.
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
  -- The proof follows the verified tex proof at
  -- `tex/claim_3_7_proof_TwoDisjointNode.tex`, working componentwise on
  -- the four `Finset` data fields `(J, V, E, L)` of each CDMG, for each
  -- of the two iteration orders (a) and (b).
  --
  -- Every sub-goal is a `Finset` equality of the form
  --   `iter.X.image (Prod.map flattenSplit flattenSplit?) = single.X`,
  -- the inner `Prod.map` only on the edge components.  The strategy
  -- is uniform: (i) `change` the goal into its fully-unfolded
  -- form (`nodeSplittingOn` is a `where`-syntax `def`, so its field
  -- projections reduce definitionally); (ii) push `.image flattenSplit`
  -- through unions (`Finset.image_union`) and compositions
  -- (`Finset.image_image`); (iii) close via helper lemmas about
  -- `flattenSplit ∘ toCopy{0,1}` and a per-element extensionality
  -- check where sdiffs remain.
  --
  -- Helper: `flattenSplit` collapses the two-stage `toCopy0` chain to
  -- the single `toCopy0 (A ∪ B)`.  Mirrors the LN's "unsplit-injection
  -- shorthand commutes with disjoint-union of split sets" reading from
  -- def_3_11; works for *any* `A, B` (the proof needs no disjointness
  -- because the case-split goes through `B ∋ v` / `A ∋ v` symmetrically,
  -- and the overlap case `v ∈ A ∩ B` is resolved by `Finset.mem_union_left`
  -- regardless).
  have flatten_toCopy0_toCopy0 : ∀ (A B : Finset Node) (v : Node),
      flattenSplit (toCopy0 (B.image SplitNode.unsplit) (toCopy0 A v))
        = toCopy0 (A ∪ B) v := by
    intro A B v
    unfold toCopy0
    by_cases hA : v ∈ A
    · -- Inner `toCopy0 A v = .copy0 v` (a `SplitNode Node`).
      rw [if_pos hA]
      -- `.copy0 v ∉ B.image .unsplit` by constructor mismatch.
      have h_notimg : SplitNode.copy0 v ∉ B.image SplitNode.unsplit := by
        intro h
        obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
        cases hweq
      rw [if_neg h_notimg]
      -- LHS now `flattenSplit (.unsplit (.copy0 v)) = .copy0 v`.
      change SplitNode.copy0 v = (if v ∈ A ∪ B then SplitNode.copy0 v else SplitNode.unsplit v)
      rw [if_pos (Finset.mem_union_left _ hA)]
    · -- Inner `toCopy0 A v = .unsplit v` (a `SplitNode Node`).
      rw [if_neg hA]
      by_cases hB : v ∈ B
      · -- `.unsplit v ∈ B.image .unsplit`.
        have h_img : SplitNode.unsplit v ∈ B.image SplitNode.unsplit :=
          Finset.mem_image.mpr ⟨v, hB, rfl⟩
        rw [if_pos h_img]
        -- LHS `flattenSplit (.copy0 (.unsplit v)) = .copy0 v`.
        change SplitNode.copy0 v = (if v ∈ A ∪ B then SplitNode.copy0 v else SplitNode.unsplit v)
        rw [if_pos (Finset.mem_union_right _ hB)]
      · -- `.unsplit v ∉ B.image .unsplit` by injectivity of `.unsplit`.
        have h_notimg : SplitNode.unsplit v ∉ B.image SplitNode.unsplit := by
          intro h
          obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
          cases hweq
          exact hB hw
        rw [if_neg h_notimg]
        -- LHS `flattenSplit (.unsplit (.unsplit v)) = .unsplit v`.
        change SplitNode.unsplit v = (if v ∈ A ∪ B then SplitNode.copy0 v else SplitNode.unsplit v)
        have hVU : v ∉ A ∪ B := fun h =>
          (Finset.mem_union.mp h).elim hA hB
        rw [if_neg hVU]
  -- Helper: `flattenSplit` collapses the two-stage `toCopy1` chain.
  -- Symmetric to `flatten_toCopy0_toCopy0`.
  have flatten_toCopy1_toCopy1 : ∀ (A B : Finset Node) (v : Node),
      flattenSplit (toCopy1 (B.image SplitNode.unsplit) (toCopy1 A v))
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
      change SplitNode.copy1 v = (if v ∈ A ∪ B then SplitNode.copy1 v else SplitNode.unsplit v)
      rw [if_pos (Finset.mem_union_left _ hA)]
    · rw [if_neg hA]
      by_cases hB : v ∈ B
      · have h_img : SplitNode.unsplit v ∈ B.image SplitNode.unsplit :=
          Finset.mem_image.mpr ⟨v, hB, rfl⟩
        rw [if_pos h_img]
        change SplitNode.copy1 v = (if v ∈ A ∪ B then SplitNode.copy1 v else SplitNode.unsplit v)
        rw [if_pos (Finset.mem_union_right _ hB)]
      · have h_notimg : SplitNode.unsplit v ∉ B.image SplitNode.unsplit := by
          intro h
          obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
          cases hweq
          exact hB hw
        rw [if_neg h_notimg]
        change SplitNode.unsplit v = (if v ∈ A ∪ B then SplitNode.copy1 v else SplitNode.unsplit v)
        have hVU : v ∉ A ∪ B := fun h =>
          (Finset.mem_union.mp h).elim hA hB
        rw [if_neg hVU]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  -- ===== Sub-goal 1: J for (a) =====
  -- `((G.J.image .unsplit).image .unsplit).image flattenSplit = G.J.image .unsplit`.
  -- Two applications of `Finset.image_image` reduce to
  -- `G.J.image (flattenSplit ∘ .unsplit ∘ .unsplit)`, and the inner
  -- composition reduces definitionally to `.unsplit` via the first
  -- pattern-match clause of `flattenSplit`.
  · change ((G.J.image SplitNode.unsplit).image SplitNode.unsplit).image flattenSplit
          = G.J.image SplitNode.unsplit
    rw [Finset.image_image, Finset.image_image]
    rfl
  -- ===== Sub-goal 2: V for (a) =====
  -- Componentwise extensionality on the iterated-vs-single output
  -- node sets.  See the V-component paragraph of the tex proof.
  · change ((((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0 ∪
              W₁.image SplitNode.copy1) \ (W₂.image SplitNode.unsplit)).image SplitNode.unsplit
            ∪ (W₂.image SplitNode.unsplit).image SplitNode.copy0
            ∪ (W₂.image SplitNode.unsplit).image SplitNode.copy1).image flattenSplit
          = (G.V \ (W₁ ∪ W₂)).image SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image SplitNode.copy0
            ∪ (W₁ ∪ W₂).image SplitNode.copy1
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy12 | hy3
      · rcases Finset.mem_union.mp hy12 with hy1 | hy2
        · -- `y ∈ (inner_diff).image .unsplit`.
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy1
          obtain ⟨hz_inner, hz_notW₂img⟩ := Finset.mem_sdiff.mp hz
          rcases Finset.mem_union.mp hz_inner with hz12 | hz3
          · rcases Finset.mem_union.mp hz12 with hz1 | hz2
            · -- `z = .unsplit v`, `v ∈ G.V \ W₁`.
              obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz1
              obtain ⟨hv_V, hv_notW₁⟩ := Finset.mem_sdiff.mp hv
              -- Disjointness with `W₂` from `hz_notW₂img`.
              have hv_notW₂ : v ∉ W₂ := fun h =>
                hz_notW₂img (Finset.mem_image.mpr ⟨v, h, rfl⟩)
              -- `flattenSplit (.unsplit (.unsplit v)) = .unsplit v`.
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
              refine Finset.mem_sdiff.mpr ⟨hv_V, ?_⟩
              intro hu
              exact (Finset.mem_union.mp hu).elim hv_notW₁ hv_notW₂
            · -- `z = .copy0 w`, `w ∈ W₁`.
              obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz2
              -- `flattenSplit (.unsplit (.copy0 w)) = .copy0 w`.
              refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
          · -- `z = .copy1 w`, `w ∈ W₁`.
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz3
            refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
        · -- `y = .copy0 (.unsplit w)`, `w ∈ W₂`.
          obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy2
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
      · -- `y = .copy1 (.unsplit w)`, `w ∈ W₂`.
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy3
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hx12 | hx3
      · rcases Finset.mem_union.mp hx12 with hx1 | hx2
        · -- `x = .unsplit v`, `v ∈ G.V \ (W₁ ∪ W₂)`.
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
          obtain ⟨hv_V, hv_notW₁₂⟩ := Finset.mem_sdiff.mp hv
          have hv_notW₁ : v ∉ W₁ := fun h => hv_notW₁₂ (Finset.mem_union_left _ h)
          have hv_notW₂ : v ∉ W₂ := fun h => hv_notW₁₂ (Finset.mem_union_right _ h)
          -- Take preimage `.unsplit (.unsplit v)`.
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.unsplit v), ?_, rfl⟩
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit v, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₁⟩, rfl⟩
          · intro h
            obtain ⟨v', hv'_mem, hv'_eq⟩ := Finset.mem_image.mp h
            cases hv'_eq
            exact hv_notW₂ hv'_mem
        · -- `x = .copy0 w`, `w ∈ W₁ ∪ W₂`.
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
          rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
          · -- `w ∈ W₁`: preimage `.unsplit (.copy0 w)`.
            refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.copy0 w), ?_, rfl⟩
            refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            refine Finset.mem_image.mpr ⟨SplitNode.copy0 w, ?_, rfl⟩
            refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
              exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
            · intro h
              obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
              cases hweq
          · -- `w ∈ W₂`: preimage `.copy0 (.unsplit w)`.
            refine Finset.mem_image.mpr ⟨SplitNode.copy0 (SplitNode.unsplit w), ?_, rfl⟩
            refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
            exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
      · -- `x = .copy1 w`, `w ∈ W₁ ∪ W₂`.
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx3
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.copy1 w), ?_, rfl⟩
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          refine Finset.mem_image.mpr ⟨SplitNode.copy1 w, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
          · intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
        · refine Finset.mem_image.mpr ⟨SplitNode.copy1 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 3: E for (a) =====
  -- The edge components decompose into three pieces after both
  -- splittings:
  --   * `G.E` edges, lifted to `(toCopy1 W₁_∪_W₂ v_1, toCopy0 W₁_∪_W₂ v_2)`;
  --   * inner-transfer edges `(.copy0 w, .copy1 w)` for `w ∈ W₁`;
  --   * outer-transfer edges `(.copy0 w, .copy1 w)` for `w ∈ W₂`.
  -- The latter two combine into `(W₁ ∪ W₂).image (fun w => (.copy0 w, .copy1 w))`,
  -- matching `single.E`.
  · -- Step 1: prove the three "lifted-piece" equalities separately, each
    --   of the form `((s.image f).image g).image (Prod.map ff) = s.image h`
    --   where `h` is the canonical single-step form.
    -- Step 2: combine them via `Finset.image_union` on the original
    --   compound LHS.
    have hG_E :
        ((G.E.image (fun e : Node × Node => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))).image
            (fun e => (toCopy1 (W₂.image SplitNode.unsplit) e.1,
                       toCopy0 (W₂.image SplitNode.unsplit) e.2))).image
          (Prod.map flattenSplit flattenSplit)
        = G.E.image (fun e : Node × Node =>
            (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr ?_
      intro e _
      change (flattenSplit (toCopy1 (W₂.image SplitNode.unsplit) (toCopy1 W₁ e.1)),
              flattenSplit (toCopy0 (W₂.image SplitNode.unsplit) (toCopy0 W₁ e.2)))
            = (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2)
      rw [flatten_toCopy0_toCopy0, flatten_toCopy1_toCopy1]
    have hW₁_tr :
        ((W₁.image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w))).image
            (fun e => (toCopy1 (W₂.image SplitNode.unsplit) e.1,
                       toCopy0 (W₂.image SplitNode.unsplit) e.2))).image
          (Prod.map flattenSplit flattenSplit)
        = W₁.image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr ?_
      intro w _
      change (flattenSplit (toCopy1 (W₂.image SplitNode.unsplit) (SplitNode.copy0 w)),
              flattenSplit (toCopy0 (W₂.image SplitNode.unsplit) (SplitNode.copy1 w)))
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
            (fun w : SplitNode Node => (SplitNode.copy0 w, SplitNode.copy1 w))).image
          (Prod.map flattenSplit flattenSplit)
        = W₂.image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr ?_
      intro w _
      rfl
    -- Combine: push `.image (Prod.map ff)` through unions, then apply
    -- `Finset.image_union` to the inner lift over `G.E ∪ W₁`.
    change ((G.E.image (fun e : Node × Node => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))
              ∪ W₁.image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w))).image
                (fun e => (toCopy1 (W₂.image SplitNode.unsplit) e.1,
                           toCopy0 (W₂.image SplitNode.unsplit) e.2))
            ∪ (W₂.image SplitNode.unsplit).image
                (fun w : SplitNode Node => (SplitNode.copy0 w, SplitNode.copy1 w))).image
              (Prod.map flattenSplit flattenSplit)
          = G.E.image (fun e : Node × Node => (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
            ∪ (W₁ ∪ W₂).image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w))
    simp only [Finset.image_union]
    rw [hG_E, hW₁_tr, hW₂_tr]
    -- Now LHS: (G.E.image (single_lift) ∪ W₁.image (single_transfer)) ∪
    --   W₂.image (single_transfer)
    --   RHS: G.E.image (single_lift) ∪ (W₁.image (single_transfer) ∪
    --   W₂.image (single_transfer))  (right-assoc from `simp` expanding
    --   `(W₁ ∪ W₂).image (transfer)` on the RHS).  Realign by
    --   `Finset.union_assoc`.
    rw [Finset.union_assoc]
  -- ===== Sub-goal 4: L for (a) =====
  -- The bidirected-edge component has a single piece: lifted edges
  -- `(toCopy0 (W₂.image .unsplit) (toCopy0 W₁ v_1), toCopy0 (...) (toCopy0 W₁ v_2))`
  -- from `G.L`, which `flattenSplit` collapses to `(toCopy0 (W₁ ∪ W₂) v_1,
  -- toCopy0 (W₁ ∪ W₂) v_2)`, matching `single.L`.
  · change ((G.L.image (fun e => (toCopy0 W₁ e.1, toCopy0 W₁ e.2))).image
                (fun e => (toCopy0 (W₂.image SplitNode.unsplit) e.1,
                           toCopy0 (W₂.image SplitNode.unsplit) e.2))).image
              (Prod.map flattenSplit flattenSplit)
          = G.L.image (fun e => (toCopy0 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro e _
    change (flattenSplit (toCopy0 (W₂.image SplitNode.unsplit) (toCopy0 W₁ e.1)),
            flattenSplit (toCopy0 (W₂.image SplitNode.unsplit) (toCopy0 W₁ e.2)))
          = (toCopy0 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2)
    rw [flatten_toCopy0_toCopy0, flatten_toCopy0_toCopy0]
  -- ===== Sub-goal 5: J for (b) =====
  -- Same shape as Sub-goal 1.
  · change ((G.J.image SplitNode.unsplit).image SplitNode.unsplit).image flattenSplit
          = G.J.image SplitNode.unsplit
    rw [Finset.image_image, Finset.image_image]
    rfl
  -- ===== Sub-goal 6: V for (b) =====
  -- Same shape as Sub-goal 2 with `W₁ ↔ W₂` swapped; the `W₁ ∪ W₂` on
  -- the RHS comes from `Finset.union_comm`.
  · change ((((G.V \ W₂).image SplitNode.unsplit ∪ W₂.image SplitNode.copy0 ∪
              W₂.image SplitNode.copy1) \ (W₁.image SplitNode.unsplit)).image SplitNode.unsplit
            ∪ (W₁.image SplitNode.unsplit).image SplitNode.copy0
            ∪ (W₁.image SplitNode.unsplit).image SplitNode.copy1).image flattenSplit
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
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.unsplit v), ?_, rfl⟩
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
          · refine Finset.mem_image.mpr ⟨SplitNode.copy0 (SplitNode.unsplit w), ?_, rfl⟩
            refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
            exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
          · refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.copy0 w), ?_, rfl⟩
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
        · refine Finset.mem_image.mpr ⟨SplitNode.copy1 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.copy1 w), ?_, rfl⟩
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          refine Finset.mem_image.mpr ⟨SplitNode.copy1 w, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
          · intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
  -- ===== Sub-goal 7: E for (b) =====
  -- Same shape as Sub-goal 3 with `W₁ ↔ W₂` swapped; the
  -- `flatten_toCopy0_toCopy0`/`flatten_toCopy1_toCopy1` helpers fire
  -- with `(A, B) = (W₂, W₁)`, giving `toCopy0/1 (W₂ ∪ W₁) v` on the RHS,
  -- which is `toCopy0/1 (W₁ ∪ W₂) v` after `Finset.union_comm`.
  · have hG_E :
        ((G.E.image (fun e : Node × Node => (toCopy1 W₂ e.1, toCopy0 W₂ e.2))).image
            (fun e => (toCopy1 (W₁.image SplitNode.unsplit) e.1,
                       toCopy0 (W₁.image SplitNode.unsplit) e.2))).image
          (Prod.map flattenSplit flattenSplit)
        = G.E.image (fun e : Node × Node =>
            (toCopy1 (W₂ ∪ W₁) e.1, toCopy0 (W₂ ∪ W₁) e.2)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr ?_
      intro e _
      change (flattenSplit (toCopy1 (W₁.image SplitNode.unsplit) (toCopy1 W₂ e.1)),
              flattenSplit (toCopy0 (W₁.image SplitNode.unsplit) (toCopy0 W₂ e.2)))
            = (toCopy1 (W₂ ∪ W₁) e.1, toCopy0 (W₂ ∪ W₁) e.2)
      rw [flatten_toCopy0_toCopy0, flatten_toCopy1_toCopy1]
    have hW₂_tr :
        ((W₂.image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w))).image
            (fun e => (toCopy1 (W₁.image SplitNode.unsplit) e.1,
                       toCopy0 (W₁.image SplitNode.unsplit) e.2))).image
          (Prod.map flattenSplit flattenSplit)
        = W₂.image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr ?_
      intro w _
      change (flattenSplit (toCopy1 (W₁.image SplitNode.unsplit) (SplitNode.copy0 w)),
              flattenSplit (toCopy0 (W₁.image SplitNode.unsplit) (SplitNode.copy1 w)))
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
            (fun w : SplitNode Node => (SplitNode.copy0 w, SplitNode.copy1 w))).image
          (Prod.map flattenSplit flattenSplit)
        = W₁.image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w)) := by
      rw [Finset.image_image, Finset.image_image]
      refine Finset.image_congr ?_
      intro w _
      rfl
    change ((G.E.image (fun e : Node × Node => (toCopy1 W₂ e.1, toCopy0 W₂ e.2))
              ∪ W₂.image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w))).image
                (fun e => (toCopy1 (W₁.image SplitNode.unsplit) e.1,
                           toCopy0 (W₁.image SplitNode.unsplit) e.2))
            ∪ (W₁.image SplitNode.unsplit).image
                (fun w : SplitNode Node => (SplitNode.copy0 w, SplitNode.copy1 w))).image
              (Prod.map flattenSplit flattenSplit)
          = G.E.image (fun e : Node × Node => (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
            ∪ (W₁ ∪ W₂).image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w))
    rw [Finset.union_comm W₁ W₂]
    simp only [Finset.image_union]
    rw [hG_E, hW₂_tr, hW₁_tr]
    rw [Finset.union_assoc]
  -- ===== Sub-goal 8: L for (b) =====
  -- Same shape as Sub-goal 4 with `W₁ ↔ W₂` swapped.
  · change ((G.L.image (fun e => (toCopy0 W₂ e.1, toCopy0 W₂ e.2))).image
                (fun e => (toCopy0 (W₁.image SplitNode.unsplit) e.1,
                           toCopy0 (W₁.image SplitNode.unsplit) e.2))).image
              (Prod.map flattenSplit flattenSplit)
          = G.L.image (fun e => (toCopy0 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
    rw [Finset.union_comm W₁ W₂]
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro e _
    change (flattenSplit (toCopy0 (W₁.image SplitNode.unsplit) (toCopy0 W₂ e.1)),
            flattenSplit (toCopy0 (W₁.image SplitNode.unsplit) (toCopy0 W₂ e.2)))
          = (toCopy0 (W₂ ∪ W₁) e.1, toCopy0 (W₂ ∪ W₁) e.2)
    rw [flatten_toCopy0_toCopy0, flatten_toCopy0_toCopy0]

end CDMG

end Causality
