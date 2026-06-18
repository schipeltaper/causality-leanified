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

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`); load-bearing for this row's statement
--   because the signature constructs `W₁ ∪ W₂` (needs `Finset.union`),
--   `W₂.image SplitNode.unsplit` (needs `Finset.image`), and four
--   `Finset.image f` equalities inside `eqViaNodeMap` — each of which
--   requires decidable equality on `Node` (and, via the auto-derived
--   `DecidableEq (SplitNode Node)` and
--   `DecidableEq (SplitNode (SplitNode Node))` instances inherited
--   from `def_3_11`'s `SplitNode` `inductive`, on the iterated and
--   single-step carriers as well).  Stronger instances (`Fintype`,
--   `LinearOrder`) are not needed at the statement level.
-- claim_3_10 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_10 --- end helper

-- ## Helper: well-typedness of the iterated SWIG splitting
--
-- For `W₁ ⊆ G.V`, `W₂ ⊆ G.V` disjoint, `W₂.image .unsplit` sits inside
-- the output-node set of `G.nodeSplittingHard hG W₁ hW₁` —
-- specifically, inside the `(G.V ∖ W₁).image .unsplit` piece by
-- disjointness.  This discharges the `hW` precondition of `def_3_12`'s
-- `nodeSplittingHard` for the *outer* SWIG in
-- `(G_{swig(W₁)})_{swig(W₂)}`.
--
-- ## Design choice
--
-- *Two-piece-union analogue of `claim_3_7`'s
--   `image_unsplit_subset_nodeSplittingOn_V`.*  `def_3_12`'s
--   `V_{swig(W₁)} = (G.V ∖ W₁).image .unsplit ∪ W₁.image .copy0`
--   contains only the `.copy0` (output-side `^o`) tagged copies of
--   `W₁`, with the `.copy1` (input-side `^i`) tagged copies *reclassified
--   to `J_{swig(W₁)}`* (cf.\ `NodeSplittingHard.lean` design bullet on
--   the literal three-piece-union-into-two-piece-union departure from
--   `def_3_11`).  The membership chain is therefore one
--   `Finset.mem_union_left` shorter than the spl analogue — the
--   `W₁.image .copy1` summand simply does not appear, and the proof
--   structure is otherwise identical (case-split on `v ∈ W₂` lifts to
--   `.unsplit v ∈ (G.V ∖ W₁).image .unsplit` via the disjointness
--   `v ∉ W₁`).
--
-- *Implicit `hG : G.IsCADMG` to match `nodeSplittingHard`'s signature.*
--   `def_3_12`'s `nodeSplittingHard` takes
--   `(G) (hG : G.IsCADMG) (W) (hW)` — see `NodeSplittingHard.lean`
--   design bullet (d) for the LN-faithfulness rationale.  The helper
--   carries `hG` as an implicit argument because the conclusion
--   `(G.nodeSplittingHard hG W₁ hW₁).V` mentions `hG` on the
--   `nodeSplittingHard` application (even though the `.V` field itself
--   does not consume `hG`, the type of the membership conclusion does
--   reference `hG` via the function application).  Implicit so call
--   sites elaborate without spelling out `hG` separately when it is
--   already in scope.
--
-- *`Disjoint W₁ W₂`, not `W₂ ⊆ G.V ∖ W₁`.*  Same canonical Mathlib
--   `Finset` shape used in `claim_3_7`'s analogue; `Finset.disjoint_right`
--   consumes / produces this form directly.  The LN's
--   "$W_1 \cap W_2 = \emptyset$" reads as exactly this `Disjoint`.
--
-- *Symmetric in `W₁` / `W₂`.*  Applied as
--   `image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj` for the
--   (a) direction (inner SWIG on `W₁`, outer lifts `W₂.image .unsplit`)
--   and as `image_unsplit_subset_nodeSplittingHard_V hW₂ hW₁ hDisj.symm`
--   for the (b) direction (inner SWIG on `W₂`, outer lifts
--   `W₁.image .unsplit`).  A single helper covers both directions; the
--   `Disjoint.symm` rotation does not change the lemma's content.
--
-- *`private`, with helper markers.*  Mirrors the
--   `subset_carrier_of_hardInterventionOn` pattern in
--   `HardInterventionsCommute.lean` (`claim_3_4`) and the
--   `image_unsplit_subset_nodeSplittingOn_V` pattern in
--   `TwoDisjointNode.lean` (`claim_3_7`).  The helper is load-bearing
--   for the main statement to type-check (it supplies the inner-`hW`
--   argument of the outer `nodeSplittingHard`); the website builder
--   pulls it out alongside the rendered statement.  `private`
--   localises it to this file.
--
-- *Scope: discharges only the inner-`hW` precondition.*  Of the two
--   propositional preconditions of the outer `nodeSplittingHard` —
--   `hG : (inner CDMG).IsCADMG` and `hW : (outer W) ⊆ (inner V)` —
--   this helper handles only the second.  The first is the *separately
--   proven* `claim_3_9.swigAcyclic`; the two helpers are complementary
--   and *both* are needed for the iterated SWIG to type-check.  Keeping
--   them as separate named lemmas (rather than a single combined
--   "iterated SWIG is well-typed" predicate) follows the LN's split of
--   "well-typedness" into a `hG`-piece (claim_3_9) and a `hW`-piece
--   (the disjointness consequence); the LN itself never combines them.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: image_unsplit_subset_nodeSplittingHard_V
-- claim_3_10 --- start helper
private lemma image_unsplit_subset_nodeSplittingHard_V
    {G : CDMG Node} {hG : G.IsCADMG} {W₁ W₂ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂.image SplitNode.unsplit ⊆ (G.nodeSplittingHard hG W₁ hW₁).V
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
-- REFACTOR-BLOCK-ORIGINAL-END: image_unsplit_subset_nodeSplittingHard_V

-- ref: claim_3_10
--
-- For any CADMG `G` and any two disjoint subsets `W₁, W₂ ⊆ G.V`, the
-- LN's triple equality
--   `(G_{swig(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{swig(W₁)}
--     = G_{swig(W₁ ∪ W₂)}`
-- decomposes (per the rewritten tex's (a) / (b) split) into two CDMG
-- equalities read up to the canonical flatten map `flattenSplit`
-- imported from `claim_3_7`'s file:
--   (a) `(G_{swig(W₁)})_{swig(W₂)} = G_{swig(W₁ ∪ W₂)}`,
--   (b) `(G_{swig(W₂)})_{swig(W₁)} = G_{swig(W₁ ∪ W₂)}`.
-- Transitivity of equality recovers the LN's "swap symmetry" reading
-- from (a) ∧ (b).
/-
LN tex (rewritten canonical statement for `claim_3_10`):

  Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ V` two subsets of
  the output-node set of `G`, with `W₁ ∩ W₂ = ∅`.  Then
    (a) `(G_{swig(W₁)})_{swig(W₂)} = G_{swig(W₁ ∪ W₂)}`,
    (b) `(G_{swig(W₂)})_{swig(W₁)} = G_{swig(W₁ ∪ W₂)}`,
  read up to the canonical bijection of carriers induced by
  `def_3_12`'s unsplit-injection convention.

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CADMG and `W_1, W_2 ⊆ V` two disjoint
  subsets of the output nodes from `G`.  Then the CADMG obtained
  from first node-splitting on `W_1` and then node-splitting on `W_2`
  is the same CADMG that arises from first node-splitting on `W_2`
  and then node-splitting on `W_1`:
    `(G_{swig(W_1)})_{swig(W_2)} = (G_{swig(W_2)})_{swig(W_1)}
       = G_{swig(W_1 ⊍ W_2)}`.

(The "CADMG" wording in the LN's prose is reconciled with the Lean
`CDMG`-typed signature via the canonical tex's "Reading of CDMG
versus CADMG" paragraph: `def_3_12`'s `nodeSplittingHard` is
`CDMG → CDMG`, and the upgrade of both sides to `CADMG` is recovered
by transporting `claim_3_9`'s `swigAcyclic` witness along the
asserted CDMG equality.)
-/
-- ## Design choice
--
-- *One theorem returning a conjunction `(a) ∧ (b)`, with the
--   joint-intervention `G_{swig(W₁ ∪ W₂)}` as the shared right-hand
--   side.*  Lean has no native triple equality; the rewritten tex's
--   `enumerate[label=(\alph*)]` block makes the two-binary-equality
--   decomposition load-bearing.  The same conjunction shape appears
--   in `HardInterventionsCommute` (claim_3_4) and in the regular-spl
--   sibling `TwoDisjointNode` (claim_3_7); reusing the pattern keeps
--   all three "commute" rows callable at parallel `.1` / `.2`
--   projections.  The LN's swap-symmetry reading
--   `(G_{swig(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{swig(W₁)}` is
--   recovered from (a) ∧ (b) via transitivity through the shared
--   right-hand side.
--
-- *Why the LHS-equals-RHS form `eqViaNodeMap iter single flattenSplit`,
--   not `eqViaNodeMap iter₁₂ iter₂₁ (refl)` or any other "direct"
--   equality between the two iterated forms.*  At the Lean level,
--   `iter₁₂ := (G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard _
--   (W₂.image .unsplit) _` and `iter₂₁ := (G.nodeSplittingHard hG W₂ hW₂).nodeSplittingHard
--   _ (W₁.image .unsplit) _` share the carrier type
--   `SplitNode (SplitNode Node)`, but their constructor wrappings on
--   the same underlying graph node disagree: a node `w₁ ∈ W₁`
--   appears as `.unsplit (.copy0 w₁)` in `iter₁₂`'s `V` field but as
--   `.copy0 (.unsplit w₁)` in `iter₂₁`'s `V` field (and analogously a
--   node `w₁ ∈ W₁` appears as `.unsplit (.copy1 w₁)` in `iter₁₂`'s
--   `J` field but as `.copy1 (.unsplit w₁)` in `iter₂₁`'s `J` field).
--   A literal `iter₁₂ = iter₂₁` is therefore *false* as a Lean
--   proposition — the four `Finset` fields contain different
--   constructor combinations even though they describe the same
--   abstract graph.  Routing both sides through the canonical
--   single-step `G_{swig(W₁ ∪ W₂)}` via the *same* `flattenSplit`
--   image-level relabelling is the mathematically faithful encoding;
--   swap symmetry between `iter₁₂` and `iter₂₁` is then recovered as
--   the transitive composite `eqViaNodeMap iter₁₂ single flattenSplit
--   ∧ eqViaNodeMap iter₂₁ single flattenSplit`, not as a raw `=`.
--   Identical reasoning underlies `claim_3_7`'s `TwoDisjointNode`
--   statement; we reuse the same encoding.
--
-- *Reuse `flattenSplit` and `eqViaNodeMap` from `claim_3_7`'s solved
--   file.*  Both definitions are purely constructor-algebra and
--   operate on the shared `SplitNode (SplitNode Node)` carrier
--   regardless of which of `def_3_11` / `def_3_12` produced the
--   nested splitting.  The cases that actually inhabit `iter₁₂`'s
--   carrier (and `iter₂₁`'s) under `def_3_12` are a *subset* of the
--   cases that inhabit them under `def_3_11` — specifically, the
--   `.unsplit (.copy1 _)` / `.copy1 (.unsplit _)` patterns appear in
--   the `J` fields (not the `V` fields) of the SWIG, but `flattenSplit`
--   collapses them identically — so the same flatten map handles both
--   the spl and SWIG iterated forms.  See the file header for the
--   "Reuse from `claim_3_7`'s solved file" paragraph and the
--   `claim_3_7` design block for `flattenSplit` / `eqViaNodeMap`'s
--   own design rationale (function-not-Equiv, four-conjunct
--   componentwise equality, image-level reasoning under a non-bijective
--   carrier function).
--
-- *Disjoint-union encoding: `W₁ ∪ W₂` together with `Disjoint W₁ W₂`,
--   not `Sum`-based `⊔`.*  Matches `def_3_12`'s `nodeSplittingHard` API,
--   which takes `W : Finset Node` and `hW : W ⊆ G.V` — so the natural
--   right-hand side is `G.nodeSplittingHard hG (W₁ ∪ W₂)
--   (Finset.union_subset hW₁ hW₂)`.  The `Disjoint W₁ W₂` hypothesis
--   (Mathlib's `Finset.Disjoint`, i.e.\ intersection-empty on
--   `Finset`) is load-bearing for the well-typedness of the iterated
--   splitting — the inner-`hW` proof
--   `image_unsplit_subset_nodeSplittingHard_V` consumes it, per the
--   rewritten tex's "Well-typedness of the iterated SWIG" paragraph.
--   It plays well with `Finset.union_subset` for the right-hand side
--   hypothesis `W₁ ∪ W₂ ⊆ G.V`, with no `Finset.disjUnion` coercion
--   gymnastics needed.  The LN's "$W_1 \cap W_2 = \emptyset$" reads
--   as exactly this `Disjoint`; matches `claim_3_7`'s choice exactly.
--
-- *`(G : CDMG Node) (hG : G.IsCADMG)` split rather than a bundled
--   `CADMG` structure.*  Section 3.1 (`def_3_7`) introduces CADMG as the
--   propositional predicate `IsCADMG : CDMG Node → Prop` (definitionally
--   `IsAcyclic`) on top of the existing `CDMG` `structure`, *not* as a
--   bundled subtype `{G : CDMG Node // G.IsAcyclic}` — see
--   `NodeSplittingHard.lean` design bullet (d) for the chapter-wide
--   rationale.  This row inherits that convention: `G` carries the
--   `CDMG` data, `hG` carries the acyclicity witness as a separate
--   `Prop`-valued argument, and `nodeSplittingHard` consumes the pair.
--   Bundling would force the LN's plain "$G$" identifier to be an
--   awkward `.val`-projection at every reference; the unbundled shape
--   keeps the asserted equality between two CDMGs (not CADMGs) at
--   exactly the form the LN writes.
--
-- *`swigAcyclic G hG Wᵢ hWᵢ` (= `claim_3_9`) feeds the *outer*
--   iterated SWIG's `hG` slot.*  The iterated form
--   `(G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard ?_ (W₂.image
--   .unsplit) ?_` demands an `IsCADMG` witness on the inner CDMG —
--   *this is non-trivial* and is precisely the content of
--   `claim_3_9.swigAcyclic`: `(G.nodeSplittingHard hG W hW).IsAcyclic`.
--   The definitional unfolding `IsCADMG := IsAcyclic` (def_3_7 item i)
--   lets this `IsAcyclic` witness be supplied directly where an
--   `IsCADMG` argument is expected, with no manual coercion.  Without
--   claim_3_9 the iterated SWIG would not type-check at all (Manager A
--   ordered claim_3_9 before claim_3_10 specifically to discharge this
--   dependency).  The same `swigAcyclic G hG Wᵢ hWᵢ` plumbing
--   construction is the canonical pattern any later row needing
--   iterated / nested SWIGs (e.g.\ proofs in the do-calculus and
--   counterfactual chapters) will reuse.
--
-- *Result is a CDMG (`eqViaNodeMap` on `CDMG (SplitNode (SplitNode Node))`
--   and `CDMG (SplitNode Node)`), not a CADMG.*  Per the canonical
--   tex's "Reading of CDMG versus CADMG" paragraph and the chapter
--   pattern: `nodeSplittingHard` returns `CDMG`, the CADMG upgrade is
--   carried by `claim_3_9`'s `swigAcyclic` separately, and the
--   asserted equality is read at the CDMG level componentwise on the
--   four `Finset` data fields.  Both iterated and single-step graphs
--   inhabit `CDMG (SplitNode _)` (with the iterated form at
--   `SplitNode (SplitNode Node)` and the single-step form at
--   `SplitNode Node`); no `CADMG` wrapper appears anywhere in the
--   signature, in line with `claim_3_7`'s analogous choice.
--
-- *Carrier-mismatch wrinkle handled via `eqViaNodeMap` + `flattenSplit`.*
--   See the module-level docstring "Carrier-mismatch wrinkle" paragraph.
--   The LN's "equality of CDMGs read up to the canonical bijection of
--   carriers" is rendered as `eqViaNodeMap iterated single flattenSplit`:
--   the four `Finset` data fields of the iterated splitting, after
--   applying `flattenSplit` field-wise, coincide with the four data
--   fields of the single splitting.  This is the strongest equality
--   form available without introducing quotient types or a `CDMG.Iso`
--   layer.  Same encoding as `claim_3_7`.
--
-- ## Known limitations of the chosen shape
--
-- *Image-level, not type-level, identification.*  `eqViaNodeMap`
--   asserts equality of the four `Finset` data fields under
--   `Finset.image flattenSplit`; it does *not* exhibit a type-level
--   bijection between `CDMG (SplitNode (SplitNode Node))` and
--   `CDMG (SplitNode Node)` (no such bijection exists — see the
--   `flattenSplit` design block in `TwoDisjointNode.lean`).  A consumer
--   that needs to *transport* a separate property from the iterated to
--   the single form (e.g.\ "every node in the iterated SWIG has parents
--   in the single SWIG") would need an additional lemma threading the
--   image-level equality through the property; this row delivers only
--   the four `Finset` equalities, not a general transport principle.
--
-- *No `CADMG`-level upgrade of the equality.*  This theorem lives at
--   the CDMG level.  A downstream consumer wanting "the two SWIGs are
--   equal *as CADMGs*" must compose this statement with `claim_3_9`'s
--   `swigAcyclic` on each side — there is no single combined lemma.
--   Acceptable because the CADMG status is a `Prop`-valued predicate
--   uniquely determined by the underlying CDMG data, so the image-level
--   CDMG equality plus the two `swigAcyclic` applications recover the
--   CADMG-level reading without ambiguity.
--
-- *Swap symmetry `iter₁₂ ↔ iter₂₁` is derived, not stated.*  The LN's
--   reading "first $W_1$ then $W_2$ equals first $W_2$ then $W_1$"
--   becomes the transitive composite of (a) and (b), not a third
--   `eqViaNodeMap iter₁₂ iter₂₁ id` conjunct (which would not type-check
--   because the two iterated carriers, though sharing the type
--   `SplitNode (SplitNode Node)`, contain different constructor
--   combinations on the same underlying node — see the LHS-equals-RHS
--   bullet above).  Consumers wanting the swap reading apply
--   transitivity on the conjunction.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: twoDisjointNodeSplittingHardCommute
-- claim_3_10 -- start statement
theorem twoDisjointNodeSplittingHardCommute (G : CDMG Node)
    (hG : G.IsCADMG) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    eqViaNodeMap
        ((G.nodeSplittingHard hG W₁ hW₁).nodeSplittingHard
            (swigAcyclic G hG W₁ hW₁)
            (W₂.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj))
        (G.nodeSplittingHard hG (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenSplit
      ∧
    eqViaNodeMap
        ((G.nodeSplittingHard hG W₂ hW₂).nodeSplittingHard
            (swigAcyclic G hG W₂ hW₂)
            (W₁.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingHard_V hW₂ hW₁ hDisj.symm))
        (G.nodeSplittingHard hG (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenSplit
-- claim_3_10 -- end statement
  := by
  -- The proof follows the verified tex proof at
  -- `tex/claim_3_10_proof_TwoDisjointNode.tex`, working componentwise on
  -- the four `Finset` data fields `(J, V, E, L)` of each CDMG, for each
  -- of the two iteration orders (a) and (b).
  --
  -- The structure parallels `claim_3_7`'s `TwoDisjointNode.lean`, with
  -- three SWIG-specific departures from the regular-spl proof:
  --   * J now has a non-trivial flatten-image — the `W^i = .copy1`
  --     copies sit in `J_{swig}` (per `def_3_12` item i), so the J
  --     sub-goals match the (smaller-but-non-trivial) shape of the V
  --     sub-goals from `claim_3_7` rather than the trivial
  --     `G.J.image .unsplit`-only shape;
  --   * V has only two pieces (`(V ∖ W).image .unsplit ∪ W.image
  --     .copy0`) instead of three — the `W.image .copy1` summand is
  --     reclassified to J;
  --   * E has only the lifted-edges clause (no transfer edges) — the
  --     SWIG construction omits `def_3_11`'s
  --     `W.image (fun w => (.copy0 w, .copy1 w))` summand, so the E
  --     sub-goals are a single `Finset.image_image` collapse without
  --     the three-piece union juggling of `claim_3_7`'s E proof.
  -- L is unchanged from `claim_3_7`: same one-sided
  -- `(toCopy0, toCopy0)`-lift, same `flatten_toCopy0_toCopy0` collapse.
  --
  -- Helper: `flattenSplit` collapses the two-stage `toCopy0` chain to
  -- the single `toCopy0 (A ∪ B)`.  Reused verbatim from `claim_3_7`'s
  -- proof body; constructor-algebra fact, no `Disjoint` hypothesis
  -- needed.
  have flatten_toCopy0_toCopy0 : ∀ (A B : Finset Node) (v : Node),
      flattenSplit (toCopy0 (B.image SplitNode.unsplit) (toCopy0 A v))
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
      change SplitNode.copy0 v = (if v ∈ A ∪ B then SplitNode.copy0 v else SplitNode.unsplit v)
      rw [if_pos (Finset.mem_union_left _ hA)]
    · rw [if_neg hA]
      by_cases hB : v ∈ B
      · have h_img : SplitNode.unsplit v ∈ B.image SplitNode.unsplit :=
          Finset.mem_image.mpr ⟨v, hB, rfl⟩
        rw [if_pos h_img]
        change SplitNode.copy0 v = (if v ∈ A ∪ B then SplitNode.copy0 v else SplitNode.unsplit v)
        rw [if_pos (Finset.mem_union_right _ hB)]
      · have h_notimg : SplitNode.unsplit v ∉ B.image SplitNode.unsplit := by
          intro h
          obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
          cases hweq
          exact hB hw
        rw [if_neg h_notimg]
        change SplitNode.unsplit v = (if v ∈ A ∪ B then SplitNode.copy0 v else SplitNode.unsplit v)
        have hVU : v ∉ A ∪ B := fun h =>
          (Finset.mem_union.mp h).elim hA hB
        rw [if_neg hVU]
  -- Helper: same collapse for `toCopy1` chains.  Symmetric to
  -- `flatten_toCopy0_toCopy0`.
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
  -- `iter₁₂.J = (G.J.image .unsplit ∪ W₁.image .copy1).image .unsplit ∪
  --              (W₂.image .unsplit).image .copy1`.  Three constructor
  -- combinations inhabit the iterated J carrier:
  --   `.unsplit (.unsplit j)` for `j ∈ G.J`
  --     ↦ `flattenSplit` first clause ↦ `.unsplit j`,
  --   `.unsplit (.copy1 w)` for `w ∈ W₁`
  --     ↦ `flattenSplit` first clause ↦ `.copy1 w`,
  --   `.copy1 (.unsplit w)` for `w ∈ W₂`
  --     ↦ `flattenSplit` `.copy1 (.unsplit w) => .copy1 w` clause ↦ `.copy1 w`.
  -- The three pieces line up with `single.J = G.J.image .unsplit ∪
  -- (W₁ ∪ W₂).image .copy1`.  Done by `ext` extensionality (the `rw`
  -- chain via `Finset.image_image` leaves function-composition residues
  -- that don't auto-`rfl` even though they reduce pointwise).
  · change ((G.J.image SplitNode.unsplit ∪ W₁.image SplitNode.copy1).image SplitNode.unsplit
              ∪ (W₂.image SplitNode.unsplit).image SplitNode.copy1).image flattenSplit
          = G.J.image SplitNode.unsplit ∪ (W₁ ∪ W₂).image SplitNode.copy1
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy1 | hy2
      · -- `y ∈ (G.J.image .unsplit ∪ W₁.image .copy1).image .unsplit`
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy1
        rcases Finset.mem_union.mp hz with hz1 | hz2
        · -- `z = .unsplit j`, `j ∈ G.J`
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz1
          refine Finset.mem_union_left _ ?_
          exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
        · -- `z = .copy1 w`, `w ∈ W₁`
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz2
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
      · -- `y = .copy1 (.unsplit w)`, `w ∈ W₂`
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy2
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · -- `x = .unsplit j`, `j ∈ G.J`
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx1
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.unsplit j), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit j, ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      · -- `x = .copy1 w`, `w ∈ W₁ ∪ W₂`
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · -- `w ∈ W₁`: preimage `.unsplit (.copy1 w)`
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.copy1 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.copy1 w, ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · -- `w ∈ W₂`: preimage `.copy1 (.unsplit w)`
          refine Finset.mem_image.mpr ⟨SplitNode.copy1 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 2: V for (a) =====
  -- Componentwise extensionality on the iterated-vs-single output node
  -- sets.  See the V-component paragraph of the tex proof.  Two-piece
  -- union per side (no `.copy1` summand) — simpler than `claim_3_7`'s
  -- three-piece V proof.
  · change ((((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0) \
              (W₂.image SplitNode.unsplit)).image SplitNode.unsplit
            ∪ (W₂.image SplitNode.unsplit).image SplitNode.copy0).image flattenSplit
          = (G.V \ (W₁ ∪ W₂)).image SplitNode.unsplit ∪ (W₁ ∪ W₂).image SplitNode.copy0
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hy with hy1 | hy2
      · -- `y ∈ (inner_diff).image .unsplit`.
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy1
        obtain ⟨hz_inner, hz_notW₂img⟩ := Finset.mem_sdiff.mp hz
        rcases Finset.mem_union.mp hz_inner with hz1 | hz2
        · -- `z = .unsplit v`, `v ∈ G.V \ W₁`.
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz1
          obtain ⟨hv_V, hv_notW₁⟩ := Finset.mem_sdiff.mp hv
          have hv_notW₂ : v ∉ W₂ := fun h =>
            hz_notW₂img (Finset.mem_image.mpr ⟨v, h, rfl⟩)
          -- `flattenSplit (.unsplit (.unsplit v)) = .unsplit v`.
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨hv_V, ?_⟩
          intro hu
          exact (Finset.mem_union.mp hu).elim hv_notW₁ hv_notW₂
        · -- `z = .copy0 w`, `w ∈ W₁`.
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz2
          -- `flattenSplit (.unsplit (.copy0 w)) = .copy0 w`.
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, Finset.mem_union_left _ hw, rfl⟩
      · -- `y = .copy0 (.unsplit w)`, `w ∈ W₂`.
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy2
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy'
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, Finset.mem_union_right _ hw, rfl⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · -- `x = .unsplit v`, `v ∈ G.V \ (W₁ ∪ W₂)`.
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨hv_V, hv_notW₁₂⟩ := Finset.mem_sdiff.mp hv
        have hv_notW₁ : v ∉ W₁ := fun h => hv_notW₁₂ (Finset.mem_union_left _ h)
        have hv_notW₂ : v ∉ W₂ := fun h => hv_notW₁₂ (Finset.mem_union_right _ h)
        -- Take preimage `.unsplit (.unsplit v)`.
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.unsplit v), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit v, ?_, rfl⟩
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · refine Finset.mem_union_left _ ?_
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
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.copy0 w, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
          · intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
        · -- `w ∈ W₂`: preimage `.copy0 (.unsplit w)`.
          refine Finset.mem_image.mpr ⟨SplitNode.copy0 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 3: E for (a) =====
  -- Single-piece edge image (no transfer edges per `def_3_12`).  Two
  -- `Finset.image_image` collapses + `Finset.image_congr` + the
  -- `flatten_toCopy{0,1}_toCopy{0,1}` helpers reduce the iterated
  -- lifting to the single-step lifting.
  · change ((G.E.image (fun e : Node × Node => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))).image
              (fun e => (toCopy1 (W₂.image SplitNode.unsplit) e.1,
                         toCopy0 (W₂.image SplitNode.unsplit) e.2))).image
            (Prod.map flattenSplit flattenSplit)
          = G.E.image (fun e : Node × Node =>
              (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro e _
    change (flattenSplit (toCopy1 (W₂.image SplitNode.unsplit) (toCopy1 W₁ e.1)),
            flattenSplit (toCopy0 (W₂.image SplitNode.unsplit) (toCopy0 W₁ e.2)))
          = (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2)
    rw [flatten_toCopy0_toCopy0, flatten_toCopy1_toCopy1]
  -- ===== Sub-goal 4: L for (a) =====
  -- Same shape as `claim_3_7`'s L proof: single piece, both endpoints
  -- via `toCopy0`, collapse via `flatten_toCopy0_toCopy0` twice.
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
  -- Same shape as Sub-goal 1 with `W₁ ↔ W₂` swapped.
  · change ((G.J.image SplitNode.unsplit ∪ W₂.image SplitNode.copy1).image SplitNode.unsplit
              ∪ (W₁.image SplitNode.unsplit).image SplitNode.copy1).image flattenSplit
          = G.J.image SplitNode.unsplit ∪ (W₁ ∪ W₂).image SplitNode.copy1
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
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.unsplit j), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit j, ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · -- `w ∈ W₁`: preimage `.copy1 (.unsplit w)` (W₁ is the outer split set)
          refine Finset.mem_image.mpr ⟨SplitNode.copy1 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · -- `w ∈ W₂`: preimage `.unsplit (.copy1 w)` (W₂ is the inner split set)
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.copy1 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.copy1 w, ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 6: V for (b) =====
  -- Same shape as Sub-goal 2 with `W₁ ↔ W₂` swapped.
  · change ((((G.V \ W₂).image SplitNode.unsplit ∪ W₂.image SplitNode.copy0) \
              (W₁.image SplitNode.unsplit)).image SplitNode.unsplit
            ∪ (W₁.image SplitNode.unsplit).image SplitNode.copy0).image flattenSplit
          = (G.V \ (W₁ ∪ W₂)).image SplitNode.unsplit ∪ (W₁ ∪ W₂).image SplitNode.copy0
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
        refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.unsplit v), ?_, rfl⟩
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
        · refine Finset.mem_image.mpr ⟨SplitNode.copy0 (SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · refine Finset.mem_image.mpr ⟨SplitNode.unsplit (SplitNode.copy0 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨SplitNode.copy0 w, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
          · intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
  -- ===== Sub-goal 7: E for (b) =====
  -- Same shape as Sub-goal 3 with `W₁ ↔ W₂` swapped; `Finset.union_comm`
  -- on the RHS flips `W₁ ∪ W₂` to `W₂ ∪ W₁` before the helpers fire.
  · change ((G.E.image (fun e : Node × Node => (toCopy1 W₂ e.1, toCopy0 W₂ e.2))).image
              (fun e => (toCopy1 (W₁.image SplitNode.unsplit) e.1,
                         toCopy0 (W₁.image SplitNode.unsplit) e.2))).image
            (Prod.map flattenSplit flattenSplit)
          = G.E.image (fun e : Node × Node =>
              (toCopy1 (W₁ ∪ W₂) e.1, toCopy0 (W₁ ∪ W₂) e.2))
    rw [Finset.union_comm W₁ W₂]
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro e _
    change (flattenSplit (toCopy1 (W₁.image SplitNode.unsplit) (toCopy1 W₂ e.1)),
            flattenSplit (toCopy0 (W₁.image SplitNode.unsplit) (toCopy0 W₂ e.2)))
          = (toCopy1 (W₂ ∪ W₁) e.1, toCopy0 (W₂ ∪ W₁) e.2)
    rw [flatten_toCopy0_toCopy0, flatten_toCopy1_toCopy1]
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
-- REFACTOR-BLOCK-ORIGINAL-END: twoDisjointNodeSplittingHardCommute

end CDMG

namespace refactor_CDMG

-- ## Refactor port — REPLACEMENT blocks for the `cdmg_typed_edges` design
--
-- The two `REFACTOR-BLOCK-REPLACEMENT` blocks below port the
-- pre-refactor declarations in this file to the post-refactor
-- `def_3_1` / `def_3_12` shapes (`refactor_CDMG` with
-- `L : Finset (Sym2 Node)`; `refactor_nodeSplittingHard` with
-- `L := G.L.image (Sym2.map (refactor_toCopy0 W))`).  Each block
-- mirrors its ORIGINAL above with the prefix `refactor_` and the
-- type / operation substitutions:
--
--   * `CDMG → refactor_CDMG`
--   * `IsCADMG → refactor_IsCADMG`
--   * `SplitNode → refactor_SplitNode`
--   * `toCopy0 / toCopy1 → refactor_toCopy0 / refactor_toCopy1`
--   * `nodeSplittingHard → refactor_nodeSplittingHard`
--   * `swigAcyclic → refactor_swigAcyclic`
--   * `flattenSplit / eqViaNodeMap / image_unsplit_subset_…` →
--     same with the `refactor_` prefix (imported from
--     `TwoDisjointNode.lean`'s refactor twin for the first two)
--
-- The J/V/E sides of the main theorem port mechanically — same
-- tactics, just renames — because `refactor_nodeSplittingHard`'s
-- J/V/E fields are unchanged from `nodeSplittingHard`'s (the
-- refactor changes only the L side).  Only the L-side (sub-goals
-- 4 and 8) is structurally reworked: ordered-pair lifting via
-- `Prod.map flattenSplit flattenSplit` becomes `Sym2`-quotient
-- lifting via `Sym2.map refactor_flattenSplit`.  The rework uses
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
-- (`CDMG → refactor_CDMG`), the splitting operation
-- (`nodeSplittingHard → refactor_nodeSplittingHard`), the
-- acyclicity predicate (`IsCADMG → refactor_IsCADMG`), and the
-- unsplit-injection constructor
-- (`SplitNode.unsplit → refactor_SplitNode.unsplit`) change.  The
-- proof body uses the same `Finset.mem_sdiff` /
-- `Finset.disjoint_right` machinery — the V-side of
-- `refactor_nodeSplittingHard` is structurally identical to the
-- pre-refactor `nodeSplittingHard`'s V-side (refactor changes
-- only the L-channel), so the lemma carries over verbatim with
-- only the rename pass.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: image_unsplit_subset_nodeSplittingHard_V (was: refactor_image_unsplit_subset_nodeSplittingHard_V)
-- claim_3_10 --- start helper
private lemma refactor_image_unsplit_subset_nodeSplittingHard_V
    {G : refactor_CDMG Node} {hG : G.refactor_IsCADMG}
    {W₁ W₂ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂.image refactor_SplitNode.unsplit ⊆
      (G.refactor_nodeSplittingHard hG W₁ hW₁).V
-- claim_3_10 --- end helper
:= by
  intro x hx
  obtain ⟨v, hvW₂, rfl⟩ := Finset.mem_image.mp hx
  -- `(G.refactor_nodeSplittingHard hG W₁ hW₁).V` unfolds to
  --   `(G.V ∖ W₁).image .unsplit ∪ W₁.image .copy0`.
  -- `v ∈ W₂` with `Disjoint W₁ W₂` gives `v ∈ G.V ∖ W₁`, hence
  -- `.unsplit v ∈ (G.V ∖ W₁).image .unsplit`.
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
  exact Finset.mem_sdiff.mpr ⟨hW₂ hvW₂, Finset.disjoint_right.mp hDisj hvW₂⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: image_unsplit_subset_nodeSplittingHard_V

-- ref: claim_3_10
--
-- Refactor port of `twoDisjointNodeSplittingHardCommute` for the
-- `cdmg_typed_edges` design.  Same statement structure as the
-- original — a conjunction `(a) ∧ (b)` of two
-- `refactor_eqViaNodeMap` equalities through the shared joint SWIG
-- `G_{swig(W₁ ∪ W₂)}` — and the same eight sub-goals (J, V, E, L
-- for each iteration order).
--
-- ## Refactor port — proof structure
--
-- * **J / V / E sub-goals (1, 2, 3, 5, 6, 7) port mechanically.**
--   The tactic blocks are verbatim from the original up to the
--   rename pass `SplitNode → refactor_SplitNode`,
--   `toCopy0 → refactor_toCopy0`, `toCopy1 → refactor_toCopy1`,
--   helper-name `flatten_toCopy0_toCopy0 →
--   flatten_refactor_toCopy0_refactor_toCopy0`, etc.  The
--   structural reason this works is that
--   `refactor_nodeSplittingHard`'s J / V / E fields are unchanged
--   from `nodeSplittingHard`'s (the refactor changes only the L
--   side); every `change`-target, every `Finset.image_image`
--   fusion, every `Finset.image_congr` pointwise check has the
--   same shape after the rename.
--
-- * **L sub-goals (4 and 8) are structurally reworked for
--   `Sym2.map`.**  The original L-side threaded the lift through
--   `Prod.map flattenSplit flattenSplit` on ordered pairs; the
--   refactor threads it through `Sym2.map refactor_flattenSplit`
--   on the `Sym2`-quotient.  The double-image fuses via
--   `Finset.image_image` exactly as before, but the inner
--   map-composition `Sym2.map f ∘ Sym2.map g` fuses (now) to
--   `Sym2.map (f ∘ g)` via Mathlib's `Sym2.map_map`.  The
--   pointwise close uses the inline helper
--   `flatten_refactor_toCopy0_refactor_toCopy0` (verbatim port of
--   `flatten_toCopy0_toCopy0`, all branches unchanged because the
--   tagged-sum carrier `refactor_SplitNode` is structurally the
--   same as the pre-refactor `SplitNode`).
--
-- * **Inline `have`-locals match the original's style.**  Per the
--   manager.md "Net-new helpers also need REPLACEMENT markers"
--   guidance: prefer inline `have`-locals over hoisted top-level
--   declarations.  The original `twoDisjointNodeSplittingHardCommute`
--   keeps `flatten_toCopy0_toCopy0` / `flatten_toCopy1_toCopy1`
--   inline; we do the same with the `refactor_`-prefixed twins.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: twoDisjointNodeSplittingHardCommute (was: refactor_twoDisjointNodeSplittingHardCommute)
-- claim_3_10 -- start statement
theorem refactor_twoDisjointNodeSplittingHardCommute (G : refactor_CDMG Node)
    (hG : G.refactor_IsCADMG) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    refactor_eqViaNodeMap
        ((G.refactor_nodeSplittingHard hG W₁ hW₁).refactor_nodeSplittingHard
            (refactor_swigAcyclic G hG W₁ hW₁)
            (W₂.image refactor_SplitNode.unsplit)
            (refactor_image_unsplit_subset_nodeSplittingHard_V hW₁ hW₂ hDisj))
        (G.refactor_nodeSplittingHard hG (W₁ ∪ W₂)
            (Finset.union_subset hW₁ hW₂))
        refactor_flattenSplit
      ∧
    refactor_eqViaNodeMap
        ((G.refactor_nodeSplittingHard hG W₂ hW₂).refactor_nodeSplittingHard
            (refactor_swigAcyclic G hG W₂ hW₂)
            (W₁.image refactor_SplitNode.unsplit)
            (refactor_image_unsplit_subset_nodeSplittingHard_V hW₂ hW₁ hDisj.symm))
        (G.refactor_nodeSplittingHard hG (W₁ ∪ W₂)
            (Finset.union_subset hW₁ hW₂))
        refactor_flattenSplit
-- claim_3_10 -- end statement
  := by
  -- Inline helpers: `refactor_flattenSplit` collapses the two-stage
  -- `refactor_toCopy0` chain to the single `refactor_toCopy0 (A ∪ B)`.
  -- Verbatim port of the original `flatten_toCopy0_toCopy0` with the
  -- refactor renames.
  have flatten_refactor_toCopy0_refactor_toCopy0 :
      ∀ (A B : Finset Node) (v : Node),
        refactor_flattenSplit
            (refactor_toCopy0 (B.image refactor_SplitNode.unsplit)
              (refactor_toCopy0 A v))
          = refactor_toCopy0 (A ∪ B) v := by
    intro A B v
    unfold refactor_toCopy0
    by_cases hA : v ∈ A
    · rw [if_pos hA]
      have h_notimg : refactor_SplitNode.copy0 v ∉ B.image refactor_SplitNode.unsplit := by
        intro h
        obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
        cases hweq
      rw [if_neg h_notimg]
      change refactor_SplitNode.copy0 v
          = (if v ∈ A ∪ B then refactor_SplitNode.copy0 v
              else refactor_SplitNode.unsplit v)
      rw [if_pos (Finset.mem_union_left _ hA)]
    · rw [if_neg hA]
      by_cases hB : v ∈ B
      · have h_img : refactor_SplitNode.unsplit v ∈ B.image refactor_SplitNode.unsplit :=
          Finset.mem_image.mpr ⟨v, hB, rfl⟩
        rw [if_pos h_img]
        change refactor_SplitNode.copy0 v
            = (if v ∈ A ∪ B then refactor_SplitNode.copy0 v
                else refactor_SplitNode.unsplit v)
        rw [if_pos (Finset.mem_union_right _ hB)]
      · have h_notimg : refactor_SplitNode.unsplit v ∉ B.image refactor_SplitNode.unsplit := by
          intro h
          obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
          cases hweq
          exact hB hw
        rw [if_neg h_notimg]
        change refactor_SplitNode.unsplit v
            = (if v ∈ A ∪ B then refactor_SplitNode.copy0 v
                else refactor_SplitNode.unsplit v)
        have hVU : v ∉ A ∪ B := fun h =>
          (Finset.mem_union.mp h).elim hA hB
        rw [if_neg hVU]
  -- Symmetric helper for `refactor_toCopy1`.
  have flatten_refactor_toCopy1_refactor_toCopy1 :
      ∀ (A B : Finset Node) (v : Node),
        refactor_flattenSplit
            (refactor_toCopy1 (B.image refactor_SplitNode.unsplit)
              (refactor_toCopy1 A v))
          = refactor_toCopy1 (A ∪ B) v := by
    intro A B v
    unfold refactor_toCopy1
    by_cases hA : v ∈ A
    · rw [if_pos hA]
      have h_notimg : refactor_SplitNode.copy1 v ∉ B.image refactor_SplitNode.unsplit := by
        intro h
        obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
        cases hweq
      rw [if_neg h_notimg]
      change refactor_SplitNode.copy1 v
          = (if v ∈ A ∪ B then refactor_SplitNode.copy1 v
              else refactor_SplitNode.unsplit v)
      rw [if_pos (Finset.mem_union_left _ hA)]
    · rw [if_neg hA]
      by_cases hB : v ∈ B
      · have h_img : refactor_SplitNode.unsplit v ∈ B.image refactor_SplitNode.unsplit :=
          Finset.mem_image.mpr ⟨v, hB, rfl⟩
        rw [if_pos h_img]
        change refactor_SplitNode.copy1 v
            = (if v ∈ A ∪ B then refactor_SplitNode.copy1 v
                else refactor_SplitNode.unsplit v)
        rw [if_pos (Finset.mem_union_right _ hB)]
      · have h_notimg : refactor_SplitNode.unsplit v ∉ B.image refactor_SplitNode.unsplit := by
          intro h
          obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
          cases hweq
          exact hB hw
        rw [if_neg h_notimg]
        change refactor_SplitNode.unsplit v
            = (if v ∈ A ∪ B then refactor_SplitNode.copy1 v
                else refactor_SplitNode.unsplit v)
        have hVU : v ∉ A ∪ B := fun h =>
          (Finset.mem_union.mp h).elim hA hB
        rw [if_neg hVU]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  -- ===== Sub-goal 1: J for (a) =====
  · change ((G.J.image refactor_SplitNode.unsplit
                ∪ W₁.image refactor_SplitNode.copy1).image refactor_SplitNode.unsplit
              ∪ (W₂.image refactor_SplitNode.unsplit).image refactor_SplitNode.copy1).image
            refactor_flattenSplit
          = G.J.image refactor_SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image refactor_SplitNode.copy1
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
          ⟨refactor_SplitNode.unsplit (refactor_SplitNode.unsplit j), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨refactor_SplitNode.unsplit j, ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · refine Finset.mem_image.mpr
            ⟨refactor_SplitNode.unsplit (refactor_SplitNode.copy1 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨refactor_SplitNode.copy1 w, ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · refine Finset.mem_image.mpr
            ⟨refactor_SplitNode.copy1 (refactor_SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨refactor_SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 2: V for (a) =====
  · change ((((G.V \ W₁).image refactor_SplitNode.unsplit
                ∪ W₁.image refactor_SplitNode.copy0) \
              (W₂.image refactor_SplitNode.unsplit)).image refactor_SplitNode.unsplit
            ∪ (W₂.image refactor_SplitNode.unsplit).image refactor_SplitNode.copy0).image
              refactor_flattenSplit
          = (G.V \ (W₁ ∪ W₂)).image refactor_SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image refactor_SplitNode.copy0
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
          ⟨refactor_SplitNode.unsplit (refactor_SplitNode.unsplit v), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨refactor_SplitNode.unsplit v, ?_, rfl⟩
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
            ⟨refactor_SplitNode.unsplit (refactor_SplitNode.copy0 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨refactor_SplitNode.copy0 w, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
          · intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
        · refine Finset.mem_image.mpr
            ⟨refactor_SplitNode.copy0 (refactor_SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨refactor_SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 3: E for (a) =====
  · change ((G.E.image (fun e : Node × Node =>
                (refactor_toCopy1 W₁ e.1, refactor_toCopy0 W₁ e.2))).image
              (fun e => (refactor_toCopy1 (W₂.image refactor_SplitNode.unsplit) e.1,
                         refactor_toCopy0 (W₂.image refactor_SplitNode.unsplit) e.2))).image
            (Prod.map refactor_flattenSplit refactor_flattenSplit)
          = G.E.image (fun e : Node × Node =>
              (refactor_toCopy1 (W₁ ∪ W₂) e.1, refactor_toCopy0 (W₁ ∪ W₂) e.2))
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro e _
    change (refactor_flattenSplit
                (refactor_toCopy1 (W₂.image refactor_SplitNode.unsplit)
                  (refactor_toCopy1 W₁ e.1)),
            refactor_flattenSplit
                (refactor_toCopy0 (W₂.image refactor_SplitNode.unsplit)
                  (refactor_toCopy0 W₁ e.2)))
          = (refactor_toCopy1 (W₁ ∪ W₂) e.1, refactor_toCopy0 (W₁ ∪ W₂) e.2)
    rw [flatten_refactor_toCopy0_refactor_toCopy0,
        flatten_refactor_toCopy1_refactor_toCopy1]
  -- ===== Sub-goal 4: L for (a) — Sym2.map rework. =====
  · change ((G.L.image (Sym2.map (refactor_toCopy0 W₁))).image
                (Sym2.map (refactor_toCopy0 (W₂.image refactor_SplitNode.unsplit)))).image
              (Sym2.map refactor_flattenSplit)
          = G.L.image (Sym2.map (refactor_toCopy0 (W₁ ∪ W₂)))
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro s _
    change Sym2.map refactor_flattenSplit
              (Sym2.map (refactor_toCopy0 (W₂.image refactor_SplitNode.unsplit))
                (Sym2.map (refactor_toCopy0 W₁) s))
          = Sym2.map (refactor_toCopy0 (W₁ ∪ W₂)) s
    rw [Sym2.map_map, Sym2.map_map]
    refine Sym2.map_congr ?_
    intro x _
    exact flatten_refactor_toCopy0_refactor_toCopy0 W₁ W₂ x
  -- ===== Sub-goal 5: J for (b) — same shape as Sub-goal 1 with W₁ ↔ W₂. =====
  · change ((G.J.image refactor_SplitNode.unsplit
                ∪ W₂.image refactor_SplitNode.copy1).image refactor_SplitNode.unsplit
              ∪ (W₁.image refactor_SplitNode.unsplit).image refactor_SplitNode.copy1).image
            refactor_flattenSplit
          = G.J.image refactor_SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image refactor_SplitNode.copy1
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
          ⟨refactor_SplitNode.unsplit (refactor_SplitNode.unsplit j), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨refactor_SplitNode.unsplit j, ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx2
        rcases Finset.mem_union.mp hw with hwW₁ | hwW₂
        · refine Finset.mem_image.mpr
            ⟨refactor_SplitNode.copy1 (refactor_SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨refactor_SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · refine Finset.mem_image.mpr
            ⟨refactor_SplitNode.unsplit (refactor_SplitNode.copy1 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨refactor_SplitNode.copy1 w, ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
  -- ===== Sub-goal 6: V for (b) — same shape as Sub-goal 2 with W₁ ↔ W₂. =====
  · change ((((G.V \ W₂).image refactor_SplitNode.unsplit
                ∪ W₂.image refactor_SplitNode.copy0) \
              (W₁.image refactor_SplitNode.unsplit)).image refactor_SplitNode.unsplit
            ∪ (W₁.image refactor_SplitNode.unsplit).image refactor_SplitNode.copy0).image
              refactor_flattenSplit
          = (G.V \ (W₁ ∪ W₂)).image refactor_SplitNode.unsplit
            ∪ (W₁ ∪ W₂).image refactor_SplitNode.copy0
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
          ⟨refactor_SplitNode.unsplit (refactor_SplitNode.unsplit v), ?_, rfl⟩
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨refactor_SplitNode.unsplit v, ?_, rfl⟩
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
            ⟨refactor_SplitNode.copy0 (refactor_SplitNode.unsplit w), ?_, rfl⟩
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_image.mpr ⟨refactor_SplitNode.unsplit w, ?_, rfl⟩
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · refine Finset.mem_image.mpr
            ⟨refactor_SplitNode.unsplit (refactor_SplitNode.copy0 w), ?_, rfl⟩
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨refactor_SplitNode.copy0 w, ?_, rfl⟩
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨w, hwW₂, rfl⟩
          · intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
  -- ===== Sub-goal 7: E for (b) — same shape as Sub-goal 3 with W₁ ↔ W₂. =====
  · change ((G.E.image (fun e : Node × Node =>
                (refactor_toCopy1 W₂ e.1, refactor_toCopy0 W₂ e.2))).image
              (fun e => (refactor_toCopy1 (W₁.image refactor_SplitNode.unsplit) e.1,
                         refactor_toCopy0 (W₁.image refactor_SplitNode.unsplit) e.2))).image
            (Prod.map refactor_flattenSplit refactor_flattenSplit)
          = G.E.image (fun e : Node × Node =>
              (refactor_toCopy1 (W₁ ∪ W₂) e.1, refactor_toCopy0 (W₁ ∪ W₂) e.2))
    rw [Finset.union_comm W₁ W₂]
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro e _
    change (refactor_flattenSplit
                (refactor_toCopy1 (W₁.image refactor_SplitNode.unsplit)
                  (refactor_toCopy1 W₂ e.1)),
            refactor_flattenSplit
                (refactor_toCopy0 (W₁.image refactor_SplitNode.unsplit)
                  (refactor_toCopy0 W₂ e.2)))
          = (refactor_toCopy1 (W₂ ∪ W₁) e.1, refactor_toCopy0 (W₂ ∪ W₁) e.2)
    rw [flatten_refactor_toCopy0_refactor_toCopy0,
        flatten_refactor_toCopy1_refactor_toCopy1]
  -- ===== Sub-goal 8: L for (b) — Sym2.map rework with W₁ ↔ W₂. =====
  · change ((G.L.image (Sym2.map (refactor_toCopy0 W₂))).image
                (Sym2.map (refactor_toCopy0 (W₁.image refactor_SplitNode.unsplit)))).image
              (Sym2.map refactor_flattenSplit)
          = G.L.image (Sym2.map (refactor_toCopy0 (W₁ ∪ W₂)))
    rw [Finset.union_comm W₁ W₂]
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro s _
    change Sym2.map refactor_flattenSplit
              (Sym2.map (refactor_toCopy0 (W₁.image refactor_SplitNode.unsplit))
                (Sym2.map (refactor_toCopy0 W₂) s))
          = Sym2.map (refactor_toCopy0 (W₂ ∪ W₁)) s
    rw [Sym2.map_map, Sym2.map_map]
    refine Sym2.map_congr ?_
    intro x _
    exact flatten_refactor_toCopy0_refactor_toCopy0 W₂ W₁ x
-- REFACTOR-BLOCK-REPLACEMENT-END: twoDisjointNodeSplittingHardCommute

end refactor_CDMG

end Causality
