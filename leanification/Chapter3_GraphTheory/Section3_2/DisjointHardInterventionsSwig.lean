import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGTypes
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.AcyclicPreservedUnderDo
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard

namespace Causality

/-!
# Disjoint hard interventions and node-splitting hard interventions
  commute (`claim_3_11`)

This file formalises the LN lemma `claim_3_11`
(`DisjointHardInterventions`, the SWIG analog of `claim_3_8`) in
section 3.2 of `graphs.tex`:

> Let `G = (J, V, E, L)` be a CADMG and `W₁ ⊆ J ∪ V`, `W₂ ⊆ V` two
> disjoint subsets of nodes of `G`.  Then
> `(G_{doit(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{doit(W₁)}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_11_statement_DisjointHardInterventions.tex`, verified
equivalent to the LN block (`addition_to_the_LN` empty).

## Carrier reading (load-bearing for this row's Lean signature)

`def_3_10` (`hardInterventionOn`) preserves the node carrier
(`Node → Node`) while `def_3_12` (`nodeSplittingHard`, SWIG) lifts
the carrier (`Node → SplitNode Node`).  Both sides of the asserted
equality therefore land in `CDMG (SplitNode Node)`:

* LHS `(G.hardInterventionOn W₁ hW₁).nodeSplittingHard _ W₂ _` — the
  inner hard intervention keeps the carrier as `Node`; the outer
  `nodeSplittingHard` lifts to `SplitNode Node`.
* RHS `(G.nodeSplittingHard hG W₂ hW₂).hardInterventionOn
  (W₁.image .unsplit) _` — the inner `nodeSplittingHard` lifts to
  `SplitNode Node`, and the outer hard intervention operates on the
  lifted carrier.  `W₁` is lifted to the split-graph carrier via
  `.image SplitNode.unsplit`, faithful to the tex spec's "Carrier
  reading of the equality" paragraph: every `w ∈ W₁` satisfies
  `w ∈ J ∪ V` (by `hW₁`) and `w ∉ W₂` (by disjointness), so `w`
  injects as its unsplit copy `.unsplit w` in the split-graph
  carrier.

Both sides have the same Lean type `CDMG (SplitNode Node)`, so the
equality is a *literal* `=` of CDMGs — mirroring the literal-`=`
pattern of `claim_3_8` (`DisjointHardInterventions`), the
node-splitting-not-SWIG analog of this row.  No `eqViaNodeMap` /
`flattenSplit` workaround is needed (contrast with `claim_3_10`'s
iterated-SWIG case, where two stacked `nodeSplittingHard`s produce
`CDMG (SplitNode (SplitNode Node))` and a carrier-relabelling is
unavoidable).

## CADMG hypothesis `(hG : G.IsCADMG)` on the signature

Unlike `claim_3_8` (whose `nodeSplittingOn` takes no acyclicity
precondition), `def_3_12`'s `nodeSplittingHard` requires
`(hG : G.IsCADMG)` on its signature (cf.\
`NodeSplittingHard.lean`'s design bullet (d)).  The RHS's inner
`nodeSplittingHard hG W₂ hW₂` is fed `hG` directly; the LHS's outer
`nodeSplittingHard ...` needs an `IsCADMG` witness on
`G.hardInterventionOn W₁ hW₁`, supplied by `claim_3_3`
(`acyclic_preserved_under_do`): if `G.IsAcyclic` (= `G.IsCADMG` by
`def_3_7` item i), then so is `G.hardInterventionOn W₁ hW₁`.  The
private wrapper `hardInterventionOn_isCADMG_of_isCADMG` below
extracts that conjunct cleanly so the main signature reads without
`.1` projections.

The body is filled in by `prove_claim_in_lean` (Manager B),
following the to-be-written tex proof at
`tex/claim_3_11_proof_DisjointHardInterventions.tex`.
-/

namespace CDMG

-- ## Statement-context variable block — `Node : Type*` with `[DecidableEq Node]`
--
-- Inherited verbatim from `def_3_1` (`CDMG.lean`); mirrors the
-- analogous `variable` line of `claim_3_8` and `claim_3_10`.
--
-- ## Design choice
--
-- *`[DecidableEq Node]` is mandatory at the statement level (not a
--   proof-side convenience).*  The wrapped signature directly mentions
--   `Disjoint W₁ W₂` on `Finset Node`, `W₁.image SplitNode.unsplit`,
--   and traverses `G.J`, `G.V`, `G.E`, `G.L` through `G.IsCADMG`
--   (`def_3_7`), `G.hardInterventionOn` (`def_3_10`), and
--   `G.nodeSplittingHard` (`def_3_12`) — each consumes `[DecidableEq
--   Node]` through `Finset`-backed membership, image, and union
--   operations.  Replacing the `Finset` encoding with `Set` to drop
--   decidability would force every downstream chapter (CBNs in ch.\ 4,
--   do-calculus in ch.\ 5, iSCMs in ch.\ 8+) to lose its `Finset`
--   pattern matching and would invalidate the `Finset.image` /
--   `Finset.disjoint_right` machinery on which both helpers below
--   depend.  The split-graph carrier `SplitNode Node` inherits
--   `[DecidableEq (SplitNode Node)]` automatically via
--   `NodeSplittingOn.lean`'s `deriving DecidableEq` clause, so no
--   additional typeclass binder is needed for the RHS's lifted carrier.
--
-- *Wrapped with helper markers (three-dash) — load-bearing for
--   website-extractor isolation.*  Litmus test: would removing the
--   `variable` line break the wrapped main signature?  YES — the
--   theorem head references `Node` and elaborates `Finset`-backed
--   operations whose instance search would fail without
--   `[DecidableEq Node]` in scope.  Lean's `variable` mechanism
--   auto-binds these into the rendered theorem head only when the
--   `variable` line is in scope at elaboration; the website extractor
--   reconstructs the wrapped signature *in isolation* from the rest
--   of the file, so the `variable` must travel with the statement via
--   helper markers — otherwise the statement-only website rendering
--   would lose `Node` and `[DecidableEq Node]` from the displayed
--   binders.  Same marker convention as `claim_3_8` and `claim_3_10`.
-- claim_3_11 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_11 --- end helper

-- ## Private helper — `IsCADMG` witness for the inner hard intervention
--
-- The LHS's outer `nodeSplittingHard ?hG W₂ ?hW₂` needs an `IsCADMG`
-- witness on `G.hardInterventionOn W₁ hW₁` (because `def_3_12`
-- requires acyclicity of its input).  `claim_3_3`
-- (`acyclic_preserved_under_do`) provides exactly this — but as the
-- first conjunct of an `(acyclic) ∧ (∀ lt, topological_order ↦ …)`
-- pair.  This wrapper projects it cleanly so the main signature
-- reads without `.1` clutter.  Not LN content (acyclicity
-- preservation is itself `claim_3_3`), so unmarked — matches
-- `claim_3_10`'s use of the imported `swigAcyclic` (`claim_3_9`)
-- inline without a local marker.
private lemma hardInterventionOn_isCADMG_of_isCADMG
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    (G.hardInterventionOn W hW).IsCADMG :=
  (acyclic_preserved_under_do G W hW hG).1

-- ## Helper — `W₂` sits inside the carrier of the inner hard intervention
--
-- The LHS `(G.hardInterventionOn W₁ hW₁).nodeSplittingHard _ W₂ ?_`
-- requires `?_ : W₂ ⊆ (G.hardInterventionOn W₁ hW₁).V`, i.e.\
-- `W₂ ⊆ G.V ∖ W₁` per `def_3_10` item ii.  The rewritten tex's
-- "Well-typedness of the inner SWIG on the LHS" paragraph proves
-- this from `W₂ ⊆ G.V` and `W₁ ∩ W₂ = ∅` (`Disjoint W₁ W₂`).
--
-- ## Design choice
--
-- *Standalone helper, wrapped with three-dash helper markers — the
--   litmus test for marker wrapping (would removing this declaration
--   break the wrapped main signature?) returns YES.*  The LHS's outer
--   `nodeSplittingHard _ W₂ ?_` reads the conclusion of this lemma as
--   its `?_`-precondition; without the named term the main theorem
--   head simply does not type-check.  This is load-bearing on the
--   *statement* (not just the proof), which is exactly why it needs to
--   travel with the rendered statement on the website — the extractor
--   pulls it out alongside the theorem head via the helper markers,
--   keeping the rendered signature self-referential and avoiding an
--   inline `by`-block in the type that would clutter the rendered
--   statement with `(G.V ∖ W₁)`-arithmetic.
--
-- *Re-derived from `claim_3_8`'s `private lemma` of the same name.*
--   Lineage: `DisjointHardInterventions.lean` defines the identical
--   helper, but it is `private`-scoped to that file, so cross-file
--   reuse is not possible.  Lifting it into a chapter-shared utility
--   was rejected for now because the `private` localisation is
--   genuinely valuable (keeps the `CDMG` namespace clean), and the
--   re-derivation is one tactic-line; the duplication is the cheaper
--   cost.  Same pattern as `swig_toCopy0_inj` in
--   `NodeSplittingHard.lean` (re-derived from `toCopy0_inj` in
--   `NodeSplittingOn.lean`).  If a third row appears that needs the
--   same lemma, a future refactor can promote it.
--
-- *Hypothesis shape `Disjoint W₁ W₂` (Mathlib `Finset` form), not
--   `W₁ ∩ W₂ = ∅` or `W₂ ⊆ G.V ∖ W₁`.*  Canonical Mathlib `Finset`
--   form used by `claim_3_8` and `claim_3_10`; `Finset.disjoint_right`
--   consumes it in one step.  Encoding the LN's "$W_1 \cap W_2 =
--   \emptyset$" as a raw `Finset.inter` equality would force a
--   `Finset.mem_inter` rewrite at every use site; encoding it as
--   `W₂ ⊆ G.V ∖ W₁` would couple this helper to the LHS-only reading
--   and would not survive a `Disjoint.symm` swap.  The `Disjoint` form
--   is also what the main theorem's `hDisj` binder ships, so no
--   conversion is needed at the call site.
--
-- *Mathlib re-use.*  Built directly on `Finset.mem_sdiff` and
--   `Finset.disjoint_right`; no rolled-our-own abstraction is needed.
-- claim_3_11 --- start helper
private lemma subset_V_of_hardInterventionOn
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.J ∪ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂ ⊆ (G.hardInterventionOn W₁ hW₁).V
-- claim_3_11 --- end helper
:= by
  intro v hv
  change v ∈ G.V \ W₁
  exact Finset.mem_sdiff.mpr ⟨hW₂ hv, Finset.disjoint_right.mp hDisj hv⟩

-- ## Helper — `W₁.image .unsplit` sits inside the carrier of the inner SWIG
--
-- The RHS `(G.nodeSplittingHard hG W₂ hW₂).hardInterventionOn
-- (W₁.image SplitNode.unsplit) ?_` requires
-- `?_ : W₁.image .unsplit ⊆
--        (G.nodeSplittingHard hG W₂ hW₂).J ∪
--        (G.nodeSplittingHard hG W₂ hW₂).V`.
-- For each `v ∈ W₁`: `v ∈ G.J ∪ G.V` by `hW₁`; if `v ∈ G.J` then
-- `.unsplit v ∈ G.J.image .unsplit ⊆ J_{swig(W₂)}`; if `v ∈ G.V`
-- then `v ∉ W₂` by `Disjoint W₁ W₂`, so `v ∈ G.V ∖ W₂` and
-- `.unsplit v ∈ (G.V ∖ W₂).image .unsplit ⊆ V_{swig(W₂)}`.  The
-- rewritten tex's "Carrier reading of the equality" paragraph
-- spells this out.
--
-- ## Design choice
--
-- *Standalone helper, wrapped with three-dash markers — litmus test
--   for marker wrapping returns YES.*  The RHS's outer
--   `hardInterventionOn (W₁.image SplitNode.unsplit) ?_` reads the
--   conclusion of this lemma as its `?_`-precondition; the wrapped
--   main theorem head does not type-check without the named term.
--   Same role as `subset_V_of_hardInterventionOn` above but on the
--   opposite side of the equality, mirroring `claim_3_8`'s pair of
--   helpers (`subset_V_of_hardInterventionOn` plus
--   `image_unsplit_subset_carrier_of_nodeSplittingOn`).  Wrapped with
--   helper markers so the website extractor pulls it out alongside
--   the rendered statement, otherwise the rendered theorem head
--   would reference an undefined symbol.  Inlining a `by`-block in
--   the type was rejected for the same reason as on the LHS — it
--   would clutter the rendered statement with split-graph carrier
--   arithmetic and duplicate the `.unsplit`-injection reasoning at
--   every future `swig`-then-`doit` use site.
--
-- *SWIG analog of claim_3_8's
--   `image_unsplit_subset_carrier_of_nodeSplittingOn`, with a
--   *two-piece* union instead of a three-piece one.*  Same structural
--   shape — case-split on `v ∈ G.J ∪ G.V`, then place `.unsplit v` in
--   the unsplit-image piece of `J_{swig(W₂)}` or `V_{swig(W₂)}`.  The
--   one structural simplification is on the `V`-branch: `def_3_12`'s
--   `V_{swig(W₂)} = (G.V ∖ W₂).image .unsplit ∪ W₂.image .copy0` is
--   a two-piece union (the `W₂.image .copy1` summand of `def_3_11`'s
--   `V_{spl(W₂)}` is reclassified into `J_{swig(W₂)}` under SWIG
--   semantics — see `NodeSplittingHard.lean`'s design bullet on the
--   `^i`-into-`J` reclassification), costing one fewer
--   `Finset.mem_union_left` in the `V`-branch compared to claim_3_8's
--   three-piece spl analog.  The `J`-branch is unchanged from
--   `claim_3_8` because `def_3_12`'s
--   `J_{swig(W₂)} = G.J.image .unsplit ∪ W₂.image .copy1` is itself
--   a two-piece union (one wider than `def_3_11`'s
--   `J_{spl(W₂)} = G.J.image .unsplit`), but the `unsplit` lift
--   reaches only the left summand so the membership chain is the
--   same length.
--
-- *Implicit `hG : G.IsCADMG`.*  The conclusion references
--   `(G.nodeSplittingHard hG W₂ hW₂).J ∪ ...` which threads `hG`
--   through the `nodeSplittingHard` application; making `hG`
--   implicit lets callers elide it when it is in scope.  Mirrors
--   `claim_3_10`'s `image_unsplit_subset_nodeSplittingHard_V` binder
--   convention.  The corresponding helper in `claim_3_8` has no
--   `hG` binder because `def_3_11`'s `nodeSplittingOn` takes no
--   acyclicity precondition — the only divergence in the binder
--   shape between this row's helper and its `claim_3_8` sibling.
--
-- *Disjointness `Disjoint W₁ W₂` is load-bearing on the `V`-branch,
--   inert on the `J`-branch.*  When `v ∈ W₁ ∩ G.J`, the lift lands
--   directly in `G.J.image .unsplit ⊆ J_{swig(W₂)}` without using
--   disjointness — SWIG (like spl) leaves the input-node side
--   untouched.  Disjointness only enters when `v ∈ W₁ ∩ G.V`, where
--   we need `v ∉ W₂` to land `.unsplit v` in
--   `(G.V ∖ W₂).image .unsplit`.  Surfacing this asymmetry in the
--   two `rcases` branches keeps the consumer's reading aligned with
--   `def_3_12`'s carrier construction.
--
-- *Mathlib re-use.*  Built on `Finset.mem_image`, `Finset.mem_union`,
--   `Finset.mem_sdiff`, and `Finset.disjoint_left`; the case-split on
--   `v ∈ G.J ∪ G.V` uses `Finset.mem_union.mp (hW₁ hv)`.  No
--   rolled-our-own abstraction is needed.
-- claim_3_11 --- start helper
private lemma image_unsplit_subset_carrier_of_nodeSplittingHard
    {G : CDMG Node} {hG : G.IsCADMG}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.J ∪ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₁.image SplitNode.unsplit ⊆
      (G.nodeSplittingHard hG W₂ hW₂).J ∪ (G.nodeSplittingHard hG W₂ hW₂).V
-- claim_3_11 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  rcases Finset.mem_union.mp (hW₁ hv) with hJ | hV
  · -- `v ∈ G.J` → `.unsplit v ∈ G.J.image .unsplit` ⊆ `J_{swig(W₂)}`
    -- (left summand of the two-piece-J union of `def_3_12` item i).
    refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · -- `v ∈ G.V`: disjointness gives `v ∉ W₂`, so `v ∈ G.V ∖ W₂` and
    -- `.unsplit v` lands in the `(G.V ∖ W₂).image .unsplit` piece of
    -- `V_{swig(W₂)} = (G.V ∖ W₂).image .unsplit ∪ W₂.image .copy0`
    -- (left summand of the two-piece-V union of `def_3_12` item ii).
    have hv_notW₂ : v ∉ W₂ := Finset.disjoint_left.mp hDisj hv
    refine Finset.mem_union_right _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hV, hv_notW₂⟩, rfl⟩

-- ref: claim_3_11
-- For any CADMG `G : CDMG Node` (`hG : G.IsCADMG`) and any two
-- subsets `W₁ ⊆ G.J ∪ G.V`, `W₂ ⊆ G.V` with `Disjoint W₁ W₂`, the
-- LN equality
--   `(G_{doit(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{doit(W₁)}`
-- holds as a literal `=` of CDMGs over the split-graph carrier
-- `SplitNode Node`.
/-
LN tex (rewritten canonical statement for `claim_3_11`):

  Let `G = (J, V, E, L)` be a CADMG and `W₁ ⊆ J ∪ V`, `W₂ ⊆ V`
  subject to `W₁ ∩ W₂ = ∅`.  Then
    `(G_{doit(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{doit(W₁)}`,
  read as a literal `=` of CDMGs over the split-graph carrier (NOT
  up to a carrier-relabelling map): the inner `swig(W₂)` on the LHS
  is well-defined because `W₂ ⊆ V ∖ W₁ = V_{doit(W₁)}` and
  `G_{doit(W₁)}` is itself a CADMG (by `claim_3_3`); the outer
  `doit(W₁)` on the RHS is well-defined because `W₁`'s nodes inject
  into the split-graph carrier as their unsplit copies `.unsplit w`
  (every `w ∈ W₁` lies in `J ∪ (V ∖ W₂)` by disjointness).

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CADMG and `W_1 ⊆ J ∪ V` and `W_2 ⊆ V`
  two disjoint subsets of nodes of `G`.  Then the CADMG obtained
  from first hard intervening on `W_1` and then node-splitting (in
  the SWIG sense of def_3_12) on `W_2` is the same CADMG that
  arises from first node-splitting on `W_2` and then hard
  intervening on `W_1`:
    `(G_{doit(W_1)})_{swig(W_2)} = (G_{swig(W_2)})_{doit(W_1)}`.
-/
-- ## Design choice
--
-- *Literal `=` of CDMGs over `SplitNode Node`, NOT
--   `eqViaNodeMap` / `flattenSplit`.*  This is the single most
--   important shape decision for this row, and the reason the
--   formalisation is structurally simpler than `claim_3_10`
--   (`TwoDisjointNodeSwig`).  Both sides apply a *single*
--   node-splitting on `W₂` and a single hard intervention on `W₁`,
--   and `hardInterventionOn` preserves the node carrier
--   (`CDMG α → CDMG α` per `def_3_10`).  No carrier mismatch
--   arises and the asserted equality is a literal `=` between two
--   terms of identical Lean type `CDMG (SplitNode Node)`.  Contrast
--   with `claim_3_10`, where iterating `nodeSplittingHard` twice
--   produces `CDMG (SplitNode (SplitNode Node))` on both sides
--   with disagreeing constructor wrappings of the same underlying
--   node (`.unsplit (.copy0 w)` vs `.copy0 (.unsplit w)`), forcing
--   the `eqViaNodeMap` / `flattenSplit` workaround.  Here the LN's
--   "the same CADMG" reading is delivered by Lean's structural `=`;
--   no carrier-relabelling map, no `Finset.image` chase through a
--   flatten function.  Mirrors `claim_3_8`'s shape exactly,
--   lifted to the SWIG side.
--
-- *`(hG : G.IsCADMG)` on the signature.*  Required by `def_3_12`'s
--   `nodeSplittingHard`, both for the RHS's inner SWIG (fed `hG`
--   directly) and for the LHS's outer SWIG (fed
--   `hardInterventionOn_isCADMG_of_isCADMG hG hW₁`, which routes
--   `hG` through `claim_3_3`'s `acyclic_preserved_under_do`).  The
--   LN's "Let `G` be a CADMG" opener maps exactly to this binder.
--   `claim_3_8`'s sibling theorem has no analogous binder because
--   `def_3_11`'s `nodeSplittingOn` does not take an acyclicity
--   precondition.
--
-- *Disjointness `Disjoint W₁ W₂` is genuinely load-bearing.*  Two
--   distinct uses inside the signature: (i) the LHS's inner
--   `swig(W₂)` needs `W₂ ⊆ G.V ∖ W₁ = V_{doit(W_1)}` (discharged
--   by `subset_V_of_hardInterventionOn`); (ii) the RHS's outer
--   `doit(W₁.image .unsplit)` needs the unsplit-lifted `W₁` to sit
--   inside `J_{swig(W₂)} ∪ V_{swig(W₂)}` (discharged by
--   `image_unsplit_subset_carrier_of_nodeSplittingHard`).  Without
--   it, a node `w ∈ W₁ ∩ W₂` would simultaneously be
--   hard-intervened (becomes an input on one side) and SWIG-split
--   (gets new copies `w^o`, `w^i` on the other); the iterated
--   operations would commit to incompatible carrier placements and
--   the equality would no longer hold.  Encoded as Mathlib's
--   `Disjoint W₁ W₂`, matching `claim_3_8` / `claim_3_10`.
--
-- *`W₁.image SplitNode.unsplit` on the RHS, not a fresh `Finset` on
--   the split carrier.*  Faithful to the rewritten tex's "Carrier
--   reading of the equality" paragraph: every `w ∈ W₁` lies in
--   `J ∪ (V ∖ W₂)` (by `hW₁` and disjointness with `W₂`), i.e.\
--   the untagged piece of `J_{swig(W₂)} ∪ V_{swig(W₂)}` under
--   `def_3_12`'s shorthand "`v^o := v^i := v` for
--   `v ∈ J ∪ (V ∖ W₂)`".  At the Lean level this untagged piece is
--   exactly the image of `SplitNode.unsplit`.  Reusing the same
--   lift convention from `claim_3_8` and `claim_3_10` keeps the
--   formalisations parallel and makes downstream composition
--   lemmas (do-calculus interactions with SWIG, ch.\ 5+) easier to
--   state.
--
-- *Single theorem, not a conjunction.*  The LN statement is a
--   single equality `LHS = RHS`, mirroring `claim_3_8`.  No
--   joint-intervention form `G_{doit(W₁) ⊍ swig(W₂)}` exists
--   because `doit` and `swig` are structurally distinct operations
--   (different carrier evolution, different field equations) and
--   do not admit a single combined invocation.
--
-- *`addition_to_the_LN` is empty.*  No deviation or addition drove
--   any shape choice; the LN block's wording is the entire spec.
--   The `def_3_10` registered deviation
--   `hard_intervention_l_symmetrized_removal` (two-sided filter on
--   `L`) is inherited from the operation level but does not surface
--   as a hypothesis at the statement level — it only affects the
--   bidirected-edge componentwise check inside the proof body
--   (Manager B's responsibility).
--
-- *Mathlib re-use.*  `Finset.image`, `Disjoint`, `Finset.mem_sdiff`,
--   and `Finset.disjoint_left` / `_right` underpin both helpers and
--   the theorem signature.  `Finset.union_subset` does not appear at
--   the statement level because no joint-intervention form occurs.
--   The split-graph carrier `SplitNode` is our own construction
--   (`def_3_11` / `def_3_12`) — no Mathlib analogue exists, but the
--   `deriving DecidableEq` clause on `SplitNode` keeps `Finset`-based
--   manipulation of the lifted carrier purely Mathlib-driven.
--   `claim_3_3`'s `acyclic_preserved_under_do` is re-used (via the
--   `hardInterventionOn_isCADMG_of_isCADMG` wrapper) to supply the
--   inner-`hG` of the LHS's outer SWIG, avoiding a duplicate proof
--   of acyclicity preservation here.
--
-- *Downstream consequences.*  Once proven, this row enables clean
--   normalisation of `doit`-then-`swig` compositions for any later
--   chapter that mixes hard interventions with SWIG semantics — most
--   notably the do-calculus + counterfactual interactions in ch.\ 5+
--   (where the SWIG construction is the geometric scaffolding for
--   single-world intervention graphs) and the iSCM identification
--   theory in ch.\ 8+.  The literal-`=` shape means the resulting
--   CDMG equalities can be `rw`'d in place at consumer sites rather
--   than transported via an `eqViaNodeMap` predicate — significantly
--   easier to consume than the carrier-relabelling form used by
--   `claim_3_10`.  Future composition rows that mix `doit` with
--   *single-application* `swig` should aim to preserve this
--   literal-`=` shape; rows that iterate `swig` will inherit
--   `claim_3_10`'s `eqViaNodeMap` form instead.
-- claim_3_11 -- start statement
theorem disjointHardInterventionsAndNodeSplittingHardsCommute
    (G : CDMG Node) (hG : G.IsCADMG)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (G.hardInterventionOn W₁ hW₁).nodeSplittingHard
        (hardInterventionOn_isCADMG_of_isCADMG hG hW₁) W₂
        (subset_V_of_hardInterventionOn hW₁ hW₂ hDisj)
      = (G.nodeSplittingHard hG W₂ hW₂).hardInterventionOn
          (W₁.image SplitNode.unsplit)
          (image_unsplit_subset_carrier_of_nodeSplittingHard hW₁ hW₂ hDisj)
-- claim_3_11 -- end statement
-- TeX proof: claim_3_11_proof_DisjointHardInterventions.tex
:= by
  -- CDMG extensionality: two CDMGs over the split-graph carrier are equal
  -- once their four data fields `(J, V, E, L)` agree.  The five
  -- propositional fields (`hJV_disj`, `hE_subset`, `hL_subset`,
  -- `hL_irrefl`, `hL_symm`) have types determined by the data fields, so
  -- proof irrelevance discharges them automatically.  Mirrors the
  -- inline-`cdmgExt` pattern of `claim_3_4` and `claim_3_8`.
  have cdmgExt : ∀ {G₁ G₂ : CDMG (SplitNode Node)},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨J₁, V₁, hJV₁, E₁, hE₁, L₁, hL₁, hLi₁, hLs₁⟩
           ⟨J₂, V₂, hJV₂, E₂, hE₂, L₂, hL₂, hLi₂, hLs₂⟩ hJ hV hE hL
    obtain rfl := hJ
    obtain rfl := hV
    obtain rfl := hE
    obtain rfl := hL
    rfl
  -- Key membership lemma: under disjointness, the `toCopy0 W₂`-lift of a
  -- `Node` lies outside `W₁.image .unsplit` iff the original `Node` lies
  -- outside `W₁`.  Implements the tex proof's "$v_k^o \notin W_1
  -- \Leftrightarrow v_k \notin W_1$" cross-check (used both in the
  -- *directed edges* section for the `e.2` head of each generator, and
  -- twice in the *bidirected edges* section for the two endpoints of
  -- each generator).
  --
  -- Case-split on `v ∈ W₂` mirrors the tex's case-split:
  --   * `v ∈ W₂`: `toCopy0 W₂ v = .copy0 v`, which is never in
  --     `W₁.image .unsplit` by constructor mismatch; on the other side
  --     `Disjoint W₁ W₂` rules out `v ∈ W₁`.  Both sides true.
  --   * `v ∉ W₂`: `toCopy0 W₂ v = .unsplit v`, which is in
  --     `W₁.image .unsplit` iff `v ∈ W₁` by injectivity of `.unsplit`.
  have toCopy0_notMem_iff : ∀ (v : Node),
      toCopy0 W₂ v ∉ W₁.image SplitNode.unsplit ↔ v ∉ W₁ := by
    intro v
    unfold toCopy0
    by_cases hvW₂ : v ∈ W₂
    · rw [if_pos hvW₂]
      refine ⟨fun _ hW₁ => Finset.disjoint_left.mp hDisj hW₁ hvW₂,
              fun _ hMem => ?_⟩
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hMem
      cases hweq
    · rw [if_neg hvW₂]
      refine ⟨fun h hW₁ => h (Finset.mem_image.mpr ⟨v, hW₁, rfl⟩),
              fun h hMem => ?_⟩
      obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hMem
      cases hweq
      exact h hw
  refine cdmgExt ?_ ?_ ?_ ?_
  -- ===== Node sets: `J` =====
  -- LHS `J`: `(G.J ∪ W₁).image .unsplit ∪ W₂.image .copy1` (after
  -- unfolding `nodeSplittingHard` applied to `G.hardInterventionOn W₁`).
  -- RHS `J`: `(G.J.image .unsplit ∪ W₂.image .copy1) ∪ W₁.image .unsplit`
  -- (after unfolding `hardInterventionOn` applied to
  -- `G.nodeSplittingHard`).  Per the tex's "Input nodes ($J$)" section:
  -- rewrite `(G.J ∪ W₁).image` via `Finset.image_union` to
  -- `G.J.image .unsplit ∪ W₁.image .unsplit`, then swap the last two
  -- summands via `Finset.union_right_comm`, matching the tex's
  -- `(J ∪ W₁) ⊍ W₂^i = (J ⊍ W₂^i) ∪ W₁` rearrangement (using
  -- `W₁ ∩ W₂^i = ∅`, which here is the structural constructor
  -- mismatch between `.unsplit` and `.copy1`).
  · change (G.J ∪ W₁).image SplitNode.unsplit ∪ W₂.image SplitNode.copy1
          = (G.J.image SplitNode.unsplit ∪ W₂.image SplitNode.copy1)
              ∪ W₁.image SplitNode.unsplit
    rw [Finset.image_union, Finset.union_right_comm]
  -- ===== Node sets: `V` =====
  -- LHS `V`: `((G.V \ W₁) \ W₂).image .unsplit ∪ W₂.image .copy0`.
  -- RHS `V`: `((G.V \ W₂).image .unsplit ∪ W₂.image .copy0)
  --             \ W₁.image .unsplit`.
  -- Per the tex's "Output nodes ($V$)" section: the two pieces of
  -- `V_{swig(W₂)}` decompose under set-difference with
  -- `W₁.image .unsplit`:
  --   * `W₂.image .copy0 \ W₁.image .unsplit = W₂.image .copy0`
  --     (constructor mismatch — `W₁ ∩ W₂^o = ∅` structurally).
  --   * `(G.V \ W₂).image .unsplit \ W₁.image .unsplit
  --       = ((G.V \ W₂) \ W₁).image .unsplit
  --       = ((G.V \ W₁) \ W₂).image .unsplit`
  --     (by injectivity of `.unsplit` and commutativity of two-step
  --     removal).
  -- We prove the equality directly via element-wise `ext`, mirroring
  -- claim_3_8's V section but with one fewer piece (no `W₂.image .copy1`
  -- summand under SWIG, since `def_3_12` reclassifies `W₂^i` into `J`).
  · change ((G.V \ W₁) \ W₂).image SplitNode.unsplit ∪ W₂.image SplitNode.copy0
          = ((G.V \ W₂).image SplitNode.unsplit ∪ W₂.image SplitNode.copy0)
            \ W₁.image SplitNode.unsplit
    ext x
    constructor
    · -- LHS → RHS direction.
      intro hx
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · -- `x` is in the inner V (RHS-pre-sdiff).
        rcases Finset.mem_union.mp hx with hx1 | hx2
        · -- `x = .unsplit v`, `v ∈ (G.V \ W₁) \ W₂` ⊆ `G.V \ W₂`.
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
          obtain ⟨hv_VW₁, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
          obtain ⟨hv_V, _⟩ := Finset.mem_sdiff.mp hv_VW₁
          refine Finset.mem_union_left _ ?_
          exact Finset.mem_image.mpr
            ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₂⟩, rfl⟩
        · -- `x = .copy0 w`, lands directly in the right summand of inner V.
          refine Finset.mem_union_right _ ?_
          exact hx2
      · -- `x ∉ W₁.image .unsplit`: case on which piece of LHS V holds x.
        rcases Finset.mem_union.mp hx with hx1 | hx2
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
    · -- RHS → LHS direction.
      intro hx
      obtain ⟨hx_inner, hx_notW₁'⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp hx_inner with hx1 | hx2
      · -- `x = .unsplit v`, `v ∈ G.V \ W₂`, and `v ∉ W₁` from
        -- `hx_notW₁'` (`.unsplit v ∉ W₁.image .unsplit` by injectivity).
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨hv_V, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
        have hv_notW₁ : v ∉ W₁ := fun h =>
          hx_notW₁' (Finset.mem_image.mpr ⟨v, h, rfl⟩)
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₁⟩, hv_notW₂⟩
      · -- `x = .copy0 w`, lands directly in the right summand of LHS V.
        refine Finset.mem_union_right _ ?_
        exact hx2
  -- ===== Directed edges: `E` =====
  -- LHS `E`: `(G.E.filter (e.2 ∉ W₁)).image
  --             (toCopy1 W₂ ·.1, toCopy0 W₂ ·.2)`.
  -- RHS `E`: `(G.E.image (toCopy1 W₂ ·.1, toCopy0 W₂ ·.2)).filter
  --             (e.2 ∉ W₁.image .unsplit)`.
  -- Per the tex's "Directed edges" section: `Finset.filter_image` swaps
  -- to a pre-image-filter form, and the filter predicate matches
  -- `e.2 ∉ W₁` via `toCopy0_notMem_iff` applied to `e.2`.  Crucially,
  -- the SWIG construction of `def_3_12` introduces NO transfer-edge
  -- piece (in contrast to `def_3_11`'s `nodeSplittingOn`), so the
  -- directed-edge case is one image-filter rewrite simpler than
  -- claim_3_8's E section — no `Finset.filter_union` pre-rewrite, no
  -- second-summand vacuous-filter argument.
  · change (G.E.filter (fun e : Node × Node => e.2 ∉ W₁)).image
            (fun e : Node × Node => (toCopy1 W₂ e.1, toCopy0 W₂ e.2))
          = (G.E.image
              (fun e : Node × Node => (toCopy1 W₂ e.1, toCopy0 W₂ e.2))).filter
              (fun e : SplitNode Node × SplitNode Node =>
                e.2 ∉ W₁.image SplitNode.unsplit)
    rw [Finset.filter_image]
    congr 1
    refine Finset.filter_congr ?_
    intro e he
    exact (toCopy0_notMem_iff e.2).symm
  -- ===== Bidirected edges: `L` =====
  -- LHS `L`: `(G.L.filter (e.1 ∉ W₁ ∧ e.2 ∉ W₁)).image
  --             (toCopy0 W₂ ·.1, toCopy0 W₂ ·.2)`.
  -- RHS `L`: `(G.L.image (toCopy0 W₂ ·.1, toCopy0 W₂ ·.2)).filter
  --             (e.1 ∉ W₁.image .unsplit ∧ e.2 ∉ W₁.image .unsplit)`.
  -- Per the tex's "Bidirected edges" section: `Finset.filter_image`
  -- swaps to a pre-image-filter form, and `toCopy0_notMem_iff` applies
  -- to both endpoints.  The two-sided filter convention here is the
  -- registered deviation `hard_intervention_l_symmetrized_removal` from
  -- `def_3_10`; per the tex's "Registered two-sided removal of `L`"
  -- paragraph, the two-sided and LN-literal one-sided readings agree
  -- under `L`'s symmetry axiom (so the tex's iff
  -- `v_k^o ∉ W_1 ↔ v_k ∉ W_1` applied to both `k = 1, 2` closes the
  -- goal).  Identical shape to claim_3_8's L section, lifted to the
  -- SWIG side without modification.
  · change (G.L.filter (fun e : Node × Node => e.1 ∉ W₁ ∧ e.2 ∉ W₁)).image
            (fun e : Node × Node => (toCopy0 W₂ e.1, toCopy0 W₂ e.2))
          = (G.L.image
              (fun e : Node × Node => (toCopy0 W₂ e.1, toCopy0 W₂ e.2))).filter
              (fun e : SplitNode Node × SplitNode Node =>
                e.1 ∉ W₁.image SplitNode.unsplit
                  ∧ e.2 ∉ W₁.image SplitNode.unsplit)
    rw [Finset.filter_image]
    congr 1
    refine Finset.filter_congr ?_
    intro e he
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(toCopy0_notMem_iff e.1).mpr h1, (toCopy0_notMem_iff e.2).mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(toCopy0_notMem_iff e.1).mp h1, (toCopy0_notMem_iff e.2).mp h2⟩

end CDMG

end Causality
