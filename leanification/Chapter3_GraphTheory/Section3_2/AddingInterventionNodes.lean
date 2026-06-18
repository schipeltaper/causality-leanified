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

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited from `def_3_1`
--   (`CDMG.lean`); load-bearing because the statement constructs
--   `W₁ ∪ W₂` (needs `Finset.union`), `W₂.image IntExtNode.unsplit`
--   (needs `Finset.image`), and `eqViaNodeMap` (which contains four
--   `Finset.image f` equalities) — every one of which requires
--   decidable equality on `Node` (and, via the auto-derived
--   `DecidableEq (IntExtNode Node)` and
--   `DecidableEq (IntExtNode (IntExtNode Node))` instances from
--   `def_3_13`, on the iterated and single-step carriers as well).
--   Stronger instances (`Fintype`, `LinearOrder`) are not needed at
--   the statement level and are deferred to the proof body's use sites.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: variable_Node
-- claim_3_14 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_14 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: variable_Node

-- ## Helper — lift `S ⊆ G.J ∪ G.V` via `.unsplit` into the carrier of `G.extendingCDMGsWith W hW`
--
-- The signatures of the (a) and (b) theorems below feed `W₂.image
-- IntExtNode.unsplit` (resp. `W₁.image IntExtNode.unsplit`) into the
-- outer `extendingCDMGsWith` / `hardInterventionOn` constructor applied
-- to the inner `G.extendingCDMGsWith W _`.  Both outer constructors
-- demand a subset proof against the inner carrier
-- `(G.extendingCDMGsWith W hW).J ∪ (G.extendingCDMGsWith W hW).V`.  The
-- rewritten tex's first well-typedness bullet (lines 39-40) proves
-- exactly this lift: every `v ∈ S ⊆ G.J ∪ G.V` injects as `.unsplit v`
-- into either `G.J.image .unsplit ⊆ (extended).J` (when `v ∈ G.J`) or
-- `G.V.image .unsplit = (extended).V` (when `v ∈ G.V`).  No
-- disjointness with `W` is needed — the `(W \ G.J).image .intCopy`
-- piece of `(extended).J` is never reached by `.unsplit`-tagged
-- elements (constructor mismatch).
--
-- ## Design choice
--
-- *Standalone helper, not an inline `by`-block in the theorem signature.*
--   The outer constructor needs a *proof term* for its `hW` argument,
--   not a tactic blob.  Inlining a `by`-block in the type was rejected
--   because (i) it would clutter the rendered statement on the website
--   with pure carrier-subset bookkeeping, and (ii) it would duplicate
--   the same `.unsplit`-injection reasoning at every of the four
--   carrier sites the theorems use (LHS_iter12 / LHS_iter21 of (a),
--   LHS / mixed_def of (b)).  Mirrors the
--   `image_unsplit_subset_nodeSplittingOn_V` pattern from `claim_3_7`
--   (`TwoDisjointNode`) and the
--   `subset_carrier_of_hardInterventionOn` pattern from `claim_3_4`
--   (`HardInterventionsCommute`).
--
-- *Subset-transport form (`S ⊆ G.J ∪ G.V → S.image .unsplit ⊆ …`), not
--   a set-equality form.*  The transport form is what the theorem
--   signatures consume directly; a separate equality lemma would be one
--   step further from the call site and would force a
--   `Finset.Subset.trans` rewrite at every use site.
--
-- *Implicit `G`, `W`, `S`; explicit `hW`, `hS`.*  Mirrors the binder
--   convention of `def_3_13` (`extendingCDMGsWith`) and `def_3_10`
--   (`hardInterventionOn`).  At the call site
--   `image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂`, the
--   implicit arguments are synthesised from the goal and the call
--   reads left-to-right as "the inner extension is on `W₁` via `hW₁`;
--   the lifted set is `S = W₂` via `hW₂`".  Symmetric in `W₁`/`W₂`: the
--   same helper covers both
--   `image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂` (for
--   `W₂.image .unsplit` inside `(G.extendingCDMGsWith W₁ hW₁)`) and
--   `image_unsplit_subset_extendingCDMGsWith_carrier hW₂ hW₁` (for
--   `W₁.image .unsplit` inside `(G.extendingCDMGsWith W₂ hW₂)`).
--
-- *No disjointness consumed.*  Sub-claims (a) and (b) both require
--   `Disjoint W₁ W₂` as a hypothesis, but the well-typedness of the
--   iterated constructors does NOT consume it (it only enters the
--   *content* of the equality, not the *type*).  See the tex's "the
--   well-typedness paragraphs do not consume disjointness" remark
--   (lines 39-43).
--
-- *`private`, with helper markers.*  Localises the lemma to this file
--   so the `CDMG` namespace stays clean.  Helper markers wrap it so the
--   website builder pulls it out alongside the rendered statement
--   (without which the theorem heads would reference undefined
--   symbols).  Downstream rows mixing intervention-node extension with
--   hard intervention (e.g.\ `claim_3_15`, the do-calculus chapters,
--   the iSCM intervention algebra of ch.\ 8+) should re-introduce the
--   same private helper at their use site rather than reach across
--   files.
--
-- *Mathlib re-use.*  Built directly on `Finset.mem_image`,
--   `Finset.mem_union`, and constructor-disjointness of `IntExtNode`;
--   no rolled-our-own abstraction is needed.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: image_unsplit_subset_extendingCDMGsWith_carrier
-- claim_3_14 --- start helper
private lemma image_unsplit_subset_extendingCDMGsWith_carrier
    {G : CDMG Node} {W : Finset Node} (hW : W ⊆ G.J ∪ G.V)
    {S : Finset Node} (hS : S ⊆ G.J ∪ G.V) :
    S.image IntExtNode.unsplit ⊆
      (G.extendingCDMGsWith W hW).J ∪ (G.extendingCDMGsWith W hW).V
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
-- REFACTOR-BLOCK-ORIGINAL-END: image_unsplit_subset_extendingCDMGsWith_carrier

-- ## Helper — carrier-subset transport for hard intervention (no disjointness)
--
-- Sub-claim (b)'s middle term `(G.hardInterventionOn W₂ hW₂).extendingCDMGsWith
-- W₁ ?_` requires `?_ : W₁ ⊆ (G.hardInterventionOn W₂ hW₂).J ∪
-- (G.hardInterventionOn W₂ hW₂).V = (G.J ∪ W₂) ∪ (G.V \ W₂)`.  This holds
-- without any disjointness: every `v ∈ W₁` with `v ∈ G.J` lands in
-- `G.J ∪ W₂`, and every `v ∈ W₁` with `v ∈ G.V` lands in either
-- `G.J ∪ W₂` (if also `v ∈ W₂`) or `G.V \ W₂` (otherwise).  Mirrors
-- `subset_carrier_of_hardInterventionOn` from `claim_3_4`
-- (`HardInterventionsCommute.lean`).
--
-- ## Design choice
--
-- *Stand-alone helper, not an inline `by`-block in the theorem signature.*
--   Same rationale as the sibling helper above:
--   `extendingCDMGsWith`'s outer constructor needs a proof term, not a
--   tactic blob, and inlining would clutter the rendered statement and
--   duplicate the case-split at every use site.  Mirrors the
--   `subset_carrier_of_hardInterventionOn` pattern from `claim_3_4`.
--
-- *`S ⊆ G.J ∪ G.V → S ⊆ (G.hardInterventionOn W hW).J ∪ …` transport, not
--   a set-equality `(G.hardInterventionOn W hW).J ∪ … = G.J ∪ G.V`.*
--   The transport form is what the statement consumes directly; a
--   separate equality lemma would force a `Finset.Subset.trans` at
--   every use site.
--
-- *No disjointness hypothesis.*  Hard intervention's carrier
--   `(G.J ∪ W) ∪ (G.V \ W)` always contains `G.J ∪ G.V` regardless of
--   whether `S` overlaps `W`: the case-split on `v ∈ W` lands either
--   side cleanly.  This mirrors `claim_3_4`'s reading and is what makes
--   the transport reusable across both (b)'s middle term and any
--   downstream `doit`-then-`doit(I_·)` row.
--
-- *`private`, with helper markers.*  Same rationale as the sibling
--   helper above.  Re-introduces the `claim_3_4` private lemma here
--   rather than reaching across files (per the standard chapter
--   convention).
--
-- *Mathlib re-use.*  Built directly on `Finset.mem_union`,
--   `Finset.mem_sdiff`; no abstraction needed.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: subset_carrier_of_hardInterventionOn
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
-- REFACTOR-BLOCK-ORIGINAL-END: subset_carrier_of_hardInterventionOn

-- ## Helper — the canonical flatten map `IntExtNode (IntExtNode Node) → IntExtNode Node`
--
-- Realises the LN's "canonical bijection of carriers" induced by
-- `def_3_13`'s convention `I_v := v` for `v ∈ J` (i.e.\ the lifted
-- `.unsplit v` plays the role of `v` itself in the inner extension).
-- On the *iterated* carrier (the elements that actually inhabit
-- `((G.extendingCDMGsWith W₁ hW₁).extendingCDMGsWith
--    (W₂.image .unsplit) ·).J ∪ … V`):
--
--   .unsplit (.unsplit v) ↦ .unsplit v   (v ∈ G.J ∪ G.V; original node)
--   .unsplit (.intCopy w) ↦ .intCopy w   (w ∈ W₁ \ G.J; inner I-copy)
--   .intCopy (.unsplit v) ↦ .intCopy v   (v ∈ W₂; outer I-copy of an
--                                          unsplit original)
--   .intCopy (.intCopy _) ↦ .intCopy _   (off-carrier; never reached
--                                          when the outer extension's
--                                          `W_j` is `Wⱼ.image .unsplit`)
--
-- The off-carrier case `.intCopy (.intCopy _)` never appears in the
-- iterated carrier because the outer extension ranges over
-- `Wⱼ.image .unsplit \ (inner J)`, every element of which has the
-- shape `.unsplit _` — so the outer `.intCopy` is only ever applied to
-- `.unsplit` arguments.  The filler value `.intCopy w` is chosen for
-- totality of the pattern match and does not affect the equality this
-- row asserts.
--
-- ## Design choice
--
-- *Function, not `Equiv` of types.*  A type-level
--   `IntExtNode (IntExtNode Node) ≃ IntExtNode Node` does not exist:
--   when `Node` is non-empty, the source has four reachable constructor
--   combinations per node and the target only two, so no bijection on
--   the underlying types is possible.  `flattenIntExt` is instead
--   injective only when restricted to the *iterated carrier*
--   `(G.J ∪ V).image .unsplit ∪ (W₁ \ G.J).image .intCopy ∪
--    W₂.image (.intCopy ∘ .unsplit)`, and the disjointness hypothesis
--   `Disjoint W₁ W₂` is precisely what makes that restricted injection
--   well-defined (without it, `.unsplit (.intCopy w)` for `w ∈ W₁` and
--   `.intCopy (.unsplit w)` for `w ∈ W₂` could both lie in the carrier
--   and would both map to `.intCopy w`, conflating two distinct
--   intervention nodes).  Image-level reasoning via
--   `Finset.image flattenIntExt` is enough for the statement; the
--   proof of the (a) theorem will only ever apply `flattenIntExt` to
--   elements actually in the iterated carrier.
--
-- *Total pattern match on `IntExtNode (IntExtNode Node)`.*  Lean
--   requires total functions; the off-carrier case
--   `.intCopy (.intCopy _)` is filled in with the simplest value that
--   keeps the pattern match exhaustive.  Its value does not affect the
--   equality this row asserts because `Finset.image` over the iterated
--   carrier never reaches it.  Mirrors the totality-fillers convention
--   in `claim_3_7`'s `flattenSplit`.
--
-- *Same `flattenIntExt` for the iter12 and iter21 directions.*  The
--   case-analysis above is symmetric in `W₁` / `W₂`: the constructors
--   `.unsplit` / `.intCopy` are blind to which `Wᵢ` the underlying node
--   belongs to.  So the same flatten map handles both iteration orders,
--   matching the `claim_3_7`'s `flattenSplit` pattern (where a single
--   flatten map covers `iter₁₂` and `iter₂₁` because `SplitNode`'s
--   constructors are also blind to `Wᵢ` provenance).
--
-- *Mathlib re-use.*  Rolled our own — Mathlib carries no general
--   "flatten nested tagged sum" map specific to the `unsplit / intCopy`
--   pair of `def_3_13`.  Mirrors the `claim_3_7` rationale.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: flattenIntExt
-- claim_3_14 --- start helper
def flattenIntExt : IntExtNode (IntExtNode Node) → IntExtNode Node
  | .unsplit (.unsplit v) => IntExtNode.unsplit v
  | .unsplit (.intCopy w) => IntExtNode.intCopy w
  | .intCopy (.unsplit v) => IntExtNode.intCopy v
  | .intCopy (.intCopy w) => IntExtNode.intCopy w
-- claim_3_14 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: flattenIntExt

-- ## Helper — the mixed-notation CDMG `G_{doit(I_{W₁}, W₂)}`
--
-- The rewritten canonical tex (lines 45-48) introduces the
-- mixed-notation `G_{doit(I_{W₁}, W₂)}` for the first time in this
-- lemma, and defines it explicitly as the composition of `doit(I_{W₁})`
-- (def_3_13) followed by `doit(W₂)` (def_3_10):
--   `G_{doit(I_{W₁}, W₂)} := (G_{doit(I_{W₁})})_{doit(W₂)}`.
-- We mirror this definition literally: the result lives in
-- `CDMG (IntExtNode Node)` (the carrier of the inner
-- `extendingCDMGsWith`), and the outer `hardInterventionOn` lifts
-- `W₂ : Finset Node` to `W₂.image IntExtNode.unsplit : Finset (IntExtNode
-- Node)` via the canonical inclusion `ι : J ∪ V ↪ IntExtNode Node`
-- (i.e.\ the `.unsplit` constructor).  The subset proof for the outer
-- `hardInterventionOn`'s `hW` argument is discharged by the sibling
-- helper `image_unsplit_subset_extendingCDMGsWith_carrier`.
--
-- ## Design choice
--
-- *Define as composition, not as a fresh primitive constructor.*  The
--   tex's `:=` makes the definition a notational abbreviation, not a
--   new operation.  Implementing it as a Lean `def` rather than a
--   theorem-side `let` keeps the abbreviation reusable by downstream
--   rows that compose `extendingCDMGsWith` with `hardInterventionOn`
--   (chapter 5 do-calculus, chapter 8+ iSCM intervention algebra).  An
--   alternative — defining the mixed notation as a stand-alone CDMG
--   record constructed field-by-field — was rejected because the tex
--   explicitly *defines* the notation as the composition, so any
--   field-level encoding would either (i) need to be proven equal to
--   the composition (extra work for no semantic gain) or (ii) deviate
--   from the LN's own definition.
--
-- *Two `hW` hypotheses (`hW₁` for inner, `hW₂` for the outer-lift's
--   `hS` precondition), no disjointness.*  The mixed notation is
--   well-defined for *any* `W₁, W₂ ⊆ G.J ∪ G.V` — disjointness is a
--   property of sub-claim (b)'s equality, not of the well-typedness of
--   the mixed-notation CDMG itself.  Mirrors the tex's "Definition of
--   the mixed-argument notation" paragraph (lines 45-48) which does
--   not mention disjointness.
--
-- *Argument order `(G : CDMG Node) (W₁ W₂ : Finset Node) (hW₁ : …)
--   (hW₂ : …)`.*  Matches the natural reading order "extend by `W₁`,
--   then hard-intervene on `W₂`": `W₁` comes first because the inner
--   `extendingCDMGsWith` is applied first.  At the call site
--   `addInterventionNodesAndHardInterventionOn G W₁ W₂ hW₁ hW₂`, the
--   ordered argument list reads top-to-bottom like the tex's
--   `G_{doit(I_{W₁}, W₂)}` notation.
--
-- *Carrier `IntExtNode Node`, not `IntExtNode (IntExtNode Node)` nor
--   a fresh tagged sum.*  Following the composition definition: the
--   inner `extendingCDMGsWith` lifts to `IntExtNode Node`, and the
--   outer `hardInterventionOn` preserves that carrier.  No carrier
--   mismatch arises for sub-claim (b) — every CDMG in the equality
--   chain lives in `CDMG (IntExtNode Node)`, which is what makes (b)
--   a literal `=` (vs. (a)'s `eqViaNodeMap`-via-`flattenIntExt`).
--
-- *Wrapped with `--- start helper` markers.*  Sub-claim (b)'s theorem
--   signature references this `def` as the mixed-notation CDMG, so
--   removing the helper would cause the theorem signature to fail to
--   compile.  Per the prompt's litmus test, the helper is wrapped so
--   the website builder pulls it out alongside the rendered statement.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: addInterventionNodesAndHardInterventionOn
-- claim_3_14 --- start helper
def addInterventionNodesAndHardInterventionOn (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V) :
    CDMG (IntExtNode Node) :=
  (G.extendingCDMGsWith W₁ hW₁).hardInterventionOn
      (W₂.image IntExtNode.unsplit)
      (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)
-- claim_3_14 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: addInterventionNodesAndHardInterventionOn

-- ref: claim_3_14 (sub-claim (a))
-- For any CDMG `G : CDMG Node` and any two disjoint subsets
-- `W₁, W₂ ⊆ G.J ∪ G.V`, the LN's triple coincidence
--   `(G_{doit(I_{W₁})})_{doit(I_{W₂})} = (G_{doit(I_{W₂})})_{doit(I_{W₁})}
--      = G_{doit(I_{W₁ ∪ W₂})}`
-- decomposes (per the rewritten tex's "componentwise" reading at line
-- 60) into two CDMG equalities read up to the canonical flatten map
-- `flattenIntExt`:
--   (a-1) `eqViaNodeMap (LHS_iter12) (RHS_joint) flattenIntExt`,
--   (a-2) `eqViaNodeMap (LHS_iter21) (RHS_joint) flattenIntExt`.
-- Transitivity recovers the LN's "swap symmetry" reading
--   `(G_{doit(I_{W₁})})_{doit(I_{W₂})} = (G_{doit(I_{W₂})})_{doit(I_{W₁})}`
-- from (a-1) ∧ (a-2) via the shared right-hand side.
/-
LN tex (rewritten canonical statement for claim_3_14, sub-claim (a)):

  Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ J ∪ V` be two
  subsets of nodes of `G` with `W₁ ∩ W₂ = ∅`.  Then
    (a) `(G_{doit(I_{W₁})})_{doit(I_{W₂})} = (G_{doit(I_{W₂})})_{doit(I_{W₁})}
            = G_{doit(I_{W₁ ∪ W₂})}`,
  read componentwise on the four components `(J, V, E, L)` of
  def \ref{def-cdmg}, with the LN's "componentwise equality" understood
  up to the canonical bijection of carriers induced by the
  unsplit-inclusion `ι : J ∪ V ↪ IntExtNode Node`.

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CDMG and `W_1, W_2 ⊆ J ∪ V` two disjoint
  subsets of nodes from `G`.  Then we have:
    `(G_{doit(I_{W_1})})_{doit(I_{W_2})} = (G_{doit(I_{W_2})})_{doit(I_{W_1})}
        = G_{doit(I_{W_1 ∪ W_2})}`.
-/
-- ## Design choice — sub-claim (a)
--
-- *One theorem returning a conjunction (a-1) ∧ (a-2), with the joint
--   `G_{doit(I_{W₁ ∪ W₂})}` as the shared right-hand side.*  Mirrors
--   the `claim_3_4` (`HardInterventionsCommute`) / `claim_3_7`
--   (`TwoDisjointNode`) pattern: a triple equality `A = B = C` is
--   decomposed as `A = C ∧ B = C`, and the LN's swap-symmetry reading
--   `A = B` is recovered via transitivity through the shared right-
--   hand side `C`.  This row inherits the pattern from `claim_3_7`
--   because the iterated extension introduces the same kind of
--   carrier nesting (`IntExtNode (IntExtNode Node)`) that `claim_3_7`
--   handled with `SplitNode (SplitNode Node)`.
--
-- *Why `eqViaNodeMap iter joint flattenIntExt`, not literal `=`.*
--   The LHS_iter12 and LHS_iter21 both live in `CDMG (IntExtNode
--   (IntExtNode Node))`, but the joint RHS lives in `CDMG (IntExtNode
--   Node)` (a strictly different Lean type).  A literal `iter = joint`
--   is therefore *not type-correct* — Lean's `=` requires the same
--   type on both sides.  The LN's "the same CDMG" reading is rendered
--   as `eqViaNodeMap`: the four `Finset` data fields of the iterated
--   extension, after applying `flattenIntExt` field-wise, coincide
--   with the four `Finset` data fields of the joint extension.  This
--   is the strongest equality form available without introducing
--   quotient types or a `CDMG.Iso` layer.  Mirrors the `claim_3_7`
--   pattern (which faces the analogous `SplitNode (SplitNode Node)`
--   vs `SplitNode Node` mismatch).
--
-- *Why a literal `iter12 = iter21` would be false in Lean even though
--   the LN reads them as the same CDMG.*  At the Lean level, LHS_iter12
--   and LHS_iter21 share the same carrier type `IntExtNode (IntExtNode
--   Node)`, but the *constructor wrappings* of the same underlying
--   intervention symbol disagree: a node `w ∈ W₁` (assuming
--   `w ∈ G.V \ G.J`) appears as `.unsplit (.intCopy w)` in iter12 (the
--   inner extension on `W₁` creates `.intCopy w : IntExtNode Node`,
--   then the outer extension wraps it under `.unsplit`) but as
--   `.intCopy (.unsplit w)` in iter21 (the inner extension on `W₂`
--   leaves `w` as `.unsplit w : IntExtNode Node`, then the outer
--   extension on `W₁` creates `.intCopy (.unsplit w)`).  A literal
--   `iter12 = iter21` is therefore *false* — the four `Finset` fields
--   contain different constructor combinations even though they
--   describe the same abstract graph.  Routing both through the
--   canonical joint `G_{doit(I_{W₁ ∪ W₂})}` via the same
--   `flattenIntExt` image-level relabelling is the mathematically
--   faithful encoding; "swap symmetry" is recovered as the transitive
--   composite.
--
-- *Disjointness `Disjoint W₁ W₂` is genuinely load-bearing for the
--   equality (a) to hold, not merely a side condition for well-
--   typedness.*  Without disjointness, a node `v ∈ W₁ ∩ W₂ ∩ G.V`
--   would receive *two* intervention edges in iter12 (one from each
--   layer of extension), whereas the joint `G_{doit(I_{W₁ ∪ W₂})}`
--   adds only a *single* intervention edge for `v` (since
--   `(W₁ ∪ W₂) \ G.J` contains `v` only once).  The disjointness
--   hypothesis is therefore content-load-bearing — the iterated
--   constructor counts each shared-node intervention twice, while
--   the joint construction counts it once, and only `W₁ ∩ W₂ = ∅`
--   collapses the two counts.  The well-typedness of the iterated
--   constructors does NOT consume disjointness (the
--   `image_unsplit_subset_extendingCDMGsWith_carrier` helper above is
--   disjointness-free); disjointness enters only inside the proof
--   body, in the componentwise checks.
--
-- *Disjoint-union encoding: `W₁ ∪ W₂` together with `Disjoint W₁ W₂`,
--   not `Finset.disjUnion`.*  Matches `def_3_13`'s `extendingCDMGsWith`
--   API which takes `W : Finset Node`, so the natural right-hand side
--   is `G.extendingCDMGsWith (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)`.
--   The `Disjoint W₁ W₂` hypothesis (Mathlib's `Finset.Disjoint`, i.e.\
--   intersection-empty) is the canonical Lean shape for the LN's
--   "`W_1 ∩ W_2 = \emptyset`" and destructs via
--   `Finset.disjoint_left`/`Finset.disjoint_right` for the field-level
--   checks downstream.  Encoding the LN's `W_1 ∩ W_2 = ∅` as a raw
--   `Finset.inter` equality was rejected because the `Disjoint` form
--   integrates more smoothly with the `Finset` API.
--
-- *`hW₁ : W₁ ⊆ G.J ∪ G.V` and `hW₂ : W₂ ⊆ G.J ∪ G.V`, not
--   `Wᵢ ⊆ G.V` (the LN's literal wording is `J ∪ V`).*  Mirrors
--   `def_3_13`'s precondition; the tex's "corner cases `W_i ⊆ J` are
--   admitted" remark (line 27) confirms this.  Overlap with `J` is
--   permitted — the corresponding intervention-node addition reduces
--   to the identity by `def_3_13`'s `I_j := j` convention (encoded
--   at the carrier level as no `.intCopy` constructor for `j ∈ G.J`),
--   and the lemma is vacuously true on that branch.  Reading
--   `Wᵢ ⊆ G.V` would be a strictly stronger hypothesis — strictly
--   *weakening* the lemma — and would not match the LN's literal
--   wording.
--
-- *Result is a CDMG equality (modulo `flattenIntExt`), not a graph-
--   isomorphism or `Equiv`.*  The LN says "the same CDMG", and the
--   four-field componentwise reading of `eqViaNodeMap` (per
--   `claim_3_7`) is the closest Lean rendering of this without
--   introducing quotient types.  Per the rewritten tex's line 60
--   ("the conjunctive unpacking into these four field-by-field
--   equalities is deferred to the proof"), the four conjuncts of
--   `eqViaNodeMap` are exactly the unpacked componentwise checks the
--   tex anticipates.
--
-- *Note on the `linter.unusedVariables` exemption below.*  The
--   tex proof for sub-claim (a) cites the `Disjoint W₁ W₂` hypothesis
--   in the J-component and E-component steps to argue "the two
--   fresh-symbol index sets are disjoint, so their union deduplicates
--   correctly".  In the Lean `Finset` encoding, however, the
--   set-union `∪` always deduplicates by definition, and the
--   set-difference identity `(W₁ \ G.J) ∪ (W₂ \ G.J) = (W₁ ∪ W₂) \ G.J`
--   holds without disjointness.  So `hDisj` is bound on the signature
--   for LN-faithfulness (the tex statement carries it) but is not
--   consumed by the proof body; the linter exemption silences the
--   resulting "unused variable" warning without dropping the binder.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: addInterventionNodes_comm_disjoint
set_option linter.unusedVariables false in
-- claim_3_14 -- start statement
theorem addInterventionNodes_comm_disjoint (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    eqViaNodeMap
        ((G.extendingCDMGsWith W₁ hW₁).extendingCDMGsWith
            (W₂.image IntExtNode.unsplit)
            (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂))
        (G.extendingCDMGsWith (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenIntExt
      ∧
    eqViaNodeMap
        ((G.extendingCDMGsWith W₂ hW₂).extendingCDMGsWith
            (W₁.image IntExtNode.unsplit)
            (image_unsplit_subset_extendingCDMGsWith_carrier hW₂ hW₁))
        (G.extendingCDMGsWith (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        flattenIntExt
-- claim_3_14 -- end statement
:= by
  -- ## Flatten collapses for image-composition manipulation.
  --
  -- Each composition `flattenIntExt ∘ .unsplit ∘ .unsplit` (etc.) reduces
  -- by `rfl` from the pattern-match clauses of `flattenIntExt` followed by
  -- β / η.  We pre-compute the three needed collapses as standalone
  -- equalities so the four field goals can chain them via `Finset.image_image`.
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
  -- ## Edge-pair collapses (E and L components carry `Prod.map`-style lifts).
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
  -- ## The carrier-sdiff lift identity (tex proof's `W \ J₁ = W \ J` step).
  --
  -- For any `W' W : Finset Node`, the set-theoretic identity
  --   `W.image .unsplit \ (G.J.image .unsplit ∪ (W' \ G.J).image .intCopy)
  --      = (W \ G.J).image .unsplit`
  -- holds because: (i) `.unsplit`-tagged elements can never lie in the
  -- `.intCopy`-tagged piece (constructor disjointness); (ii)
  -- `.unsplit v ∈ G.J.image .unsplit ↔ v ∈ G.J` (constructor injectivity).
  -- This realises the tex proof's freshness clause: `W \ J₁ = W \ J`
  -- because the fresh `I_w` symbols (here `.intCopy`-tagged) are
  -- type-disjoint from `.unsplit`-tagged nodes.
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
  --
  -- `(W₁ \ G.J) ∪ (W₂ \ G.J) = (W₁ ∪ W₂) \ G.J` is pure set algebra
  -- (Mathlib's `Finset.union_sdiff_distrib` reversed).  Disjointness
  -- of `W₁` and `W₂` is *not* consumed here — the identity holds for
  -- any pair of sets and any common subtrahend.
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
  · change ((G.L.image
                (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
                (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
            (Prod.map flattenIntExt flattenIntExt)
          = G.L.image (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
    exact h_E_lift_uu_collapse G.L
  -- ===================== (a-2): iter₂₁ → joint =====================
  -- Same arguments with `W₁ ↔ W₂` swapped; the joint RHS still uses
  -- `W₁ ∪ W₂`, so the final `Finset.union_comm W₁ W₂` step realigns
  -- the union after the sdiff-collapse.
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
  · change ((G.L.image
                (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
                (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
            (Prod.map flattenIntExt flattenIntExt)
          = G.L.image (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
    exact h_E_lift_uu_collapse G.L
-- REFACTOR-BLOCK-ORIGINAL-END: addInterventionNodes_comm_disjoint

-- ref: claim_3_14 (sub-claim (b))
-- For any CDMG `G : CDMG Node` and any two disjoint subsets
-- `W₁, W₂ ⊆ G.J ∪ G.V`, the LN's triple coincidence
--   `(G_{doit(I_{W₁})})_{doit(W₂)} = (G_{doit(W₂)})_{doit(I_{W₁})}
--      = G_{doit(I_{W₁}, W₂)}`
-- decomposes into the conjunction of two literal CDMG equalities
-- (both over the carrier `IntExtNode Node`, with no flatten map needed):
--   (b-1) `(G.extendingCDMGsWith W₁ _).hardInterventionOn (W₂.image .unsplit) _
--             = addInterventionNodesAndHardInterventionOn G W₁ W₂ hW₁ hW₂`,
--   (b-2) `(G.hardInterventionOn W₂ _).extendingCDMGsWith W₁ _
--             = addInterventionNodesAndHardInterventionOn G W₁ W₂ hW₁ hW₂`.
-- The first conjunct (b-1) is `rfl` by the definition of
-- `addInterventionNodesAndHardInterventionOn` (which is literally
-- `(G.extendingCDMGsWith W₁ hW₁).hardInterventionOn (W₂.image .unsplit) _`);
-- it is included for parity with sub-claim (a)'s
-- `iter₁₂ = joint ∧ iter₂₁ = joint` shape and to make the LN's
-- "three CDMGs coincide" reading explicit in the theorem signature.
-- The second conjunct (b-2) is the genuine content — the LN's
-- "the genuine content is `LHS = middle`" remark (line 58) reads, after
-- folding `LHS := addInterventionNodesAndHardInterventionOn …`, as
-- `middle = addInterventionNodesAndHardInterventionOn …`.
/-
LN tex (rewritten canonical statement for claim_3_14, sub-claim (b)):

  Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ J ∪ V` be two
  subsets of nodes of `G` with `W₁ ∩ W₂ = ∅`.  Define
    `G_{doit(I_{W₁}, W₂)} := (G_{doit(I_{W₁})})_{doit(W₂)}`.
  Then
    (b) `(G_{doit(I_{W₁})})_{doit(W₂)} = (G_{doit(W₂)})_{doit(I_{W₁})}
            = G_{doit(I_{W₁}, W₂)}`,
  read componentwise on the four components `(J, V, E, L)`.  Equivalently,
  the equality `(G_{doit(I_{W₁})})_{doit(W₂)} = (G_{doit(W₂)})_{doit(I_{W₁})}`
  is the genuine content; the third term is a recap of the defining
  equation of `G_{doit(I_{W₁}, W₂)}`.

LN block (verbatim, for backup):

  We also have:
    `(G_{doit(I_{W_1})})_{doit(W_2)} = (G_{doit(W_2)})_{doit(I_{W_1})}
       = G_{doit(I_{W_1}, W_2)}`.
-/
-- ## Design choice — sub-claim (b)
--
-- *One theorem returning a conjunction (b-1) ∧ (b-2), mirroring (a)'s
--   shape.*  Same rationale as sub-claim (a)'s decomposition: the LN's
--   triple coincidence is rendered as a conjunction of two binary
--   equalities, both with the mixed-notation `def`
--   `addInterventionNodesAndHardInterventionOn` as the shared right-
--   hand side.  This matches the (a) ∧ (b) shape of `claim_3_4`
--   (`HardInterventionsCommute`) and gives consumers a uniform `.1` /
--   `.2` projection convention across sub-claims (a) and (b).
--
-- *Literal `=` of CDMGs (not `eqViaNodeMap`, no flatten map).*  Per
--   the module-level docstring's "Carrier-mismatch wrinkle" paragraph:
--   `hardInterventionOn` preserves the node carrier, so applying it
--   either as the outer constructor (LHS of (b)) or as the inner
--   constructor (middle of (b)) yields a CDMG over the same carrier
--   `IntExtNode Node`.  No carrier mismatch arises, and the LN's
--   "the same CDMG" reading is delivered by Lean's structural `=`
--   directly.  Mirrors the literal-`=` pattern of `claim_3_4`
--   (`HardInterventionsCommute`).
--
-- *(b-1) is `rfl` by definition; (b-2) is the genuine content.*  By
--   `addInterventionNodesAndHardInterventionOn`'s definition, the
--   LHS of (b) is literally the helper def, so (b-1) is closed by
--   `rfl`.  The second conjunct (b-2) is the LN's "genuine content"
--   (line 58): the commutativity of intervention-node addition and
--   hard intervention.  Stating both conjuncts (rather than just
--   (b-2)) preserves the tex's three-CDMG presentation in the
--   theorem signature and parallels (a)'s
--   `iter₁₂ = joint ∧ iter₂₁ = joint` shape.
--
-- *Disjointness `Disjoint W₁ W₂` is genuinely load-bearing for (b-2),
--   not merely a side condition.*  Without disjointness, a node
--   `v ∈ W₁ ∩ W₂ ∩ (G.V \ G.J)` would receive a fresh `.intCopy v`
--   on the LHS (since `v ∈ W₁ \ G.J`) but would land in `J'` (with no
--   `.intCopy v`) on the middle term (since after `doit(W₂)`,
--   `v ∈ G.J ∪ W₂ = J'`, so `v ∈ W₁ ∩ J'` means `v ∉ W₁ \ J'` and no
--   fresh `.intCopy v` is created).  These two intervention layouts
--   disagree, so disjointness is content-load-bearing for the
--   equality.  Per `def_3_13`'s `W ∩ J = ∅`-corner-case behaviour
--   (`I_j := j` for `j ∈ J ∩ W`), overlap with `J` alone is
--   admissible — only `W₁ ∩ W₂ \ G.J ≠ ∅` triggers the layout
--   mismatch.
--
-- *Same `hW₁`, `hW₂`, `hDisj` binder shape as (a).*  Mirrors the (a)
--   theorem's binder order so consumers calling both theorems pass
--   identical hypothesis lists.  At the call site
--   `addInterventionNodes_comm_hardIntervention G W₁ W₂ hW₁ hW₂ hDisj`,
--   the argument list reads top-to-bottom like the tex's
--   "Let `G`, `W₁, W₂ ⊆ J ∪ V` with `W₁ ∩ W₂ = ∅`".
--
-- *Carrier of all three CDMGs is `IntExtNode Node`.*  Both the LHS
--   `(G.extendingCDMGsWith W₁ hW₁).hardInterventionOn (W₂.image
--   .unsplit) _` and the middle `(G.hardInterventionOn W₂ hW₂).
--   extendingCDMGsWith W₁ _` land in `CDMG (IntExtNode Node)`: the
--   inner `extendingCDMGsWith` lifts `Node → IntExtNode Node`, and
--   the outer / inner `hardInterventionOn` preserves whichever
--   carrier it acts on.  The mixed-notation helper
--   `addInterventionNodesAndHardInterventionOn` also lives in
--   `CDMG (IntExtNode Node)` by construction.  This shared carrier is
--   what makes (b) a literal-`=` claim (vs. (a)'s `eqViaNodeMap`).
--
-- *Outer-`hardInterventionOn`'s `hW` is discharged by
--   `image_unsplit_subset_extendingCDMGsWith_carrier` (same helper as
--   (a) uses).*  The outer `hardInterventionOn` of LHS has type
--   `(extended).hardInterventionOn (W₂.image .unsplit) ?_`, where `?_`
--   needs `W₂.image .unsplit ⊆ (extended).J ∪ (extended).V`.  The
--   sibling helper above discharges this, reusing it from (a).
--
-- *Inner-`extendingCDMGsWith`'s `hW` for the middle term is
--   discharged by `subset_carrier_of_hardInterventionOn`.*  The middle
--   `(G.hardInterventionOn W₂ hW₂).extendingCDMGsWith W₁ ?_` needs
--   `?_ : W₁ ⊆ (G.hardInterventionOn W₂ hW₂).J ∪ (G.hardInterventionOn
--   W₂ hW₂).V`.  The sibling helper above transports `hW₁` across
--   the hard-intervention carrier (no disjointness needed —
--   mechanically the same transport as in `claim_3_4`).
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: addInterventionNodes_comm_hardIntervention
-- claim_3_14 -- start statement
theorem addInterventionNodes_comm_hardIntervention (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (G.extendingCDMGsWith W₁ hW₁).hardInterventionOn
        (W₂.image IntExtNode.unsplit)
        (image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)
      = addInterventionNodesAndHardInterventionOn G W₁ W₂ hW₁ hW₂
      ∧
    (G.hardInterventionOn W₂ hW₂).extendingCDMGsWith W₁
        (subset_carrier_of_hardInterventionOn hW₂ hW₁)
      = addInterventionNodesAndHardInterventionOn G W₁ W₂ hW₁ hW₂
-- claim_3_14 -- end statement
:= by
  -- ## Inline CDMG extensionality on `CDMG (IntExtNode Node)`.
  --
  -- Two CDMGs are equal if their four data fields agree; the five
  -- propositional fields (`hJV_disj`, `hE_subset`, `hL_subset`,
  -- `hL_irrefl`, `hL_symm`) follow by proof irrelevance once the
  -- data fields are unified.  Mirrors `claim_3_4`'s `cdmgExt` helper.
  have cdmgExt : ∀ {G₁' G₂' : CDMG (IntExtNode Node)},
      G₁'.J = G₂'.J → G₁'.V = G₂'.V → G₁'.E = G₂'.E → G₁'.L = G₂'.L → G₁' = G₂' := by
    rintro ⟨J₁, V₁, hJV₁, E₁, hE₁, L₁, hL₁, hLi₁, hLs₁⟩
           ⟨J₂, V₂, hJV₂, E₂, hE₂, L₂, hL₂, hLi₂, hLs₂⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL
    rfl
  -- ## Disjointness-consuming carrier identity: `W₁ \ (G.J ∪ W₂) = W₁ \ G.J`.
  --
  -- This is the load-bearing place where `hDisj` enters the proof.
  -- The middle term's inner extension `(G.hardInterventionOn W₂ hW₂)
  -- .extendingCDMGsWith W₁ _` ranges the fresh `.intCopy w` symbols
  -- over `W₁ \ (G.J ∪ W₂)` (since after the hard intervention `G₂.J =
  -- G.J ∪ W₂`); the disjointness `W₁ ∩ W₂ = ∅` forces this set to
  -- collapse to `W₁ \ G.J`, matching the LHS's `(G.extendingCDMGsWith
  -- W₁ hW₁).hardInterventionOn …` (which ranges over `W₁ \ G.J`
  -- inside the inner extension, untouched by the outer hard
  -- intervention).
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
  -- Conjunction split: (b-1) closes by `rfl` (LHS is literally the
  -- definition of `addInterventionNodesAndHardInterventionOn`); (b-2)
  -- is the genuine content, established field-by-field via `cdmgExt`.
  refine ⟨rfl, ?_⟩
  -- ## (b-2): `middle = mixed` field-by-field.
  refine cdmgExt ?_ ?_ ?_ ?_
  -- ---------- J component ----------
  --   middle.J = (G.J ∪ W₂).image .unsplit ∪ (W₁ \ (G.J ∪ W₂)).image .intCopy
  --   mixed.J  = (G.J.image .unsplit ∪ (W₁ \ G.J).image .intCopy) ∪ W₂.image .unsplit
  -- Substituting `W₁ \ (G.J ∪ W₂) = W₁ \ G.J` and distributing
  -- `(G.J ∪ W₂).image .unsplit` reduces both sides to the same
  -- three-piece union up to reassociation / reordering.
  · change (G.J ∪ W₂).image IntExtNode.unsplit ∪ (W₁ \ (G.J ∪ W₂)).image IntExtNode.intCopy
          = G.J.image IntExtNode.unsplit ∪ (W₁ \ G.J).image IntExtNode.intCopy ∪
              W₂.image IntExtNode.unsplit
    rw [h_W₁_sdiff_collapse, Finset.image_union]
    rw [Finset.union_assoc, Finset.union_comm (W₂.image IntExtNode.unsplit) _,
        ← Finset.union_assoc]
  -- ---------- V component ----------
  --   middle.V = (G.V \ W₂).image .unsplit
  --   mixed.V  = G.V.image .unsplit \ W₂.image .unsplit
  -- These are equal because `.unsplit` is injective.
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
  --   middle.E = (G.E.filter (e.2 ∉ W₂)).image (.unsplit-lift) ∪
  --              (W₁ \ (G.J ∪ W₂)).image (.intCopy-.unsplit-transfer)
  --   mixed.E  = (G.E.image (.unsplit-lift) ∪
  --              (W₁ \ G.J).image (.intCopy-.unsplit-transfer)).filter
  --                (e.2 ∉ W₂.image .unsplit)
  -- After applying `h_W₁_sdiff_collapse` and pushing the filter through
  -- the union (`Finset.filter_union`), the two pieces match by the
  -- usual `.unsplit`-injection-based filter/image swap; the
  -- W₁-transfer piece's filter is vacuous because every
  -- `w ∈ W₁ \ G.J ⊆ W₁` satisfies `w ∉ W₂` by `hDisj`.
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
    -- Piece 1: (G.E.filter (e.2 ∉ W₂)).image (.unsplit-lift)
    --           = (G.E.image (.unsplit-lift)).filter (e.2 ∉ W₂.image .unsplit).
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
    -- Piece 2: (W₁ \ G.J).image (.intCopy-.unsplit-transfer)
    --           = ((W₁ \ G.J).image (.intCopy-.unsplit-transfer)).filter
    --                 (e.2 ∉ W₂.image .unsplit).
    -- The filter is vacuous on the W₁-transfer piece by disjointness.
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
  -- ---------- L component ----------
  --   middle.L = (G.L.filter (e.1 ∉ W₂ ∧ e.2 ∉ W₂)).image (.unsplit-lift)
  --   mixed.L  = (G.L.image (.unsplit-lift)).filter
  --                (e.1 ∉ W₂.image .unsplit ∧ e.2 ∉ W₂.image .unsplit)
  -- Standard filter/image swap via `.unsplit`-injectivity, two-sided.
  · change (G.L.filter (fun e : Node × Node => e.1 ∉ W₂ ∧ e.2 ∉ W₂)).image
              (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
          = (G.L.image
              (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).filter
              (fun e : IntExtNode Node × IntExtNode Node =>
                e.1 ∉ W₂.image IntExtNode.unsplit ∧ e.2 ∉ W₂.image IntExtNode.unsplit)
    ext ⟨a, b⟩
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨e, ⟨heL, he1, he2⟩, hab⟩
      have hae : a = IntExtNode.unsplit e.1 := by
        have := congrArg Prod.fst hab; simpa using this.symm
      have hbe : b = IntExtNode.unsplit e.2 := by
        have := congrArg Prod.snd hab; simpa using this.symm
      refine ⟨⟨e, heL, hab⟩, ?_, ?_⟩
      · rintro ⟨w, hwW, hweq⟩
        rw [hae] at hweq
        injection hweq with hwe
        exact he1 (hwe ▸ hwW)
      · rintro ⟨w, hwW, hweq⟩
        rw [hbe] at hweq
        injection hweq with hwe
        exact he2 (hwe ▸ hwW)
    · rintro ⟨⟨e, heL, hab⟩, h1, h2⟩
      have hae : a = IntExtNode.unsplit e.1 := by
        have := congrArg Prod.fst hab; simpa using this.symm
      have hbe : b = IntExtNode.unsplit e.2 := by
        have := congrArg Prod.snd hab; simpa using this.symm
      refine ⟨e, ⟨heL, ?_, ?_⟩, hab⟩
      · intro he1
        apply h1
        rw [hae]
        exact ⟨e.1, he1, rfl⟩
      · intro he2
        apply h2
        rw [hbe]
        exact ⟨e.2, he2, rfl⟩
-- REFACTOR-BLOCK-ORIGINAL-END: addInterventionNodes_comm_hardIntervention

end CDMG

-- ## `open CDMG` — bring `IntExtNode` and `refactor_extendingCDMGsWith`
-- into scope for the refactor twin
--
-- `def_3_13`'s `ExtendingCDMGsWith.lean` chose the single-namespace
-- pattern: the shared `inductive IntExtNode` and the refactor twin
-- `refactor_extendingCDMGsWith` both live inside `namespace CDMG`
-- alongside the pre-refactor `extendingCDMGsWith`.  Our refactor twin
-- below operates inside `namespace refactor_CDMG`, so we need to
-- bring those two identifiers into scope explicitly.  Dot notation
-- (`G.refactor_extendingCDMGsWith W hW`) would not work — it resolves
-- via the receiver's type namespace (`refactor_CDMG`), and
-- `refactor_extendingCDMGsWith` is registered under `CDMG`, not
-- `refactor_CDMG`.  Function-style calls (`refactor_extendingCDMGsWith
-- G W hW`) with `open CDMG` are the cleanest fix.  No name collisions
-- arise because every refactor-twin declaration below carries the
-- `refactor_` prefix.  `refactor_hardInterventionOn` and
-- `refactor_eqViaNodeMap` *are* in `namespace refactor_CDMG`, so dot
-- notation `G.refactor_hardInterventionOn` and function-style
-- `refactor_eqViaNodeMap` resolve directly without further imports.
namespace refactor_CDMG
open CDMG

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: variable_Node (was: refactor_variable_Node)
-- claim_3_14 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_14 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: variable_Node

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: image_unsplit_subset_extendingCDMGsWith_carrier (was: refactor_image_unsplit_subset_extendingCDMGsWith_carrier)
-- claim_3_14 --- start helper
private lemma refactor_image_unsplit_subset_extendingCDMGsWith_carrier
    {G : refactor_CDMG Node} {W : Finset Node} (hW : W ⊆ G.J ∪ G.V)
    {S : Finset Node} (hS : S ⊆ G.J ∪ G.V) :
    S.image IntExtNode.unsplit ⊆
      (refactor_extendingCDMGsWith G W hW).J ∪ (refactor_extendingCDMGsWith G W hW).V
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
-- REFACTOR-BLOCK-REPLACEMENT-END: image_unsplit_subset_extendingCDMGsWith_carrier

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: subset_carrier_of_hardInterventionOn (was: refactor_subset_carrier_of_hardInterventionOn)
-- claim_3_14 --- start helper
private lemma refactor_subset_carrier_of_hardInterventionOn
    {G : refactor_CDMG Node} {W : Finset Node} (hW : W ⊆ G.J ∪ G.V)
    {S : Finset Node} (hS : S ⊆ G.J ∪ G.V) :
    S ⊆ (G.refactor_hardInterventionOn W hW).J ∪ (G.refactor_hardInterventionOn W hW).V
-- claim_3_14 --- end helper
:= by
  intro v hv
  change v ∈ (G.J ∪ W) ∪ (G.V \ W)
  rcases Finset.mem_union.mp (hS hv) with hJ | hV
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
  · by_cases hW' : v ∈ W
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hW')
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, hW'⟩)
-- REFACTOR-BLOCK-REPLACEMENT-END: subset_carrier_of_hardInterventionOn

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: flattenIntExt (was: refactor_flattenIntExt)
-- claim_3_14 --- start helper
def refactor_flattenIntExt : IntExtNode (IntExtNode Node) → IntExtNode Node
  | .unsplit (.unsplit v) => IntExtNode.unsplit v
  | .unsplit (.intCopy w) => IntExtNode.intCopy w
  | .intCopy (.unsplit v) => IntExtNode.intCopy v
  | .intCopy (.intCopy w) => IntExtNode.intCopy w
-- claim_3_14 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: flattenIntExt

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: addInterventionNodesAndHardInterventionOn (was: refactor_addInterventionNodesAndHardInterventionOn)
-- claim_3_14 --- start helper
def refactor_addInterventionNodesAndHardInterventionOn (G : refactor_CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V) :
    refactor_CDMG (IntExtNode Node) :=
  (refactor_extendingCDMGsWith G W₁ hW₁).refactor_hardInterventionOn
      (W₂.image IntExtNode.unsplit)
      (refactor_image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)
-- claim_3_14 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: addInterventionNodesAndHardInterventionOn

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: addInterventionNodes_comm_disjoint (was: refactor_addInterventionNodes_comm_disjoint)
set_option linter.unusedVariables false in
-- claim_3_14 -- start statement
theorem refactor_addInterventionNodes_comm_disjoint (G : refactor_CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    refactor_eqViaNodeMap
        (refactor_extendingCDMGsWith
            (refactor_extendingCDMGsWith G W₁ hW₁)
            (W₂.image IntExtNode.unsplit)
            (refactor_image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂))
        (refactor_extendingCDMGsWith G (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        refactor_flattenIntExt
      ∧
    refactor_eqViaNodeMap
        (refactor_extendingCDMGsWith
            (refactor_extendingCDMGsWith G W₂ hW₂)
            (W₁.image IntExtNode.unsplit)
            (refactor_image_unsplit_subset_extendingCDMGsWith_carrier hW₂ hW₁))
        (refactor_extendingCDMGsWith G (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂))
        refactor_flattenIntExt
-- claim_3_14 -- end statement
:= by
  -- ## Flatten collapses for image-composition manipulation.
  --
  -- J/V flatten collapses (Node carrier) — port verbatim from the
  -- pre-refactor theorem, only `flattenIntExt → refactor_flattenIntExt`.
  have h_uu_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image IntExtNode.unsplit).image refactor_flattenIntExt
      = S.image IntExtNode.unsplit := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_iu_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image IntExtNode.intCopy).image refactor_flattenIntExt
      = S.image IntExtNode.intCopy := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_ui_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.intCopy).image IntExtNode.unsplit).image refactor_flattenIntExt
      = S.image IntExtNode.intCopy := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  -- E-pair collapses (Node × Node carrier; E field unchanged by refactor).
  have h_E_lift_uu_collapse : ∀ (S : Finset (Node × Node)),
      ((S.image (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
          (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
        (Prod.map refactor_flattenIntExt refactor_flattenIntExt)
      = S.image (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_W_transfer_inner_collapse : ∀ (S : Finset Node),
      ((S.image (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
          (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
        (Prod.map refactor_flattenIntExt refactor_flattenIntExt)
      = S.image (fun w : Node => (IntExtNode.intCopy w, IntExtNode.unsplit w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_W_transfer_outer_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image
          (fun w : IntExtNode Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
        (Prod.map refactor_flattenIntExt refactor_flattenIntExt)
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
  -- equality of `(refactor_flattenIntExt ∘ .unsplit) ∘ .unsplit` and
  -- `.unsplit` is by definitional pattern-match on
  -- `refactor_flattenIntExt (.unsplit (.unsplit v)) = .unsplit v`,
  -- hence `Sym2.map_congr` closes the goal via `rfl`.
  have h_L_lift_uu_collapse : ∀ (S : Finset (Sym2 Node)),
      ((S.image (Sym2.map IntExtNode.unsplit)).image
          (Sym2.map IntExtNode.unsplit)).image
        (Sym2.map refactor_flattenIntExt)
      = S.image (Sym2.map IntExtNode.unsplit) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro s _
    change Sym2.map refactor_flattenIntExt
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
              IntExtNode.intCopy).image refactor_flattenIntExt
          = G.J.image IntExtNode.unsplit ∪ ((W₁ ∪ W₂) \ G.J).image IntExtNode.intCopy
    rw [h_sdiff W₁ W₂]
    simp only [Finset.image_union]
    rw [h_uu_collapse, h_ui_collapse, h_iu_collapse]
    rw [Finset.union_assoc, ← Finset.image_union, h_sdiff_union]
  -- Sub-goal 2: V component for iter₁₂.
  · change ((G.V.image IntExtNode.unsplit).image IntExtNode.unsplit).image refactor_flattenIntExt
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
            (Prod.map refactor_flattenIntExt refactor_flattenIntExt)
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
            (Sym2.map refactor_flattenIntExt)
          = G.L.image (Sym2.map IntExtNode.unsplit)
    exact h_L_lift_uu_collapse G.L
  -- ===================== (a-2): iter₂₁ → joint =====================
  -- Sub-goal 5: J component for iter₂₁.
  · change ((G.J.image IntExtNode.unsplit ∪ (W₂ \ G.J).image IntExtNode.intCopy).image
              IntExtNode.unsplit
            ∪ (W₁.image IntExtNode.unsplit \
                (G.J.image IntExtNode.unsplit ∪
                  (W₂ \ G.J).image IntExtNode.intCopy)).image
              IntExtNode.intCopy).image refactor_flattenIntExt
          = G.J.image IntExtNode.unsplit ∪ ((W₁ ∪ W₂) \ G.J).image IntExtNode.intCopy
    rw [h_sdiff W₂ W₁]
    simp only [Finset.image_union]
    rw [h_uu_collapse, h_ui_collapse, h_iu_collapse]
    rw [Finset.union_assoc, ← Finset.image_union, h_sdiff_union', Finset.union_comm W₂ W₁]
  -- Sub-goal 6: V component for iter₂₁.
  · change ((G.V.image IntExtNode.unsplit).image IntExtNode.unsplit).image refactor_flattenIntExt
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
            (Prod.map refactor_flattenIntExt refactor_flattenIntExt)
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
            (Sym2.map refactor_flattenIntExt)
          = G.L.image (Sym2.map IntExtNode.unsplit)
    exact h_L_lift_uu_collapse G.L
-- REFACTOR-BLOCK-REPLACEMENT-END: addInterventionNodes_comm_disjoint

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: addInterventionNodes_comm_hardIntervention (was: refactor_addInterventionNodes_comm_hardIntervention)
-- claim_3_14 -- start statement
theorem refactor_addInterventionNodes_comm_hardIntervention (G : refactor_CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (refactor_extendingCDMGsWith G W₁ hW₁).refactor_hardInterventionOn
        (W₂.image IntExtNode.unsplit)
        (refactor_image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)
      = refactor_addInterventionNodesAndHardInterventionOn G W₁ W₂ hW₁ hW₂
      ∧
    refactor_extendingCDMGsWith (G.refactor_hardInterventionOn W₂ hW₂) W₁
        (refactor_subset_carrier_of_hardInterventionOn hW₂ hW₁)
      = refactor_addInterventionNodesAndHardInterventionOn G W₁ W₂ hW₁ hW₂
-- claim_3_14 -- end statement
:= by
  -- ## Inline refactor_CDMG extensionality on `refactor_CDMG (IntExtNode Node)`.
  --
  -- Two refactor_CDMGs are equal if their four data fields agree; the
  -- four propositional fields (`hJV_disj`, `hE_subset`, `hL_subset`,
  -- `hL_irrefl`) follow by proof irrelevance once the data fields are
  -- unified.  `refactor_CDMG` has 8 fields (one fewer than the
  -- pre-refactor `CDMG`'s 9 — `hL_symm` is gone under the Sym2
  -- encoding).
  have cdmgExt : ∀ {G₁' G₂' : refactor_CDMG (IntExtNode Node)},
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
-- REFACTOR-BLOCK-REPLACEMENT-END: addInterventionNodes_comm_hardIntervention

end refactor_CDMG

end Causality
