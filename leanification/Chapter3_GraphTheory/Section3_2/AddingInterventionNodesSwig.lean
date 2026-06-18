import Chapter3_GraphTheory.Section3_2.NodeSplittingHard
import Chapter3_GraphTheory.Section3_2.ExtendingCDMGsWith
import Chapter3_GraphTheory.Section3_2.TwoDisjointNode
import Chapter3_GraphTheory.Section3_2.AcyclicHardInterventionTopologicalOrder

namespace Causality

/-!
# Adding intervention nodes commutes with disjoint node-splitting hard interventions (`claim_3_15`)

This file formalises the LN claim `claim_3_15`
(`\label{adding-intervention-nodes-commutes-with-disjoint-node-splitting-hard-interventions}`
in `graphs.tex`, the SWIG analog of `claim_3_14`): for any CADMG
`G = (J, V, E, L)` and any two disjoint subsets `W₁ ⊆ V`,
`W₂ ⊆ J ∪ V`, the order of (i) introducing intervention nodes
`I_{W₂}` via `def_3_13`'s `extendingCDMGsWith` and (ii) performing
the node-splitting hard intervention `swig(W₁)` via `def_3_12`'s
`nodeSplittingHard` does not matter:
`(G_{swig(W₁)})_{doit(I_{W₂})} = (G_{doit(I_{W₂})})_{swig(W₁)}`.

## Carrier-mismatch wrinkle (the load-bearing Lean-shape decision)

The two sides of the LN's displayed equality live in *formally
distinct* iterated-tagged-sum Lean carriers:

* LHS `(G_{swig(W₁)})_{doit(I_{W₂})}` lives in
  `CDMG (IntExtNode (SplitNode Node))` — first `nodeSplittingHard`
  lifts to `SplitNode Node`, then `extendingCDMGsWith` wraps that
  under `IntExtNode`.
* RHS `(G_{doit(I_{W₂})})_{swig(W₁)}` lives in
  `CDMG (SplitNode (IntExtNode Node))` — first
  `extendingCDMGsWith` lifts to `IntExtNode Node`, then
  `nodeSplittingHard` wraps that under `SplitNode`.

`IntExtNode (SplitNode Node)` and `SplitNode (IntExtNode Node)` are
not Lean-equal as types, so a literal `=` between the two CDMGs is
not type-correct.  The LN's "the same CDMG" reading is rendered
via `claim_3_7`'s `eqViaNodeMap` predicate, with a canonical
flatten function `flattenSwigDoit : SplitNode (IntExtNode Node) →
IntExtNode (SplitNode Node)` that bridges the two carriers on the
reachable subset.  Same paradigm as `claim_3_14`(a)'s
`flattenIntExt`, applied here to the two-step swig-then-extend
tower vs. extend-then-swig tower instead of the iterated extend
tower.

The authoritative spec is the rewritten canonical tex statement
at `leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_15_statement_AddingInterventionNodes.tex`, verified
equivalent to the LN block (`graphs.tex` L877-886).
-/

namespace CDMG

-- ## Helper — variable binders for this row's declarations
--
-- *`variable` block, not `def`-local binders on each declaration.*
--   Mirrors the convention of every section-3.2 row.  The implicit
--   `Node : Type*` and `[DecidableEq Node]` auto-bind into the
--   helpers and the main theorem signature.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: variable_Node
-- claim_3_15 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_15 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: variable_Node

-- ## Private helper — `IsCADMG` witness for the inner extension
--
-- One-sentence summary: discharges the `IsCADMG` precondition that
-- the outer `nodeSplittingHard` of the LN-RHS branch (first operand
-- of `eqViaNodeMap` below) needs on the inner `extendingCDMGsWith`.
--
-- The RHS's outer `nodeSplittingHard ?hG ?W ?hW` needs an `IsCADMG`
-- witness on `G.extendingCDMGsWith W₂ hW₂` (because `def_3_12`
-- requires acyclicity of its input).  `claim_3_13`'s `extAcyclic`
-- provides exactly this — and since `IsCADMG := IsAcyclic` by
-- `def_3_7`, the projection is definitional.  Not LN content
-- (acyclicity preservation is `claim_3_13`), so unmarked — matches
-- `claim_3_11`'s use of `hardInterventionOn_isCADMG_of_isCADMG`
-- inline without a marker.
--
-- ## Design choice
--
-- *Thin specialisation wrapper, not a re-proof.*  Defined as the
--   exact term `extAcyclic G W hW hG`, capitalising on the
--   definitional unfolding `IsCADMG := IsAcyclic`; no separate
--   acyclicity argument is recomputed here.  Inlining
--   `extAcyclic hG hW₂` directly at the call site in the main
--   theorem signature was rejected for readability — the named
--   helper makes the LN-RHS branch's structure of the theorem head
--   `(G.extendingCDMGsWith W₂ hW₂).nodeSplittingHard ⟨isCADMG⟩ …`
--   read more transparently.
--
-- *No helper-marker wrap.*  This lemma is not LN content (the LN's
--   own remark after `def_3_13` is what `claim_3_13` formalises);
--   it exists purely as a Lean-side plumbing convenience.  Per the
--   chapter convention, plumbing helpers used only at a single
--   theorem head and not referenced by name in the LN are kept
--   marker-less so the website renderer does not pull them out as
--   first-class declarations.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: extendingCDMGsWith_isCADMG_of_isCADMG
private lemma extendingCDMGsWith_isCADMG_of_isCADMG
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    (G.extendingCDMGsWith W hW).IsCADMG :=
  extAcyclic G W hW hG
-- REFACTOR-BLOCK-ORIGINAL-END: extendingCDMGsWith_isCADMG_of_isCADMG

-- ## Helper — `W₁.image .unsplit ⊆ V_{doit(I_{W₂})}`
--
-- The RHS `(G.extendingCDMGsWith W₂ hW₂).nodeSplittingHard _
-- (W₁.image IntExtNode.unsplit) ?_` requires
-- `?_ : W₁.image .unsplit ⊆ (G.extendingCDMGsWith W₂ hW₂).V`.
-- By `def_3_13` item ii, `V_{doit(I_{W₂})} = G.V.image .unsplit`.
-- Since `W₁ ⊆ G.V` by `hW₁`, every `v ∈ W₁` lifts to
-- `.unsplit v ∈ G.V.image .unsplit`.  No disjointness needed.
--
-- ## Design choice
--
-- *Standalone helper, wrapped with three-dash markers — litmus test
--   for marker wrapping returns YES.*  The RHS's outer
--   `nodeSplittingHard _ (W₁.image .unsplit) ?_` reads the
--   conclusion of this lemma as its `?_`-precondition; the wrapped
--   main theorem head does not type-check without the named term.
--   Mirrors the `image_unsplit_subset_extendingCDMGsWith_carrier`
--   helper pattern from `claim_3_14`.
--
-- *Implicit `G`, `W₁`, `W₂`; explicit `hW₁`.*  At the call site
--   `image_unsplit_subset_extendingCDMGsWith_V hW₁`, the implicit
--   arguments are synthesised from the goal.  `hW₂` is not consumed
--   (the conclusion mentions `(G.extendingCDMGsWith W₂ hW₂).V`
--   which forces both `W₂` and `hW₂` via the goal-driven unifier).
--
-- *No disjointness consumed.*  Only `hW₁ : W₁ ⊆ G.V` is needed —
--   the extension preserves `V` literally (`V_{doit(I_W)} := V`,
--   per `def_3_13` item ii), so disjointness from `W₂` plays no
--   role on the `V`-component.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: image_unsplit_subset_extendingCDMGsWith_V
-- claim_3_15 --- start helper
private lemma image_unsplit_subset_extendingCDMGsWith_V
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V)
    {W₂ : Finset Node} {hW₂ : W₂ ⊆ G.J ∪ G.V} :
    W₁.image IntExtNode.unsplit ⊆ (G.extendingCDMGsWith W₂ hW₂).V
-- claim_3_15 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change IntExtNode.unsplit v ∈ G.V.image IntExtNode.unsplit
  exact Finset.mem_image.mpr ⟨v, hW₁ hv, rfl⟩
-- REFACTOR-BLOCK-ORIGINAL-END: image_unsplit_subset_extendingCDMGsWith_V

-- ## Helper — `W₂.image .unsplit ⊆ J_{swig(W₁)} ∪ V_{swig(W₁)}`
--
-- The LHS `(G.nodeSplittingHard hG W₁ hW₁).extendingCDMGsWith
-- (W₂.image SplitNode.unsplit) ?_` requires
-- `?_ : W₂.image .unsplit ⊆
--        (G.nodeSplittingHard hG W₁ hW₁).J ∪
--        (G.nodeSplittingHard hG W₁ hW₁).V`.
-- For each `w ∈ W₂`: `w ∈ G.J ∪ G.V` by `hW₂`; if `w ∈ G.J` then
-- `.unsplit w ∈ G.J.image .unsplit ⊆ J_{swig(W₁)}`; if `w ∈ G.V`
-- then `w ∉ W₁` by `Disjoint W₁ W₂`, so `w ∈ G.V \ W₁` and
-- `.unsplit w ∈ (G.V \ W₁).image .unsplit ⊆ V_{swig(W₁)}`.
-- Parallels the `claim_3_11` helper
-- `image_unsplit_subset_carrier_of_nodeSplittingHard` but with the
-- role of `W₁`/`W₂` swapped (here `W₂` is the lifted set and `W₁`
-- is the split set).
--
-- ## Design choice
--
-- *Standalone helper, wrapped with three-dash markers — litmus test
--   returns YES.*  The LHS's outer `extendingCDMGsWith` reads the
--   conclusion of this lemma as its `?_`-precondition; without the
--   named term, the wrapped main theorem head does not type-check.
--
-- *Implicit `hG`.*  Mirrors `claim_3_11`'s
--   `image_unsplit_subset_carrier_of_nodeSplittingHard` binder
--   convention: `hG` is inferred from the
--   `G.nodeSplittingHard hG W₁ hW₁` expression in the goal.
--
-- *Disjointness `Disjoint W₁ W₂` is load-bearing on the
--   `V`-branch.*  Without it, a `w ∈ W₂ ∩ W₁ ∩ G.V` would *not*
--   lie in `G.V \ W₁`, so `.unsplit w` could not be routed through
--   the `(G.V \ W₁).image .unsplit` summand of
--   `V_{swig(W₁)}` — it would have to land instead in
--   `W₁.image .copy0`, which has the wrong constructor.  The
--   well-typedness of the LHS therefore requires `Disjoint W₁ W₂`.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: image_unsplit_subset_nodeSplittingHard_carrier
-- claim_3_15 --- start helper
private lemma image_unsplit_subset_nodeSplittingHard_carrier
    {G : CDMG Node} {hG : G.IsCADMG}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.J ∪ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂.image SplitNode.unsplit ⊆
      (G.nodeSplittingHard hG W₁ hW₁).J ∪ (G.nodeSplittingHard hG W₁ hW₁).V
-- claim_3_15 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change SplitNode.unsplit v ∈
    (G.J.image SplitNode.unsplit ∪ W₁.image SplitNode.copy1) ∪
      ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0)
  rcases Finset.mem_union.mp (hW₂ hv) with hJ | hV
  · refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · have hvW₁ : v ∉ W₁ := Finset.disjoint_right.mp hDisj hv
    refine Finset.mem_union_right _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hV, hvW₁⟩, rfl⟩
-- REFACTOR-BLOCK-ORIGINAL-END: image_unsplit_subset_nodeSplittingHard_carrier

-- ## Helper — the canonical flatten map
--   `SplitNode (IntExtNode Node) → IntExtNode (SplitNode Node)`
--
-- Realises the LN's "canonical relabelling identifying" the LHS and
-- RHS carriers (rewritten tex's "Distinct carriers and the
-- canonical relabelling identifying them" paragraph).  The two
-- carriers each encode the same five-piece node universe
-- `J ∪ (V \ W₁) ∪ W₁^o ∪ W₁^i ∪ {I_w | w ∈ W₂ \ J}` but with the
-- constructor wrappings in opposite orders.  On the reachable
-- subset:
--
--   .unsplit (.unsplit v) ↦ .unsplit (.unsplit v)
--                            (v ∈ J ∪ (V \ W₁); original node `v`)
--   .unsplit (.intCopy w) ↦ .intCopy  (.unsplit w)
--                            (w ∈ W₂ \ J;       intervention `I_w`)
--   .copy0   (.unsplit w) ↦ .unsplit (.copy0 w)
--                            (w ∈ W₁;           output split `w^o`)
--   .copy1   (.unsplit w) ↦ .unsplit (.copy1 w)
--                            (w ∈ W₁;           input split `w^i`)
--   .copy0   (.intCopy w) ↦ .intCopy  (.unsplit w)   (off-carrier)
--   .copy1   (.intCopy w) ↦ .intCopy  (.unsplit w)   (off-carrier)
--
-- The off-carrier cases `.copy0 (.intCopy _)` and `.copy1 (.intCopy _)`
-- never appear in the RHS carrier: the outer `nodeSplittingHard`
-- ranges over `W₁.image IntExtNode.unsplit`, every element of which
-- has the form `.unsplit _`, so the outer `.copy0` / `.copy1` is
-- only ever applied to `.unsplit` arguments.  The fillers
-- `.intCopy (.unsplit w)` are chosen for totality and do not affect
-- the equality this row asserts.
--
-- ## Design choice
--
-- *Function, not `Equiv` of types.*  A type-level
--   `SplitNode (IntExtNode Node) ≃ IntExtNode (SplitNode Node)`
--   does not exist: when `Node` is non-empty, the source has six
--   reachable constructor combinations per node and the target only
--   four, so no bijection on the underlying types is possible.
--   `flattenSwigDoit` is instead injective only when restricted to
--   the *reachable RHS carrier*, and the disjointness hypothesis
--   `Disjoint W₁ W₂` is precisely what makes that restricted
--   injection well-defined (without it, an element of `W₁ ∩ W₂`
--   would receive two different intervention-vs-split-tag readings
--   that would collide).  Image-level reasoning via
--   `Finset.image flattenSwigDoit` is enough for the statement; the
--   proof phase will only apply `flattenSwigDoit` to elements
--   actually in the reachable RHS carrier.
--
-- *Direction `SplitNode (IntExtNode Node) → IntExtNode (SplitNode Node)`
--   (RHS → LHS), not the reverse.*  Both directions would work
--   mathematically.  We pick RHS → LHS so the theorem reads
--   `eqViaNodeMap RHS LHS flattenSwigDoit`, matching the
--   `eqViaNodeMap iter joint flatten` convention established by
--   `claim_3_7` (`twoDisjointNodeSplittingsCommute`) and
--   `claim_3_14` (`addInterventionNodes_comm_disjoint`): the side
--   whose carrier is being relabelled sits on the left, the side
--   whose carrier is the chosen "target" sits on the right.  The
--   LHS's `IntExtNode (SplitNode Node)` is naturally read as the
--   target because the LN writes the equation `LHS = RHS` with
--   `LHS` on the left and the "first split then add intervention
--   nodes on the SWIG carrier" reading is closer to the LN's prose
--   ("the CDMG that arises from first introducing intervention
--   nodes ... is the same as the CDMG that arises from first
--   splitting...").
--
-- *Total pattern match on `SplitNode (IntExtNode Node)`.*  Lean
--   requires total functions; the off-carrier cases are filled in
--   with the simplest semantically-aligned value.  Mirrors
--   `claim_3_14`'s `flattenIntExt` and `claim_3_7`'s `flattenSplit`
--   totality-filler convention.
--
-- *Mathlib re-use.*  Rolled our own — Mathlib carries no general
--   "flatten heterogeneous nested tagged sum" map.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: flattenSwigDoit
-- claim_3_15 --- start helper
def flattenSwigDoit : SplitNode (IntExtNode Node) → IntExtNode (SplitNode Node)
  | .unsplit (.unsplit v) => IntExtNode.unsplit (SplitNode.unsplit v)
  | .unsplit (.intCopy w) => IntExtNode.intCopy (SplitNode.unsplit w)
  | .copy0 (.unsplit w) => IntExtNode.unsplit (SplitNode.copy0 w)
  | .copy0 (.intCopy w) => IntExtNode.intCopy (SplitNode.unsplit w)
  | .copy1 (.unsplit w) => IntExtNode.unsplit (SplitNode.copy1 w)
  | .copy1 (.intCopy w) => IntExtNode.intCopy (SplitNode.unsplit w)
-- claim_3_15 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: flattenSwigDoit

-- ref: claim_3_15
--
-- For any CADMG `G : CDMG Node` (`hG : G.IsCADMG`), any subset
-- `W₁ ⊆ G.V` (`hW₁`), any subset `W₂ ⊆ G.J ∪ G.V` (`hW₂`), and
-- any disjointness `Disjoint W₁ W₂` (`hDisj`), the LN's displayed
-- equality
--   `(G_{swig(W₁)})_{doit(I_{W₂})} = (G_{doit(I_{W₂})})_{swig(W₁)}`
-- is rendered (per the rewritten tex's "Distinct carriers and the
-- canonical relabelling identifying them" paragraph) as
-- `eqViaNodeMap RHS LHS flattenSwigDoit`: the four `Finset` data
-- fields of the RHS, after applying `flattenSwigDoit` field-wise,
-- coincide with the four data fields of the LHS.
/-
LN tex (rewritten canonical statement for `claim_3_15`):

  Let `G = (J, V, E, L)` be a CADMG and let `W₁ ⊆ V`,
  `W₂ ⊆ J ∪ V` be subsets with `W₁ ∩ W₂ = ∅`.  Then, modulo the
  canonical relabelling identifying the two distinct iterated-
  tagged-sum carriers `IntExtNode (SplitNode Node)` (LHS) and
  `SplitNode (IntExtNode Node)` (RHS),
    `(G_{swig(W₁)})_{doit(I_{W₂})} = (G_{doit(I_{W₂})})_{swig(W₁)}`,
  read componentwise on the four components `(J, V, E, L)` of
  `def_3_1`.

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CADMG and `W_1 ⊆ V` and
  `W_2 ⊆ J ∪ V` two disjoint subsets of nodes from `G`.  Then the
  CADMG that arises from first introducing intervention nodes
  `I_{W_2}` and then splitting the nodes from `W_1` is the same
  as the CADMG that arises from first splitting the nodes from
  `W_1` and then introducing the intervention nodes `I_{W_2}`:
    `(G_{swig(W_1)})_{doit(I_{W_2})} = (G_{doit(I_{W_2})})_{swig(W_1)}`.
-/
-- ## Design choice
--
-- *Single theorem, no conjunction.*  Unlike `claim_3_14`(a) which
--   asserts a triple coincidence
--   `iter12 = iter21 = joint` and decomposes into two `eqViaNodeMap`
--   conjuncts through a shared joint, `claim_3_15` asserts a
--   *single* binary equality `LHS = RHS` with no third "joint"
--   form available (the SWIG and the extension are heterogeneous
--   operations, so there is no `G_{swig+doit(W₁ ∪ W₂)}` collapse).
--   One `eqViaNodeMap RHS LHS flattenSwigDoit` captures the LN's
--   equality directly.
--
-- *Why `eqViaNodeMap RHS LHS flattenSwigDoit`, not literal `=`.*
--   LHS lives in `CDMG (IntExtNode (SplitNode Node))`; RHS lives in
--   `CDMG (SplitNode (IntExtNode Node))`.  These carriers are not
--   Lean-equal as types, so a literal `LHS = RHS` is not
--   type-correct.  The LN's displayed `=` is implicitly modulo the
--   canonical relabelling identifying the two iterated-tagged-sum
--   carriers (rewritten tex's "Distinct carriers and the canonical
--   relabelling identifying them" paragraph); we render that
--   relabelling explicitly via the bijection-on-the-reachable-subset
--   `flattenSwigDoit`.  The `eqViaNodeMap` predicate from `claim_3_7`
--   then captures the LN's "the same CDMG up to canonical
--   relabelling" reading by asserting componentwise equality of the
--   four `Finset` data fields after applying `flattenSwigDoit`
--   field-wise.  Same paradigm as `claim_3_14`(a)'s
--   `eqViaNodeMap iter12 joint flattenIntExt`.
--
-- *Explicit mapping LN-equation-side ↔ Lean-operand.*  The LN's
--   displayed `(G_{swig(W₁)})_{doit(I_{W₂})} =
--   (G_{doit(I_{W₂})})_{swig(W₁)}` has its LN-LHS on the left of `=`
--   ("swig first, then extend") and its LN-RHS on the right
--   ("extend first, then swig").  In the Lean signature below, the
--   FIRST operand of `eqViaNodeMap` is
--   `(G.extendingCDMGsWith W₂ hW₂).nodeSplittingHard …` — "extend
--   first, then split", carrier `SplitNode (IntExtNode Node)` —
--   which is the *LN-RHS*; and the SECOND operand is
--   `(G.nodeSplittingHard hG W₁ hW₁).extendingCDMGsWith …` — "split
--   first, then extend", carrier `IntExtNode (SplitNode Node)` —
--   which is the *LN-LHS*.  Reading the Lean term: "the LN-RHS,
--   after `flattenSwigDoit`-relabelling, equals the LN-LHS
--   componentwise".  The `flattenSwigDoit` arrow points
--   `SplitNode (IntExtNode Node) → IntExtNode (SplitNode Node)`,
--   i.e.\ first-operand-carrier → second-operand-carrier =
--   LN-RHS-carrier → LN-LHS-carrier.
--
-- *Hypotheses in the order `(G) (hG) (W₁) (hW₁) (W₂) (hW₂)
--   (hDisj)`.*  `hG : G.IsCADMG` is a *separate* `Prop`-level
--   hypothesis adjacent to `G`, not baked into the type of `G`.
--   The underlying `structure CDMG` (`def_3_1`) is more permissive
--   than the LN's "CADMG" (it allows cycles); the LN's "Let `G` be
--   a CADMG" lands as the propositional predicate
--   `IsCADMG := IsAcyclic` (`def_3_7`) carried as a separate
--   argument.  This matches `def_3_12` `nodeSplittingHard`'s
--   signature `(G : CDMG Node) (hG : G.IsCADMG) …`, which is the
--   constructor consumed by the inner SWIG on the LN-LHS branch,
--   and the `claim_3_11` `DisjointHardInterventions` binder
--   convention.  `W₁` precedes `W₂` to match the LN's wording
--   order ("Let `W_1 ⊆ V` and `W_2 ⊆ J ∪ V`"); each `Wᵢ` is
--   immediately followed by its `hWᵢ` so the call sites read
--   left-to-right like the LN.  `hDisj` is last because it
--   constrains the *pair* `(W₁, W₂)` rather than either set
--   individually.
--
-- *`hW₁ : W₁ ⊆ G.V` (LN's `W_1 ⊆ V`) and
--   `hW₂ : W₂ ⊆ G.J ∪ G.V` (LN's `W_2 ⊆ J ∪ V`).*  The asymmetry
--   is dictated by the preconditions of the two constructors:
--   `nodeSplittingHard` requires `W ⊆ G.V` (acts on output nodes),
--   while `extendingCDMGsWith` admits any `W ⊆ G.J ∪ G.V` (the
--   `I_j := j` convention of `def_3_13` makes the `J ∩ W` overlap
--   harmless).  Matches the rewritten tex's "the typings are
--   dictated by the preconditions of the two constructors involved"
--   paragraph.
--
-- *Disjointness `Disjoint W₁ W₂` (Mathlib `Finset` form).*
--   Canonical Lean shape for the LN's `W_1 ∩ W_2 = ∅`.  Required
--   *for well-typedness* of the LHS's outer `extendingCDMGsWith`
--   (via `image_unsplit_subset_nodeSplittingHard_carrier`'s
--   case-split on the `V`-branch), not just for the equality —
--   so it appears on the signature, not merely as a proof-body
--   side condition.
--
-- *Direction of the `eqViaNodeMap` (RHS on the left, LHS on the
--   right).*  Following `claim_3_14`(a)'s convention, the side
--   whose carrier is being relabelled (RHS, via `flattenSwigDoit`
--   to the LHS carrier) sits on the left of `eqViaNodeMap`, and
--   the side whose carrier is the chosen target sits on the right.
--   The reverse direction would also be mathematically correct but
--   would require a different (inverse) flatten function and would
--   not match the established convention.
--
-- *No case-split in the statement for `W₂ ∩ J ≠ ∅` corner cases.*
--   The LN-critic surfaced two corner cases of "introducing
--   intervention nodes `I_{W₂}`" when `W₂` intersects `J`: (i) if
--   `W₂ ⊆ J` then `G_{doit(I_{W₂})} = G` by `def_3_13`'s `I_j := j`
--   convention (no fresh nodes, no new edges), and the LN's
--   displayed equality degenerates to the trivial
--   `G_{swig(W₁)} = G_{swig(W₁)}`; (ii) if `W₂ ∩ J ≠ ∅` and
--   `W₂ ∩ V ≠ ∅` then `doit(I_{W₂})` is a *partial* no-op (fresh
--   `I_w` introduced only for `w ∈ W₂ ∖ J`, with the `W₂ ∩ J`
--   branch untouched).  The Lean statement contains no case-split
--   on these — and intentionally so.  `def_3_13`'s carrier-level
--   encoding (`IntExtNode.intCopy` only ranges over `W ∖ J`, with
--   the `J ∩ W` branch absorbed by `IntExtNode.unsplit`) makes the
--   `I_j := j` convention a *type-level* fact rather than a
--   side-condition: both `extendingCDMGsWith` and the iterated
--   `nodeSplittingHard ∘ extendingCDMGsWith` automatically degenerate
--   on the `W₂ ∩ J` branch, and `eqViaNodeMap` together with
--   `flattenSwigDoit` automatically tracks the degeneration through
--   both sides of the equality.  A reader expecting case-splits
--   ("what if `W₂ ⊆ J`?") will not find them; they live one level
--   below, in the constructor definitions of `IntExtNode` and
--   `extendingCDMGsWith`.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: addInterventionNodes_comm_swig
-- claim_3_15 -- start statement
theorem addInterventionNodes_comm_swig (G : CDMG Node) (hG : G.IsCADMG)
    (W₁ : Finset Node) (hW₁ : W₁ ⊆ G.V)
    (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    eqViaNodeMap
        ((G.extendingCDMGsWith W₂ hW₂).nodeSplittingHard
            (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
            (W₁.image IntExtNode.unsplit)
            (image_unsplit_subset_extendingCDMGsWith_V hW₁))
        ((G.nodeSplittingHard hG W₁ hW₁).extendingCDMGsWith
            (W₂.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingHard_carrier hW₁ hW₂ hDisj))
        flattenSwigDoit
-- claim_3_15 -- end statement
  := by
  -- TeX proof: claim_3_15_proof_AddingInterventionNodes.tex.  Structure
  -- mirrors `claim_3_14`(a) but with a swig-then-extend tower vs.\ an
  -- extend-then-swig tower; the relabelling `flattenSwigDoit` bridges
  -- `SplitNode (IntExtNode Node)` (LN-RHS carrier) → `IntExtNode
  -- (SplitNode Node)` (LN-LHS carrier).
  -- ## Single-node flatten collapses (J / V components).
  --
  -- Each of these reduces a chained `(S.image inner).image outer).image
  -- flattenSwigDoit` to a single `S.image (flatten outer inner)` form by
  -- two applications of `Finset.image_image` followed by `rfl`, exploiting
  -- the relevant pattern-match clause of `flattenSwigDoit`.
  have h_uu_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image SplitNode.unsplit).image flattenSwigDoit
      = S.image (fun v => IntExtNode.unsplit (SplitNode.unsplit v)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_iu_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.intCopy).image SplitNode.unsplit).image flattenSwigDoit
      = S.image (fun w => IntExtNode.intCopy (SplitNode.unsplit w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_c0u_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image SplitNode.copy0).image flattenSwigDoit
      = S.image (fun w => IntExtNode.unsplit (SplitNode.copy0 w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_c1u_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image SplitNode.copy1).image flattenSwigDoit
      = S.image (fun w => IntExtNode.unsplit (SplitNode.copy1 w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  -- ## J-side sdiff identity.
  --
  -- `W₂.image .unsplit \ (G.J.image .unsplit ∪ W₁.image .copy1)
  --    = (W₂ \ G.J).image .unsplit` because constructor injectivity of
  -- `.unsplit` collapses the `G.J`-piece to a `W₂ ∩ G.J` removal, and
  -- constructor disjointness `.unsplit ≠ .copy1` eliminates the
  -- `W₁`-piece outright.  No `Disjoint W₁ W₂` consumption.
  have h_J_sdiff : W₂.image SplitNode.unsplit \
      (G.J.image SplitNode.unsplit ∪ W₁.image SplitNode.copy1)
      = (W₂ \ G.J).image SplitNode.unsplit := by
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
  -- ## V-side sdiff identity.
  --
  -- `G.V.image .unsplit \ W₁.image .unsplit = (G.V \ W₁).image .unsplit`
  -- by constructor injectivity of `IntExtNode.unsplit`.  No `Disjoint
  -- W₁ W₂` consumption.
  have h_V_sdiff : G.V.image (IntExtNode.unsplit (Node := Node)) \
      W₁.image IntExtNode.unsplit
      = (G.V \ W₁).image IntExtNode.unsplit := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxV, hxNot⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨v, hvV, rfl⟩ := Finset.mem_image.mp hxV
      have hv_notW₁ : v ∉ W₁ := by
        intro hw
        apply hxNot
        exact Finset.mem_image.mpr ⟨v, hw, rfl⟩
      exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvV, hv_notW₁⟩, rfl⟩
    · intro hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hvV, hv_notW₁⟩ := Finset.mem_sdiff.mp hv
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨v, hvV, rfl⟩, ?_⟩
      intro h_in
      obtain ⟨w, hw, hwEq⟩ := Finset.mem_image.mp h_in
      cases hwEq
      exact hv_notW₁ hw
  -- ## Pointwise identity for `toCopy1 (W₁.image .unsplit) ∘ .unsplit`.
  --
  -- `flattenSwigDoit (toCopy1 (W₁.image .unsplit) (.unsplit v))
  --    = .unsplit (toCopy1 W₁ v)` for every `v : Node`.  By case-split on
  -- `v ∈ W₁`: the `if` branches of `toCopy1` line up via the equivalence
  -- `.unsplit v ∈ W₁.image .unsplit ↔ v ∈ W₁` (constructor injectivity),
  -- and the post-`flattenSwigDoit` rewrites are pattern-match clauses of
  -- `flattenSwigDoit`.  No disjointness.
  have h_flat_toCopy1_unsplit : ∀ (v : Node),
      flattenSwigDoit (toCopy1 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit v))
      = IntExtNode.unsplit (toCopy1 W₁ v) := by
    intro v
    unfold toCopy1
    by_cases hv : v ∈ W₁
    · have h₁ : IntExtNode.unsplit v ∈ W₁.image IntExtNode.unsplit :=
        Finset.mem_image.mpr ⟨v, hv, rfl⟩
      rw [if_pos h₁, if_pos hv]
      rfl
    · have h₁ : IntExtNode.unsplit v ∉ W₁.image IntExtNode.unsplit := by
        intro h
        obtain ⟨v', hv', hveq⟩ := Finset.mem_image.mp h
        cases hveq
        exact hv hv'
      rw [if_neg h₁, if_neg hv]
      rfl
  -- ## Pointwise identity for `toCopy0 (W₁.image .unsplit) ∘ .unsplit`.
  --
  -- Symmetric to `h_flat_toCopy1_unsplit` with `.copy1 ↦ .copy0`.
  have h_flat_toCopy0_unsplit : ∀ (v : Node),
      flattenSwigDoit (toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit v))
      = IntExtNode.unsplit (toCopy0 W₁ v) := by
    intro v
    unfold toCopy0
    by_cases hv : v ∈ W₁
    · have h₁ : IntExtNode.unsplit v ∈ W₁.image IntExtNode.unsplit :=
        Finset.mem_image.mpr ⟨v, hv, rfl⟩
      rw [if_pos h₁, if_pos hv]
      rfl
    · have h₁ : IntExtNode.unsplit v ∉ W₁.image IntExtNode.unsplit := by
        intro h
        obtain ⟨v', hv', hveq⟩ := Finset.mem_image.mp h
        cases hveq
        exact hv hv'
      rw [if_neg h₁, if_neg hv]
      rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  -- ===================== Sub-goal 1: J component =====================
  -- LHS: `((G.J.image .unsplit ∪ (W₂ \ G.J).image .intCopy).image
  --        SplitNode.unsplit ∪ (W₁.image .unsplit).image .copy1).image
  --        flattenSwigDoit`
  -- RHS: `(G.J.image .unsplit ∪ W₁.image .copy1).image IntExtNode.unsplit
  --       ∪ (W₂.image .unsplit \
  --           (G.J.image .unsplit ∪ W₁.image .copy1)).image .intCopy`
  -- After `h_J_sdiff` and the four collapses, both sides reduce to the
  -- same three-piece union (up to associativity / commutativity of `∪`).
  · change (((G.J.image IntExtNode.unsplit ∪ (W₂ \ G.J).image IntExtNode.intCopy).image
                SplitNode.unsplit
              ∪ (W₁.image IntExtNode.unsplit).image SplitNode.copy1).image flattenSwigDoit
            = (G.J.image SplitNode.unsplit ∪ W₁.image SplitNode.copy1).image
                IntExtNode.unsplit
              ∪ (W₂.image SplitNode.unsplit \
                  (G.J.image SplitNode.unsplit ∪ W₁.image SplitNode.copy1)).image
                IntExtNode.intCopy)
    rw [h_J_sdiff]
    simp only [Finset.image_union]
    rw [h_uu_collapse, h_iu_collapse, h_c1u_collapse]
    -- RHS pieces: each is `S.image f.image g`; collapse via image_image.
    rw [show (G.J.image SplitNode.unsplit).image (IntExtNode.unsplit (Node := SplitNode Node))
            = G.J.image (fun j => IntExtNode.unsplit (SplitNode.unsplit j))
          from Finset.image_image,
        show (W₁.image SplitNode.copy1).image (IntExtNode.unsplit (Node := SplitNode Node))
            = W₁.image (fun w => IntExtNode.unsplit (SplitNode.copy1 w))
          from Finset.image_image,
        show ((W₂ \ G.J).image SplitNode.unsplit).image
                (IntExtNode.intCopy (Node := SplitNode Node))
            = (W₂ \ G.J).image (fun w => IntExtNode.intCopy (SplitNode.unsplit w))
          from Finset.image_image]
    -- LHS: A ∪ B ∪ C with B = (W₂ \ G.J)-piece, C = W₁-piece.
    -- RHS: A ∪ C ∪ B.  Swap B and C.
    rw [Finset.union_assoc,
        Finset.union_comm ((W₂ \ G.J).image (fun w => IntExtNode.intCopy (SplitNode.unsplit w)))
            (W₁.image (fun w => IntExtNode.unsplit (SplitNode.copy1 w))),
        ← Finset.union_assoc]
  -- ===================== Sub-goal 2: V component =====================
  -- LHS: `((G.V.image .unsplit \ W₁.image .unsplit).image .unsplit
  --        ∪ (W₁.image .unsplit).image .copy0).image flattenSwigDoit`
  -- RHS: `((G.V \ W₁).image .unsplit ∪ W₁.image .copy0).image .unsplit`
  · change ((G.V.image IntExtNode.unsplit \ W₁.image IntExtNode.unsplit).image
              SplitNode.unsplit
            ∪ (W₁.image IntExtNode.unsplit).image SplitNode.copy0).image flattenSwigDoit
          = ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0).image
              IntExtNode.unsplit
    rw [h_V_sdiff]
    simp only [Finset.image_union]
    rw [h_uu_collapse, h_c0u_collapse]
    rw [show ((G.V \ W₁).image SplitNode.unsplit).image
              (IntExtNode.unsplit (Node := SplitNode Node))
            = (G.V \ W₁).image (fun v => IntExtNode.unsplit (SplitNode.unsplit v))
          from Finset.image_image,
        show (W₁.image SplitNode.copy0).image (IntExtNode.unsplit (Node := SplitNode Node))
            = W₁.image (fun w => IntExtNode.unsplit (SplitNode.copy0 w))
          from Finset.image_image]
  -- ===================== Sub-goal 3: E component =====================
  -- LHS: nodeSplittingHard applied to extendingCDMGsWith.  Splits into
  --   G.E branch (lifted edges) and (W₂ \ G.J) branch (fresh intervention
  --   edges).  Disjointness is consumed only on the (W₂ \ G.J) branch.
  · change ((G.E.image (fun e : Node × Node =>
                  (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
              ∪ (W₂ \ G.J).image (fun w : Node =>
                  (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
                (fun e : IntExtNode Node × IntExtNode Node =>
                  (toCopy1 (W₁.image IntExtNode.unsplit) e.1,
                   toCopy0 (W₁.image IntExtNode.unsplit) e.2))).image
              (Prod.map flattenSwigDoit flattenSwigDoit)
            = (G.E.image (fun e : Node × Node => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))).image
                (fun e : SplitNode Node × SplitNode Node =>
                  (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
              ∪ (W₂.image SplitNode.unsplit \
                  (G.J.image SplitNode.unsplit ∪ W₁.image SplitNode.copy1)).image
                (fun w : SplitNode Node => (IntExtNode.intCopy w, IntExtNode.unsplit w))
    rw [h_J_sdiff]
    simp only [Finset.image_union, Finset.image_image]
    refine congr_arg₂ (· ∪ ·) ?_ ?_
    · -- G.E branch: pointwise rewrite using h_flat_toCopy{0,1}_unsplit.
      refine Finset.image_congr ?_
      intro e _
      change (flattenSwigDoit (toCopy1 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit e.1)),
            flattenSwigDoit (toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit e.2)))
          = (IntExtNode.unsplit (toCopy1 W₁ e.1), IntExtNode.unsplit (toCopy0 W₁ e.2))
      rw [h_flat_toCopy1_unsplit, h_flat_toCopy0_unsplit]
    · -- (W₂ \ G.J) branch: disjointness gives `w ∉ W₁`, so both toCopy_i
      -- calls land in the `.unsplit` branch; flattenSwigDoit reduces.
      refine Finset.image_congr ?_
      intro w hw
      obtain ⟨hw_W₂, _⟩ := Finset.mem_sdiff.mp hw
      have hw_notW₁ : w ∉ W₁ := Finset.disjoint_right.mp hDisj hw_W₂
      change (flattenSwigDoit (toCopy1 (W₁.image IntExtNode.unsplit) (IntExtNode.intCopy w)),
            flattenSwigDoit (toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit w)))
          = (IntExtNode.intCopy (SplitNode.unsplit w), IntExtNode.unsplit (SplitNode.unsplit w))
      unfold toCopy1 toCopy0
      have h1 : IntExtNode.intCopy w ∉ W₁.image IntExtNode.unsplit := by
        intro h
        obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
        cases hweq
      have h2 : IntExtNode.unsplit w ∉ W₁.image IntExtNode.unsplit := by
        intro h
        obtain ⟨v', hv', hveq⟩ := Finset.mem_image.mp h
        cases hveq
        exact hw_notW₁ hv'
      rw [if_neg h1, if_neg h2]
      rfl
  -- ===================== Sub-goal 4: L component =====================
  -- LHS: nodeSplittingHard's L on extendingCDMGsWith's L (single image
  --   over G.L; no fresh edges).  Pointwise rewrite using
  --   h_flat_toCopy0_unsplit.
  · change ((G.L.image (fun e : Node × Node =>
                (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
              (fun e : IntExtNode Node × IntExtNode Node =>
                (toCopy0 (W₁.image IntExtNode.unsplit) e.1,
                 toCopy0 (W₁.image IntExtNode.unsplit) e.2))).image
              (Prod.map flattenSwigDoit flattenSwigDoit)
            = (G.L.image (fun e : Node × Node => (toCopy0 W₁ e.1, toCopy0 W₁ e.2))).image
                (fun e : SplitNode Node × SplitNode Node =>
                  (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
    simp only [Finset.image_image]
    refine Finset.image_congr ?_
    intro e _
    change (flattenSwigDoit (toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit e.1)),
          flattenSwigDoit (toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit e.2)))
        = (IntExtNode.unsplit (toCopy0 W₁ e.1), IntExtNode.unsplit (toCopy0 W₁ e.2))
    rw [h_flat_toCopy0_unsplit, h_flat_toCopy0_unsplit]
-- REFACTOR-BLOCK-ORIGINAL-END: addInterventionNodes_comm_swig

end CDMG

-- ## Post-refactor port (`cdmg_typed_edges`)
--
-- The block below is the refactor twin of the row's declarations
-- against the `cdmg_typed_edges` redesign of `def_3_1` — same
-- mathematical content, retyped against `refactor_CDMG` and
-- `refactor_SplitNode`.  Only the L sub-goal genuinely changes
-- shape; the J / V / E sub-goals port mechanically because those
-- fields are untouched by the refactor (the refactor only restructures
-- L).
--
-- The L sub-goal uses `Sym2.map` in place of `Prod.map .unsplit .unsplit`,
-- and closes via `Sym2.map_map` (fuses two stages of `Sym2.map` into a
-- single one) followed by `Sym2.map_congr` (reduces to a pointwise
-- identity at the underlying-`Node` level).  The pointwise identity
-- `refactor_flattenSwigDoit (refactor_toCopy0 (W₁.image .unsplit)
-- (.unsplit a)) = .unsplit (refactor_toCopy0 W₁ a)` is the same `Node`-
-- level case-split as the original `h_flat_toCopy0_unsplit`, with only
-- the `refactor_` prefix added.  Mirrors `claim_3_14`'s sibling
-- refactor twin `refactor_addInterventionNodes_comm_disjoint`'s L
-- handling around `h_L_lift_uu_collapse`.
namespace refactor_CDMG
open CDMG

-- ## Helper — variable binders for this row's refactor-twin declarations
--
-- One-sentence summary: identical `Node : Type*` + `[DecidableEq Node]`
-- binders to the pre-refactor variable line, re-declared inside
-- `namespace refactor_CDMG` so the refactor-twin helpers and theorem
-- below pick them up the same way the pre-refactor block (still in
-- `namespace CDMG`) does.
--
-- ## Design choice
--
-- *`variable` block, not `def`-local binders on each refactor-twin
--   declaration.*  Mirrors the pre-refactor pattern verbatim — the
--   implicit `Node : Type*` and `[DecidableEq Node]` auto-bind into
--   every subsequent helper signature and into the main theorem.
--
-- *Re-declared inside `namespace refactor_CDMG`, not relied on from
--   the outer `namespace CDMG` `variable` line.*  Lean's `variable`
--   binders are namespace-scoped; closing `end CDMG` (line 724) drops
--   the original binders.  We re-declare here so every refactor-twin
--   signature picks up `Node` / `DecidableEq Node` automatically
--   without a per-declaration `{Node : Type*} [DecidableEq Node]`
--   prefix.  No name collision with the pre-refactor variable line —
--   the two `variable` blocks live in distinct namespaces.
--
-- *Why a second `namespace refactor_CDMG` wrapper (vs.\ keeping
--   everything in `namespace CDMG`).*  The wrapper keeps the
--   refactor-twin declarations' field-projector dot notation aligned
--   with their *carrier* type: `(G : refactor_CDMG Node).J` resolves
--   via `refactor_CDMG.J`, which lives in this namespace, and
--   `G.refactor_nodeSplittingHard …` resolves via
--   `refactor_CDMG.refactor_nodeSplittingHard`.  Inlining everything
--   under `namespace CDMG` would force fully-qualified
--   `refactor_CDMG.J` at every use site (since dot notation routes
--   through the carrier's namespace, not the ambient one), or force
--   us to name the helpers `refactor_CDMG.refactor_<name>` directly
--   — both noisier than the namespace wrapper.  The `open CDMG`
--   immediately below this `variable` line brings the shared
--   identifiers (`IntExtNode`, `refactor_extendingCDMGsWith`,
--   `refactor_toCopy0`, `refactor_toCopy1`, etc., which were
--   declared inside `namespace CDMG` in `def_3_13` / `def_3_12`'s
--   refactor twins) into scope so we can call them function-style
--   without qualification.  Same pattern as `claim_3_14`'s refactor
--   twin in `AddingInterventionNodes.lean`.
--
-- *Mathlib re-use.*  Standard Lean `variable` mechanism; no Mathlib
--   structure involved.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: variable_Node (was: refactor_variable_Node)
-- claim_3_15 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_15 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: variable_Node

-- ## Private helper — `refactor_IsCADMG` witness for the inner
--   extension (refactor twin)
--
-- One-sentence summary: refactor port of
-- `extendingCDMGsWith_isCADMG_of_isCADMG`; discharges the
-- `refactor_IsCADMG` precondition that the RHS branch's outer
-- `refactor_nodeSplittingHard` needs on its inner
-- `refactor_extendingCDMGsWith` argument.
--
-- Refactor port of `extendingCDMGsWith_isCADMG_of_isCADMG`.
-- Mechanical rename: `CDMG → refactor_CDMG`,
-- `extendingCDMGsWith → refactor_extendingCDMGsWith`,
-- `IsCADMG → refactor_IsCADMG`, `extAcyclic → refactor_extAcyclic`.
-- The definitional unfolding `refactor_IsCADMG := refactor_IsAcyclic`
-- (cf.\ `def_3_7` refactor twin) makes the projection from
-- `refactor_extAcyclic`'s `refactor_IsAcyclic` conclusion to the
-- ambient `refactor_IsCADMG` goal definitional, exactly as in the
-- pre-refactor encoding.
--
-- ## Design choice
--
-- *Net-new declaration in this refactor port, not a rename of a
--   pre-existing entity.*  Although the surface text is a copy of
--   `extendingCDMGsWith_isCADMG_of_isCADMG` with each upstream
--   identifier prefixed `refactor_`, the resulting lemma is a fresh
--   declaration: its conclusion's type mentions
--   `refactor_extendingCDMGsWith`, which is a *different* function
--   from `extendingCDMGsWith` (it operates on `refactor_CDMG`, which
--   is a *different* structure from `CDMG`).  The pre-refactor
--   lemma cannot serve the refactor variant, so the rename is
--   forced.  See the BEFORE/AFTER block on `refactor_CDMG` in
--   `CDMG.lean` for the underlying structural divergence between
--   `CDMG` and `refactor_CDMG` (the `Sym2` encoding of L).
--
-- *Same Prop-level shape as the pre-refactor.*  Stays a `private`
--   plumbing lemma — not LN content, no helper marker — because the
--   refactor preserves the constructor signature shape of
--   `refactor_nodeSplittingHard`: it still takes a separate
--   `(hG : G.refactor_IsCADMG)` argument, and the LN-RHS branch's
--   outer `refactor_nodeSplittingHard ?hG ?W ?hW` still consumes
--   exactly this `refactor_IsCADMG` witness on the inner
--   `refactor_extendingCDMGsWith G W₂ hW₂`.
--
-- *Mathlib re-use.*  Same as the pre-refactor — the helper is a
--   thin term-mode wrapper around `refactor_extAcyclic` (the
--   `claim_3_13` refactor twin's acyclicity-preservation theorem);
--   no Mathlib API is involved.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: extendingCDMGsWith_isCADMG_of_isCADMG (was: refactor_extendingCDMGsWith_isCADMG_of_isCADMG)
private lemma refactor_extendingCDMGsWith_isCADMG_of_isCADMG
    {G : refactor_CDMG Node} (hG : G.refactor_IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    (refactor_extendingCDMGsWith G W hW).refactor_IsCADMG :=
  refactor_extAcyclic G W hW hG
-- REFACTOR-BLOCK-REPLACEMENT-END: extendingCDMGsWith_isCADMG_of_isCADMG

-- ## Helper — `W₁.image .unsplit ⊆ V_{doit(I_{W₂})}` (refactor twin)
--
-- One-sentence summary: refactor port of
-- `image_unsplit_subset_extendingCDMGsWith_V`; discharges the
-- `?_ : W₁.image .unsplit ⊆ (refactor_extendingCDMGsWith G W₂ hW₂).V`
-- precondition that the LN-RHS branch's outer
-- `refactor_nodeSplittingHard … (W₁.image IntExtNode.unsplit) ?_`
-- needs.
--
-- Refactor port of `image_unsplit_subset_extendingCDMGsWith_V`.
-- Mechanical rename: `CDMG → refactor_CDMG`,
-- `extendingCDMGsWith → refactor_extendingCDMGsWith`.  The
-- `V`-component of `refactor_extendingCDMGsWith` is structurally
-- identical to the pre-refactor `extendingCDMGsWith` (the refactor
-- only touches L), so the proof body carries over verbatim with the
-- rename.
--
-- ## Design choice
--
-- *Why the lemma needs a refactor twin at all.*  The pre-refactor
--   `image_unsplit_subset_extendingCDMGsWith_V` is privately scoped
--   to the pre-refactor `addInterventionNodes_comm_swig` proof; its
--   conclusion's type mentions `(G.extendingCDMGsWith W₂ hW₂).V`
--   for `G : CDMG Node`.  The refactor-twin theorem needs the
--   analogous fact for `G : refactor_CDMG Node`, with conclusion
--   `(refactor_extendingCDMGsWith G W₂ hW₂).V`.  Since `CDMG` and
--   `refactor_CDMG` are *distinct structures*, the pre-refactor
--   lemma cannot serve the refactor variant — a separate twin is
--   required.  Driven by the upstream rename, not by a design
--   change in this row.
--
-- *Body unchanged from the pre-refactor.*  Per the upstream
--   `refactor_CDMG` design-choice comment in `CDMG.lean`, the
--   refactor touches only the L-channel encoding (ordered pairs +
--   symmetry → `Sym2`); the `J`, `V`, and `E` fields are
--   structurally untouched, and so is
--   `refactor_extendingCDMGsWith`'s definition of its `V` field
--   (`V_{doit(I_W)} := G.V.image .unsplit`, identical to its
--   pre-refactor counterpart).  The proof body therefore ports
--   tactic-for-tactic with only the `CDMG → refactor_CDMG` /
--   `extendingCDMGsWith → refactor_extendingCDMGsWith` renames.
--
-- *Binder convention unchanged.*  Implicit `G`, `W₁`, `W₂`, `hW₂`;
--   explicit `hW₁`.  Matches the pre-refactor binder convention
--   verbatim so the call site at the refactor-twin theorem head
--   (`refactor_image_unsplit_subset_extendingCDMGsWith_V hW₁`)
--   reads identically to the pre-refactor call site.
--
-- *Mathlib re-use.*  Same as the pre-refactor — `Finset.mem_image`
--   forward and back, no Mathlib-level lemma about
--   `refactor_extendingCDMGsWith` is invoked (and none exists; the
--   constructor's `V`-field is exposed directly).
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: image_unsplit_subset_extendingCDMGsWith_V (was: refactor_image_unsplit_subset_extendingCDMGsWith_V)
-- claim_3_15 --- start helper
private lemma refactor_image_unsplit_subset_extendingCDMGsWith_V
    {G : refactor_CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V)
    {W₂ : Finset Node} {hW₂ : W₂ ⊆ G.J ∪ G.V} :
    W₁.image IntExtNode.unsplit ⊆ (refactor_extendingCDMGsWith G W₂ hW₂).V
-- claim_3_15 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change IntExtNode.unsplit v ∈ G.V.image IntExtNode.unsplit
  exact Finset.mem_image.mpr ⟨v, hW₁ hv, rfl⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: image_unsplit_subset_extendingCDMGsWith_V

-- ## Helper — `W₂.image .unsplit ⊆ J_{swig(W₁)} ∪ V_{swig(W₁)}`
--   (refactor twin)
--
-- One-sentence summary: refactor port of
-- `image_unsplit_subset_nodeSplittingHard_carrier`; discharges the
-- `?_ : W₂.image .unsplit ⊆ (G.refactor_nodeSplittingHard hG W₁ hW₁).J
--                            ∪ (G.refactor_nodeSplittingHard hG W₁ hW₁).V`
-- precondition that the LN-LHS branch's outer
-- `(G.refactor_nodeSplittingHard hG W₁ hW₁).refactor_extendingCDMGsWith
-- (W₂.image refactor_SplitNode.unsplit) ?_` needs.
--
-- Refactor port of `image_unsplit_subset_nodeSplittingHard_carrier`.
-- Mechanical rename: `CDMG → refactor_CDMG`,
-- `SplitNode → refactor_SplitNode`,
-- `nodeSplittingHard → refactor_nodeSplittingHard`.  The J / V
-- partition of `refactor_nodeSplittingHard` is structurally
-- identical to the pre-refactor `nodeSplittingHard` (the refactor
-- only touches L), so the proof body carries over verbatim with the
-- rename.
--
-- ## Design choice
--
-- *Why the lemma needs a refactor twin at all.*  Same reason as
--   `refactor_image_unsplit_subset_extendingCDMGsWith_V`: the
--   conclusion mentions `(G.refactor_nodeSplittingHard hG W₁ hW₁).J`
--   and `.V`, which only exist for `G : refactor_CDMG Node` —
--   `refactor_nodeSplittingHard` operates on `refactor_CDMG`, a
--   distinct structure from `CDMG`.  The lemma is forced by the
--   refactor's upstream rename, not by a substantive design change.
--
-- *Body carries over verbatim under the rename.*  The
--   case-split on `w ∈ G.J` vs.\ `w ∈ G.V` and the disjointness-
--   driven routing of `w ∈ G.V \ W₁ ⊆ (G.V \ W₁).image .unsplit`
--   are identical to the pre-refactor.  `refactor_nodeSplittingHard`'s
--   J / V definitions
--   (`J ∪ W₁`-style image union, `V \ W₁`-style image union plus
--   `W₁`'s `.copy0` copy) are structurally identical to
--   `nodeSplittingHard`'s — the upstream `refactor_CDMG` design-choice
--   comment in `CDMG.lean` documents that only the L channel
--   changed.
--
-- *Disjointness `Disjoint W₁ W₂` is still load-bearing on the
--   `V`-branch.*  Unchanged from the pre-refactor — without it, a
--   `w ∈ W₂ ∩ W₁ ∩ G.V` could not be routed through the
--   `(G.V \ W₁).image .unsplit` summand of `V_{swig(W₁)}` (it
--   would have to land in `W₁.image refactor_SplitNode.copy0`,
--   which has the wrong constructor).  Surfacing the same constraint
--   here as in the pre-refactor preserves the well-typedness
--   guarantee for the LHS's outer `refactor_extendingCDMGsWith`.
--
-- *Binder convention unchanged.*  Implicit `G`, `hG`, `W₁`, `W₂`;
--   explicit `hW₁`, `hW₂`, `hDisj`.  Matches the pre-refactor
--   verbatim so the call site at the refactor-twin theorem head
--   (`refactor_image_unsplit_subset_nodeSplittingHard_carrier hW₁
--   hW₂ hDisj`) reads identically to the pre-refactor.
--
-- *Mathlib re-use.*  Same as the pre-refactor — `Finset.mem_image`,
--   `Finset.disjoint_right`, `Finset.mem_sdiff`; no new Mathlib API
--   is engaged by the refactor.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: image_unsplit_subset_nodeSplittingHard_carrier (was: refactor_image_unsplit_subset_nodeSplittingHard_carrier)
-- claim_3_15 --- start helper
private lemma refactor_image_unsplit_subset_nodeSplittingHard_carrier
    {G : refactor_CDMG Node} {hG : G.refactor_IsCADMG}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.J ∪ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂.image refactor_SplitNode.unsplit ⊆
      (G.refactor_nodeSplittingHard hG W₁ hW₁).J ∪
        (G.refactor_nodeSplittingHard hG W₁ hW₁).V
-- claim_3_15 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change refactor_SplitNode.unsplit v ∈
    (G.J.image refactor_SplitNode.unsplit ∪ W₁.image refactor_SplitNode.copy1) ∪
      ((G.V \ W₁).image refactor_SplitNode.unsplit ∪ W₁.image refactor_SplitNode.copy0)
  rcases Finset.mem_union.mp (hW₂ hv) with hJ | hV
  · refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · have hvW₁ : v ∉ W₁ := Finset.disjoint_right.mp hDisj hv
    refine Finset.mem_union_right _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hV, hvW₁⟩, rfl⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: image_unsplit_subset_nodeSplittingHard_carrier

-- ## Helper — the canonical flatten map (refactor twin)
--
-- One-sentence summary: refactor port of `flattenSwigDoit`; the same
-- pattern-matched bridge function as the pre-refactor, but operating
-- between the typed inductives `refactor_SplitNode (IntExtNode Node)`
-- (LN-RHS carrier under the refactor) and
-- `IntExtNode (refactor_SplitNode Node)` (LN-LHS carrier under the
-- refactor).
--
-- Refactor port of `flattenSwigDoit`.  Mechanical rename: the
-- `SplitNode` in the function signature and pattern-match clauses
-- becomes `refactor_SplitNode`.  The body is unchanged — every
-- pattern-match clause is a constructor-level identity that
-- transports verbatim across the rename (`refactor_SplitNode`'s
-- three constructors `.unsplit`, `.copy0`, `.copy1` are named
-- identically to the pre-refactor `SplitNode`).  The off-carrier
-- fillers `.intCopy (.unsplit _)` for `.copy0 (.intCopy _)` and
-- `.copy1 (.intCopy _)` are unchanged in semantics.  See the
-- pre-refactor design block above the original `flattenSwigDoit` for
-- the substantive design rationale (function vs.\ `Equiv`, direction
-- of the map, totality fillers, no Mathlib re-use).
--
-- ## Design choice
--
-- *Net-new declaration, not a rename of `flattenSwigDoit` itself.*
--   This is one of the few places in the refactor where we *must*
--   produce a brand-new `refactor_*` declaration even though the
--   refactor's primary change is to `def_3_1`'s L-channel encoding.
--   The reason: `SplitNode` (the pre-refactor inductive from
--   `def_3_12`) and `refactor_SplitNode` (the refactor twin) are
--   *distinct Lean inductive types* — they share constructor names
--   `.unsplit`, `.copy0`, `.copy1` only by convention, not at the
--   type-equality level.  So the existing
--   `flattenSwigDoit : SplitNode (IntExtNode Node) → IntExtNode (SplitNode Node)`
--   cannot serve the refactor variant, whose carriers
--   `refactor_SplitNode (IntExtNode Node)` and
--   `IntExtNode (refactor_SplitNode Node)` Lean treats as entirely
--   different types from the pre-refactor carriers.  A separate
--   `refactor_flattenSwigDoit` is therefore required.  Wrapped with
--   `REFACTOR-BLOCK-REPLACEMENT-…` markers but with no companion
--   ORIGINAL block: this is net-new in the REPLACEMENT, and Phase 7
--   cleanup's strict refusal rule for top-level `refactor_*`
--   declarations without REPLACEMENT markers is satisfied by the
--   marker block we placed here.
--
-- *Function direction `refactor_SplitNode (IntExtNode Node) →
--   IntExtNode (refactor_SplitNode Node)` matches the pre-refactor
--   pre-`SplitNode → IntExtNode` direction.*  Picked so the call
--   site `refactor_eqViaNodeMap RHS LHS refactor_flattenSwigDoit`
--   below pattern-matches the
--   `eqViaNodeMap iter joint flatten` convention established by
--   `claim_3_7` and inherited through `claim_3_14`(a) — the
--   "RHS-with-relabelling = LHS componentwise" reading.  Reversing
--   the arrow would have worked mathematically but would have broken
--   the convention shared across the section.
--
-- *Pattern-match shape ported verbatim.*  Each of the six clauses is
--   a constructor-level identity that transports across the rename
--   without any reasoning.  No Mathlib API is invoked; rolled our
--   own, same as the pre-refactor.
--
-- *Limitation (carried over from the pre-refactor).*  Not a
--   bijection on types — `refactor_flattenSwigDoit` is only
--   injective when restricted to the *reachable* RHS carrier
--   (`{.unsplit (.unsplit _)} ∪ {.unsplit (.intCopy _)} ∪
--   {.copy0 (.unsplit _)} ∪ {.copy1 (.unsplit _)}`); the
--   `.copy0 (.intCopy _)` and `.copy1 (.intCopy _)` cases are
--   filler-only and do not participate in the
--   `refactor_eqViaNodeMap` claim.  Disjointness `Disjoint W₁ W₂`
--   on the main theorem is precisely what keeps the reachable
--   image well-behaved.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: flattenSwigDoit (was: refactor_flattenSwigDoit)
-- claim_3_15 --- start helper
def refactor_flattenSwigDoit :
    refactor_SplitNode (IntExtNode Node) → IntExtNode (refactor_SplitNode Node)
  | .unsplit (.unsplit v) => IntExtNode.unsplit (refactor_SplitNode.unsplit v)
  | .unsplit (.intCopy w) => IntExtNode.intCopy (refactor_SplitNode.unsplit w)
  | .copy0 (.unsplit w) => IntExtNode.unsplit (refactor_SplitNode.copy0 w)
  | .copy0 (.intCopy w) => IntExtNode.intCopy (refactor_SplitNode.unsplit w)
  | .copy1 (.unsplit w) => IntExtNode.unsplit (refactor_SplitNode.copy1 w)
  | .copy1 (.intCopy w) => IntExtNode.intCopy (refactor_SplitNode.unsplit w)
-- claim_3_15 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: flattenSwigDoit

-- ref: claim_3_15 — refactor twin
--
-- For any `G : refactor_CDMG Node` (`hG : G.refactor_IsCADMG`), any
-- `W₁ ⊆ G.V` (`hW₁`), any `W₂ ⊆ G.J ∪ G.V` (`hW₂`), and any
-- `Disjoint W₁ W₂` (`hDisj`), the LN's displayed equality
--   `(G_{swig(W₁)})_{doit(I_{W₂})} = (G_{doit(I_{W₂})})_{swig(W₁)}`
-- is rendered (per the rewritten tex twin's "Distinct carriers and
-- the canonical relabelling identifying them" paragraph) as
-- `refactor_eqViaNodeMap RHS LHS refactor_flattenSwigDoit`.
--
-- The mathematical content is unchanged from the pre-refactor sibling
-- `addInterventionNodes_comm_swig`.  Under the `cdmg_typed_edges`
-- refactor only the L-field's encoding changes — from
-- `Finset (Node × Node) + hL_symm` to `Finset (Sym2 Node)` — so the
-- J / V / E sub-goals port mechanically under a rename pass while the
-- L sub-goal is restructured around `Sym2`-quotient API
-- (`Sym2.map`, `Sym2.map_map`, `Sym2.map_congr`).  The pointwise
-- `Node`-level identity at the bottom of the L sub-goal is the same
-- `h_flat_toCopy0_unsplit` case-split as the original.
--
-- ## Design choice (the main theorem)
--
-- *Mechanical port, not a re-derivation.*  This row is a DEPENDENT
--   in refactor `cdmg_typed_edges`, pulled in because root `def_3_1`
--   changed underneath it.  The mathematical content of the LN
--   claim is unchanged; only the upstream L-channel encoding
--   changed.  Every type and helper that mentioned the pre-refactor
--   `CDMG` / `SplitNode` / `IsCADMG` / `extendingCDMGsWith` /
--   `nodeSplittingHard` is mechanically renamed to its
--   `refactor_*` counterpart.  See the upstream design-choice
--   comment on `refactor_CDMG` in `CDMG.lean` for the `Sym2`
--   encoding rationale and downstream consequences — we do not
--   re-litigate that choice here; this row only consumes it.
--
-- *L-channel encoding change is not visible in the theorem's
--   shape, only in the tactic block.*  The theorem statement
--   itself is identical in shape to the pre-refactor sibling —
--   same four binder pairs, same `refactor_eqViaNodeMap`
--   componentwise reading, same `refactor_flattenSwigDoit`
--   relabelling — because `refactor_eqViaNodeMap` is defined the
--   same componentwise-over-`(J, V, E, L)` way as `eqViaNodeMap`.
--   The encoding change shows up only in the L sub-goal's tactic
--   block (sub-goal 4), where lifts that read `Prod.map _ _` in
--   the pre-refactor read `Sym2.map _` here, and the two-stage
--   composition closes via `Sym2.map_map` + `Sym2.map_congr`
--   instead of `Finset.image_image` + `congr_arg₂`.  The J / V / E
--   sub-goals are line-for-line ports under the rename pass — see
--   the comment block at line 727 for the structural framing.
--
-- *Why all six pre-refactor design choices port over without
--   re-litigation.*  Single-theorem-no-conjunction;
--   `refactor_eqViaNodeMap` not literal `=`; explicit LN-side ↔
--   Lean-operand mapping; binder order `(G) (hG) (W₁) (hW₁) (W₂)
--   (hW₂) (hDisj)`; `Disjoint W₁ W₂` as Mathlib `Finset`
--   disjointness; direction of `refactor_eqViaNodeMap` with RHS on
--   the left; no case-split for `W₂ ∩ J ≠ ∅` corner cases.  All
--   six are upstream-encoding-agnostic — none of them depends on
--   how L is encoded — so each ports verbatim from the
--   pre-refactor design block (lines 329-441) under the
--   `eqViaNodeMap → refactor_eqViaNodeMap`,
--   `flattenSwigDoit → refactor_flattenSwigDoit` renames.  Read
--   the pre-refactor block for the substantive justifications;
--   they apply unchanged here.
--
-- *Why no `addition_to_the_LN` revision was needed.*  The wording-
--   check report flagged two related subtleties
--   (`w2_in_J_makes_doit_a_no_op_via_Ij_identification` and
--   `w2_partial_overlap_with_J_partial_no_op`) about the LN's
--   "introducing intervention nodes `I_{W₂}`" prose being ambiguous
--   when `W₂ ∩ J ≠ ∅`.  Both are *resolved at the carrier-encoding
--   level* by `def_3_13`'s `IntExtNode.intCopy`-only-ranges-over-
--   `W₂ ∖ J` convention, which is preserved verbatim by the
--   `cdmg_typed_edges` refactor (the refactor changes L only).
--   The convention propagates through both
--   `refactor_extendingCDMGsWith` and the iterated
--   `refactor_nodeSplittingHard ∘ refactor_extendingCDMGsWith`
--   automatically, and `refactor_eqViaNodeMap` with
--   `refactor_flattenSwigDoit` tracks the degeneration through
--   both sides.  No statement-level case-split required.
--
-- *Mathlib re-use.*  The L-component sub-goal's `Sym2.map`,
--   `Sym2.map_map`, and `Sym2.map_congr` are the precise Mathlib
--   APIs the upstream `refactor_CDMG` design-choice block named as
--   the payoff for the `Sym2` encoding (so the `Sym2` lift commutes
--   functorially with composition and lifts pointwise identities).
--   Their use here is the predicted Mathlib re-use — no rolling
--   our own `Sym2`-level lemmas.  The J / V / E sub-goals continue
--   to use Mathlib's `Finset.image_image`, `Finset.image_union`,
--   `Finset.image_congr`, `Finset.union_assoc`, `Finset.union_comm`
--   exactly as the pre-refactor.
--
-- *Constraints / known limitations carried over.*  Identical to the
--   pre-refactor: `refactor_flattenSwigDoit` is total but injective
--   only on the reachable RHS carrier (so a hypothetical attempt
--   to invert the equality without `Disjoint W₁ W₂` would fail);
--   the `IntExtNode.unsplit` vs.\ `IntExtNode.intCopy` branch in
--   `def_3_13`'s `refactor_extendingCDMGsWith` makes the `W₂ ∩ J`
--   corner cases degenerate quietly rather than via an explicit
--   case-split.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: addInterventionNodes_comm_swig (was: refactor_addInterventionNodes_comm_swig)
-- claim_3_15 -- start statement
theorem refactor_addInterventionNodes_comm_swig (G : refactor_CDMG Node) (hG : G.refactor_IsCADMG)
    (W₁ : Finset Node) (hW₁ : W₁ ⊆ G.V)
    (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    refactor_eqViaNodeMap
        ((refactor_extendingCDMGsWith G W₂ hW₂).refactor_nodeSplittingHard
            (refactor_extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
            (W₁.image IntExtNode.unsplit)
            (refactor_image_unsplit_subset_extendingCDMGsWith_V hW₁))
        (refactor_extendingCDMGsWith
            (G.refactor_nodeSplittingHard hG W₁ hW₁)
            (W₂.image refactor_SplitNode.unsplit)
            (refactor_image_unsplit_subset_nodeSplittingHard_carrier hW₁ hW₂ hDisj))
        refactor_flattenSwigDoit
-- claim_3_15 -- end statement
  := by
  -- TeX proof: refactor_claim_3_15_proof_AddingInterventionNodes.tex.
  -- Same structure as the pre-refactor sibling, with J / V / E sub-goals
  -- ported mechanically and the L sub-goal restructured around
  -- `Sym2.map` / `Sym2.map_map` / `Sym2.map_congr`.
  -- ## Single-node flatten collapses (J / V components).
  have h_uu_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image refactor_SplitNode.unsplit).image
          refactor_flattenSwigDoit
      = S.image (fun v => IntExtNode.unsplit (refactor_SplitNode.unsplit v)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_iu_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.intCopy).image refactor_SplitNode.unsplit).image
          refactor_flattenSwigDoit
      = S.image (fun w => IntExtNode.intCopy (refactor_SplitNode.unsplit w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_c0u_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image refactor_SplitNode.copy0).image
          refactor_flattenSwigDoit
      = S.image (fun w => IntExtNode.unsplit (refactor_SplitNode.copy0 w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_c1u_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image refactor_SplitNode.copy1).image
          refactor_flattenSwigDoit
      = S.image (fun w => IntExtNode.unsplit (refactor_SplitNode.copy1 w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  -- ## J-side sdiff identity.
  have h_J_sdiff : W₂.image refactor_SplitNode.unsplit \
      (G.J.image refactor_SplitNode.unsplit ∪ W₁.image refactor_SplitNode.copy1)
      = (W₂ \ G.J).image refactor_SplitNode.unsplit := by
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
  -- ## V-side sdiff identity.
  have h_V_sdiff : G.V.image (IntExtNode.unsplit (Node := Node)) \
      W₁.image IntExtNode.unsplit
      = (G.V \ W₁).image IntExtNode.unsplit := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxV, hxNot⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨v, hvV, rfl⟩ := Finset.mem_image.mp hxV
      have hv_notW₁ : v ∉ W₁ := by
        intro hw
        apply hxNot
        exact Finset.mem_image.mpr ⟨v, hw, rfl⟩
      exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvV, hv_notW₁⟩, rfl⟩
    · intro hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hvV, hv_notW₁⟩ := Finset.mem_sdiff.mp hv
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨v, hvV, rfl⟩, ?_⟩
      intro h_in
      obtain ⟨w, hw, hwEq⟩ := Finset.mem_image.mp h_in
      cases hwEq
      exact hv_notW₁ hw
  -- ## Pointwise identity for `refactor_toCopy1 (W₁.image .unsplit) ∘ .unsplit`.
  have h_flat_toCopy1_unsplit : ∀ (v : Node),
      refactor_flattenSwigDoit
          (refactor_toCopy1 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit v))
      = IntExtNode.unsplit (refactor_toCopy1 W₁ v) := by
    intro v
    unfold refactor_toCopy1
    by_cases hv : v ∈ W₁
    · have h₁ : IntExtNode.unsplit v ∈ W₁.image IntExtNode.unsplit :=
        Finset.mem_image.mpr ⟨v, hv, rfl⟩
      rw [if_pos h₁, if_pos hv]
      rfl
    · have h₁ : IntExtNode.unsplit v ∉ W₁.image IntExtNode.unsplit := by
        intro h
        obtain ⟨v', hv', hveq⟩ := Finset.mem_image.mp h
        cases hveq
        exact hv hv'
      rw [if_neg h₁, if_neg hv]
      rfl
  -- ## Pointwise identity for `refactor_toCopy0 (W₁.image .unsplit) ∘ .unsplit`.
  have h_flat_toCopy0_unsplit : ∀ (v : Node),
      refactor_flattenSwigDoit
          (refactor_toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit v))
      = IntExtNode.unsplit (refactor_toCopy0 W₁ v) := by
    intro v
    unfold refactor_toCopy0
    by_cases hv : v ∈ W₁
    · have h₁ : IntExtNode.unsplit v ∈ W₁.image IntExtNode.unsplit :=
        Finset.mem_image.mpr ⟨v, hv, rfl⟩
      rw [if_pos h₁, if_pos hv]
      rfl
    · have h₁ : IntExtNode.unsplit v ∉ W₁.image IntExtNode.unsplit := by
        intro h
        obtain ⟨v', hv', hveq⟩ := Finset.mem_image.mp h
        cases hveq
        exact hv hv'
      rw [if_neg h₁, if_neg hv]
      rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  -- ===================== Sub-goal 1: J component =====================
  · change (((G.J.image IntExtNode.unsplit ∪ (W₂ \ G.J).image IntExtNode.intCopy).image
                refactor_SplitNode.unsplit
              ∪ (W₁.image IntExtNode.unsplit).image refactor_SplitNode.copy1).image
              refactor_flattenSwigDoit
            = (G.J.image refactor_SplitNode.unsplit ∪ W₁.image refactor_SplitNode.copy1).image
                IntExtNode.unsplit
              ∪ (W₂.image refactor_SplitNode.unsplit \
                  (G.J.image refactor_SplitNode.unsplit ∪ W₁.image refactor_SplitNode.copy1)).image
                IntExtNode.intCopy)
    rw [h_J_sdiff]
    simp only [Finset.image_union]
    rw [h_uu_collapse, h_iu_collapse, h_c1u_collapse]
    rw [show (G.J.image refactor_SplitNode.unsplit).image
            (IntExtNode.unsplit (Node := refactor_SplitNode Node))
            = G.J.image (fun j => IntExtNode.unsplit (refactor_SplitNode.unsplit j))
          from Finset.image_image,
        show (W₁.image refactor_SplitNode.copy1).image
            (IntExtNode.unsplit (Node := refactor_SplitNode Node))
            = W₁.image (fun w => IntExtNode.unsplit (refactor_SplitNode.copy1 w))
          from Finset.image_image,
        show ((W₂ \ G.J).image refactor_SplitNode.unsplit).image
                (IntExtNode.intCopy (Node := refactor_SplitNode Node))
            = (W₂ \ G.J).image (fun w => IntExtNode.intCopy (refactor_SplitNode.unsplit w))
          from Finset.image_image]
    rw [Finset.union_assoc,
        Finset.union_comm
            ((W₂ \ G.J).image (fun w => IntExtNode.intCopy (refactor_SplitNode.unsplit w)))
            (W₁.image (fun w => IntExtNode.unsplit (refactor_SplitNode.copy1 w))),
        ← Finset.union_assoc]
  -- ===================== Sub-goal 2: V component =====================
  · change ((G.V.image IntExtNode.unsplit \ W₁.image IntExtNode.unsplit).image
              refactor_SplitNode.unsplit
            ∪ (W₁.image IntExtNode.unsplit).image refactor_SplitNode.copy0).image
              refactor_flattenSwigDoit
          = ((G.V \ W₁).image refactor_SplitNode.unsplit ∪
              W₁.image refactor_SplitNode.copy0).image
              IntExtNode.unsplit
    rw [h_V_sdiff]
    simp only [Finset.image_union]
    rw [h_uu_collapse, h_c0u_collapse]
    rw [show ((G.V \ W₁).image refactor_SplitNode.unsplit).image
              (IntExtNode.unsplit (Node := refactor_SplitNode Node))
            = (G.V \ W₁).image (fun v => IntExtNode.unsplit (refactor_SplitNode.unsplit v))
          from Finset.image_image,
        show (W₁.image refactor_SplitNode.copy0).image
              (IntExtNode.unsplit (Node := refactor_SplitNode Node))
            = W₁.image (fun w => IntExtNode.unsplit (refactor_SplitNode.copy0 w))
          from Finset.image_image]
  -- ===================== Sub-goal 3: E component =====================
  · change ((G.E.image (fun e : Node × Node =>
                  (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
              ∪ (W₂ \ G.J).image (fun w : Node =>
                  (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
                (fun e : IntExtNode Node × IntExtNode Node =>
                  (refactor_toCopy1 (W₁.image IntExtNode.unsplit) e.1,
                   refactor_toCopy0 (W₁.image IntExtNode.unsplit) e.2))).image
              (Prod.map refactor_flattenSwigDoit refactor_flattenSwigDoit)
            = (G.E.image (fun e : Node × Node =>
                (refactor_toCopy1 W₁ e.1, refactor_toCopy0 W₁ e.2))).image
                (fun e : refactor_SplitNode Node × refactor_SplitNode Node =>
                  (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
              ∪ (W₂.image refactor_SplitNode.unsplit \
                  (G.J.image refactor_SplitNode.unsplit ∪
                    W₁.image refactor_SplitNode.copy1)).image
                (fun w : refactor_SplitNode Node =>
                  (IntExtNode.intCopy w, IntExtNode.unsplit w))
    rw [h_J_sdiff]
    simp only [Finset.image_union, Finset.image_image]
    refine congr_arg₂ (· ∪ ·) ?_ ?_
    · refine Finset.image_congr ?_
      intro e _
      change (refactor_flattenSwigDoit
                (refactor_toCopy1 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit e.1)),
              refactor_flattenSwigDoit
                (refactor_toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit e.2)))
          = (IntExtNode.unsplit (refactor_toCopy1 W₁ e.1),
             IntExtNode.unsplit (refactor_toCopy0 W₁ e.2))
      rw [h_flat_toCopy1_unsplit, h_flat_toCopy0_unsplit]
    · refine Finset.image_congr ?_
      intro w hw
      obtain ⟨hw_W₂, _⟩ := Finset.mem_sdiff.mp hw
      have hw_notW₁ : w ∉ W₁ := Finset.disjoint_right.mp hDisj hw_W₂
      change (refactor_flattenSwigDoit
                (refactor_toCopy1 (W₁.image IntExtNode.unsplit) (IntExtNode.intCopy w)),
              refactor_flattenSwigDoit
                (refactor_toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit w)))
          = (IntExtNode.intCopy (refactor_SplitNode.unsplit w),
             IntExtNode.unsplit (refactor_SplitNode.unsplit w))
      unfold refactor_toCopy1 refactor_toCopy0
      have h1 : IntExtNode.intCopy w ∉ W₁.image IntExtNode.unsplit := by
        intro h
        obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
        cases hweq
      have h2 : IntExtNode.unsplit w ∉ W₁.image IntExtNode.unsplit := by
        intro h
        obtain ⟨v', hv', hveq⟩ := Finset.mem_image.mp h
        cases hveq
        exact hw_notW₁ hv'
      rw [if_neg h1, if_neg h2]
      rfl
  -- ===================== Sub-goal 4: L component =====================
  -- The genuine encoding-change sub-goal: under the `cdmg_typed_edges`
  -- refactor, L migrates from `Finset (Node × Node)` to
  -- `Finset (Sym2 Node)`, so the lifts are `Sym2.map` rather than
  -- `Prod.map _ _`.  Close by fusing the two-stage Sym2.map composition
  -- via `Sym2.map_map` and reducing to the pointwise
  -- `h_flat_toCopy0_unsplit` identity via `Sym2.map_congr`.  Mirrors
  -- the L sub-goal pattern in `claim_3_14`'s refactor twin
  -- (`h_L_lift_uu_collapse`).
  · change ((G.L.image (Sym2.map IntExtNode.unsplit)).image
              (Sym2.map (refactor_toCopy0 (W₁.image IntExtNode.unsplit)))).image
              (Sym2.map refactor_flattenSwigDoit)
            = (G.L.image (Sym2.map (refactor_toCopy0 W₁))).image
                (Sym2.map IntExtNode.unsplit)
    rw [Finset.image_image, Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro s _
    change Sym2.map refactor_flattenSwigDoit
            (Sym2.map (refactor_toCopy0 (W₁.image IntExtNode.unsplit))
              (Sym2.map IntExtNode.unsplit s))
          = Sym2.map IntExtNode.unsplit (Sym2.map (refactor_toCopy0 W₁) s)
    rw [Sym2.map_map, Sym2.map_map, Sym2.map_map]
    refine Sym2.map_congr ?_
    intro a _
    exact h_flat_toCopy0_unsplit a
-- REFACTOR-BLOCK-REPLACEMENT-END: addInterventionNodes_comm_swig

end refactor_CDMG

end Causality
