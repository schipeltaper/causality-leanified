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
-- claim_3_15 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_15 --- end helper

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
private lemma extendingCDMGsWith_isCADMG_of_isCADMG
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    (G.extendingCDMGsWith W hW).IsCADMG :=
  extAcyclic G W hW hG

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
-- claim_3_15 --- start helper
def flattenSwigDoit : SplitNode (IntExtNode Node) → IntExtNode (SplitNode Node)
  | .unsplit (.unsplit v) => IntExtNode.unsplit (SplitNode.unsplit v)
  | .unsplit (.intCopy w) => IntExtNode.intCopy (SplitNode.unsplit w)
  | .copy0 (.unsplit w) => IntExtNode.unsplit (SplitNode.copy0 w)
  | .copy0 (.intCopy w) => IntExtNode.intCopy (SplitNode.unsplit w)
  | .copy1 (.unsplit w) => IntExtNode.unsplit (SplitNode.copy1 w)
  | .copy1 (.intCopy w) => IntExtNode.intCopy (SplitNode.unsplit w)
-- claim_3_15 --- end helper

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

end CDMG

end Causality
