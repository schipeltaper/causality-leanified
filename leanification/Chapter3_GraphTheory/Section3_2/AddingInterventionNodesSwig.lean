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

-- ## Post-refactor port (`cdmg_typed_edges`)
--
-- The block below is the refactor twin of the row's declarations
-- against the `cdmg_typed_edges` redesign of `def_3_1` — same
-- mathematical content, retyped against `CDMG` and
-- `SplitNode`.  Only the L sub-goal genuinely changes
-- shape; the J / V / E sub-goals port mechanically because those
-- fields are untouched by the refactor (the refactor only restructures
-- L).
--
-- The L sub-goal uses `Sym2.map` in place of `Prod.map .unsplit .unsplit`,
-- and closes via `Sym2.map_map` (fuses two stages of `Sym2.map` into a
-- single one) followed by `Sym2.map_congr` (reduces to a pointwise
-- identity at the underlying-`Node` level).  The pointwise identity
-- `flattenSwigDoit (toCopy0 (W₁.image .unsplit)
-- (.unsplit a)) = .unsplit (toCopy0 W₁ a)` is the same `Node`-
-- level case-split as the original `h_flat_toCopy0_unsplit`, with only
-- the `refactor_` prefix added.  Mirrors `claim_3_14`'s sibling
-- refactor twin `addInterventionNodes_comm_disjoint`'s L
-- handling around `h_L_lift_uu_collapse`.
namespace CDMG
open CDMG

-- ## Helper — variable binders for this row's refactor-twin declarations
--
-- One-sentence summary: identical `Node : Type*` + `[DecidableEq Node]`
-- binders to the pre-refactor variable line, re-declared inside
-- `namespace CDMG` so the refactor-twin helpers and theorem
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
-- *Re-declared inside `namespace CDMG`, not relied on from
--   the outer `namespace CDMG` `variable` line.*  Lean's `variable`
--   binders are namespace-scoped; closing `end CDMG` (line 724) drops
--   the original binders.  We re-declare here so every refactor-twin
--   signature picks up `Node` / `DecidableEq Node` automatically
--   without a per-declaration `{Node : Type*} [DecidableEq Node]`
--   prefix.  No name collision with the pre-refactor variable line —
--   the two `variable` blocks live in distinct namespaces.
--
-- *Why a second `namespace CDMG` wrapper (vs.\ keeping
--   everything in `namespace CDMG`).*  The wrapper keeps the
--   refactor-twin declarations' field-projector dot notation aligned
--   with their *carrier* type: `(G : CDMG Node).J` resolves
--   via `CDMG.J`, which lives in this namespace, and
--   `G.nodeSplittingHard …` resolves via
--   `CDMG.nodeSplittingHard`.  Inlining everything
--   under `namespace CDMG` would force fully-qualified
--   `CDMG.J` at every use site (since dot notation routes
--   through the carrier's namespace, not the ambient one), or force
--   us to name the helpers `CDMG.refactor_<name>` directly
--   — both noisier than the namespace wrapper.  The `open CDMG`
--   immediately below this `variable` line brings the shared
--   identifiers (`IntExtNode`, `extendingCDMGsWith`,
--   `toCopy0`, `toCopy1`, etc., which were
--   declared inside `namespace CDMG` in `def_3_13` / `def_3_12`'s
--   refactor twins) into scope so we can call them function-style
--   without qualification.  Same pattern as `claim_3_14`'s refactor
--   twin in `AddingInterventionNodes.lean`.
--
-- *Mathlib re-use.*  Standard Lean `variable` mechanism; no Mathlib
--   structure involved.
-- claim_3_15 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_15 --- end helper

-- ## Private helper — `IsCADMG` witness for the inner
--   extension (refactor twin)
--
-- One-sentence summary: refactor port of
-- `extendingCDMGsWith_isCADMG_of_isCADMG`; discharges the
-- `IsCADMG` precondition that the RHS branch's outer
-- `nodeSplittingHard` needs on its inner
-- `extendingCDMGsWith` argument.
--
-- Refactor port of `extendingCDMGsWith_isCADMG_of_isCADMG`.
-- Mechanical rename: `CDMG → CDMG`,
-- `extendingCDMGsWith → extendingCDMGsWith`,
-- `IsCADMG → IsCADMG`, `extAcyclic → extAcyclic`.
-- The definitional unfolding `IsCADMG := IsAcyclic`
-- (cf.\ `def_3_7` refactor twin) makes the projection from
-- `extAcyclic`'s `IsAcyclic` conclusion to the
-- ambient `IsCADMG` goal definitional, exactly as in the
-- pre-refactor encoding.
--
-- ## Design choice
--
-- *Net-new declaration in this refactor port, not a rename of a
--   pre-existing entity.*  Although the surface text is a copy of
--   `extendingCDMGsWith_isCADMG_of_isCADMG` with each upstream
--   identifier prefixed `refactor_`, the resulting lemma is a fresh
--   declaration: its conclusion's type mentions
--   `extendingCDMGsWith`, which is a *different* function
--   from `extendingCDMGsWith` (it operates on `CDMG`, which
--   is a *different* structure from `CDMG`).  The pre-refactor
--   lemma cannot serve the refactor variant, so the rename is
--   forced.  See the BEFORE/AFTER block on `CDMG` in
--   `CDMG.lean` for the underlying structural divergence between
--   `CDMG` and `CDMG` (the `Sym2` encoding of L).
--
-- *Same Prop-level shape as the pre-refactor.*  Stays a `private`
--   plumbing lemma — not LN content, no helper marker — because the
--   refactor preserves the constructor signature shape of
--   `nodeSplittingHard`: it still takes a separate
--   `(hG : G.IsCADMG)` argument, and the LN-RHS branch's
--   outer `nodeSplittingHard ?hG ?W ?hW` still consumes
--   exactly this `IsCADMG` witness on the inner
--   `extendingCDMGsWith G W₂ hW₂`.
--
-- *Mathlib re-use.*  Same as the pre-refactor — the helper is a
--   thin term-mode wrapper around `extAcyclic` (the
--   `claim_3_13` refactor twin's acyclicity-preservation theorem);
--   no Mathlib API is involved.
private lemma extendingCDMGsWith_isCADMG_of_isCADMG
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    (extendingCDMGsWith G W hW).IsCADMG :=
  extAcyclic G W hW hG

-- ## Helper — `W₁.image .unsplit ⊆ V_{doit(I_{W₂})}` (refactor twin)
--
-- One-sentence summary: refactor port of
-- `image_unsplit_subset_extendingCDMGsWith_V`; discharges the
-- `?_ : W₁.image .unsplit ⊆ (extendingCDMGsWith G W₂ hW₂).V`
-- precondition that the LN-RHS branch's outer
-- `nodeSplittingHard … (W₁.image IntExtNode.unsplit) ?_`
-- needs.
--
-- Refactor port of `image_unsplit_subset_extendingCDMGsWith_V`.
-- Mechanical rename: `CDMG → CDMG`,
-- `extendingCDMGsWith → extendingCDMGsWith`.  The
-- `V`-component of `extendingCDMGsWith` is structurally
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
--   analogous fact for `G : CDMG Node`, with conclusion
--   `(extendingCDMGsWith G W₂ hW₂).V`.  Since `CDMG` and
--   `CDMG` are *distinct structures*, the pre-refactor
--   lemma cannot serve the refactor variant — a separate twin is
--   required.  Driven by the upstream rename, not by a design
--   change in this row.
--
-- *Body unchanged from the pre-refactor.*  Per the upstream
--   `CDMG` design-choice comment in `CDMG.lean`, the
--   refactor touches only the L-channel encoding (ordered pairs +
--   symmetry → `Sym2`); the `J`, `V`, and `E` fields are
--   structurally untouched, and so is
--   `extendingCDMGsWith`'s definition of its `V` field
--   (`V_{doit(I_W)} := G.V.image .unsplit`, identical to its
--   pre-refactor counterpart).  The proof body therefore ports
--   tactic-for-tactic with only the `CDMG → CDMG` /
--   `extendingCDMGsWith → extendingCDMGsWith` renames.
--
-- *Binder convention unchanged.*  Implicit `G`, `W₁`, `W₂`, `hW₂`;
--   explicit `hW₁`.  Matches the pre-refactor binder convention
--   verbatim so the call site at the refactor-twin theorem head
--   (`image_unsplit_subset_extendingCDMGsWith_V hW₁`)
--   reads identically to the pre-refactor call site.
--
-- *Mathlib re-use.*  Same as the pre-refactor — `Finset.mem_image`
--   forward and back, no Mathlib-level lemma about
--   `extendingCDMGsWith` is invoked (and none exists; the
--   constructor's `V`-field is exposed directly).
-- claim_3_15 --- start helper
private lemma image_unsplit_subset_extendingCDMGsWith_V
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V)
    {W₂ : Finset Node} {hW₂ : W₂ ⊆ G.J ∪ G.V} :
    W₁.image IntExtNode.unsplit ⊆ (extendingCDMGsWith G W₂ hW₂).V
-- claim_3_15 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change IntExtNode.unsplit v ∈ G.V.image IntExtNode.unsplit
  exact Finset.mem_image.mpr ⟨v, hW₁ hv, rfl⟩

-- ## Helper — `W₂.image .unsplit ⊆ J_{swig(W₁)} ∪ V_{swig(W₁)}`
--   (refactor twin)
--
-- One-sentence summary: refactor port of
-- `image_unsplit_subset_nodeSplittingHard_carrier`; discharges the
-- `?_ : W₂.image .unsplit ⊆ (G.nodeSplittingHard hG W₁ hW₁).J
--                            ∪ (G.nodeSplittingHard hG W₁ hW₁).V`
-- precondition that the LN-LHS branch's outer
-- `(G.nodeSplittingHard hG W₁ hW₁).extendingCDMGsWith
-- (W₂.image SplitNode.unsplit) ?_` needs.
--
-- Refactor port of `image_unsplit_subset_nodeSplittingHard_carrier`.
-- Mechanical rename: `CDMG → CDMG`,
-- `SplitNode → SplitNode`,
-- `nodeSplittingHard → nodeSplittingHard`.  The J / V
-- partition of `nodeSplittingHard` is structurally
-- identical to the pre-refactor `nodeSplittingHard` (the refactor
-- only touches L), so the proof body carries over verbatim with the
-- rename.
--
-- ## Design choice
--
-- *Why the lemma needs a refactor twin at all.*  Same reason as
--   `image_unsplit_subset_extendingCDMGsWith_V`: the
--   conclusion mentions `(G.nodeSplittingHard hG W₁ hW₁).J`
--   and `.V`, which only exist for `G : CDMG Node` —
--   `nodeSplittingHard` operates on `CDMG`, a
--   distinct structure from `CDMG`.  The lemma is forced by the
--   refactor's upstream rename, not by a substantive design change.
--
-- *Body carries over verbatim under the rename.*  The
--   case-split on `w ∈ G.J` vs.\ `w ∈ G.V` and the disjointness-
--   driven routing of `w ∈ G.V \ W₁ ⊆ (G.V \ W₁).image .unsplit`
--   are identical to the pre-refactor.  `nodeSplittingHard`'s
--   J / V definitions
--   (`J ∪ W₁`-style image union, `V \ W₁`-style image union plus
--   `W₁`'s `.copy0` copy) are structurally identical to
--   `nodeSplittingHard`'s — the upstream `CDMG` design-choice
--   comment in `CDMG.lean` documents that only the L channel
--   changed.
--
-- *Disjointness `Disjoint W₁ W₂` is still load-bearing on the
--   `V`-branch.*  Unchanged from the pre-refactor — without it, a
--   `w ∈ W₂ ∩ W₁ ∩ G.V` could not be routed through the
--   `(G.V \ W₁).image .unsplit` summand of `V_{swig(W₁)}` (it
--   would have to land in `W₁.image SplitNode.copy0`,
--   which has the wrong constructor).  Surfacing the same constraint
--   here as in the pre-refactor preserves the well-typedness
--   guarantee for the LHS's outer `extendingCDMGsWith`.
--
-- *Binder convention unchanged.*  Implicit `G`, `hG`, `W₁`, `W₂`;
--   explicit `hW₁`, `hW₂`, `hDisj`.  Matches the pre-refactor
--   verbatim so the call site at the refactor-twin theorem head
--   (`image_unsplit_subset_nodeSplittingHard_carrier hW₁
--   hW₂ hDisj`) reads identically to the pre-refactor.
--
-- *Mathlib re-use.*  Same as the pre-refactor — `Finset.mem_image`,
--   `Finset.disjoint_right`, `Finset.mem_sdiff`; no new Mathlib API
--   is engaged by the refactor.
-- claim_3_15 --- start helper
private lemma image_unsplit_subset_nodeSplittingHard_carrier
    {G : CDMG Node} {hG : G.IsCADMG}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.J ∪ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂.image SplitNode.unsplit ⊆
      (G.nodeSplittingHard hG W₁ hW₁).J ∪
        (G.nodeSplittingHard hG W₁ hW₁).V
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

-- ## Helper — the canonical flatten map (refactor twin)
--
-- One-sentence summary: refactor port of `flattenSwigDoit`; the same
-- pattern-matched bridge function as the pre-refactor, but operating
-- between the typed inductives `SplitNode (IntExtNode Node)`
-- (LN-RHS carrier under the refactor) and
-- `IntExtNode (SplitNode Node)` (LN-LHS carrier under the
-- refactor).
--
-- Refactor port of `flattenSwigDoit`.  Mechanical rename: the
-- `SplitNode` in the function signature and pattern-match clauses
-- becomes `SplitNode`.  The body is unchanged — every
-- pattern-match clause is a constructor-level identity that
-- transports verbatim across the rename (`SplitNode`'s
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
--   `def_3_12`) and `SplitNode` (the refactor twin) are
--   *distinct Lean inductive types* — they share constructor names
--   `.unsplit`, `.copy0`, `.copy1` only by convention, not at the
--   type-equality level.  So the existing
--   `flattenSwigDoit : SplitNode (IntExtNode Node) → IntExtNode (SplitNode Node)`
--   cannot serve the refactor variant, whose carriers
--   `SplitNode (IntExtNode Node)` and
--   `IntExtNode (SplitNode Node)` Lean treats as entirely
--   different types from the pre-refactor carriers.  A separate
--   `flattenSwigDoit` is therefore required.  Wrapped with
--   `REFACTOR-BLOCK-REPLACEMENT-…` markers but with no companion
--   ORIGINAL block: this is net-new in the REPLACEMENT, and Phase 7
--   cleanup's strict refusal rule for top-level `refactor_*`
--   declarations without REPLACEMENT markers is satisfied by the
--   marker block we placed here.
--
-- *Function direction `SplitNode (IntExtNode Node) →
--   IntExtNode (SplitNode Node)` matches the pre-refactor
--   pre-`SplitNode → IntExtNode` direction.*  Picked so the call
--   site `eqViaNodeMap RHS LHS flattenSwigDoit`
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
--   bijection on types — `flattenSwigDoit` is only
--   injective when restricted to the *reachable* RHS carrier
--   (`{.unsplit (.unsplit _)} ∪ {.unsplit (.intCopy _)} ∪
--   {.copy0 (.unsplit _)} ∪ {.copy1 (.unsplit _)}`); the
--   `.copy0 (.intCopy _)` and `.copy1 (.intCopy _)` cases are
--   filler-only and do not participate in the
--   `eqViaNodeMap` claim.  Disjointness `Disjoint W₁ W₂`
--   on the main theorem is precisely what keeps the reachable
--   image well-behaved.
-- claim_3_15 --- start helper
def flattenSwigDoit :
    SplitNode (IntExtNode Node) → IntExtNode (SplitNode Node)
  | .unsplit (.unsplit v) => IntExtNode.unsplit (SplitNode.unsplit v)
  | .unsplit (.intCopy w) => IntExtNode.intCopy (SplitNode.unsplit w)
  | .copy0 (.unsplit w) => IntExtNode.unsplit (SplitNode.copy0 w)
  | .copy0 (.intCopy w) => IntExtNode.intCopy (SplitNode.unsplit w)
  | .copy1 (.unsplit w) => IntExtNode.unsplit (SplitNode.copy1 w)
  | .copy1 (.intCopy w) => IntExtNode.intCopy (SplitNode.unsplit w)
-- claim_3_15 --- end helper

-- ref: claim_3_15 — refactor twin
--
-- For any `G : CDMG Node` (`hG : G.IsCADMG`), any
-- `W₁ ⊆ G.V` (`hW₁`), any `W₂ ⊆ G.J ∪ G.V` (`hW₂`), and any
-- `Disjoint W₁ W₂` (`hDisj`), the LN's displayed equality
--   `(G_{swig(W₁)})_{doit(I_{W₂})} = (G_{doit(I_{W₂})})_{swig(W₁)}`
-- is rendered (per the rewritten tex twin's "Distinct carriers and
-- the canonical relabelling identifying them" paragraph) as
-- `eqViaNodeMap RHS LHS flattenSwigDoit`.
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
--   comment on `CDMG` in `CDMG.lean` for the `Sym2`
--   encoding rationale and downstream consequences — we do not
--   re-litigate that choice here; this row only consumes it.
--
-- *L-channel encoding change is not visible in the theorem's
--   shape, only in the tactic block.*  The theorem statement
--   itself is identical in shape to the pre-refactor sibling —
--   same four binder pairs, same `eqViaNodeMap`
--   componentwise reading, same `flattenSwigDoit`
--   relabelling — because `eqViaNodeMap` is defined the
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
--   `eqViaNodeMap` not literal `=`; explicit LN-side ↔
--   Lean-operand mapping; binder order `(G) (hG) (W₁) (hW₁) (W₂)
--   (hW₂) (hDisj)`; `Disjoint W₁ W₂` as Mathlib `Finset`
--   disjointness; direction of `eqViaNodeMap` with RHS on
--   the left; no case-split for `W₂ ∩ J ≠ ∅` corner cases.  All
--   six are upstream-encoding-agnostic — none of them depends on
--   how L is encoded — so each ports verbatim from the
--   pre-refactor design block (lines 329-441) under the
--   `eqViaNodeMap → eqViaNodeMap`,
--   `flattenSwigDoit → flattenSwigDoit` renames.  Read
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
--   `extendingCDMGsWith` and the iterated
--   `nodeSplittingHard ∘ extendingCDMGsWith`
--   automatically, and `eqViaNodeMap` with
--   `flattenSwigDoit` tracks the degeneration through
--   both sides.  No statement-level case-split required.
--
-- *Mathlib re-use.*  The L-component sub-goal's `Sym2.map`,
--   `Sym2.map_map`, and `Sym2.map_congr` are the precise Mathlib
--   APIs the upstream `CDMG` design-choice block named as
--   the payoff for the `Sym2` encoding (so the `Sym2` lift commutes
--   functorially with composition and lifts pointwise identities).
--   Their use here is the predicted Mathlib re-use — no rolling
--   our own `Sym2`-level lemmas.  The J / V / E sub-goals continue
--   to use Mathlib's `Finset.image_image`, `Finset.image_union`,
--   `Finset.image_congr`, `Finset.union_assoc`, `Finset.union_comm`
--   exactly as the pre-refactor.
--
-- *Constraints / known limitations carried over.*  Identical to the
--   pre-refactor: `flattenSwigDoit` is total but injective
--   only on the reachable RHS carrier (so a hypothetical attempt
--   to invert the equality without `Disjoint W₁ W₂` would fail);
--   the `IntExtNode.unsplit` vs.\ `IntExtNode.intCopy` branch in
--   `def_3_13`'s `extendingCDMGsWith` makes the `W₂ ∩ J`
--   corner cases degenerate quietly rather than via an explicit
--   case-split.

-- ## Helper: `flattenSwigDoit` is `InjOn` on the iterated graph's J ∪ V
--
-- Net-new helper introduced by refactor `eqViaNodeMap_injective`
-- to discharge the strengthened predicate's `Set.InjOn` conjunct
-- for the carrier map `flattenSwigDoit`.
--
-- ### Role
--
-- Establishes `Set.InjOn flattenSwigDoit` on the carrier set of
-- the iterated CDMG `(G_{doit(I_{W₂})})_{swig(W₁)}` (the
-- predicate's first-argument / "LHS" side of
-- `eqViaNodeMap`, which is the SOURCE of
-- `flattenSwigDoit`).  This is the substantively new work of the
-- refactor: the four image-equality conjuncts (J, V, E, L) port
-- verbatim from the existing (cdmg_typed_edges) twin via the
-- destructuring binder in
-- `addInterventionNodes_comm_swig`; only the new
-- InjOn conjunct requires a substantively new proof, concentrated
-- here.
--
-- ### Why a separate lemma (rather than inlined in the main theorem)?
--
-- Mirrors the sibling refactor `claim_3_14`'s
-- `flattenIntExt_injOn_of_disjoint` and the root
-- refactor `claim_3_7`'s `flattenSplit_injOn_of_disjoint`.
-- The proof argument is also geometrically clean enough to deserve
-- its own name: a four-cell partition of the iterated LHS graph's
-- `J ∪ V` (cells (1) `ι_swig(ι_doit(J ∪ (V \ W₁)))` merged into
-- a single `.unsplit (.unsplit _)` pattern; cell (2)
-- `ι_swig({I_w | w ∈ W₂ \ J})` as `.unsplit (.intCopy _)`;
-- cell (3) `W₁^o` as `.copy0 (.unsplit _)`; cell (4) `W₁^i` as
-- `.copy1 (.unsplit _)`) followed by a 4 × 4 = 16 case analysis
-- with structural-equality / no-confusion closures, mirroring the
-- verified tex twin's "Injectivity of the canonical flatten map
-- `flattenSwigDoit` on the iterated LHS carrier's J ∪ V"
-- paragraph one-to-one.
--
-- ### Why `Set.InjOn` on `↑(...).J ∪ ↑(...).V` (matching the predicate's carrier set verbatim)?
--
-- Pasted directly from `eqViaNodeMap`'s first-conjunct
-- shape so that the consumer call site in the main theorem can
-- plug this lemma in with no Set-arithmetic glue.  The
-- iterated-graph operand is the same one that appears on the
-- left of `eqViaNodeMap` in the main theorem statement,
-- so the carrier sets line up definitionally.
--
-- ### Why disjointness is NOT load-bearing on the InjOn proof
--
-- In stark contrast to `claim_3_14`'s sibling
-- `flattenIntExt_injOn_of_disjoint` (where the
-- cell-(3)-vs-cell-(4) collision `IntExtNode.intCopy w₁ =
-- IntExtNode.intCopy w₂` for `w₁ ∈ W₁ \ J`, `w₂ ∈ W₂ \ J`
-- forces `w₁ = w₂ ∈ W₁ ∩ W₂` and is closed only by the
-- disjointness hypothesis), here the four cells produce four
-- pairwise-distinct "outer-constructor / inner-constructor"
-- signatures under `flattenSwigDoit`:
--   * cell (1) `.unsplit (.unsplit a) ↦ IntExtNode.unsplit (SplitNode.unsplit a)`;
--   * cell (2) `.unsplit (.intCopy w) ↦ IntExtNode.intCopy (SplitNode.unsplit w)`;
--   * cell (3) `.copy0 (.unsplit w) ↦ IntExtNode.unsplit (SplitNode.copy0 w)`;
--   * cell (4) `.copy1 (.unsplit w) ↦ IntExtNode.unsplit (SplitNode.copy1 w)`.
-- All six cross-cell collision patterns are ruled out
-- structurally: outer `IntExtNode.unsplit` vs `IntExtNode.intCopy`
-- mismatches at the outer constructor; the three pairs sharing
-- outer `IntExtNode.unsplit` differ at the inner `SplitNode`
-- constructor (`unsplit` vs `copy0` vs `copy1`).  Lean's
-- recursive `cases heq` no-confusion handles both kinds of
-- mismatch.  See the verified tex twin's "Across-cell
-- injectivity" paragraph for the structural argument; the
-- disjointness hypothesis `Disjoint W₁ W₂` is consumed elsewhere
-- in the refactor (in the E-component bookkeeping of the
-- original) but NOT in this InjOn paragraph.  The `hDisj`
-- parameter is kept in the signature for caller-side
-- consistency with the sibling helpers
-- `flattenIntExt_injOn_of_disjoint` and
-- `flattenSplit_injOn_of_disjoint` (which DO consume
-- disjointness in their cross-cell branches); the
-- `linter.unusedVariables` opt-out below is intentional.
set_option linter.unusedVariables false in
private lemma flattenSwigDoit_injOn_of_disjoint
    (G : CDMG Node) (hG : G.IsCADMG)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.V)
    (hW₂ : W₂ ⊆ G.J ∪ G.V) (hDisj : Disjoint W₁ W₂) :
    Set.InjOn flattenSwigDoit
        ((↑((extendingCDMGsWith G W₂ hW₂).nodeSplittingHard
              (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
              (W₁.image IntExtNode.unsplit)
              (image_unsplit_subset_extendingCDMGsWith_V hW₁)).J :
            Set (SplitNode (IntExtNode Node))) ∪
          ↑((extendingCDMGsWith G W₂ hW₂).nodeSplittingHard
              (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
              (W₁.image IntExtNode.unsplit)
              (image_unsplit_subset_extendingCDMGsWith_V hW₁)).V) := by
  -- Classify each element of the iterated graph's J ∪ V into one
  -- of 4 disjoint patterns (the four cells of the verified tex
  -- twin's "Four-cell decomposition of the iterated LHS carrier").
  -- Cells (1J) and (1V) of the tex are merged here into a single
  -- `.unsplit (.unsplit a)` pattern, since the constructor chain
  -- and the within-cell injectivity argument are identical.
  have classify : ∀ z : SplitNode (IntExtNode Node),
      z ∈ ((extendingCDMGsWith G W₂ hW₂).nodeSplittingHard
              (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
              (W₁.image IntExtNode.unsplit)
              (image_unsplit_subset_extendingCDMGsWith_V hW₁)).J ∪
          ((extendingCDMGsWith G W₂ hW₂).nodeSplittingHard
              (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
              (W₁.image IntExtNode.unsplit)
              (image_unsplit_subset_extendingCDMGsWith_V hW₁)).V →
      (∃ a : Node, z = SplitNode.unsplit (IntExtNode.unsplit a))
        ∨ (∃ w : Node, z = SplitNode.unsplit (IntExtNode.intCopy w))
        ∨ (∃ w : Node, z = SplitNode.copy0 (IntExtNode.unsplit w))
        ∨ (∃ w : Node, z = SplitNode.copy1 (IntExtNode.unsplit w)) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hJ | hV
    · -- z ∈ iterated graph's J
      change z ∈ (G.J.image IntExtNode.unsplit ∪
                    (W₂ \ G.J).image IntExtNode.intCopy).image
                  SplitNode.unsplit ∪
                (W₁.image IntExtNode.unsplit).image SplitNode.copy1 at hJ
      rcases Finset.mem_union.mp hJ with hJ1 | hJ2
      · -- outer SplitNode.unsplit branch: z = .unsplit y
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hJ1
        rcases Finset.mem_union.mp hy with hyJ | hyW
        · -- y = .unsplit j, j ∈ G.J → cell (1)
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyJ
          exact Or.inl ⟨j, rfl⟩
        · -- y = .intCopy w, w ∈ W₂ \ G.J → cell (2)
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hyW
          exact Or.inr (Or.inl ⟨w, rfl⟩)
      · -- outer SplitNode.copy1 branch: z = .copy1 y, y ∈ W₁.image .unsplit → cell (4)
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hJ2
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
        exact Or.inr (Or.inr (Or.inr ⟨w, rfl⟩))
    · -- z ∈ iterated graph's V
      change z ∈ (G.V.image IntExtNode.unsplit \
                    W₁.image IntExtNode.unsplit).image
                  SplitNode.unsplit ∪
                (W₁.image IntExtNode.unsplit).image SplitNode.copy0 at hV
      rcases Finset.mem_union.mp hV with hV1 | hV2
      · -- outer SplitNode.unsplit branch: z = .unsplit y
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hV1
        obtain ⟨hyV, _⟩ := Finset.mem_sdiff.mp hy
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hyV
        -- v ∈ G.V (and v ∉ W₁ by the sdiff, unused here) → cell (1)
        exact Or.inl ⟨v, rfl⟩
      · -- outer SplitNode.copy0 branch: z = .copy0 y, y ∈ W₁.image .unsplit → cell (3)
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hV2
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
        exact Or.inr (Or.inr (Or.inl ⟨w, rfl⟩))
  -- Main InjOn argument.
  intro x hx y hy heq
  -- Convert hx, hy from Set membership to Finset disjunction-then-union.
  have hx' : x ∈ ((extendingCDMGsWith G W₂ hW₂).nodeSplittingHard
                    (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
                    (W₁.image IntExtNode.unsplit)
                    (image_unsplit_subset_extendingCDMGsWith_V hW₁)).J ∪
              ((extendingCDMGsWith G W₂ hW₂).nodeSplittingHard
                    (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
                    (W₁.image IntExtNode.unsplit)
                    (image_unsplit_subset_extendingCDMGsWith_V hW₁)).V := by
    rcases hx with h | h
    · exact Finset.mem_union_left _ (Finset.mem_coe.mp h)
    · exact Finset.mem_union_right _ (Finset.mem_coe.mp h)
  have hy' : y ∈ ((extendingCDMGsWith G W₂ hW₂).nodeSplittingHard
                    (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
                    (W₁.image IntExtNode.unsplit)
                    (image_unsplit_subset_extendingCDMGsWith_V hW₁)).J ∪
              ((extendingCDMGsWith G W₂ hW₂).nodeSplittingHard
                    (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
                    (W₁.image IntExtNode.unsplit)
                    (image_unsplit_subset_extendingCDMGsWith_V hW₁)).V := by
    rcases hy with h | h
    · exact Finset.mem_union_left _ (Finset.mem_coe.mp h)
    · exact Finset.mem_union_right _ (Finset.mem_coe.mp h)
  -- Classify x and y into one of 4 patterns each (4 × 4 = 16 subcases).
  rcases classify x hx' with
    ⟨xa, rfl⟩ | ⟨xw, rfl⟩ | ⟨xw, rfl⟩ | ⟨xw, rfl⟩ <;>
  rcases classify y hy' with
    ⟨ya, rfl⟩ | ⟨yw, rfl⟩ | ⟨yw, rfl⟩ | ⟨yw, rfl⟩ <;>
  -- Each of the 16 cases has `heq` of the form
  -- `<IntExtNode.C> (<SplitNode.C> _) = <IntExtNode.C> (<SplitNode.C> _)`
  -- after definitional unfolding of `flattenSwigDoit`.  Close by:
  -- (a) diagonal (4): inject both layers, subst inner var, rfl;
  -- (b) outer- or inner-mismatch (12): `cases heq` derives False
  --     via Lean's recursive no-confusion on the constructor chain.
  -- No disjointness consumed: the four flatten-image signatures are
  -- pairwise distinct on outer × inner constructor pairs.
  first
  | (injection heq with h; injection h with h'; subst h'; rfl)
  | cases heq

-- ref: claim_3_15
--
-- ## Refactor: `addInterventionNodes_comm_swig`
--
-- Refactor of `addInterventionNodes_comm_swig` for refactor
-- `eqViaNodeMap_injective`.  Same single `eqViaNodeMap` shape
-- as the original (one bridge between the LN's LHS and RHS
-- iterated carriers via `flattenSwigDoit`), but the predicate
-- `eqViaNodeMap` is replaced by the strengthened
-- `eqViaNodeMap` (carrying a fifth `Set.InjOn`
-- conjunct on the carrier map).
--
-- ### What's reused from the original
--
-- The four image-equality conjuncts (`J`, `V`, `E`, `L`) come
-- straight from the existing (cdmg_typed_edges)
-- `addInterventionNodes_comm_swig` via the destructuring binder
-- in the opening `obtain ⟨hJ, hV, hE, hL⟩ := ...` line.  The
-- refactor does NOT redo the ~250-line J/V/E/L bookkeeping --
-- it would produce a bit-for-bit identical tactic block, so
-- reusing the original keeps the LN-to-Lean correspondence
-- one-to-one and the file size manageable.  The new content is
-- purely the InjOn discharge (the single `exact` line below the
-- destructure).
--
-- ### Why the InjOn discharge is non-trivial
--
-- The carrier map `flattenSwigDoit` is not globally injective on
-- `SplitNode (IntExtNode Node)`: the off-iterated-graph filler
-- patterns `.copy0 (.intCopy w)` and `.copy1 (.intCopy w)` both
-- map to `IntExtNode.intCopy (SplitNode.unsplit w)`, which also
-- coincides with the image of cell (2)'s `.unsplit (.intCopy w)`.
-- The witnessing InjOn property holds only on the iterated
-- graph's `J ∪ V`, where the four reachable cells produce four
-- pairwise-distinct outer-constructor / inner-constructor
-- signatures and the filler patterns are excluded.  See the
-- helper comment above for the structural argument.
--
-- ### Why disjointness is needed by the helper but NOT by the InjOn step
--
-- The helper signature still carries `hDisj : Disjoint W₁ W₂`
-- because the type-level well-typedness of the LHS iterated
-- graph `(extendingCDMGsWith G W₂ hW₂).nodeSplittingHard ...`
-- depends on `image_unsplit_subset_extendingCDMGsWith_V hW₁` --
-- which does NOT consume disjointness on its own -- but the
-- whole-row-level hypothesis is part of the refactor twin's
-- signature.  The InjOn argument itself uses only
-- structural constructor injectivity / mismatch; disjointness
-- is consumed elsewhere in the proof (in the E-component
-- bookkeeping of the original `addInterventionNodes_comm_swig`,
-- where `W₂ \ G.J ⊆ V \ W₁` is the load-bearing step that
-- forces the head of each fresh intervention edge `I_w → w`
-- onto the unsplit-untagged side of `V_{swig(W₁)}`).
-- ## Helper: pre-injectivity-refactor `addInterventionNodes_comm_swig`
--
-- Returns the four image-equality conjuncts (per `imageEqs` from
-- `TwoDisjointNode.lean`), proof body verbatim from the
-- pre-injectivity-refactor `addInterventionNodes_comm_swig`. The new public
-- theorem below adds the `Set.InjOn` proofs on top.
private theorem addInterventionNodes_comm_swig_imageEqs (G : CDMG Node) (hG : G.IsCADMG)
    (W₁ : Finset Node) (hW₁ : W₁ ⊆ G.V)
    (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    imageEqs
        ((extendingCDMGsWith G W₂ hW₂).nodeSplittingHard
            (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
            (W₁.image IntExtNode.unsplit)
            (image_unsplit_subset_extendingCDMGsWith_V hW₁))
        (extendingCDMGsWith
            (G.nodeSplittingHard hG W₁ hW₁)
            (W₂.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingHard_carrier hW₁ hW₂ hDisj))
        flattenSwigDoit
  := by
  -- TeX proof: refactor_claim_3_15_proof_AddingInterventionNodes.tex.
  -- Same structure as the pre-refactor sibling, with J / V / E sub-goals
  -- ported mechanically and the L sub-goal restructured around
  -- `Sym2.map` / `Sym2.map_map` / `Sym2.map_congr`.
  -- ## Single-node flatten collapses (J / V components).
  have h_uu_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image SplitNode.unsplit).image
          flattenSwigDoit
      = S.image (fun v => IntExtNode.unsplit (SplitNode.unsplit v)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_iu_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.intCopy).image SplitNode.unsplit).image
          flattenSwigDoit
      = S.image (fun w => IntExtNode.intCopy (SplitNode.unsplit w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_c0u_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image SplitNode.copy0).image
          flattenSwigDoit
      = S.image (fun w => IntExtNode.unsplit (SplitNode.copy0 w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  have h_c1u_collapse : ∀ (S : Finset Node),
      ((S.image IntExtNode.unsplit).image SplitNode.copy1).image
          flattenSwigDoit
      = S.image (fun w => IntExtNode.unsplit (SplitNode.copy1 w)) := by
    intro S
    rw [Finset.image_image, Finset.image_image]
    rfl
  -- ## J-side sdiff identity.
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
  have h_flat_toCopy1_unsplit : ∀ (v : Node),
      flattenSwigDoit
          (toCopy1 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit v))
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
  have h_flat_toCopy0_unsplit : ∀ (v : Node),
      flattenSwigDoit
          (toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit v))
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
  · change (((G.J.image IntExtNode.unsplit ∪ (W₂ \ G.J).image IntExtNode.intCopy).image
                SplitNode.unsplit
              ∪ (W₁.image IntExtNode.unsplit).image SplitNode.copy1).image
              flattenSwigDoit
            = (G.J.image SplitNode.unsplit ∪ W₁.image SplitNode.copy1).image
                IntExtNode.unsplit
              ∪ (W₂.image SplitNode.unsplit \
                  (G.J.image SplitNode.unsplit ∪ W₁.image SplitNode.copy1)).image
                IntExtNode.intCopy)
    rw [h_J_sdiff]
    simp only [Finset.image_union]
    rw [h_uu_collapse, h_iu_collapse, h_c1u_collapse]
    rw [show (G.J.image SplitNode.unsplit).image
            (IntExtNode.unsplit (Node := SplitNode Node))
            = G.J.image (fun j => IntExtNode.unsplit (SplitNode.unsplit j))
          from Finset.image_image,
        show (W₁.image SplitNode.copy1).image
            (IntExtNode.unsplit (Node := SplitNode Node))
            = W₁.image (fun w => IntExtNode.unsplit (SplitNode.copy1 w))
          from Finset.image_image,
        show ((W₂ \ G.J).image SplitNode.unsplit).image
                (IntExtNode.intCopy (Node := SplitNode Node))
            = (W₂ \ G.J).image (fun w => IntExtNode.intCopy (SplitNode.unsplit w))
          from Finset.image_image]
    rw [Finset.union_assoc,
        Finset.union_comm
            ((W₂ \ G.J).image (fun w => IntExtNode.intCopy (SplitNode.unsplit w)))
            (W₁.image (fun w => IntExtNode.unsplit (SplitNode.copy1 w))),
        ← Finset.union_assoc]
  -- ===================== Sub-goal 2: V component =====================
  · change ((G.V.image IntExtNode.unsplit \ W₁.image IntExtNode.unsplit).image
              SplitNode.unsplit
            ∪ (W₁.image IntExtNode.unsplit).image SplitNode.copy0).image
              flattenSwigDoit
          = ((G.V \ W₁).image SplitNode.unsplit ∪
              W₁.image SplitNode.copy0).image
              IntExtNode.unsplit
    rw [h_V_sdiff]
    simp only [Finset.image_union]
    rw [h_uu_collapse, h_c0u_collapse]
    rw [show ((G.V \ W₁).image SplitNode.unsplit).image
              (IntExtNode.unsplit (Node := SplitNode Node))
            = (G.V \ W₁).image (fun v => IntExtNode.unsplit (SplitNode.unsplit v))
          from Finset.image_image,
        show (W₁.image SplitNode.copy0).image
              (IntExtNode.unsplit (Node := SplitNode Node))
            = W₁.image (fun w => IntExtNode.unsplit (SplitNode.copy0 w))
          from Finset.image_image]
  -- ===================== Sub-goal 3: E component =====================
  · change ((G.E.image (fun e : Node × Node =>
                  (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
              ∪ (W₂ \ G.J).image (fun w : Node =>
                  (IntExtNode.intCopy w, IntExtNode.unsplit w))).image
                (fun e : IntExtNode Node × IntExtNode Node =>
                  (toCopy1 (W₁.image IntExtNode.unsplit) e.1,
                   toCopy0 (W₁.image IntExtNode.unsplit) e.2))).image
              (Prod.map flattenSwigDoit flattenSwigDoit)
            = (G.E.image (fun e : Node × Node =>
                (toCopy1 W₁ e.1, toCopy0 W₁ e.2))).image
                (fun e : SplitNode Node × SplitNode Node =>
                  (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
              ∪ (W₂.image SplitNode.unsplit \
                  (G.J.image SplitNode.unsplit ∪
                    W₁.image SplitNode.copy1)).image
                (fun w : SplitNode Node =>
                  (IntExtNode.intCopy w, IntExtNode.unsplit w))
    rw [h_J_sdiff]
    simp only [Finset.image_union, Finset.image_image]
    refine congr_arg₂ (· ∪ ·) ?_ ?_
    · refine Finset.image_congr ?_
      intro e _
      change (flattenSwigDoit
                (toCopy1 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit e.1)),
              flattenSwigDoit
                (toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit e.2)))
          = (IntExtNode.unsplit (toCopy1 W₁ e.1),
             IntExtNode.unsplit (toCopy0 W₁ e.2))
      rw [h_flat_toCopy1_unsplit, h_flat_toCopy0_unsplit]
    · refine Finset.image_congr ?_
      intro w hw
      obtain ⟨hw_W₂, _⟩ := Finset.mem_sdiff.mp hw
      have hw_notW₁ : w ∉ W₁ := Finset.disjoint_right.mp hDisj hw_W₂
      change (flattenSwigDoit
                (toCopy1 (W₁.image IntExtNode.unsplit) (IntExtNode.intCopy w)),
              flattenSwigDoit
                (toCopy0 (W₁.image IntExtNode.unsplit) (IntExtNode.unsplit w)))
          = (IntExtNode.intCopy (SplitNode.unsplit w),
             IntExtNode.unsplit (SplitNode.unsplit w))
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
  -- The genuine encoding-change sub-goal: under the `cdmg_typed_edges`
  -- refactor, L migrates from `Finset (Node × Node)` to
  -- `Finset (Sym2 Node)`, so the lifts are `Sym2.map` rather than
  -- `Prod.map _ _`.  Close by fusing the two-stage Sym2.map composition
  -- via `Sym2.map_map` and reducing to the pointwise
  -- `h_flat_toCopy0_unsplit` identity via `Sym2.map_congr`.  Mirrors
  -- the L sub-goal pattern in `claim_3_14`'s refactor twin
  -- (`h_L_lift_uu_collapse`).
  · change ((G.L.image (Sym2.map IntExtNode.unsplit)).image
              (Sym2.map (toCopy0 (W₁.image IntExtNode.unsplit)))).image
              (Sym2.map flattenSwigDoit)
            = (G.L.image (Sym2.map (toCopy0 W₁))).image
                (Sym2.map IntExtNode.unsplit)
    rw [Finset.image_image, Finset.image_image, Finset.image_image]
    refine Finset.image_congr ?_
    intro s _
    change Sym2.map flattenSwigDoit
            (Sym2.map (toCopy0 (W₁.image IntExtNode.unsplit))
              (Sym2.map IntExtNode.unsplit s))
          = Sym2.map IntExtNode.unsplit (Sym2.map (toCopy0 W₁) s)
    rw [Sym2.map_map, Sym2.map_map, Sym2.map_map]
    refine Sym2.map_congr ?_
    intro a _
    exact h_flat_toCopy0_unsplit a

-- claim_3_15 -- start statement
theorem addInterventionNodes_comm_swig
    (G : CDMG Node) (hG : G.IsCADMG)
    (W₁ : Finset Node) (hW₁ : W₁ ⊆ G.V)
    (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.J ∪ G.V)
    (hDisj : Disjoint W₁ W₂) :
    eqViaNodeMap
        ((extendingCDMGsWith G W₂ hW₂).nodeSplittingHard
            (extendingCDMGsWith_isCADMG_of_isCADMG hG hW₂)
            (W₁.image IntExtNode.unsplit)
            (image_unsplit_subset_extendingCDMGsWith_V hW₁))
        (extendingCDMGsWith
            (G.nodeSplittingHard hG W₁ hW₁)
            (W₂.image SplitNode.unsplit)
            (image_unsplit_subset_nodeSplittingHard_carrier hW₁ hW₂ hDisj))
        flattenSwigDoit
-- claim_3_15 -- end statement

  := by
  obtain ⟨hJ, hV, hE, hL⟩ :=
    addInterventionNodes_comm_swig_imageEqs G hG W₁ hW₁ W₂ hW₂ hDisj
  refine ⟨?_, hJ, hV, hE, hL⟩
  exact flattenSwigDoit_injOn_of_disjoint G hG W₁ W₂ hW₁ hW₂ hDisj
end CDMG

end Causality
