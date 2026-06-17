import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.CDMGTypes
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_1.AcyclicIffTopologicalOrder
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn

namespace Causality

/-!
# Split topological order (`claim_3_6`)

This file formalises the LN remark `claim_3_6` (`SplitTopologicalOrder`
in `graphs.tex`, section 3.2):

> For a CADMG `G = (J, V, E, L)`, also `G_{spl(W)}` is acyclic.  If
> `<` is any topological order of `G` given by enumerating
> `J ∪ V = {v_1 < v_2 < ⋯ < v_n}`, then a topological order for
> `G_{spl(W)}` can be achieved by assigning, for `v_j ∈ W`, the index
> `j - 1/3` to `v_j^0` and `j + 1/3` to `v_j^1`, and then ordering all
> nodes according to their index value.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_6_statement_SplitTopologicalOrder.tex`,
verified equivalent to the LN block by `verify_tex_statement_only` and
`verify_tex_statement_equivalence`.  No `addition_to_the_LN` clauses
were attached; the rewrite folded the LN-critic's two working-phase
subtleties directly into the canonical tex as non-load-bearing
clarifications:

* `unsplit_nodes_implicit_index_retention` — the LN's literal text
  assigns indices only to the tagged copies `v_j^0`, `v_j^1` of split
  nodes `v_j ∈ W`, and is silent on the indices of unsplit nodes
  `v_j ∈ J ∪ (V ∖ W)`.  The canonical tex spec records the natural and
  only-consistent reading: unsplit nodes retain their original index
  `j`.
* `orientation_convention_v0_below_v1` — the construction's correctness
  rests on the convention `w^0 < w^1` in `<_{spl}`, matching the
  `def_3_11` tagging convention (transfer edge `(w^0, w^1)`, incoming
  edges reattached at `w^0`, outgoing edges leaving `w^1`).

The remark bundles two sub-claims under one `\begin{Rem}`:

* (a) **Acyclicity preservation.** `G_{spl(W)}` is acyclic
  (`def_3_6`'s `IsAcyclic`).
* (b) **Explicit topological order on `G_{spl(W)}`.** For every
  topological order `<` of `G`, the relation `<_{spl}` on
  `SplitNode Node` defined below is a topological order of
  `G_{spl(W)}` (`def_3_8`'s `IsTopologicalOrder`).

Both sub-claims share the same hypotheses (`G.IsCADMG` and
`W ⊆ G.V`); they are stated as **two separate theorems**
(`splAcyclic` and `splTopologicalOrder`) — see the
"single theorem vs.\ two separate theorems" design-choice bullet
below for the rationale.

The proof bodies are filled in by `prove_claim_in_lean` (Manager B),
following the verified TeX proof at
`tex/claim_3_6_proof_SplitTopologicalOrder.tex`.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  Both fixtures are load-bearing for this
--   row's statement because the signature references `CDMG Node`
--   (`def_3_1`), `G.IsCADMG` (`def_3_7`), `G.nodeSplittingOn W hW`
--   (`def_3_11`), `(G.nodeSplittingOn W hW).IsAcyclic` (`def_3_6`),
--   `G.IsTopologicalOrder lt` (`def_3_8`), and
--   `(G.nodeSplittingOn W hW).IsTopologicalOrder (splOrder lt)`
--   (which goes through the split CDMG's
--   `Pa : SplitNode Node → Set (SplitNode Node)` from `def_3_5`, in
--   turn requiring `[DecidableEq (SplitNode Node)]` — provided
--   automatically by `def_3_11`'s `deriving DecidableEq` on the
--   tagged-sum inductive).  Stronger instances (`Fintype`,
--   `LinearOrder`) are not needed at the statement level.
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  Matches the convention in every sibling
--   file in `Section3_2/` (`HardInterventionOn.lean`,
--   `AcyclicPreservedUnderDo.lean`, `HardInterventionsCommute.lean`,
--   `BifurcationAlternative.lean`, `NodeSplittingOn.lean`) and in
--   `Section3_1/`.  The two-dash marker is reserved for declarations
--   whose body is the formalised LN content of the row; this
--   `variable` line is statement-typing infrastructure binding the
--   implicit `Node` type and its `DecidableEq` instance that the
--   helper `splOrder` and the two main theorems all reference.
-- claim_3_6 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_6 --- end helper

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: splOrder
-- ## Helper: the LN's `<_{spl}` order on `SplitNode Node`
--
-- The LN constructs `<_{spl}` via an index map
-- `φ : J_{spl(W)} ∪ V_{spl(W)} → ℚ` that assigns
--
--   * `φ(v_j) := j`         for `v_j ∈ J ∪ (V ∖ W)` (unsplit node
--     retains its original index `j` from the topological order
--     enumeration `v_1 < … < v_n`);
--   * `φ(w^0) := j - 1/3`   for `w = v_j ∈ W`;
--   * `φ(w^1) := j + 1/3`   for `w = v_j ∈ W`;
--
-- and then defines `x <_{spl} y :⇔ φ(x) < φ(y)` via the standard
-- strict order on `ℚ`.
--
-- *Equivalence with the case-analysis below.*  The integer indices and
-- `ℚ`-arithmetic are *devices* the LN uses to give a concrete formula;
-- semantically the resulting relation is fully determined by the
-- underlying `<` on `J ∪ V` and the constructor tag (`unsplit` /
-- `copy0` / `copy1`).  Concretely, since the integer indices `j` are
-- distinct for distinct nodes and `1/3 < 1`, the inequality
-- `φ(x) < φ(y)` reduces — case by case on the two constructors — to a
-- comparison involving only `lt` on the underlying nodes plus, in some
-- mixed-tag cases, an equality clause `u = w`.  Working through each
-- of the nine constructor pairs:
--
--   (`unsplit u`, `unsplit v`):   `idx(u) < idx(v)`
--                                       ⟺  `lt u v`.
--   (`unsplit u`, `copy0 w`):    `idx(u) < idx(w) - 1/3`
--                                       ⟺  `idx(u) < idx(w)`
--                                       ⟺  `lt u w`.
--   (`unsplit u`, `copy1 w`):    `idx(u) < idx(w) + 1/3`
--                                       ⟺  `idx(u) ≤ idx(w)`
--                                       ⟺  `lt u w ∨ u = w`.
--   (`copy0 v`, `unsplit u`):    `idx(v) - 1/3 < idx(u)`
--                                       ⟺  `idx(v) ≤ idx(u)`
--                                       ⟺  `lt v u ∨ v = u`.
--   (`copy0 v`, `copy0 w`):     `idx(v) - 1/3 < idx(w) - 1/3`
--                                       ⟺  `lt v w`.
--   (`copy0 v`, `copy1 w`):     `idx(v) - 1/3 < idx(w) + 1/3`
--                                       ⟺  `idx(v) ≤ idx(w)`
--                                       ⟺  `lt v w ∨ v = w`.
--   (`copy1 v`, `unsplit u`):    `idx(v) + 1/3 < idx(u)`
--                                       ⟺  `idx(v) < idx(u)`
--                                       ⟺  `lt v u`.
--   (`copy1 v`, `copy0 w`):     `idx(v) + 1/3 < idx(w) - 1/3`
--                                       ⟺  `idx(v) < idx(w)`
--                                       ⟺  `lt v w`.
--   (`copy1 v`, `copy1 w`):     `idx(v) + 1/3 < idx(w) + 1/3`
--                                       ⟺  `lt v w`.
--
-- The case analysis below is the literal transcription.  Note that the
-- order is morally the *lex* order on the pair (base node, copy tag)
-- where the copy tag takes the three values `-1` (`copy0`), `0`
-- (`unsplit`), `+1` (`copy1`); the case analysis spells the lex order
-- out explicitly per constructor pair instead of going through the
-- numeric tag.
--
-- ## Design choice
--
-- *Case-analysis encoding, not `ℚ`-arithmetic.*  Three reasons to skip
--   the `ℚ` device.  (a) **Reuses no Mathlib infrastructure.**  The
--   `ℚ`-based encoding would require manually enumerating
--   `J ∪ V = {v_1 < … < v_n}`, constructing a function `idx : Node → ℕ`
--   (or `ℤ`) on the carrier `G.J ∪ G.V`, lifting it through
--   `SplitNode Node`, and then composing with the `ℚ`-coercion `+ ⅓` /
--   `- ⅓` — all just to produce a relation that is determined by `lt`
--   and the constructor tag.  No Mathlib lemma fires automatically on
--   such a custom index function.  (b) **Hides the lex structure.**
--   The case-analysis form makes the lex structure immediate: the
--   trichotomy / transitivity / parent-precedence proofs in
--   `splTopologicalOrder` can `cases` on the two constructors and read
--   off the underlying-`lt` clause directly, with no `ℚ`-arithmetic
--   detour.  (c) **Sidesteps the implicit-index-retention subtlety.**
--   The LN-critic surfaced the working-phase subtlety
--   `unsplit_nodes_implicit_index_retention`: the LN's literal text
--   leaves the indices of unsplit nodes implicit.  Encoding `<_{spl}`
--   as case analysis on `SplitNode Node` makes the rule "unsplit nodes
--   compare via the underlying `lt`" *structurally* visible (the first
--   constructor pair below), with no separate `idx : Node → ℕ` axiom
--   needed.  The canonical tex spec records the same case-analysis
--   reading as the only-consistent reading of the LN's prose; this
--   Lean encoding makes that reading literal.
--
-- *`W` does NOT appear in the signature.*  A naive translation of the
--   LN would parameterise `<_{spl}` by `W : Finset Node` (since the
--   construction is *defined* with respect to `W`).  But the
--   lex / case-analysis encoding depends only on `lt` and the
--   constructor tags — the `W`-dependence is *absorbed into the
--   tagged-sum carrier* `SplitNode Node` already (a `copy0 w` is a
--   distinct constructor from `unsplit w` regardless of whether
--   `w ∈ W`, because `SplitNode` is a `def_3_11` `inductive` with
--   three formally-distinct constructors).  Taking `W` as an extra
--   argument would be pure noise: every call site `splOrder lt x y`
--   would pass `W` through but never consume it.  The membership
--   facts that DO depend on `W` (whether a given `SplitNode Node`
--   inhabits `J_{spl(W)} ∪ V_{spl(W)}`) live in the underlying CDMG
--   `G.nodeSplittingOn W hW` and are checked at the use-site of
--   `IsTopologicalOrder`, not inside `splOrder` itself.  Downstream
--   theorems (`splTopologicalOrder`, and any chapter-4 SWIG / chapter-5
--   do-calculus consumer that lifts a topological order through node
--   splitting) quantify `W` at the theorem level and apply
--   `splOrder lt` against the carrier of `G.nodeSplittingOn W hW`
--   directly; threading `W` inside `splOrder` would force every such
--   consumer to project it back out.
--
-- *Lex orientation `copy0 < unsplit < copy1` (for the same base node)
--   is load-bearing — flipping it invalidates sub-claim (b).*  The
--   case analysis below picks `splOrder lt (.copy0 w) (.copy1 w) =
--   lt w w ∨ w = w` (so `.copy0 w < .copy1 w` always) and
--   symmetrically `.copy0 v < .unsplit u < .copy1 u` whenever the base
--   nodes agree.  This is not an arbitrary tie-breaking convention —
--   it is forced by `def_3_11`'s edge-orientation conventions:
--   (i) the transfer edge added in `def_3_11` item iii is
--   `(w^0, w^1)` (NOT `(w^1, w^0)`), so the parent-precedence clause
--   of `def_3_8`'s `IsTopologicalOrder` for `G.nodeSplittingOn W hW`
--   demands `.copy0 w < .copy1 w` in any witness order;
--   (ii) every incoming edge onto `w ∈ W` is reattached at `w^0` and
--   every outgoing edge from `w` leaves `w^1` (`def_3_11` item iii,
--   first set-builder: `(v_1, v_2) ∈ G.E` lifts to
--   `(v_1^1, v_2^0) ∈ E_{spl(W)}`), so an unsplit ancestor `u` of `w`
--   (with `lt u w`) parents `w^0` and similarly `w^1` parents an
--   unsplit descendant `u'` of `w` (with `lt w u'`) — both forcing
--   the same `copy0 < unsplit < copy1` ordering at each base node.
--   Under the opposite tagging convention (transfer edge
--   `(w^1, w^0)`, incoming at `w^1`, outgoing from `w^0`), the
--   symmetric LN index assignment `j ∓ ⅓` to `w^{0/1}` would NOT
--   produce a topological order — `sub-claim (b)` is correct as
--   stated precisely because the index choice matches `def_3_11`'s
--   tagging convention.  This is exactly the LN-critic working-phase
--   subtlety `orientation_convention_v0_below_v1` that the canonical
--   tex spec records in its "Compatibility of the tagging convention"
--   paragraph; the Lean encoding bakes the convention literally into
--   the case analysis (lines below), so any future refactor of
--   `def_3_11`'s tagging convention would force a coordinated
--   refactor of `splOrder`'s case analysis here.
--
-- *`Prop`-valued binary relation `SplitNode Node → SplitNode Node → Prop`,
--   not a `LT (SplitNode Node)` typeclass or a `Decidable` instance.*
--   Mirrors `def_3_8`'s `IsTopologicalOrder` argument shape: that
--   predicate takes `lt : Node → Node → Prop` as an explicit external
--   argument (see `TopologicalOrder.lean`'s "explicit external
--   argument, not a typeclass `[LT Node]`" design block).  We follow
--   the same convention here so `(G.nodeSplittingOn W hW).IsTopologicalOrder (splOrder lt)`
--   reads literally as "the relation `splOrder lt` is a topological
--   order of the split graph".  A `[LT (SplitNode Node)]` instance
--   would force a single canonical order per `SplitNode Node` type,
--   colliding with the LN's parameterisation by *the* topological
--   order `lt` we are lifting.
--
-- *Three-dash `--- helper` markers, not two-dash `-- statement`
--   markers.*  `splOrder` is *helper-for-statement*: the main LN
--   content of the row lives in the two `splAcyclic` and
--   `splTopologicalOrder` theorems below (each getting its own
--   two-dash statement markers), and `splOrder` exists to give
--   `splTopologicalOrder`'s conclusion a clean handle on the
--   explicitly-constructed lifted order.  The website builder pulls
--   helper-marked declarations alongside the main statement so the
--   rendered statement is self-contained.  Matches the convention in
--   `TopologicalOrder.lean`'s `IsTotalOrder` (the helper supporting
--   `IsTopologicalOrder`).
-- claim_3_6 --- start helper
def splOrder (lt : Node → Node → Prop) :
    SplitNode Node → SplitNode Node → Prop
  | .unsplit u, .unsplit v => lt u v
  | .unsplit u, .copy0 w   => lt u w
  | .unsplit u, .copy1 w   => lt u w ∨ u = w
  | .copy0 v,   .unsplit u => lt v u ∨ v = u
  | .copy0 v,   .copy0 w   => lt v w
  | .copy0 v,   .copy1 w   => lt v w ∨ v = w
  | .copy1 v,   .unsplit u => lt v u
  | .copy1 v,   .copy0 w   => lt v w
  | .copy1 v,   .copy1 w   => lt v w
-- claim_3_6 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: splOrder

-- ## Proof-only helpers (private; live above the theorems)
--
-- The lemmas below are infrastructure for the proofs of `splAcyclic`
-- and `splTopologicalOrder`.  They are deliberately private, carry no
-- marker comments, and do not appear in the rendered statement.  See
-- `tex/claim_3_6_proof_SplitTopologicalOrder.tex` for the TeX proof
-- these helpers implement.
--
-- *`baseOf` / `tagOf`.*  Project a `SplitNode Node` onto its underlying
--   base node (`.unsplit u`, `.copy0 w`, `.copy1 w` all carry one node
--   argument) and its copy tag in `{0, 1, 2}` (with the convention
--   `.copy0 ↦ 0 < .unsplit ↦ 1 < .copy1 ↦ 2` so that the lex order
--   matches `splOrder`'s case analysis).
--
-- *`splOrder_iff`.*  The lex characterisation of `splOrder`: equivalent
--   to "base node strictly less, OR base nodes equal and tag strictly
--   less".  Reduces the 27-way case analysis of transitivity (and the
--   9-way analyses of irreflexivity / trichotomy) on the case-analysis
--   form to plain lex reasoning.
--
-- *`splitNode_ext`.*  Two `SplitNode Node` agreeing on base and tag are
--   equal.  Used in the trichotomy proof to recover `x = y` from
--   `baseOf x = baseOf y ∧ tagOf x = tagOf y`.
--
-- *`baseOf_mem`.*  Membership `x ∈ G_spl` projects to membership
--   `baseOf x ∈ G` via the four pieces of the disjoint-union carrier.
--
-- *`splOrder_lifted_edge` / `splOrder_transfer_edge`.*  The two
--   parent-precedence subcases corresponding to `def_3_11`'s two
--   edge-set clauses (lifted edges from `G.E` and transfer edges
--   `(w^0, w^1)`).
--
-- *`aux_splTopologicalOrder`.*  The shared workhorse: the full
--   `IsTopologicalOrder` content for the split graph under
--   `splOrder lt`, used by both `splAcyclic` (which routes through
--   `claim_3_2`) and `splTopologicalOrder` (which is a direct wrapper).
--   The private auxiliary form is needed because `splAcyclic` precedes
--   `splTopologicalOrder` in the file (statement-marker order) but
--   the corollary route from sub-claim (b) to sub-claim (a) requires
--   the topological-order content first.

private def baseOf : SplitNode Node → Node
  | .unsplit u => u
  | .copy0 w => w
  | .copy1 w => w

private def tagOf : SplitNode Node → ℕ
  | .copy0 _ => 0
  | .unsplit _ => 1
  | .copy1 _ => 2

omit [DecidableEq Node] in
private lemma splOrder_iff (lt : Node → Node → Prop) (x y : SplitNode Node) :
    splOrder lt x y ↔
      lt (baseOf x) (baseOf y) ∨ (baseOf x = baseOf y ∧ tagOf x < tagOf y) := by
  cases x <;> cases y <;> simp [splOrder, baseOf, tagOf]

omit [DecidableEq Node] in
private lemma splitNode_ext {x y : SplitNode Node}
    (hbase : baseOf x = baseOf y) (htag : tagOf x = tagOf y) : x = y := by
  cases x <;> cases y <;> simp_all [baseOf, tagOf]

private lemma baseOf_mem {G : CDMG Node} {W : Finset Node} (hW : W ⊆ G.V)
    {x : SplitNode Node} (hx : x ∈ G.nodeSplittingOn W hW) :
    baseOf x ∈ G := by
  change baseOf x ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp hx with hJ | hV
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hJ
    exact Finset.mem_union_left _ hj
  · rcases Finset.mem_union.mp hV with hV12 | hC1
    · rcases Finset.mem_union.mp hV12 with hVuns | hC0
      · obtain ⟨v, hvVW, rfl⟩ := Finset.mem_image.mp hVuns
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hvVW).1
      · obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hC0
        exact Finset.mem_union_right _ (hW hwW)
    · obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hC1
      exact Finset.mem_union_right _ (hW hwW)

private lemma splOrder_lifted_edge {lt : Node → Node → Prop} (W : Finset Node)
    {v1 v2 : Node} (h : lt v1 v2) :
    splOrder lt (toCopy1 W v1) (toCopy0 W v2) := by
  unfold toCopy0 toCopy1
  split_ifs <;> exact h

omit [DecidableEq Node] in
private lemma splOrder_transfer_edge {lt : Node → Node → Prop} {w : Node} :
    splOrder lt (SplitNode.copy0 w) (SplitNode.copy1 w) :=
  Or.inr rfl

private lemma aux_splTopologicalOrder (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.V)
    (lt : Node → Node → Prop) (hlt : G.IsTopologicalOrder lt) :
    (G.nodeSplittingOn W hW).IsTopologicalOrder (splOrder lt) := by
  obtain ⟨⟨h_irrefl, h_trans, h_tri⟩, h_pa⟩ := hlt
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- Irreflexivity
    intro x hx hsplx
    rw [splOrder_iff] at hsplx
    rcases hsplx with hlt_xx | ⟨_, htag⟩
    · exact h_irrefl (baseOf x) (baseOf_mem hW hx) hlt_xx
    · exact Nat.lt_irrefl _ htag
  · -- Transitivity
    intro x hx y hy z hz hxy hyz
    rw [splOrder_iff] at hxy hyz ⊢
    rcases hxy with hlt_xy | ⟨hbase_xy, htag_xy⟩
    · rcases hyz with hlt_yz | ⟨hbase_yz, _⟩
      · left
        exact h_trans (baseOf x) (baseOf_mem hW hx) (baseOf y) (baseOf_mem hW hy)
          (baseOf z) (baseOf_mem hW hz) hlt_xy hlt_yz
      · left; rw [← hbase_yz]; exact hlt_xy
    · rcases hyz with hlt_yz | ⟨hbase_yz, htag_yz⟩
      · left; rw [hbase_xy]; exact hlt_yz
      · right
        exact ⟨hbase_xy.trans hbase_yz, htag_xy.trans htag_yz⟩
  · -- Trichotomy
    intro x hx y hy
    rcases h_tri (baseOf x) (baseOf_mem hW hx) (baseOf y) (baseOf_mem hW hy)
      with hlt_xy | hbase_eq | hlt_yx
    · left; rw [splOrder_iff]; left; exact hlt_xy
    · rcases Nat.lt_trichotomy (tagOf x) (tagOf y) with htag | htag | htag
      · left; rw [splOrder_iff]; right; exact ⟨hbase_eq, htag⟩
      · right; left; exact splitNode_ext hbase_eq htag
      · right; right; rw [splOrder_iff]; right; exact ⟨hbase_eq.symm, htag⟩
    · right; right; rw [splOrder_iff]; left; exact hlt_yx
  · -- Parent precedence
    intro u w h_pa_uw
    obtain ⟨_, h_uw_E⟩ := h_pa_uw
    rcases Finset.mem_union.mp h_uw_E with hLifted | hTransfer
    · -- Lifted edge: (u, w) = (toCopy1 W v1, toCopy0 W v2) for (v1, v2) ∈ G.E
      obtain ⟨⟨v1, v2⟩, he_E, h_eq⟩ := Finset.mem_image.mp hLifted
      simp only [Prod.mk.injEq] at h_eq
      obtain ⟨h_u_eq, h_w_eq⟩ := h_eq
      rw [← h_u_eq, ← h_w_eq]
      have hv1_in_G : v1 ∈ G := (G.hE_subset he_E).1
      have hlt_v1_v2 : lt v1 v2 := h_pa v1 v2 ⟨hv1_in_G, he_E⟩
      exact splOrder_lifted_edge W hlt_v1_v2
    · -- Transfer edge: (u, w) = (.copy0 w', .copy1 w') for w' ∈ W
      obtain ⟨w', _, h_eq⟩ := Finset.mem_image.mp hTransfer
      simp only [Prod.mk.injEq] at h_eq
      obtain ⟨h_u_eq, h_w_eq⟩ := h_eq
      rw [← h_u_eq, ← h_w_eq]
      exact splOrder_transfer_edge

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: splAcyclic
-- ref: claim_3_6 (sub-claim (a), acyclicity preservation)
--
-- For a CADMG `G` and `W ⊆ G.V`, the node-split graph
-- `G.nodeSplittingOn W hW` (`def_3_11`) is acyclic in the sense of
-- `def_3_6`'s `IsAcyclic`.
--
-- *Why this hypothesis is load-bearing.*  Without the CADMG
-- precondition, the construction of `def_3_11` does NOT preserve
-- acyclicity: per the rewritten tex spec's "Role of the CADMG
-- precondition" paragraph, a directed self-loop `(w, w) ∈ G.E` for
-- `w ∈ W` would, under `def_3_11`'s item iii, generate both a lifted
-- edge `(w^1, w^0) ∈ E_{spl(W)}` (from the first set-builder) and the
-- transfer edge `(w^0, w^1) ∈ E_{spl(W)}` (from the second
-- set-builder), realising a length-2 directed cycle
-- `w^0 → w^1 → w^0` in the split graph.  `G.IsCADMG` rules out
-- directed self-loops on `G.V` (via `def_3_6`'s no-directed-self-loop
-- consequence), which is exactly the no-2-cycle precondition this
-- sub-claim needs.
/-
LN tex (sub-claim (a), from the rewritten canonical statement for
`claim_3_6`):

  (a) `G_{spl(W)}` is acyclic.  The CDMG `G_{spl(W)}` is acyclic in
      the sense of def \ref{def-acylic}, i.e.\ for every
      `x ∈ J_{spl(W)} ∪ V_{spl(W)} = J ∪ (V ∖ W) ⊍ W^0 ⊍ W^1`, there
      does not exist any non-trivial directed walk from `x` to itself
      in `G_{spl(W)}`.
-/
-- ## Design choice
--
-- *Single-theorem statement (sub-claim (a) only), separated from
--   sub-claim (b).*  See the shared "one theorem vs.\ two separate
--   theorems" bullet in the `splTopologicalOrder` design block below.
--   Briefly: `splAcyclic` is the standalone acyclicity-preservation
--   fact that downstream consumers like `claim_3_12`
--   HardInterventionNodeSplit are expected to need *on its own*
--   (without dragging in the topological-order construction);
--   keeping it as its own theorem lets those consumers state
--   `G.splAcyclic hCADMG W hW` without ever mentioning `splOrder` or
--   a chosen `lt`.
--
-- *`G.IsCADMG`, not `G.IsAcyclic`.*  See the shared bullet in the
--   `splTopologicalOrder` design block below; the same choice applies
--   here.  LN-faithful naming (`def_3_7` item i) wins over the
--   micro-simplification of inlining the `IsAcyclic` alias.
--
-- *Hypotheses ordered `(G, hCADMG, W, hW)`.*  Mirrors the LN reading
--   "For a CADMG `G` ... and `W ⊆ V`, ..."  `hW` follows `W` because
--   `nodeSplittingOn` takes `(W : Finset Node) (hW : W ⊆ G.V)` in
--   that order, so the application `G.nodeSplittingOn W hW` in the
--   conclusion reads left-to-right with the binder block.
--
-- *Conclusion `(G.nodeSplittingOn W hW).IsAcyclic`, not
--   `IsAcyclic (G.nodeSplittingOn W hW)`.*  Dot-notation matches the
--   chapter convention (`G.IsAcyclic`, `G.IsCADMG`, `G.IsADMG`, …) and
--   reads as "the split graph is acyclic".  Both spellings are
--   syntactically equivalent in Lean; dot-notation is preferred for
--   readability.
--
-- *Downstream consumers.*  `claim_3_12` (HardInterventionNodeSplit)
--   needs the acyclicity of the split graph to compose
--   `nodeSplittingOn` with `hardInterventionOn` in the SWIG
--   construction (a CADMG goes to a CADMG under both operations).
--   `splAcyclic` is the precondition that lets the composition close
--   (every CADMG can be hard-intervened on without losing
--   acyclicity, by `claim_3_3` / `AcyclicPreservedUnderDo.lean`;
--   without `splAcyclic`, the node-split intermediate stage would
--   not be a CADMG and the composition would not be well-typed in
--   the `CADMG → CADMG → CADMG` sense).
-- claim_3_6 -- start statement
theorem splAcyclic (G : CDMG Node) (hCADMG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V) :
    (G.nodeSplittingOn W hW).IsAcyclic
-- claim_3_6 -- end statement
  := by
  have hAcyclic : G.IsAcyclic := hCADMG
  obtain ⟨lt, hlt⟩ := (acyclic_iff_topological_order G).mp hAcyclic
  exact (acyclic_iff_topological_order (G.nodeSplittingOn W hW)).mpr
    ⟨splOrder lt, aux_splTopologicalOrder G W hW lt hlt⟩
-- REFACTOR-BLOCK-ORIGINAL-END: splAcyclic

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: splTopologicalOrder
-- ref: claim_3_6 (sub-claim (b), explicit topological-order construction)
--
-- For a CADMG `G`, a subset `W ⊆ G.V`, and any topological order `lt`
-- of `G` in the sense of `def_3_8`, the lifted relation `splOrder lt`
-- (see the helper block above) is a topological order of the
-- node-split graph `G.nodeSplittingOn W hW`.
--
-- Unfolded, `(G.nodeSplittingOn W hW).IsTopologicalOrder (splOrder lt)`
-- asserts (per `def_3_8`):
--
--   * `splOrder lt` is a strict total order on
--     `J_{spl(W)} ∪ V_{spl(W)}` (irreflexive, transitive,
--     trichotomous; via the nested `IsTotalOrder` projection);
--   * for every parent–child pair `v ∈ (G.nodeSplittingOn W hW).Pa w`,
--     we have `splOrder lt v w`.
--
-- The parent-precedence clause is the load-bearing content of the
-- construction: every edge of `E_{spl(W)}` is one of (i) a lifted edge
-- `(v_1^1, v_2^0)` arising from `(v_1, v_2) ∈ G.E` — where
-- parent-precedence under `splOrder` follows from
-- parent-precedence under `lt` (which `hlt` provides) plus the
-- copy-tag inequality `tag(v_1^1) = +1 ≥ 0 = tag(v_2^0) + ?`
-- (handled by the corresponding mixed-tag case of `splOrder`); or
-- (ii) a transfer edge `(w^0, w^1)` for `w ∈ W` — where
-- parent-precedence under `splOrder` follows from
-- `splOrder lt (.copy0 w) (.copy1 w) = lt w w ∨ w = w = True`.
/-
LN tex (sub-claim (b), from the rewritten canonical statement for
`claim_3_6`):

  (b) An explicit topological order on `G_{spl(W)}` obtained from any
      topological order on `G`.  For every topological order `<` of
      `G` ..., the binary relation `<_{spl}` on
      `J_{spl(W)} ∪ V_{spl(W)}` defined below is a topological order
      of `G_{spl(W)}` in the sense of def \ref{def-topological-order}.

      Index map.  Define `φ : J_{spl(W)} ∪ V_{spl(W)} → ℚ` by case
      analysis on the disjoint-union carrier
      `J ∪ (V ∖ W) ⊍ W^0 ⊍ W^1`: ...
       ... `φ(v_j) := j` for unsplit `v_j ∈ J ∪ (V ∖ W)`;
       ... `φ(w^0) := j - 1/3`, `φ(w^1) := j + 1/3` for `w = v_j ∈ W`.

      Order from index map.  Define
        `x <_{spl} y :⇔ φ(x) < φ(y)`
      for `x, y ∈ J_{spl(W)} ∪ V_{spl(W)}`, where the right-hand
      inequality is the standard strict order on `ℚ`.
-/
-- ## Design choice
--
-- *One theorem vs.\ two separate theorems — picked TWO.*  The LN
--   bundles (a) and (b) inside one `\begin{Rem}`, but the two
--   sub-claims have *different downstream consumers*: `claim_3_12`
--   HardInterventionNodeSplit is expected to need only (a) — the
--   acyclicity of the split graph — to compose `nodeSplittingOn` with
--   `hardInterventionOn` in the SWIG construction.  Bundling (a) and
--   (b) into a single `splAcyclic ∧ splTopologicalOrder`-shaped
--   theorem would force every such consumer to take a topological-
--   order argument it does not use (or to project through `.1` /
--   pattern-match, adding noise at every call site).  Splitting them
--   keeps each statement focused and matches the chapter convention
--   in `def_3_7`'s `IsCADMG`, `IsADMG`, `IsDAG`, … (one
--   atomic-condition predicate per sub-statement).  The LN-faithful
--   reading of "the remark holds" is preserved because both theorems
--   are stated under the same `-- ref: claim_3_6 ...` heading and
--   read as the two sub-claims of one remark.
--
-- *`G.IsCADMG`, not `G.IsAcyclic`.*  The LN reads "For a CADMG `G`",
--   referring explicitly to `def_3_7`'s named attribute.  `IsCADMG`
--   unfolds to `IsAcyclic` (`def_3_7` item i — see
--   `CDMGTypes.lean`), so the two would be interchangeable at the
--   *content* level.  We pick `IsCADMG` to keep the Lean signature
--   LN-faithful (a reader greps `CADMG` from the LN and finds the
--   matching Lean hypothesis without a translation step); the proof
--   body can `unfold CDMG.IsCADMG at hCADMG` if it needs the
--   `IsAcyclic` form for downstream lemma matching.  See
--   `BifurcationAlternative.lean` (claim_3_5) for the precedent —
--   that theorem takes the LN-named hypothesis `hCADMG : G.IsCADMG`
--   via the analogous reading of "a CADMG `G`".
--
-- *`lt` and `hlt` as explicit positional arguments, not bundled into
--   an inner `∀ lt, …` quantifier.*  The LN's "for every topological
--   order `<` of `G`" is universal over `lt`, but encoding it as an
--   *outer* binder on the theorem is equivalent and substantially
--   more ergonomic at the call site: consumers that want to apply
--   `splTopologicalOrder` to a specific `lt` write
--   `G.splTopologicalOrder hCADMG W hW lt hlt` directly, rather than
--   `(G.splTopologicalOrder hCADMG W hW) lt hlt` after destructuring
--   the inner forall.  Logically the two forms agree, so the choice
--   is purely an ergonomic one.  Matches the chapter convention of
--   carrying universal-quantifier inputs as outermost positional
--   arguments (cf.\ `def_3_8`'s `IsTopologicalOrder`'s explicit
--   external `lt` argument and `def_3_9`'s `Pred` taking `lt` and
--   `h : G.IsTotalOrder lt` as explicit arguments — see
--   `TopologicalOrder.lean`).
--
-- *`lt` typed as a bare `Node → Node → Prop`, not as a
--   `[LinearOrder Node]` / `[StrictTotalOrder Node]` / `[LT Node]`
--   typeclass instance.*  The LN's "for any topological order `<` of
--   `G`" universally quantifies over an arbitrary binary relation
--   that *happens* to satisfy `G.IsTopologicalOrder` (`def_3_8`); it
--   does NOT presume `Node` carries a canonical, typeclass-resolved
--   order.  Encoding `lt` as a positional `Node → Node → Prop`
--   argument matches that reading exactly: every well-foundedness /
--   totality / parent-precedence property the proof body needs is
--   carried by the *hypothesis* `hlt : G.IsTopologicalOrder lt`, not
--   by an ambient instance.  A typeclass formulation would have two
--   ergonomic costs: (i) every consumer wanting to apply this theorem
--   would need to manufacture a `LinearOrder Node` instance even when
--   they only have a one-off topological order in hand (e.g. one
--   produced by `claim_3_4`'s `existsTopologicalOrder` witness), and
--   (ii) a global `[LT Node]` instance would lock in a single
--   canonical order per `Node` type, colliding with the LN's
--   parameterisation by *any* topological order.  Matches the
--   chapter convention in `def_3_8`'s `IsTopologicalOrder` (see
--   `TopologicalOrder.lean`'s "explicit external argument, not a
--   typeclass `[LT Node]`" design block), and is the natural
--   counterpart on the input side of the same `Prop`-valued-relation
--   design bullet for the output `splOrder` (see `splOrder`'s design
--   block above).
--
-- *Conclusion `IsTopologicalOrder (splOrder lt)`, not a fresh
--   indexed-order predicate.*  We reuse `def_3_8`'s
--   `IsTopologicalOrder` *verbatim* against the *split* CDMG: every
--   ingredient is already in place because `G.nodeSplittingOn W hW`
--   is a `CDMG (SplitNode Node)` (per `def_3_11`'s return type) and
--   `IsTopologicalOrder` is polymorphic in the node type.  No
--   `IsTopologicalOrderIndexed` / `IsTopologicalOrderOnSplit`
--   variant is introduced.  This is what makes the LN's "is a
--   topological order of `G_{spl(W)}`" formulation transport
--   verbatim onto the Lean side.
--
-- *Hypotheses ordered `(G, hCADMG, W, hW, lt, hlt)`.*  Matches the
--   `splAcyclic` ordering, then adds `(lt, hlt)` at the end (the
--   *additional* hypotheses sub-claim (b) needs over (a)).  This
--   reads as "for any CADMG `G`, any `W ⊆ G.V`, and any topological
--   order `lt` of `G`, ..." — LN order modulo the natural
--   `(W, hW)`-block grouping that downstream consumers expect.
--
-- *`splOrder` (not `splOrder lt W`) in the conclusion.*  See the
--   "`W` does NOT appear in `splOrder`'s signature" bullet in
--   `splOrder`'s design block above.  The `W`-dependence of the
--   split graph lives entirely in `G.nodeSplittingOn W hW`'s
--   underlying carrier (`SplitNode Node`) and edge set
--   (`E_{spl(W)}` parameterised by `W`); `splOrder` itself reads
--   the constructor tag and the underlying `lt`, no `W` needed.
--
-- *Downstream consumers.*  `claim_3_12` (HardInterventionNodeSplit)
--   may consume `splTopologicalOrder` if its proof needs to
--   transport a topological order from `G` to the SWIG composition
--   `(G.nodeSplittingOn W hW).hardInterventionOn W' hW'` via this
--   row's lifted order; more typically, however, that row uses only
--   `splAcyclic` and constructs its own topological order on the
--   composition fresh.  Chapter-5 do-calculus rule-3 proofs may also
--   consume `splTopologicalOrder` to give explicit orderings on SWIG
--   graphs.
-- claim_3_6 -- start statement
theorem splTopologicalOrder (G : CDMG Node) (hCADMG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V)
    (lt : Node → Node → Prop) (hlt : G.IsTopologicalOrder lt) :
    (G.nodeSplittingOn W hW).IsTopologicalOrder (splOrder lt)
-- claim_3_6 -- end statement
  := by
  -- `hCADMG` is carried in the signature for LN-faithfulness (the LN reads
  -- "For a CADMG `G`") but is not consumed in this proof: the
  -- topological-order construction of sub-claim~(b) only uses that the
  -- supplied `lt` *is* a topological order, not acyclicity of `G` directly.
  -- See the design-choice block above for the LN-faithfulness rationale.
  let _ := hCADMG
  exact aux_splTopologicalOrder G W hW lt hlt
-- REFACTOR-BLOCK-ORIGINAL-END: splTopologicalOrder

end CDMG

namespace refactor_CDMG

-- ## Design choice — statement context (refactor twin)
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Both fixtures are
--   inherited from `def_3_1`'s refactor twin (`refactor_CDMG`).  The
--   refactor twin's signature references `refactor_CDMG Node`
--   (root `def_3_1`), `G.refactor_IsCADMG` (`def_3_7` refactor twin),
--   `G.refactor_nodeSplittingOn W hW` (`def_3_11` refactor twin),
--   `(G.refactor_nodeSplittingOn W hW).refactor_IsAcyclic` (`def_3_6`
--   refactor twin), `G.refactor_IsTopologicalOrder lt` (`def_3_8`
--   refactor twin), and
--   `(G.refactor_nodeSplittingOn W hW).refactor_IsTopologicalOrder
--    (refactor_splOrder lt)` (which goes through the split CDMG's
--   `refactor_Pa` from `def_3_5` refactor twin, in turn requiring
--   `[DecidableEq (refactor_SplitNode Node)]` — provided automatically
--   by `def_3_11`'s refactor twin via `deriving DecidableEq` on the
--   tagged-sum inductive `refactor_SplitNode`).  No new typeclasses
--   are needed: the mathematical content of the claim is unchanged by
--   the refactor — the bidirected-edge set `L` plays no role in either
--   sub-claim, so the `Finset (Node × Node) → Finset (Sym2 Node)`
--   retyping at root `def_3_1` does not reach this row at all.
--
-- *Three-dash `--- start helper` marker.*  Same convention as the
--   pre-refactor block above and as every sibling refactor twin in
--   `Section3_1/` and `Section3_2/`.
-- claim_3_6 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_6 --- end helper

-- ## Helper: the LN's `<_{spl}` order on `refactor_SplitNode Node`
--
-- *One-sentence summary.*  A `Prop`-valued binary relation on
-- `refactor_SplitNode Node` realising the LN's lifted topological
-- order `<_{spl}` via 9-way case analysis on the two constructor
-- tags, parameterised by an arbitrary `lt : Node → Node → Prop` on
-- the underlying node type.
--
-- The LN constructs `<_{spl}` via an index map
-- `φ : J_{spl(W)} ∪ V_{spl(W)} → ℚ` that assigns
--
--   * `φ(v_j) := j`         for `v_j ∈ J ∪ (V ∖ W)` (unsplit node
--     retains its original index `j` from the topological order
--     enumeration `v_1 < … < v_n`);
--   * `φ(w^0) := j - 1/3`   for `w = v_j ∈ W`;
--   * `φ(w^1) := j + 1/3`   for `w = v_j ∈ W`;
--
-- and then defines `x <_{spl} y :⇔ φ(x) < φ(y)` via the standard
-- strict order on `ℚ`.  Since the integer indices `j` are distinct
-- for distinct nodes and `1/3 < 1`, the inequality `φ(x) < φ(y)`
-- reduces — case by case on the two constructors — to a comparison
-- involving only `lt` on the underlying nodes plus, in some mixed-tag
-- cases, an equality clause `u = w`.  Morally, the resulting relation
-- is a *lex* order on the pair `(base node, copy tag)` where the copy
-- tag takes the three values `-1` (`copy0`), `0` (`unsplit`), `+1`
-- (`copy1`); the 9 cases below are the literal transcription of that
-- reduction.
--
-- ## Design choice
--
-- *Case-analysis encoding, not `ℚ`-arithmetic.*  Three reasons to
--   skip the `ℚ` device.  (a) **Reuses no Mathlib infrastructure.**
--   The `ℚ`-based encoding would require manually enumerating
--   `J ∪ V = {v_1 < … < v_n}`, constructing a function
--   `idx : Node → ℕ` on the carrier `G.J ∪ G.V`, lifting it through
--   `refactor_SplitNode Node`, and then composing with the
--   `ℚ`-coercion `+ ⅓` / `- ⅓` — all just to produce a relation that
--   is determined by `lt` and the constructor tag.  No Mathlib lemma
--   fires automatically on such a custom index function.  (b) **Hides
--   the lex structure.**  The case-analysis form makes the lex
--   structure immediate: the trichotomy / transitivity /
--   parent-precedence proofs in `refactor_splTopologicalOrder` can
--   `cases` on the two constructors and read off the underlying-`lt`
--   clause directly, with no `ℚ`-arithmetic detour.  (c) **Sidesteps
--   the implicit-index-retention subtlety.**  The LN-critic surfaced
--   the working-phase subtlety `unsplit_nodes_implicit_index_retention`:
--   the LN's literal text leaves the indices of unsplit nodes
--   implicit.  Encoding `<_{spl}` as case analysis on
--   `refactor_SplitNode Node` makes the rule "unsplit nodes compare
--   via the underlying `lt`" *structurally* visible (the first
--   constructor pair below), with no separate `idx : Node → ℕ` axiom
--   needed.  The canonical tex spec records the same case-analysis
--   reading as the only-consistent reading of the LN's prose; this
--   Lean encoding makes that reading literal.
--
-- *`W` does NOT appear in the signature.*  A naive translation of
--   the LN would parameterise `<_{spl}` by `W : Finset Node` (since
--   the construction is *defined* with respect to `W`).  But the
--   lex / case-analysis encoding depends only on `lt` and the
--   constructor tags — the `W`-dependence is *absorbed into the
--   tagged-sum carrier* `refactor_SplitNode Node` already (a
--   `copy0 w` is a distinct constructor from `unsplit w` regardless
--   of whether `w ∈ W`, because `refactor_SplitNode` is a `def_3_11`
--   `inductive` with three formally-distinct constructors).  Taking
--   `W` as an extra argument would be pure noise: every call site
--   `refactor_splOrder lt x y` would pass `W` through but never
--   consume it.  The membership facts that DO depend on `W` (whether
--   a given `refactor_SplitNode Node` inhabits
--   `J_{spl(W)} ∪ V_{spl(W)}`) live in the underlying CDMG
--   `G.refactor_nodeSplittingOn W hW` and are checked at the
--   use-site of `refactor_IsTopologicalOrder`, not inside
--   `refactor_splOrder` itself.  Downstream theorems
--   (`refactor_splTopologicalOrder`, and any chapter-4 SWIG /
--   chapter-5 do-calculus consumer that lifts a topological order
--   through node splitting) quantify `W` at the theorem level and
--   apply `refactor_splOrder lt` against the carrier of
--   `G.refactor_nodeSplittingOn W hW` directly.
--
-- *Lex orientation `copy0 < unsplit < copy1` (for the same base
--   node) is load-bearing — flipping it invalidates sub-claim (b).*
--   The case analysis below picks
--   `refactor_splOrder lt (.copy0 w) (.copy1 w) = lt w w ∨ w = w`
--   (so `.copy0 w < .copy1 w` always) and symmetrically
--   `.copy0 v < .unsplit u < .copy1 u` whenever the base nodes
--   agree.  This is not an arbitrary tie-breaking convention — it is
--   forced by `def_3_11`'s edge-orientation conventions:
--   (i) the transfer edge added in `def_3_11` item iii is
--   `(w^0, w^1)` (NOT `(w^1, w^0)`), so the parent-precedence clause
--   of `def_3_8`'s `refactor_IsTopologicalOrder` for
--   `G.refactor_nodeSplittingOn W hW` demands
--   `.copy0 w < .copy1 w` in any witness order;
--   (ii) every incoming edge onto `w ∈ W` is reattached at `w^0` and
--   every outgoing edge from `w` leaves `w^1` (`def_3_11` item iii,
--   first set-builder: `(v_1, v_2) ∈ G.E` lifts to
--   `(v_1^1, v_2^0) ∈ E_{spl(W)}`), so an unsplit ancestor `u` of `w`
--   (with `lt u w`) parents `w^0` and similarly `w^1` parents an
--   unsplit descendant `u'` of `w` (with `lt w u'`) — both forcing
--   the same `copy0 < unsplit < copy1` ordering at each base node.
--   Under the opposite tagging convention (transfer edge
--   `(w^1, w^0)`, incoming at `w^1`, outgoing from `w^0`), the
--   symmetric LN index assignment `j ∓ ⅓` to `w^{0/1}` would NOT
--   produce a topological order.  This is exactly the LN-critic
--   working-phase subtlety `orientation_convention_v0_below_v1` that
--   the canonical tex spec records; the Lean encoding bakes the
--   convention literally into the case analysis, so any future
--   refactor of `def_3_11`'s tagging convention would force a
--   coordinated refactor here.
--
-- *`Prop`-valued binary relation
--   `refactor_SplitNode Node → refactor_SplitNode Node → Prop`, not
--   a `LT (refactor_SplitNode Node)` typeclass or a `Decidable`
--   instance.*  Mirrors `def_3_8`'s `refactor_IsTopologicalOrder`
--   argument shape: that predicate takes `lt : Node → Node → Prop`
--   as an explicit external argument (see `TopologicalOrder.lean`'s
--   "explicit external argument, not a typeclass `[LT Node]`" design
--   block).  We follow the same convention here so
--   `(G.refactor_nodeSplittingOn W hW).refactor_IsTopologicalOrder
--    (refactor_splOrder lt)` reads literally as "the relation
--   `refactor_splOrder lt` is a topological order of the split
--   graph".  A `[LT (refactor_SplitNode Node)]` instance would force
--   a single canonical order per `refactor_SplitNode Node` type,
--   colliding with the LN's parameterisation by *the* topological
--   order `lt` we are lifting.
--
-- *Three-dash `--- helper` markers, not two-dash `-- statement`
--   markers.*  `refactor_splOrder` is *helper-for-statement*: the
--   main LN content of the row lives in the two `refactor_splAcyclic`
--   and `refactor_splTopologicalOrder` theorems below (each getting
--   its own two-dash statement markers), and `refactor_splOrder`
--   exists to give `refactor_splTopologicalOrder`'s conclusion a
--   clean handle on the explicitly-constructed lifted order.  The
--   website builder pulls helper-marked declarations alongside the
--   main statement so the rendered statement is self-contained.
--   Matches the convention in `TopologicalOrder.lean`'s
--   `refactor_IsTotalOrder` (the helper supporting
--   `refactor_IsTopologicalOrder`).
--
-- *Independent of the bidirected-edge channel `L`.*  This helper
--   reads only the constructor tag of `refactor_SplitNode Node` and
--   the underlying `lt` on `Node`; it never inspects the `L` field
--   of any CDMG.  Both sub-claims of `claim_3_6` are
--   `(J, V, E)`-skeleton claims (acyclicity via directed walks on
--   `E`; topological order via `refactor_Pa` defined from `E` alone),
--   and `refactor_splOrder` reflects this in its signature.  See
--   `def_3_1`'s docstring on `refactor_CDMG` for the canonical
--   `L`-channel design (typed as `Finset (Sym2 Node)` with
--   `Sym2.IsDiag`-style irreflexivity) — none of that detail reaches
--   this helper or the two theorems it supports.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: splOrder (was: refactor_splOrder)
-- claim_3_6 --- start helper
def refactor_splOrder (lt : Node → Node → Prop) :
    refactor_SplitNode Node → refactor_SplitNode Node → Prop
  | .unsplit u, .unsplit v => lt u v
  | .unsplit u, .copy0 w   => lt u w
  | .unsplit u, .copy1 w   => lt u w ∨ u = w
  | .copy0 v,   .unsplit u => lt v u ∨ v = u
  | .copy0 v,   .copy0 w   => lt v w
  | .copy0 v,   .copy1 w   => lt v w ∨ v = w
  | .copy1 v,   .unsplit u => lt v u
  | .copy1 v,   .copy0 w   => lt v w
  | .copy1 v,   .copy1 w   => lt v w
-- claim_3_6 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: splOrder

-- ## Proof-only helpers (private; live above the theorems)
--
-- The lemmas below are infrastructure for the proofs of
-- `refactor_splAcyclic` and `refactor_splTopologicalOrder`.  They are
-- deliberately private, carry no helper marker comments, and do not
-- appear in the rendered statement.  Each is wrapped in its own
-- REPLACEMENT marker pair so the Phase 7 cleanup script renames
-- `refactor_<name>` → `<name>` across the codebase.

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: baseOf (was: refactor_baseOf)
private def refactor_baseOf : refactor_SplitNode Node → Node
  | .unsplit u => u
  | .copy0 w => w
  | .copy1 w => w
-- REFACTOR-BLOCK-REPLACEMENT-END: baseOf

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: tagOf (was: refactor_tagOf)
private def refactor_tagOf : refactor_SplitNode Node → ℕ
  | .copy0 _ => 0
  | .unsplit _ => 1
  | .copy1 _ => 2
-- REFACTOR-BLOCK-REPLACEMENT-END: tagOf

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: splOrder_iff (was: refactor_splOrder_iff)
omit [DecidableEq Node] in
private lemma refactor_splOrder_iff (lt : Node → Node → Prop)
    (x y : refactor_SplitNode Node) :
    refactor_splOrder lt x y ↔
      lt (refactor_baseOf x) (refactor_baseOf y) ∨
        (refactor_baseOf x = refactor_baseOf y ∧
          refactor_tagOf x < refactor_tagOf y) := by
  cases x <;> cases y <;> simp [refactor_splOrder, refactor_baseOf, refactor_tagOf]
-- REFACTOR-BLOCK-REPLACEMENT-END: splOrder_iff

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: splitNode_ext (was: refactor_splitNode_ext)
omit [DecidableEq Node] in
private lemma refactor_splitNode_ext {x y : refactor_SplitNode Node}
    (hbase : refactor_baseOf x = refactor_baseOf y)
    (htag : refactor_tagOf x = refactor_tagOf y) : x = y := by
  cases x <;> cases y <;> simp_all [refactor_baseOf, refactor_tagOf]
-- REFACTOR-BLOCK-REPLACEMENT-END: splitNode_ext

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: baseOf_mem (was: refactor_baseOf_mem)
private lemma refactor_baseOf_mem {G : refactor_CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.V) {x : refactor_SplitNode Node}
    (hx : x ∈ G.refactor_nodeSplittingOn W hW) :
    refactor_baseOf x ∈ G := by
  change refactor_baseOf x ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp hx with hJ | hV
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hJ
    exact Finset.mem_union_left _ hj
  · rcases Finset.mem_union.mp hV with hV12 | hC1
    · rcases Finset.mem_union.mp hV12 with hVuns | hC0
      · obtain ⟨v, hvVW, rfl⟩ := Finset.mem_image.mp hVuns
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hvVW).1
      · obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hC0
        exact Finset.mem_union_right _ (hW hwW)
    · obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hC1
      exact Finset.mem_union_right _ (hW hwW)
-- REFACTOR-BLOCK-REPLACEMENT-END: baseOf_mem

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: splOrder_lifted_edge (was: refactor_splOrder_lifted_edge)
private lemma refactor_splOrder_lifted_edge {lt : Node → Node → Prop}
    (W : Finset Node) {v1 v2 : Node} (h : lt v1 v2) :
    refactor_splOrder lt (refactor_toCopy1 W v1) (refactor_toCopy0 W v2) := by
  unfold refactor_toCopy0 refactor_toCopy1
  split_ifs <;> exact h
-- REFACTOR-BLOCK-REPLACEMENT-END: splOrder_lifted_edge

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: splOrder_transfer_edge (was: refactor_splOrder_transfer_edge)
omit [DecidableEq Node] in
private lemma refactor_splOrder_transfer_edge {lt : Node → Node → Prop} {w : Node} :
    refactor_splOrder lt (refactor_SplitNode.copy0 w) (refactor_SplitNode.copy1 w) :=
  Or.inr rfl
-- REFACTOR-BLOCK-REPLACEMENT-END: splOrder_transfer_edge

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: aux_splTopologicalOrder (was: refactor_aux_splTopologicalOrder)
private lemma refactor_aux_splTopologicalOrder (G : refactor_CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.V)
    (lt : Node → Node → Prop) (hlt : G.refactor_IsTopologicalOrder lt) :
    (G.refactor_nodeSplittingOn W hW).refactor_IsTopologicalOrder
      (refactor_splOrder lt) := by
  obtain ⟨⟨h_irrefl, h_trans, h_tri⟩, h_pa⟩ := hlt
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- Irreflexivity
    intro x hx hsplx
    rw [refactor_splOrder_iff] at hsplx
    rcases hsplx with hlt_xx | ⟨_, htag⟩
    · exact h_irrefl (refactor_baseOf x) (refactor_baseOf_mem hW hx) hlt_xx
    · exact Nat.lt_irrefl _ htag
  · -- Transitivity
    intro x hx y hy z hz hxy hyz
    rw [refactor_splOrder_iff] at hxy hyz ⊢
    rcases hxy with hlt_xy | ⟨hbase_xy, htag_xy⟩
    · rcases hyz with hlt_yz | ⟨hbase_yz, _⟩
      · left
        exact h_trans (refactor_baseOf x) (refactor_baseOf_mem hW hx)
          (refactor_baseOf y) (refactor_baseOf_mem hW hy)
          (refactor_baseOf z) (refactor_baseOf_mem hW hz) hlt_xy hlt_yz
      · left; rw [← hbase_yz]; exact hlt_xy
    · rcases hyz with hlt_yz | ⟨hbase_yz, htag_yz⟩
      · left; rw [hbase_xy]; exact hlt_yz
      · right
        exact ⟨hbase_xy.trans hbase_yz, htag_xy.trans htag_yz⟩
  · -- Trichotomy
    intro x hx y hy
    rcases h_tri (refactor_baseOf x) (refactor_baseOf_mem hW hx)
      (refactor_baseOf y) (refactor_baseOf_mem hW hy)
      with hlt_xy | hbase_eq | hlt_yx
    · left; rw [refactor_splOrder_iff]; left; exact hlt_xy
    · rcases Nat.lt_trichotomy (refactor_tagOf x) (refactor_tagOf y)
        with htag | htag | htag
      · left; rw [refactor_splOrder_iff]; right; exact ⟨hbase_eq, htag⟩
      · right; left; exact refactor_splitNode_ext hbase_eq htag
      · right; right; rw [refactor_splOrder_iff]; right
        exact ⟨hbase_eq.symm, htag⟩
    · right; right; rw [refactor_splOrder_iff]; left; exact hlt_yx
  · -- Parent precedence
    intro u w h_pa_uw
    obtain ⟨_, h_uw_E⟩ := h_pa_uw
    rcases Finset.mem_union.mp h_uw_E with hLifted | hTransfer
    · -- Lifted edge: (u, w) = (refactor_toCopy1 W v1, refactor_toCopy0 W v2)
      -- for (v1, v2) ∈ G.E
      obtain ⟨⟨v1, v2⟩, he_E, h_eq⟩ := Finset.mem_image.mp hLifted
      simp only [Prod.mk.injEq] at h_eq
      obtain ⟨h_u_eq, h_w_eq⟩ := h_eq
      rw [← h_u_eq, ← h_w_eq]
      have hv1_in_G : v1 ∈ G := (G.hE_subset he_E).1
      have hlt_v1_v2 : lt v1 v2 := h_pa v1 v2 ⟨hv1_in_G, he_E⟩
      exact refactor_splOrder_lifted_edge W hlt_v1_v2
    · -- Transfer edge: (u, w) = (.copy0 w', .copy1 w') for w' ∈ W
      obtain ⟨w', _, h_eq⟩ := Finset.mem_image.mp hTransfer
      simp only [Prod.mk.injEq] at h_eq
      obtain ⟨h_u_eq, h_w_eq⟩ := h_eq
      rw [← h_u_eq, ← h_w_eq]
      exact refactor_splOrder_transfer_edge
-- REFACTOR-BLOCK-REPLACEMENT-END: aux_splTopologicalOrder

-- ref: claim_3_6 (sub-claim (a), acyclicity preservation)
--
-- For a CADMG `G` and `W ⊆ G.V`, the node-split graph
-- `G.refactor_nodeSplittingOn W hW` (`def_3_11`) is acyclic in the
-- sense of `def_3_6`'s `refactor_IsAcyclic`.
--
-- *Why the `refactor_IsCADMG` hypothesis is load-bearing.*  Without
-- the CADMG precondition, the construction of `def_3_11` does NOT
-- preserve acyclicity: per the rewritten tex spec's "Role of the
-- CADMG precondition" paragraph, a directed self-loop
-- `(w, w) ∈ G.E` for `w ∈ W` would, under `def_3_11`'s item iii,
-- generate both a lifted edge `(w^1, w^0) ∈ E_{spl(W)}` (from the
-- first set-builder) and the transfer edge
-- `(w^0, w^1) ∈ E_{spl(W)}` (from the second set-builder), realising
-- a length-2 directed cycle `w^0 → w^1 → w^0` in the split graph.
-- `G.refactor_IsCADMG` rules out directed self-loops on `G.V` (via
-- `def_3_6`'s no-directed-self-loop consequence), which is exactly
-- the no-2-cycle precondition this sub-claim needs.
/-
LN tex (sub-claim (a), from the rewritten canonical statement for
`claim_3_6`):

  (a) `G_{spl(W)}` is acyclic.  The CDMG `G_{spl(W)}` is acyclic in
      the sense of def \ref{def-acylic}, i.e.\ for every
      `x ∈ J_{spl(W)} ∪ V_{spl(W)} = J ∪ (V ∖ W) ⊍ W^0 ⊍ W^1`, there
      does not exist any non-trivial directed walk from `x` to itself
      in `G_{spl(W)}`.
-/
-- ## Design choice
--
-- *Single-theorem statement (sub-claim (a) only), separated from
--   sub-claim (b).*  See the shared "one theorem vs.\ two separate
--   theorems" bullet in the `refactor_splTopologicalOrder` design
--   block below.  Briefly: `refactor_splAcyclic` is the standalone
--   acyclicity-preservation fact that downstream consumers like
--   `claim_3_12` HardInterventionNodeSplit are expected to need *on
--   its own* (without dragging in the topological-order
--   construction); keeping it as its own theorem lets those
--   consumers state `G.refactor_splAcyclic hCADMG W hW` without
--   ever mentioning `refactor_splOrder` or a chosen `lt`.
--
-- *`refactor_IsCADMG`, not `refactor_IsAcyclic`.*  See the shared
--   bullet in the `refactor_splTopologicalOrder` design block below;
--   the same choice applies here.  LN-faithful naming (`def_3_7`
--   item i) wins over the micro-simplification of inlining the
--   `refactor_IsAcyclic` alias — the LN reads "For a CADMG `G`",
--   referring explicitly to `def_3_7`'s named attribute, so a reader
--   who greps `CADMG` from the LN finds the matching Lean hypothesis
--   without a translation step.  At the proof level, `refactor_IsCADMG`
--   unfolds to `refactor_IsAcyclic` (`def_3_7` item i), so any proof
--   step that needs the acyclicity form can `unfold
--   refactor_CDMG.refactor_IsCADMG at hCADMG`.
--
-- *Hypotheses ordered `(G, hCADMG, W, hW)`.*  Mirrors the LN reading
--   "For a CADMG `G` ... and `W ⊆ V`, ..."  `hW` follows `W` because
--   `refactor_nodeSplittingOn` takes `(W : Finset Node) (hW : W ⊆ G.V)`
--   in that order, so the application `G.refactor_nodeSplittingOn W hW`
--   in the conclusion reads left-to-right with the binder block.
--
-- *Conclusion `(G.refactor_nodeSplittingOn W hW).refactor_IsAcyclic`,
--   not `refactor_IsAcyclic (G.refactor_nodeSplittingOn W hW)`.*
--   Dot-notation matches the chapter convention (`G.refactor_IsAcyclic`,
--   `G.refactor_IsCADMG`, `G.refactor_IsADMG`, …) and reads as "the
--   split graph is acyclic".  Both spellings are syntactically
--   equivalent in Lean; dot-notation is preferred for readability.
--
-- *Downstream consumers.*  `claim_3_12` (HardInterventionNodeSplit)
--   needs the acyclicity of the split graph to compose
--   `refactor_nodeSplittingOn` with `refactor_hardInterventionOn` in
--   the SWIG construction (a CADMG goes to a CADMG under both
--   operations).  `refactor_splAcyclic` is the precondition that
--   lets the composition close (every CADMG can be hard-intervened
--   on without losing acyclicity, by `claim_3_3` /
--   `AcyclicPreservedUnderDo.lean`; without `refactor_splAcyclic`,
--   the node-split intermediate stage would not be a CADMG and the
--   composition would not be well-typed in the
--   `CADMG → CADMG → CADMG` sense).
--
-- *Independent of the bidirected-edge channel `L`.*  None of
--   `refactor_IsCADMG`, `refactor_nodeSplittingOn`,
--   `refactor_IsAcyclic` consumes the `L` field of the underlying
--   CDMG record at the level of *this* statement: acyclicity is a
--   property of directed walks on the `E`-side alone.  The CDMG
--   record itself carries an `L`-channel (see `def_3_1`'s docstring
--   on `refactor_CDMG` for the `Finset (Sym2 Node)` encoding), and
--   `refactor_nodeSplittingOn` populates the split graph's
--   `L`-channel via `Sym2.map (refactor_toCopy0 W)`, but acyclicity
--   of the result reads only the new `E`-side.  Sub-claim (a) is
--   therefore robust under any future change to the `L`-channel
--   encoding.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: splAcyclic (was: refactor_splAcyclic)
-- claim_3_6 -- start statement
theorem refactor_splAcyclic (G : refactor_CDMG Node) (hCADMG : G.refactor_IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V) :
    (G.refactor_nodeSplittingOn W hW).refactor_IsAcyclic
-- claim_3_6 -- end statement
  := by
  have hAcyclic : G.refactor_IsAcyclic := hCADMG
  obtain ⟨lt, hlt⟩ := (refactor_acyclic_iff_topological_order G).mp hAcyclic
  exact (refactor_acyclic_iff_topological_order
      (G.refactor_nodeSplittingOn W hW)).mpr
    ⟨refactor_splOrder lt, refactor_aux_splTopologicalOrder G W hW lt hlt⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: splAcyclic

-- ref: claim_3_6 (sub-claim (b), explicit topological-order construction)
--
-- For a CADMG `G`, a subset `W ⊆ G.V`, and any topological order
-- `lt` of `G` in the sense of `def_3_8`, the lifted relation
-- `refactor_splOrder lt` (see the helper block above) is a
-- topological order of the node-split graph
-- `G.refactor_nodeSplittingOn W hW`.
--
-- Unfolded,
-- `(G.refactor_nodeSplittingOn W hW).refactor_IsTopologicalOrder
--  (refactor_splOrder lt)` asserts (per `def_3_8`):
--
--   * `refactor_splOrder lt` is a strict total order on
--     `J_{spl(W)} ∪ V_{spl(W)}` (irreflexive, transitive,
--     trichotomous; via the nested `refactor_IsTotalOrder`
--     projection);
--   * for every parent–child pair
--     `v ∈ (G.refactor_nodeSplittingOn W hW).refactor_Pa w`,
--     we have `refactor_splOrder lt v w`.
--
-- The parent-precedence clause is the load-bearing content of the
-- construction: every edge of `E_{spl(W)}` is one of (i) a lifted
-- edge `(v_1^1, v_2^0)` arising from `(v_1, v_2) ∈ G.E` — where
-- parent-precedence under `refactor_splOrder` follows from
-- parent-precedence under `lt` (which `hlt` provides) plus the
-- copy-tag inequality, handled by the corresponding mixed-tag case
-- of `refactor_splOrder`; or (ii) a transfer edge `(w^0, w^1)` for
-- `w ∈ W` — where parent-precedence under `refactor_splOrder`
-- follows from
-- `refactor_splOrder lt (.copy0 w) (.copy1 w) = lt w w ∨ w = w =
--  True`.
/-
LN tex (sub-claim (b), from the rewritten canonical statement for
`claim_3_6`):

  (b) An explicit topological order on `G_{spl(W)}` obtained from any
      topological order on `G`.  For every topological order `<` of
      `G` ..., the binary relation `<_{spl}` on
      `J_{spl(W)} ∪ V_{spl(W)}` defined below is a topological order
      of `G_{spl(W)}` in the sense of def \ref{def-topological-order}.

      Index map.  Define `φ : J_{spl(W)} ∪ V_{spl(W)} → ℚ` by case
      analysis on the disjoint-union carrier
      `J ∪ (V ∖ W) ⊍ W^0 ⊍ W^1`: ...
       ... `φ(v_j) := j` for unsplit `v_j ∈ J ∪ (V ∖ W)`;
       ... `φ(w^0) := j - 1/3`, `φ(w^1) := j + 1/3` for `w = v_j ∈ W`.

      Order from index map.  Define
        `x <_{spl} y :⇔ φ(x) < φ(y)`
      for `x, y ∈ J_{spl(W)} ∪ V_{spl(W)}`, where the right-hand
      inequality is the standard strict order on `ℚ`.
-/
-- ## Design choice
--
-- *One theorem vs.\ two separate theorems — picked TWO.*  The LN
--   bundles (a) and (b) inside one `\begin{Rem}`, but the two
--   sub-claims have *different downstream consumers*: `claim_3_12`
--   HardInterventionNodeSplit is expected to need only (a) — the
--   acyclicity of the split graph — to compose
--   `refactor_nodeSplittingOn` with `refactor_hardInterventionOn`
--   in the SWIG construction.  Bundling (a) and (b) into a single
--   `refactor_splAcyclic ∧ refactor_splTopologicalOrder`-shaped
--   theorem would force every such consumer to take a topological-
--   order argument it does not use (or to project through `.1` /
--   pattern-match, adding noise at every call site).  Splitting
--   them keeps each statement focused and matches the chapter
--   convention in `def_3_7`'s `refactor_IsCADMG`, `refactor_IsADMG`,
--   `refactor_IsDAG`, … (one atomic-condition predicate per
--   sub-statement).  The LN-faithful reading of "the remark holds"
--   is preserved because both theorems are stated under the same
--   `claim_3_6` ref and read as the two sub-claims of one remark.
--
-- *`refactor_IsCADMG`, not `refactor_IsAcyclic`.*  The LN reads
--   "For a CADMG `G`", referring explicitly to `def_3_7`'s named
--   attribute.  `refactor_IsCADMG` unfolds to `refactor_IsAcyclic`
--   (`def_3_7` item i — see `CDMGTypes.lean`), so the two would be
--   interchangeable at the *content* level.  We pick
--   `refactor_IsCADMG` to keep the Lean signature LN-faithful (a
--   reader greps `CADMG` from the LN and finds the matching Lean
--   hypothesis without a translation step); the proof body can
--   `unfold refactor_CDMG.refactor_IsCADMG at hCADMG` if it needs
--   the `refactor_IsAcyclic` form for downstream lemma matching.
--   See `BifurcationAlternative.lean` (claim_3_5) for the
--   precedent — that theorem takes the LN-named hypothesis
--   `hCADMG : G.refactor_IsCADMG` via the analogous reading of "a
--   CADMG `G`".
--
-- *`lt` and `hlt` as explicit positional arguments, not bundled
--   into an inner `∀ lt, …` quantifier.*  The LN's "for every
--   topological order `<` of `G`" is universal over `lt`, but
--   encoding it as an *outer* binder on the theorem is equivalent
--   and substantially more ergonomic at the call site: consumers
--   that want to apply `refactor_splTopologicalOrder` to a specific
--   `lt` write
--   `G.refactor_splTopologicalOrder hCADMG W hW lt hlt` directly,
--   rather than
--   `(G.refactor_splTopologicalOrder hCADMG W hW) lt hlt` after
--   destructuring the inner forall.  Logically the two forms agree,
--   so the choice is purely an ergonomic one.  Matches the chapter
--   convention of carrying universal-quantifier inputs as
--   outermost positional arguments (cf.\ `def_3_8`'s
--   `refactor_IsTopologicalOrder`'s explicit external `lt` argument
--   and `def_3_9`'s `refactor_Pred` taking `lt` and
--   `h : G.refactor_IsTotalOrder lt` as explicit arguments — see
--   `TopologicalOrder.lean`).
--
-- *`lt` typed as a bare `Node → Node → Prop`, not as a
--   `[LinearOrder Node]` / `[StrictTotalOrder Node]` / `[LT Node]`
--   typeclass instance.*  The LN's "for any topological order `<`
--   of `G`" universally quantifies over an arbitrary binary
--   relation that *happens* to satisfy `G.refactor_IsTopologicalOrder`
--   (`def_3_8`); it does NOT presume `Node` carries a canonical,
--   typeclass-resolved order.  Encoding `lt` as a positional
--   `Node → Node → Prop` argument matches that reading exactly:
--   every well-foundedness / totality / parent-precedence property
--   the proof body needs is carried by the *hypothesis*
--   `hlt : G.refactor_IsTopologicalOrder lt`, not by an ambient
--   instance.  A typeclass formulation would have two ergonomic
--   costs: (i) every consumer wanting to apply this theorem would
--   need to manufacture a `LinearOrder Node` instance even when
--   they only have a one-off topological order in hand (e.g. one
--   produced by `claim_3_4`'s `refactor_existsTopologicalOrder`
--   witness), and (ii) a global `[LT Node]` instance would lock in
--   a single canonical order per `Node` type, colliding with the
--   LN's parameterisation by *any* topological order.  Matches the
--   chapter convention in `def_3_8`'s `refactor_IsTopologicalOrder`
--   (see `TopologicalOrder.lean`'s "explicit external argument, not
--   a typeclass `[LT Node]`" design block), and is the natural
--   counterpart on the input side of the same
--   `Prop`-valued-relation design bullet for the output
--   `refactor_splOrder` (see `refactor_splOrder`'s design block
--   above).
--
-- *Conclusion `refactor_IsTopologicalOrder (refactor_splOrder lt)`,
--   not a fresh indexed-order predicate.*  We reuse `def_3_8`'s
--   `refactor_IsTopologicalOrder` *verbatim* against the *split*
--   CDMG: every ingredient is already in place because
--   `G.refactor_nodeSplittingOn W hW` is a
--   `refactor_CDMG (refactor_SplitNode Node)` (per `def_3_11`'s
--   return type) and `refactor_IsTopologicalOrder` is polymorphic in
--   the node type.  No
--   `refactor_IsTopologicalOrderIndexed` /
--   `refactor_IsTopologicalOrderOnSplit` variant is introduced.
--   This is what makes the LN's "is a topological order of
--   `G_{spl(W)}`" formulation transport verbatim onto the Lean side.
--
-- *Hypotheses ordered `(G, hCADMG, W, hW, lt, hlt)`.*  Matches the
--   `refactor_splAcyclic` ordering, then adds `(lt, hlt)` at the
--   end (the *additional* hypotheses sub-claim (b) needs over (a)).
--   This reads as "for any CADMG `G`, any `W ⊆ G.V`, and any
--   topological order `lt` of `G`, ..." — LN order modulo the
--   natural `(W, hW)`-block grouping that downstream consumers
--   expect.
--
-- *`refactor_splOrder` (not `refactor_splOrder lt W`) in the
--   conclusion.*  See the "`W` does NOT appear in
--   `refactor_splOrder`'s signature" bullet in `refactor_splOrder`'s
--   design block above.  The `W`-dependence of the split graph
--   lives entirely in `G.refactor_nodeSplittingOn W hW`'s underlying
--   carrier (`refactor_SplitNode Node`) and edge set
--   (`E_{spl(W)}` parameterised by `W`); `refactor_splOrder` itself
--   reads the constructor tag and the underlying `lt`, no `W`
--   needed.
--
-- *Downstream consumers.*  `claim_3_12` (HardInterventionNodeSplit)
--   may consume `refactor_splTopologicalOrder` if its proof needs to
--   transport a topological order from `G` to the SWIG composition
--   `(G.refactor_nodeSplittingOn W hW).refactor_hardInterventionOn
--    W' hW'` via this row's lifted order; more typically, however,
--   that row uses only `refactor_splAcyclic` and constructs its own
--   topological order on the composition fresh.  Chapter-5
--   do-calculus rule-3 proofs may also consume
--   `refactor_splTopologicalOrder` to give explicit orderings on
--   SWIG graphs.
--
-- *Independent of the bidirected-edge channel `L`.*
--   `refactor_IsTopologicalOrder` only inspects
--   `refactor_IsTotalOrder` (totality conditions on `J ∪ V`) and
--   `refactor_Pa` (parent set from `G.E` alone) — both
--   `(J, V, E)`-skeleton facts.  `refactor_splOrder` reads only the
--   constructor tag of `refactor_SplitNode` and the underlying
--   `lt`, so it likewise does not touch `L`.  See `def_3_1`'s
--   docstring on `refactor_CDMG` for the canonical `L`-channel
--   design; none of that detail reaches this theorem.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: splTopologicalOrder (was: refactor_splTopologicalOrder)
-- claim_3_6 -- start statement
theorem refactor_splTopologicalOrder (G : refactor_CDMG Node) (hCADMG : G.refactor_IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V)
    (lt : Node → Node → Prop) (hlt : G.refactor_IsTopologicalOrder lt) :
    (G.refactor_nodeSplittingOn W hW).refactor_IsTopologicalOrder (refactor_splOrder lt)
-- claim_3_6 -- end statement
  := by
  -- `hCADMG` is carried in the signature for LN-faithfulness (the LN reads
  -- "For a CADMG `G`") but is not consumed in this proof: the
  -- topological-order construction of sub-claim~(b) only uses that the
  -- supplied `lt` *is* a topological order, not acyclicity of `G` directly.
  -- See the design-choice block above for the LN-faithfulness rationale.
  let _ := hCADMG
  exact refactor_aux_splTopologicalOrder G W hW lt hlt
-- REFACTOR-BLOCK-REPLACEMENT-END: splTopologicalOrder

end refactor_CDMG

end Causality
