import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.CDMGTypes
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_1.AcyclicIffTopologicalOrder
import Chapter3_GraphTheory.Section3_2.ExtendingCDMGsWith

namespace Causality

/-!
# Acyclicity and topological orders under intervention-node extension
(`claim_3_13`)

This file formalises the LN remark `claim_3_13`
(`AcyclicHardInterventionTopologicalOrder` in `graphs.tex`,
section 3.2):

> If a CDMG `G = (J, V, E, L)` is acyclic then also `G_{\doit(I_W)}`
> is acyclic and a topological order for `G_{\doit(I_W)}` is also one
> for `G`.  Any topological order of `G` can be extended to one for
> `G_{\doit(I_W)}`, e.g.\ by putting all the `I_w` nodes first in the
> ordering.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_13_statement_AcyclicHardInterventionTopologicalOrder.tex`,
verified equivalent to the LN block by `verify_tex_statement_only`
and `verify_tex_statement_equivalence`.  `addition_to_the_LN` is
empty — the LN block plus the rewritten tex is the full spec.  The
rewrite folded four LN-critic working-phase subtleties into the
canonical tex as structural resolutions:

* `all_I_w_first_clashes_with_J_cap_W_nonempty` — the LN's
  "all `I_w` first" phrasing is ambiguous when `W ∩ J ≠ ∅`,
  because `def_3_13` carries the notational convention
  `I_j := j` for `j ∈ J ∩ W`.  Resolved at the type level by
  `def_3_13`'s `IntExtNode`: `.intCopy` is constructed only for
  `w ∈ W \ G.J`, so the natural Lean reading "all `.intCopy`
  precede all `.unsplit`" applies *only* to fresh intervention
  nodes; the `J ∩ W` nodes stay as `.unsplit j` and retain their
  original `<_G` position.
* `extend_meaning_unspecified` — what "extend" means is left
  implicit by the LN.  Adopted the strict reading: the extension
  `≺` on `IntExtNode Node`, restricted along `.unsplit`, equals
  the original `<_G` on `Node`.  Encoded in the file via the
  `restrictOrder` / `extOrder` helpers below.
* `top_order_node_set_mismatch` — the LN's "is also one for `G`"
  reads loosely because the carriers differ.  Resolved at the type
  level by the carrier change `Node` → `IntExtNode Node`: the two
  `IsTopologicalOrder` predicates are literally different relations,
  and the translation is made explicit via `restrictOrder` (for the
  restriction direction, sub-claim (b)) and `extOrder` (for the
  extension direction, sub-claim (c)).
* `order_among_I_w_unspecified` — the LN leaves the relative order
  among the fresh `I_w` unspecified.  Free design choice: in
  `extOrder`, the `(.intCopy w₁, .intCopy w₂)` case is `lt w₁ w₂`,
  reusing the underlying `lt`'s well-foundedness / trichotomy on
  the target nodes `w₁, w₂ ∈ W \ G.J ⊆ G.V ⊆ J ∪ V`.

The remark bundles three sub-claims under one `\begin{Rem}`:

* (a) **Acyclicity preservation.**  `G.extendingCDMGsWith W hW`
  is acyclic (`def_3_6`'s `IsAcyclic`) whenever `G` is.
* (b) **Restriction direction.**  Any topological order on
  `G.extendingCDMGsWith W hW` (carrier `IntExtNode Node`)
  restricts via `restrictOrder` to a topological order on `G`
  (carrier `Node`).
* (c) **Extension direction.**  Any topological order on `G`
  extends via `extOrder` to a topological order on
  `G.extendingCDMGsWith W hW`.

The three sub-claims are stated as **three separate theorems**
(`extAcyclic`, `extRestrictsTopologicalOrder`,
`extExtendsTopologicalOrder`), mirroring the
`splAcyclic` / `splTopologicalOrder` split in
`SplitTopologicalOrder.lean` and the
`swigAcyclic` / `swigTopologicalOrder` split in `SwigAcyclic.lean`
(both of which face the same carrier change via tagged-sum
inductive).  Acyclicity of `G` is *only* required for sub-claim (a);
sub-claims (b) and (c) work for an arbitrary CDMG.

The proof bodies are filled in by `prove_claim_in_lean` (Manager B),
following the verified TeX proof at
`tex/claim_3_13_proof_AcyclicHardInterventionTopologicalOrder.tex`
(to be written).
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  Both fixtures are load-bearing for this
--   row's statement because the signatures reference `CDMG Node`
--   (`def_3_1`), `G.IsAcyclic` (`def_3_6`),
--   `G.extendingCDMGsWith W hW` (`def_3_13`) producing a
--   `CDMG (IntExtNode Node)`, `G.IsTopologicalOrder lt` (`def_3_8`),
--   and `(G.extendingCDMGsWith W hW).IsTopologicalOrder lt'` —
--   which goes through the extended CDMG's
--   `Pa : IntExtNode Node → Set (IntExtNode Node)` from `def_3_5`, in
--   turn requiring `[DecidableEq (IntExtNode Node)]` (provided
--   automatically by `def_3_13`'s `deriving DecidableEq` on the
--   tagged-sum inductive).  Stronger instances (`Fintype`,
--   `LinearOrder`) are not needed at the statement level.
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  Matches the convention in every sibling
--   file in `Section3_2/` (`HardInterventionOn.lean`,
--   `AcyclicPreservedUnderDo.lean`, `SplitTopologicalOrder.lean`,
--   `SwigAcyclic.lean`, `ExtendingCDMGsWith.lean`).  The two-dash
--   marker is reserved for declarations whose body is the formalised
--   LN content of the row; this `variable` line is statement-typing
--   infrastructure binding the implicit `Node` type and its
--   `DecidableEq` instance that the two helpers and all three main
--   theorems' signatures reference.
-- claim_3_13 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_13 --- end helper

-- ## Helper: the LN's "all `I_w` first" extension order on
-- `IntExtNode Node`
--
-- One-sentence summary: `extOrder lt` lifts a strict relation
-- `lt : Node → Node → Prop` on the original carrier `Node` to a
-- strict relation `extOrder lt : IntExtNode Node → IntExtNode Node →
-- Prop` on the extended carrier, by case analysis on the two
-- `IntExtNode` constructors: every `.intCopy w` precedes every
-- `.unsplit v`, and within each tag class the order delegates to
-- `lt` on the underlying base nodes.
--
-- *Case analysis (literal LN translation).*  The four cases
--   correspond exactly to the four cases of the rewritten canonical
--   tex's "Example construction" formula:
--     · `(.intCopy w₁, .intCopy w₂)  ↦  lt w₁ w₂`
--       (the LN's `I_{w_1} ≺ I_{w_2} :⇔ w_1 <_G w_2` clause; uses
--       that `w₁, w₂ ∈ W \ G.J ⊆ G.V ⊆ J ∪ V`, so `lt` is defined
--       on both targets);
--     · `(.intCopy _, .unsplit _)    ↦  True`
--       (the LN's "all fresh `I_w` precede all elements of `J ∪ V`");
--     · `(.unsplit _, .intCopy _)    ↦  False`
--       (the contrapositive of the above);
--     · `(.unsplit u₁, .unsplit u₂)  ↦  lt u₁ u₂`
--       (the LN's "among the elements of `J ∪ V`, `≺` is `<_G`
--       itself" — load-bearing for the strict-extension property
--       below).
/-
LN tex fragment (rewritten canonical statement,
"Example construction (the LN's `put all $I_w$ first`)"):

  A concrete witness `≺` for the existential of sub-claim (c) is
  the following "fresh intervention nodes first" relation: for
  `x, y ∈ J_{doit(I_W)} ∪ V_{doit(I_W)} = (J ∪ V) ⊍ {I_w | w ∈ W ∖ J}`,
    `x ≺ y :⇔`
      · `w_1 <_G w_2`  if `x = I_{w_1}`, `y = I_{w_2}`,
                        `w_1, w_2 ∈ W ∖ J`;
      · `true`         if `x = I_w` for some `w ∈ W ∖ J` and
                        `y ∈ J ∪ V`;
      · `false`        if `x ∈ J ∪ V` and `y = I_w` for some
                        `w ∈ W ∖ J`;
      · `v_1 <_G v_2`  if `x = v_1`, `y = v_2`, `v_1, v_2 ∈ J ∪ V`.
-/
-- ## Design choice
--
-- *Case-analysis encoding, not the LN's `ℚ`-arithmetic detour.*
--   Same paradigm as `splOrder` in `SplitTopologicalOrder.lean` and
--   reused in `SwigAcyclic.lean`: the lex-on-tag-then-base structure
--   is made *structurally visible* on the constructor, so the proof
--   side (Manager B) can `cases` on the two constructors and read
--   off the `lt` clauses directly, with no rational-arithmetic
--   detour.  The four-case table is the literal transcription of the
--   LN's piecewise rule above.
--
-- *Subtlety-1 resolution (`all_I_w_first_clashes_with_J_cap_W_nonempty`).*
--   The LN-critic worried that "put all `I_w` first" reshuffles the
--   `J ∩ W` nodes when read literally, because `def_3_13` defines
--   `I_W = (J ∩ W) ∪ {I_w | w ∈ W \ J}` with the convention
--   `I_j := j`.  This file *cannot* exhibit that pathology: every
--   `intCopy`-image in `def_3_13`'s `extendingCDMGsWith` ranges over
--   `W \ G.J` (never `W`), so no `.intCopy j` is ever constructed
--   for `j ∈ G.J ∩ W`.  Concretely, `extOrder lt`'s "all `.intCopy`
--   precede all `.unsplit`" applies *only* to fresh intervention
--   nodes (`w ∈ W \ G.J`); the `j ∈ G.J ∩ W` cases stay as
--   `.unsplit j` and retain their original `lt`-position.  The
--   restriction along `.unsplit` (cf. `restrictOrder` below) is
--   therefore `lt` verbatim, which is exactly the LN's intended
--   "strict extension" reading.
--
-- *Subtlety-4 resolution (`order_among_I_w_unspecified`) — design
--   freedom.*  The LN does not pin down the relative order *among*
--   the fresh `I_w` nodes (and could not: the fresh nodes are
--   pairwise non-adjacent in `G_{\doit(I_W)}`, so any total order on
--   `{I_w | w ∈ W \ G.J}` respects parent-precedence).  We choose
--   the `lt w₁ w₂` ordering on `(.intCopy w₁, .intCopy w₂)` because
--   it (i) reuses `lt`'s well-foundedness / trichotomy on
--   `w₁, w₂ ∈ W \ G.J ⊆ G.V` for free in the proof of
--   `extExtendsTopologicalOrder`, and (ii) avoids inventing an
--   arbitrary enumeration of `W \ G.J`.  Any other strict total
--   order on the fresh nodes would equally well discharge the
--   topological-order requirement; this is the cheapest one.
--
-- *Lex orientation `.intCopy < .unsplit` (matching the LN's
--   "fresh intervention nodes first").*  Forced by the
--   parent-precedence clause: every fresh edge of `def_3_13` item iii
--   is `(.intCopy w, .unsplit w)` for `w ∈ W \ G.J`, so any
--   topological order on the extension must satisfy
--   `extOrder lt (.intCopy w) (.unsplit w)` — which the second case
--   of the definition (`True`) discharges by construction.  Reversing
--   the orientation would break the parent-precedence proof at the
--   fresh-edge sub-case.
--
-- *`W` does NOT appear in `extOrder`'s signature.*  Same rationale
--   as `splOrder` in `SplitTopologicalOrder.lean`: the `W`-dependence
--   is absorbed into the tagged-sum carrier `IntExtNode Node` (a
--   `.intCopy w` is a formally distinct constructor from
--   `.unsplit w` regardless of whether `w ∈ W \ G.J`); the
--   membership facts that *do* depend on `W` are checked at the
--   use-site of `IsTopologicalOrder` against
--   `G.extendingCDMGsWith W hW`, not inside `extOrder` itself.
--
-- *`Prop`-valued binary relation, not a `LT (IntExtNode Node)`
--   typeclass.*  Mirrors `def_3_8`'s `IsTopologicalOrder` argument
--   shape — `lt` is an explicit external argument the LN universally
--   quantifies over.  A typeclass `[LT (IntExtNode Node)]` would
--   force exactly one canonical order per `IntExtNode Node` type,
--   colliding with the LN's parameterisation by *the* topological
--   order `lt` we are lifting.
--
-- *Three-dash `--- helper` markers (not the two-dash `-- statement`
--   markers).*  Litmus test: removing `extOrder` would cause
--   `extExtendsTopologicalOrder`'s conclusion type to fail to
--   compile, so the helper must travel alongside the main statement
--   in the rendered surface.  Matches the `splOrder` /
--   `restrictOrder` precedents.
-- claim_3_13 --- start helper
def extOrder (lt : Node → Node → Prop) :
    IntExtNode Node → IntExtNode Node → Prop
  | .intCopy w1, .intCopy w2 => lt w1 w2
  | .intCopy _,  .unsplit _  => True
  | .unsplit _,  .intCopy _  => False
  | .unsplit u1, .unsplit u2 => lt u1 u2
-- claim_3_13 --- end helper

-- ## Helper: the canonical restriction of a relation on
-- `IntExtNode Node` to `Node` along `.unsplit`
--
-- One-sentence summary: `restrictOrder lt'` pulls a strict relation
-- `lt' : IntExtNode Node → IntExtNode Node → Prop` back through the
-- canonical inclusion `Node ↪ IntExtNode Node` (the `.unsplit`
-- constructor), producing a strict relation on the original `Node`
-- carrier.
/-
LN tex fragment (rewritten canonical statement, sub-claim (b)
"Restriction direction"):

  For every strict total order `≺` on
  `J_{doit(I_W)} ∪ V_{doit(I_W)}`, if `≺` is a topological order of
  `G_{doit(I_W)}`, then the binary relation `<_G` on `J ∪ V` defined
  by
    `v_1 <_G v_2  :⇔  ι(v_1) ≺ ι(v_2)`     for `v_1, v_2 ∈ J ∪ V`
  is a topological order of `G`.
-/
-- ## Design choice
--
-- *Realisation of the LN's `ι : J ∪ V ↪ J_{doit(I_W)} ∪ V_{doit(I_W)}`.*
--   The canonical tex's `ι` is the set-theoretic inclusion
--   `v ↦ v`; in the Lean encoding (`def_3_13`'s tagged-sum carrier),
--   the inclusion is realised constructor-wise as `.unsplit`.  The
--   restriction `restrictOrder lt' v1 v2 := lt' (.unsplit v1)
--   (.unsplit v2)` is therefore the literal Lean rendering of the
--   LN's `ι(v_1) ≺ ι(v_2)`.
--
-- *Subtlety-2 resolution (`extend_meaning_unspecified`) — strict
--   reading.*  We adopt the standard mathematical reading of "extend
--   a strict total order": the extension `≺` on the larger carrier,
--   restricted to the smaller carrier, equals the original `<_G`.
--   `restrictOrder` is the restriction operation; sub-claim (b)
--   says this restriction is again a topological order, and
--   sub-claim (c) says any `<_G` arises this way from some `≺`
--   (with the witness `≺ := extOrder <_G` satisfying
--   `restrictOrder (extOrder <_G) = <_G` on the nose by case 4 of
--   `extOrder`).
--
-- *Subtlety-3 resolution (`top_order_node_set_mismatch`) — type
--   level.*  The LN's loose "is also one for `G`" prose is made
--   precise by the type-level distinction:
--   `(G.extendingCDMGsWith W hW).IsTopologicalOrder` lives on
--   `IntExtNode Node → IntExtNode Node → Prop`, while
--   `G.IsTopologicalOrder` lives on `Node → Node → Prop`.  The two
--   are different relation types entirely; `restrictOrder` is the
--   bridge from the former to the latter.
--
-- *Definition body is a `fun`, not a `match`.*  No case analysis is
--   needed — every restricted pair lives in the `(.unsplit,
--   .unsplit)` slot.  A one-line lambda is the most direct
--   transcription.
--
-- *`Prop`-valued, not a typeclass.*  Same rationale as `extOrder` —
--   the LN universally quantifies over `lt'`, so a typeclass would
--   force exactly one canonical order per `IntExtNode Node`,
--   colliding with the LN's existential quantification over `<_G`.
--
-- *Three-dash `--- helper` markers.*  Litmus test: removing
--   `restrictOrder` would cause `extRestrictsTopologicalOrder`'s
--   conclusion type to fail to compile, so the helper must travel
--   alongside the main statement in the rendered surface.  Matches
--   the `extOrder` / `splOrder` precedents.
-- claim_3_13 --- start helper
def restrictOrder (lt' : IntExtNode Node → IntExtNode Node → Prop) :
    Node → Node → Prop :=
  fun v1 v2 => lt' (.unsplit v1) (.unsplit v2)
-- claim_3_13 --- end helper

-- ## Proof-only helpers (private; live above the theorems)
--
-- The lemmas below are infrastructure for the proofs of `extAcyclic`,
-- `extRestrictsTopologicalOrder`, and `extExtendsTopologicalOrder`.
-- They are deliberately private, carry no marker comments, and do not
-- appear in the rendered statement.  Mirrors the analogous block in
-- `SwigAcyclic.lean` / `SplitTopologicalOrder.lean`; differences from
-- those precedents flow from `IntExtNode`'s two-constructor shape
-- (vs `SplitNode`'s three) and from `extOrder`'s lex orientation with
-- *tag* as the primary key (`.intCopy ↦ 0 < .unsplit ↦ 1`) — encoding
-- the LN's "fresh intervention nodes first" semantics — rather than
-- splOrder's lex with *base* as primary key.

private def baseOf : IntExtNode Node → Node
  | .unsplit u => u
  | .intCopy w => w

private def tagOf : IntExtNode Node → ℕ
  | .intCopy _ => 0
  | .unsplit _ => 1

omit [DecidableEq Node] in
private lemma extOrder_iff (lt : Node → Node → Prop) (x y : IntExtNode Node) :
    extOrder lt x y ↔
      tagOf x < tagOf y ∨ (tagOf x = tagOf y ∧ lt (baseOf x) (baseOf y)) := by
  cases x <;> cases y <;> simp [extOrder, baseOf, tagOf]

omit [DecidableEq Node] in
private lemma intExtNode_ext {x y : IntExtNode Node}
    (hbase : baseOf x = baseOf y) (htag : tagOf x = tagOf y) : x = y := by
  cases x <;> cases y <;> simp_all [baseOf, tagOf]

private lemma baseOf_mem_ext {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {x : IntExtNode Node} (hx : x ∈ G.extendingCDMGsWith W hW) :
    baseOf x ∈ G := by
  change baseOf x ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp hx with hJ | hV
  · -- `x ∈ J' = G.J.image .unsplit ∪ (W \ G.J).image .intCopy`
    rcases Finset.mem_union.mp hJ with hJuns | hIC
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hJuns
      exact Finset.mem_union_left _ hj
    · obtain ⟨w, hwWJ, rfl⟩ := Finset.mem_image.mp hIC
      obtain ⟨hwW, hwNJ⟩ := Finset.mem_sdiff.mp hwWJ
      rcases Finset.mem_union.mp (hW hwW) with hwJ | hwV
      · exact absurd hwJ hwNJ
      · exact Finset.mem_union_right _ hwV
  · -- `x ∈ V' = G.V.image .unsplit`
    obtain ⟨v, hvV, rfl⟩ := Finset.mem_image.mp hV
    exact Finset.mem_union_right _ hvV

private lemma unsplit_mem_ext {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {v : Node} (hv : v ∈ G) :
    IntExtNode.unsplit v ∈ G.extendingCDMGsWith W hW := by
  change IntExtNode.unsplit v ∈
    (G.extendingCDMGsWith W hW).J ∪ (G.extendingCDMGsWith W hW).V
  rcases Finset.mem_union.mp hv with hJ | hV
  · refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · refine Finset.mem_union_right _ ?_
    exact Finset.mem_image.mpr ⟨v, hV, rfl⟩

omit [DecidableEq Node] in
private lemma extOrder_lifted_edge {lt : Node → Node → Prop}
    {v1 v2 : Node} (h : lt v1 v2) :
    extOrder lt (IntExtNode.unsplit v1) (IntExtNode.unsplit v2) :=
  h

omit [DecidableEq Node] in
private lemma extOrder_intCopy_edge {lt : Node → Node → Prop} {w : Node} :
    extOrder lt (IntExtNode.intCopy w) (IntExtNode.unsplit w) :=
  trivial

private lemma aux_extTopologicalOrder (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.J ∪ G.V)
    (lt : Node → Node → Prop) (hlt : G.IsTopologicalOrder lt) :
    (G.extendingCDMGsWith W hW).IsTopologicalOrder (extOrder lt) := by
  obtain ⟨⟨h_irrefl, h_trans, h_tri⟩, h_pa⟩ := hlt
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- Irreflexivity
    intro x hx hextx
    rw [extOrder_iff] at hextx
    rcases hextx with htag | ⟨_, hlt_xx⟩
    · exact Nat.lt_irrefl _ htag
    · exact h_irrefl (baseOf x) (baseOf_mem_ext (hW := hW) hx) hlt_xx
  · -- Transitivity
    intro x hx y hy z hz hxy hyz
    rw [extOrder_iff] at hxy hyz ⊢
    rcases hxy with htag_xy | ⟨htag_eq_xy, hlt_xy⟩
    · rcases hyz with htag_yz | ⟨htag_eq_yz, _⟩
      · left; exact htag_xy.trans htag_yz
      · left; rw [← htag_eq_yz]; exact htag_xy
    · rcases hyz with htag_yz | ⟨htag_eq_yz, hlt_yz⟩
      · left; rw [htag_eq_xy]; exact htag_yz
      · right
        refine ⟨htag_eq_xy.trans htag_eq_yz, ?_⟩
        exact h_trans (baseOf x) (baseOf_mem_ext (hW := hW) hx)
          (baseOf y) (baseOf_mem_ext (hW := hW) hy)
          (baseOf z) (baseOf_mem_ext (hW := hW) hz) hlt_xy hlt_yz
  · -- Trichotomy
    intro x hx y hy
    rcases Nat.lt_trichotomy (tagOf x) (tagOf y) with htag | htag | htag
    · left; rw [extOrder_iff]; left; exact htag
    · rcases h_tri (baseOf x) (baseOf_mem_ext (hW := hW) hx)
        (baseOf y) (baseOf_mem_ext (hW := hW) hy)
        with hlt_xy | hbase_eq | hlt_yx
      · left; rw [extOrder_iff]; right; exact ⟨htag, hlt_xy⟩
      · right; left; exact intExtNode_ext hbase_eq htag
      · right; right; rw [extOrder_iff]; right; exact ⟨htag.symm, hlt_yx⟩
    · right; right; rw [extOrder_iff]; left; exact htag
  · -- Parent precedence — two cases on `def_3_13`'s two edge-set-builders.
    intro u w h_pa_uw
    obtain ⟨_, h_uw_E⟩ := h_pa_uw
    rcases Finset.mem_union.mp h_uw_E with hLifted | hFresh
    · -- Lifted edge: (u, w) = (.unsplit v1, .unsplit v2) for (v1, v2) ∈ G.E
      obtain ⟨⟨v1, v2⟩, he_E, h_eq⟩ := Finset.mem_image.mp hLifted
      simp only [Prod.mk.injEq] at h_eq
      obtain ⟨h_u_eq, h_w_eq⟩ := h_eq
      rw [← h_u_eq, ← h_w_eq]
      have hv1_in_G : v1 ∈ G := (G.hE_subset he_E).1
      have hlt_v1_v2 : lt v1 v2 := h_pa v1 v2 ⟨hv1_in_G, he_E⟩
      exact extOrder_lifted_edge hlt_v1_v2
    · -- Fresh intervention edge: (u, w) = (.intCopy w', .unsplit w'),
      -- w' ∈ W \ G.J; case 2 of `extOrder` is `True` by construction.
      obtain ⟨w', _, h_eq⟩ := Finset.mem_image.mp hFresh
      simp only [Prod.mk.injEq] at h_eq
      obtain ⟨h_u_eq, h_w_eq⟩ := h_eq
      rw [← h_u_eq, ← h_w_eq]
      exact extOrder_intCopy_edge

-- ref: claim_3_13 (sub-claim (a), acyclicity preservation)
--
-- For a CDMG `G`, a subset `W ⊆ G.J ∪ G.V`, and the assumption that
-- `G` is acyclic (`def_3_6`), the extended CDMG
-- `G.extendingCDMGsWith W hW` (`def_3_13`) is itself acyclic.
--
-- *Why acyclicity of `G` is load-bearing here, but not for (b)/(c).*
-- The `(.intCopy w, .unsplit w)` edges added by `def_3_13` item iii
-- have a fresh source `.intCopy w` with no incoming edges (by the
-- freshness clause), so they cannot themselves participate in a
-- cycle.  All other edges of the extension are lifts of `G.E` along
-- `.unsplit`, which form a cycle iff their preimage in `G.E` does.
-- Hence acyclicity of the extension reduces to acyclicity of `G` —
-- the load-bearing hypothesis is precisely `G.IsAcyclic`.
/-
LN tex (sub-claim (a), from the rewritten canonical statement):

  (a) Acyclicity is preserved by adding intervention nodes.  If `G`
      is acyclic in the sense of def \ref{def-acylic}, then
      `G_{\doit(I_W)}` is acyclic in the sense of
      def \ref{def-acylic}, i.e.\ for every
      `x ∈ J_{\doit(I_W)} ∪ V_{\doit(I_W)} = (J ∪ V)
        ⊍ {I_w | w ∈ W \ J}`,
      there does not exist any non-trivial directed walk from `x` to
      itself in `G_{\doit(I_W)}`.
-/
-- ## Design choice
--
-- *Single-theorem statement (sub-claim (a) only), separated from
--   (b) and (c).*  See the shared "three theorems vs.\ one
--   conjunction" bullet on `extExtendsTopologicalOrder` below; the
--   carrier change `Node → IntExtNode Node` plus the
--   different-hypothesis split (only (a) needs `hAcyclic`) forces
--   the same shape that `claim_3_6` (`SplitTopologicalOrder`) and
--   `claim_3_9` (`SwigAcyclic`) use.  Downstream consumers (ch.\ 4
--   CBN factorisation on the extended graph; ch.\ 5 do-calculus
--   identification arguments) typically need (a) on its own to lift
--   the extension's `CDMG (IntExtNode Node)` return type to an
--   `IsCADMG` graph and invoke chapter-4 / 5 results — keeping (a)
--   as its own theorem lets those consumers state
--   `G.extAcyclic W hW hAcyc` without ever mentioning `extOrder` /
--   `restrictOrder` / a chosen `lt`.
--
-- *`G.IsAcyclic`, not `G.IsCADMG`.*  Departs from `swigAcyclic`'s
--   `hCADMG` choice because `def_3_13`'s `extendingCDMGsWith` does
--   *not* require `IsCADMG` in its signature (unlike `def_3_12`'s
--   `nodeSplittingHard`, which does).  Threading `IsCADMG` here
--   would be over-committed: the LN reads "If a CDMG `G` is acyclic
--   then `G_{\doit(I_W)}` is acyclic", with no `IsCADMG` involved.
--   Consumers that have `IsCADMG` in hand can pass its acyclicity
--   projection.
--
-- *Hypotheses ordered `(G, W, hW, hAcyc)`.*  Matches `def_3_13`
--   `extendingCDMGsWith`'s binder ordering `(G, W, hW)` and appends
--   the acyclicity hypothesis at the end.  Mirrors the
--   `swigAcyclic` / `splAcyclic` convention.
--
-- *`W : Finset Node`, not `Set Node`.*  Matches `def_3_13`'s
--   signature exactly — see the `W : Finset Node` design block in
--   `ExtendingCDMGsWith.lean`.
--
-- *Conclusion via dot-notation `(G.extendingCDMGsWith W hW).IsAcyclic`.*
--   Chapter convention; reads as "the extension is acyclic".
--
-- *Downstream consumers.*  ch.\ 5 do-calculus and ch.\ 8+ iSCM
--   intervention algebra rely on the extension being a CADMG; the
--   `IsAcyclic` witness this theorem produces is the precondition
--   for that lift.
-- claim_3_13 -- start statement
theorem extAcyclic (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.J ∪ G.V)
    (hAcyc : G.IsAcyclic) :
    (G.extendingCDMGsWith W hW).IsAcyclic
-- claim_3_13 -- end statement
  := by
  -- TeX proof: tex/claim_3_13_proof_AcyclicHardInterventionTopologicalOrder.tex
  -- Corollary derivation from sub-claim (c) via `claim_3_2`'s
  -- `acyclic_iff_topological_order`: extract a topological order of `G`
  -- via `(claim_3_2).mp`, lift to one of the extension via
  -- `aux_extTopologicalOrder`, conclude via `(claim_3_2).mpr`.  Mirrors
  -- `swigAcyclic`'s structure in `SwigAcyclic.lean`.
  obtain ⟨lt, hlt⟩ := (acyclic_iff_topological_order G).mp hAcyc
  exact (acyclic_iff_topological_order (G.extendingCDMGsWith W hW)).mpr
    ⟨extOrder lt, aux_extTopologicalOrder G W hW lt hlt⟩

-- ref: claim_3_13 (sub-claim (b), restriction direction)
--
-- For a CDMG `G`, a subset `W ⊆ G.J ∪ G.V`, and a topological order
-- `lt'` on the extension `G.extendingCDMGsWith W hW` (carrier
-- `IntExtNode Node`), the restricted relation `restrictOrder lt'`
-- on `Node` (defined above by pulling `lt'` back through `.unsplit`)
-- is a topological order on the original CDMG `G`.
--
-- Unfolded, the conclusion asserts:
--   * `restrictOrder lt'` is a strict total order on `J ∪ V`
--     (irreflexive, transitive, trichotomous; via the nested
--     `IsTotalOrder` projection);
--   * for every parent-child pair `v ∈ G.Pa w`, we have
--     `restrictOrder lt' v w`, i.e.
--     `lt' (.unsplit v) (.unsplit w)`.
--
-- *No `hAcyclic` hypothesis.*  Sub-claim (b) does not require
-- acyclicity of `G` — the proof needs only the membership lift
-- `v ∈ G → .unsplit v ∈ G.extendingCDMGsWith W hW` and the edge
-- lift `(v1, v2) ∈ G.E → (.unsplit v1, .unsplit v2) ∈
-- E_{ext}`, both of which are pure carrier-shape facts.
/-
LN tex (sub-claim (b), from the rewritten canonical statement):

  (b) Restriction direction: every topological order of
      `G_{\doit(I_W)}` restricts to one of `G` along `ι`.  For every
      strict total order `≺` on `J_{\doit(I_W)} ∪ V_{\doit(I_W)}`,
      if `≺` is a topological order of `G_{\doit(I_W)}` ..., then
      the binary relation `<_G` on `J ∪ V` defined by
        `v_1 <_G v_2  :⇔  ι(v_1) ≺ ι(v_2)`
      for `v_1, v_2 ∈ J ∪ V` is a topological order of `G`.
-/
-- ## Design choice
--
-- *Separate theorem from (a) and (c).*  See the shared "three
--   theorems vs.\ one conjunction" bullet on
--   `extExtendsTopologicalOrder` below.  The carrier change forces
--   different statement shapes for (b) and (c) — (b) takes an
--   `lt'` on `IntExtNode Node`, (c) takes an `lt` on `Node` — so
--   bundling them into one theorem would force a destructured
--   product type at every use site.
--
-- *No `hAcyclic` hypothesis.*  Acyclicity of `G` is unnecessary
--   for the restriction direction — the parent-precedence /
--   total-order properties transport pointwise via `.unsplit`'s
--   constructor injectivity.  Mirrors `claim_3_3` sub-claim (b)'s
--   structure (`AcyclicPreservedUnderDo.lean`): topological-order
--   preservation does *not* require the hypothesis of acyclicity
--   on `G`.  Minimalist signatures over LN-faithful bundling: the
--   LN reads the three sub-claims together under one acyclicity
--   antecedent ("If `G` is acyclic then ..."), but the
--   parent-precedence and order-restriction arguments are
--   structurally independent of the acyclicity premise.  Consumers
--   that have `hAcyclic` in scope can simply discard it.
--
-- *Hypotheses ordered `(G, W, hW, lt', hlt')`.*  Matches the
--   `extAcyclic` ordering on the shared prefix `(G, W, hW)` and
--   appends `(lt', hlt')` — the *additional* hypotheses sub-claim
--   (b) needs over the bare CDMG signature.  Mirrors
--   `swigTopologicalOrder`'s binder ordering after the carrier-
--   change pattern.
--
-- *`lt'` typed as a bare relation, not via a typeclass.*  Same
--   rationale as `def_3_8`'s `IsTopologicalOrder` — the universal
--   quantification over `lt'` is exposed at the binder level, not
--   resolved silently.
--
-- *Universal quantification over `lt'` lives as an outermost
--   positional binder, not an inner `∀ lt', ...`.*  Same
--   convention as `swigTopologicalOrder` / `splTopologicalOrder`;
--   ergonomic at the call site (`G.extRestrictsTopologicalOrder W
--   hW lt' hlt'` reads left-to-right).
--
-- *Conclusion via `G.IsTopologicalOrder (restrictOrder lt')`.*
--   The `restrictOrder` helper carries the carrier translation
--   `IntExtNode Node → Node` (via the `.unsplit` constructor),
--   making the LN's "the binary relation `<_G` on `J ∪ V` defined
--   by `ι(v_1) ≺ ι(v_2)`" literal at the type level.
--
-- *Downstream consumers.*  ch.\ 5 do-calculus identification
--   arguments that move from a topological order on the extension
--   back to a topological order on the original CDMG (e.g.\ to
--   align factorisation indices between the pre- and
--   post-intervention factorisations) consume this theorem.
-- claim_3_13 -- start statement
theorem extRestrictsTopologicalOrder (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V)
    (lt' : IntExtNode Node → IntExtNode Node → Prop)
    (hlt' : (G.extendingCDMGsWith W hW).IsTopologicalOrder lt') :
    G.IsTopologicalOrder (restrictOrder lt')
-- claim_3_13 -- end statement
  := by
  -- TeX proof: tex/claim_3_13_proof_AcyclicHardInterventionTopologicalOrder.tex
  -- Verify each of the four `IsTopologicalOrder` clauses for
  -- `restrictOrder lt'` on `G` by pulling the corresponding clause for
  -- `lt'` on the extension back through `.unsplit` via
  -- `unsplit_mem_ext` (membership lift) and the lifted-edge clause of
  -- `def_3_13` item iii (parent-precedence lift).
  obtain ⟨⟨h_irrefl', h_trans', h_tri'⟩, h_pa'⟩ := hlt'
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- Irreflexivity
    intro v hv hlt_vv
    exact h_irrefl' (.unsplit v) (unsplit_mem_ext (hW := hW) hv) hlt_vv
  · -- Transitivity
    intro u hu v hv w hw huv hvw
    exact h_trans' (.unsplit u) (unsplit_mem_ext (hW := hW) hu)
      (.unsplit v) (unsplit_mem_ext (hW := hW) hv)
      (.unsplit w) (unsplit_mem_ext (hW := hW) hw) huv hvw
  · -- Trichotomy
    intro v hv w hw
    rcases h_tri' (.unsplit v) (unsplit_mem_ext (hW := hW) hv)
        (.unsplit w) (unsplit_mem_ext (hW := hW) hw)
      with hlt | heq | hlt
    · left; exact hlt
    · right; left; exact IntExtNode.unsplit.inj heq
    · right; right; exact hlt
  · -- Parent precedence
    intro v w h_pa_vw
    obtain ⟨hv_mem, hvw_E⟩ := h_pa_vw
    refine h_pa' (.unsplit v) (.unsplit w) ⟨unsplit_mem_ext (hW := hW) hv_mem, ?_⟩
    -- goal: (.unsplit v, .unsplit w) ∈ (extension).E
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨(v, w), hvw_E, rfl⟩

-- ref: claim_3_13 (sub-claim (c), extension direction)
--
-- For a CDMG `G`, a subset `W ⊆ G.J ∪ G.V`, and a topological
-- order `lt` on `G` (carrier `Node`), the lifted relation
-- `extOrder lt` on `IntExtNode Node` (defined above by the
-- "all fresh `I_w` first" lex case analysis) is a topological order
-- on the extension `G.extendingCDMGsWith W hW`.
--
-- Unfolded, the conclusion asserts:
--   * `extOrder lt` is a strict total order on
--     `J_{\doit(I_W)} ∪ V_{\doit(I_W)}` (irreflexive, transitive,
--     trichotomous; via the nested `IsTotalOrder` projection);
--   * for every parent-child pair
--     `v ∈ (G.extendingCDMGsWith W hW).Pa w`, we have
--     `extOrder lt v w`.
--
-- The parent-precedence clause splits into two sub-cases on
-- `def_3_13`'s two edge-set-builders: (i) lifted edges
-- `(.unsplit v1, .unsplit v2)` for `(v1, v2) ∈ G.E`, discharged by
-- `lt`'s own parent-precedence and the fourth case of `extOrder`;
-- (ii) fresh edges `(.intCopy w, .unsplit w)` for `w ∈ W \ G.J`,
-- discharged by the second case of `extOrder` (which is `True` by
-- construction).
--
-- *Strict-extension property is built in by construction.*  By
-- the fourth case of `extOrder`, `extOrder lt (.unsplit v1)
-- (.unsplit v2) = lt v1 v2`, so the restriction of `extOrder lt`
-- along `.unsplit` (= `restrictOrder (extOrder lt)`) equals `lt`
-- verbatim.  This discharges the LN's strict reading of "extend":
-- the conclusion `(G.extendingCDMGsWith W hW).IsTopologicalOrder
-- (extOrder lt)` together with the definitional equality
-- `restrictOrder (extOrder lt) = lt` say that `extOrder lt` is a
-- topological order on the extension whose restriction (via `ι`)
-- is the original `lt`.
/-
LN tex (sub-claim (c), from the rewritten canonical statement):

  (c) Extension direction: every topological order of `G` extends
      to one of `G_{\doit(I_W)}`.  For every strict total order
      `<_G` on `J ∪ V`, if `<_G` is a topological order of `G` ...,
      then there exists a strict total order `≺` on
      `J_{\doit(I_W)} ∪ V_{\doit(I_W)}` such that
        · `≺` is a topological order of `G_{\doit(I_W)}`; and
        · `≺` extends `<_G` along `ι` in the strict sense ...

  The "Example construction (the LN's `put all I_w first`)"
  paragraph then provides the explicit witness used here, which is
  exactly `extOrder lt`.
-/
-- ## Design choice
--
-- *Three theorems vs.\ one bundled conjunction theorem — picked
--   three.*  The LN bundles (a), (b), and (c) inside one
--   `\begin{Rem}`, but the three sub-claims have *different
--   hypotheses and carriers*:
--     · (a) takes `hAcyc : G.IsAcyclic` and concludes a property
--       of the extension (no order argument);
--     · (b) takes `lt' : IntExtNode Node → ... → Prop` and produces
--       a relation on `Node`;
--     · (c) takes `lt : Node → ... → Prop` and produces a relation
--       on `IntExtNode Node`.
--   Bundling them into one conjunction theorem would force every
--   consumer to take all three arguments (acyclicity, `lt'`, `lt`)
--   it does not need, or to project through `.1` / `.2` / `.2.1` /
--   `.2.2` with substantial use-site noise.  Three separate
--   theorems keep each statement focused and let downstream
--   consumers cite the sub-claim they need by name.  Matches the
--   `claim_3_6` (`splAcyclic` / `splTopologicalOrder`) and
--   `claim_3_9` (`swigAcyclic` / `swigTopologicalOrder`) carrier-
--   change pattern (extended here to three theorems because (b)'s
--   restriction direction was absent in the spl / swig analogs).
--
-- *Conclusion-only existence witness, not separate
--   "extends-`lt`" theorem.*  Sub-claim (c) is *strictly* a
--   topological-order claim about `extOrder lt`; the
--   strict-extension property (`restrictOrder (extOrder lt) = lt`)
--   is true *definitionally* by case 4 of `extOrder` (which is
--   `lt v1 v2`).  A separate theorem stating "`restrictOrder
--   (extOrder lt) = lt`" was rejected because it is a one-step
--   `rfl` / `funext` whose content is fully visible in `extOrder`'s
--   case analysis; consumers can prove it inline when needed.
--
-- *Hypotheses ordered `(G, W, hW, lt, hlt)`.*  Matches the
--   `extAcyclic` and `extRestrictsTopologicalOrder` orderings on
--   the shared prefix `(G, W, hW)` and appends `(lt, hlt)` — the
--   *additional* hypotheses sub-claim (c) needs.  Mirrors
--   `swigTopologicalOrder` / `splTopologicalOrder`.
--
-- *No `hAcyclic` hypothesis.*  Same as (b): the extension
--   direction does not require `G` to be acyclic — even on a
--   cyclic `G`, any topological-order witness `lt` (vacuously
--   satisfying parent-precedence) lifts to a topological-order
--   witness on the extension.  In practice no cyclic `G` admits a
--   topological order, so this is mostly a clean-signature win,
--   not a substantive extra generality.
--
-- *`lt` typed as a bare relation, not via a typeclass.*  Same
--   rationale as `def_3_8`'s `IsTopologicalOrder`.
--
-- *Universal quantification over `lt` lives as an outermost
--   positional binder.*  Same convention as
--   `extRestrictsTopologicalOrder` / `swigTopologicalOrder` /
--   `splTopologicalOrder`.
--
-- *Conclusion via `(G.extendingCDMGsWith W hW).IsTopologicalOrder
--   (extOrder lt)`.*  The `extOrder` helper carries the carrier
--   translation `Node → IntExtNode Node` (via the `.unsplit` /
--   `.intCopy` case analysis), and the LN's "put all `I_w` first"
--   prose is realised structurally by the four-case definition
--   above.
--
-- *Downstream consumers.*  ch.\ 5 do-calculus and counterfactual
--   identification chapters that need an explicit topological
--   order on the extension (to factorise joint kernels along the
--   extended carrier, or to read off mechanism conditionals in
--   parent-precedence order) consume this theorem.  Also used by
--   `extAcyclic`'s proof (via `claim_3_2`'s
--   `acyclic_iff_topological_order`) — `extOrder lt` lifted from
--   any topological order of `G` yields the existence witness
--   that closes the corollary route from (c) to (a).
-- claim_3_13 -- start statement
theorem extExtendsTopologicalOrder (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V)
    (lt : Node → Node → Prop) (hlt : G.IsTopologicalOrder lt) :
    (G.extendingCDMGsWith W hW).IsTopologicalOrder (extOrder lt)
-- claim_3_13 -- end statement
  := by
  -- TeX proof: tex/claim_3_13_proof_AcyclicHardInterventionTopologicalOrder.tex
  -- One-line wrapper around the private workhorse `aux_extTopologicalOrder`.
  -- Mirrors `swigTopologicalOrder`'s wrapper in `SwigAcyclic.lean`.
  exact aux_extTopologicalOrder G W hW lt hlt

end CDMG

end Causality
