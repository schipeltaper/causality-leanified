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

end CDMG

namespace CDMG

/-!
## Refactor twins for `claim_3_13` against the `def_3_1` retyping
(`cdmg_typed_edges` refactor)

This namespace holds the `def_3_1`-refactor twins of `claim_3_13`'s
three sub-claim theorems and two exposed helpers, against the
post-refactor `def_3_1` shape `CDMG` with
`L : Finset (Sym2 Node)` (rather than the pre-refactor
`L : Finset (Node × Node)` paired with `hL_symm` / `hL_irrefl`).
The five rendered declarations and the nine private workhorses below
are *mechanical name-bumps* of their counterparts in the
pre-refactor `namespace CDMG` block above; the upstream identifier
substitution is:

  · `CDMG`                          → `CDMG`              (def_3_1)
  · `IsAcyclic`                     → `IsAcyclic`         (def_3_6)
  · `IsTopologicalOrder`            → `IsTopologicalOrder`(def_3_8)
  · `acyclic_iff_topological_order` →
        `acyclic_iff_topological_order`                   (claim_3_2)
  · `extendingCDMGsWith`            → `extendingCDMGsWith`(def_3_13)
  · `extOrder` / `restrictOrder`    → `extOrder` /
                                       `restrictOrder`
  · all nine private helpers gain the `refactor_` prefix.

**The `L : Finset (Sym2 Node)` retyping does not reach this row.**
None of the three theorems (`extAcyclic`,
`extRestrictsTopologicalOrder`,
`extExtendsTopologicalOrder`) — nor any of the nine private
workhorses or the two exposed helpers — inspects `G.L`.  Every proof
reads only `G.J`, `G.V`, `G.E`, the constructor tag of `IntExtNode`,
and the lifted `lt`.  Concretely:

  · *(a) acyclicity* is a property of directed walks on the
    `E`-channel alone (`def_3_6`'s `IsAcyclic` quantifies
    only over `Walk` builders that follow `.forwardE` edges drawn
    from `G.E`);
  · *(b)/(c) topological order* unfolds to
    `IsTotalOrder` on `J ∪ V` (no `L`-dependence) plus the
    parent-precedence clause from `def_3_5`'s `Pa` (reads
    only `G.E`);
  · *`extendingCDMGsWith`* populates the extension's `L`
    via `L' := G.L.image (Sym2.map IntExtNode.unsplit)` (see
    `ExtendingCDMGsWith.lean`'s refactor twin), but no clause of
    this remark touches that field.

Consequently the port introduces zero `Sym2.lift` / `Sym2.mk`
boilerplate at any L-manipulation site (because there are no
L-manipulation sites here), and every design rationale recorded in
the pre-refactor `namespace CDMG` block above carries over verbatim
to the corresponding refactor twin — the per-declaration design
blocks below say *which* pre-refactor rationale carries and *why
the refactor doesn't perturb it*, rather than re-deriving the
rationale from scratch.

The `IntExtNode` tagged sum is *shared* between the two namespaces
(defined once inside `namespace CDMG` of `ExtendingCDMGsWith.lean`
and not re-introduced here); the `open CDMG` directive below brings
both `IntExtNode` and the upstream `extendingCDMGsWith`
into scope so the refactor twin can pattern-match
`.intCopy` / `.unsplit` and apply `extendingCDMGsWith`
function-style.  `addition_to_the_LN` is empty for this row, so
there are no addition-driven design choices to mention beyond what
the pre-refactor block records.
-/

-- ## `open CDMG` — bring `IntExtNode` and `extendingCDMGsWith`
-- into scope for the refactor twin
--
-- `def_3_13`'s `ExtendingCDMGsWith.lean` chose the single-namespace
-- pattern: the shared `inductive IntExtNode` and the refactor twin
-- `extendingCDMGsWith` both live inside `namespace CDMG`
-- alongside the pre-refactor `extendingCDMGsWith`.  Our refactor twin
-- below operates inside `namespace CDMG`, so we need to
-- bring those two identifiers into scope explicitly.  Dot notation
-- (`extendingCDMGsWith G W hW`) would not work — it resolves
-- via the receiver's type namespace (`CDMG`), and
-- `extendingCDMGsWith` is registered under `CDMG`, not
-- `CDMG`.  Function-style calls (`extendingCDMGsWith
-- G W hW`) with `open CDMG` are the cleanest fix.  No name collisions
-- arise because every refactor-twin declaration below carries the
-- `refactor_` prefix.
open CDMG

-- ## Design choice — statement context (refactor twin)
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Both fixtures are
--   inherited from `def_3_1`'s refactor twin (`CDMG`).  The
--   refactor twin's signatures reference `CDMG Node` (root
--   `def_3_1`), `G.IsAcyclic` (`def_3_6` refactor twin),
--   `extendingCDMGsWith G W hW` (`def_3_13` refactor twin)
--   producing a `CDMG (IntExtNode Node)` over the *shared*
--   tagged-sum carrier `IntExtNode` (which is untouched by the
--   refactor — see `ExtendingCDMGsWith.lean`'s shared `inductive
--   IntExtNode` block), `G.IsTopologicalOrder lt`
--   (`def_3_8` refactor twin), and
--   `(extendingCDMGsWith G W hW).IsTopologicalOrder lt'`
--   (which goes through the extended CDMG's `Pa` from
--   `def_3_5` refactor twin, in turn requiring
--   `[DecidableEq (IntExtNode Node)]` — provided automatically by
--   `def_3_13`'s `deriving DecidableEq` on the tagged-sum inductive).
--   No new typeclasses are needed: the mathematical content of this
--   row is unchanged by the refactor — the bidirected-edge set `L`
--   plays no role in any sub-claim, so the
--   `Finset (Node × Node) → Finset (Sym2 Node)` retyping at root
--   `def_3_1` does not reach this row at all.
--
-- *Three-dash `--- start helper` marker.*  Same convention as the
--   pre-refactor block above and as every sibling refactor twin in
--   `Section3_1/` and `Section3_2/`.

-- claim_3_13 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_13 --- end helper

-- ## Helper (refactor twin): the LN's "all `I_w` first" extension
-- order on `IntExtNode Node`
--
-- One-sentence summary: `extOrder lt` lifts a strict
-- relation `lt : Node → Node → Prop` on the original carrier
-- `Node` to a strict relation `IntExtNode Node → IntExtNode Node
-- → Prop` on the extended carrier, by the same four-case lex
-- analysis as the pre-refactor `extOrder` — every `.intCopy w`
-- precedes every `.unsplit v`, and within each tag class the order
-- delegates to `lt` on the underlying base nodes.
--
-- This helper is the *witness consumed by sub-claim (c)*
-- (`extExtendsTopologicalOrder`) and routed through the
-- private workhorse `aux_extTopologicalOrder`; it must
-- live alongside the rendered statements because removing it would
-- make sub-claim (c)'s conclusion type fail to compile.
--
-- ## Design choice
--
-- *Identical encoding to the pre-refactor `extOrder`; only the
--   upstream identifier changes from `extOrder` →
--   `extOrder`.*  The bidirected-edge `L`-channel retyping
--   at root `def_3_1` does not propagate to this helper:
--   `extOrder` reads only the constructor tag (`.intCopy`
--   / `.unsplit`) and the underlying `lt`, never touching `G.L`
--   (in fact it does not even take a `G` argument — see the
--   `W`-independence bullet below).  Every design rationale from
--   the pre-refactor `extOrder` block carries over verbatim:
--
--   · *Four-case match over `ℚ`-arithmetic.*  Mirrors the LN's
--     piecewise rule on `J_{doit(I_W)} ∪ V_{doit(I_W)}` directly,
--     no rational-offset detour.
--   · *`.intCopy < .unsplit` lex orientation.*  Forced by the
--     LN's "fresh intervention nodes first" and by
--     parent-precedence on `def_3_13` item iii's fresh edges
--     `(.intCopy w, .unsplit w)` — discharged by case 2 of the
--     match (`True`).
--   · *Subtlety-1 resolution
--     (`all_I_w_first_clashes_with_J_cap_W_nonempty`).*  Inherited
--     verbatim from the pre-refactor block via the shared
--     `IntExtNode`: `def_3_13`'s refactor twin
--     `extendingCDMGsWith` *also* constructs `.intCopy w`
--     only for `w ∈ W \ G.J` (the type-level fix happens upstream
--     at `def_3_13`, not in this row), so "all `.intCopy` first"
--     never reshuffles `J ∩ W` nodes here either.
--   · *Subtlety-4 resolution (`order_among_I_w_unspecified`).*
--     Inherited verbatim from the pre-refactor block: the
--     `(.intCopy w₁, .intCopy w₂) ↦ lt w₁ w₂` clause picks the
--     canonical lift of `lt` to `W \ G.J`, free of arbitrary
--     enumeration.
--   · *`Prop`-valued binary relation, not a typeclass.*  Matches
--     `def_3_8`'s refactor twin `IsTopologicalOrder`
--     argument shape — `lt` is universally quantified, not
--     typeclass-resolved.
--   · *`W`-independence absorbed into the carrier.*  The
--     `W`-dependence travels through the constructor tag of
--     `IntExtNode Node`; membership-in-`W` is checked at the
--     use-site against `extendingCDMGsWith G W hW`, not
--     inside `extOrder`.
--
-- *Refactor-specific note (function-style call rather than
--   dot-notation).*  Inside `namespace CDMG`,
--   `extOrder` is a top-level def whose application
--   `extOrder lt` reads identically pre/post-refactor —
--   no `Sym2.mk` / `Sym2.lift` boilerplate is introduced because
--   the helper has no `L` dependency.

-- claim_3_13 --- start helper
def extOrder (lt : Node → Node → Prop) :
    IntExtNode Node → IntExtNode Node → Prop
  | .intCopy w1, .intCopy w2 => lt w1 w2
  | .intCopy _,  .unsplit _  => True
  | .unsplit _,  .intCopy _  => False
  | .unsplit u1, .unsplit u2 => lt u1 u2
-- claim_3_13 --- end helper

-- ## Helper (refactor twin): the canonical restriction of a
-- relation on `IntExtNode Node` to `Node` along `.unsplit`
--
-- One-sentence summary: `restrictOrder lt'` pulls a
-- strict relation `lt' : IntExtNode Node → IntExtNode Node → Prop`
-- back through the canonical inclusion `Node ↪ IntExtNode Node`
-- (the `.unsplit` constructor), producing a strict relation on the
-- original `Node` carrier.  It is the *concrete witness consumed
-- by sub-claim (b)* (`extRestrictsTopologicalOrder`).
--
-- ## Design choice
--
-- *Identical encoding to the pre-refactor `restrictOrder`; only
--   the upstream identifier changes from `restrictOrder` →
--   `restrictOrder`.*  The bidirected-edge `L`-channel
--   retyping at root `def_3_1` does not propagate: this helper
--   routes through the shared `IntExtNode.unsplit` constructor
--   and never reads `G.L`.  Every design rationale from the
--   pre-refactor `restrictOrder` block carries over verbatim:
--
--   · *Realisation of the LN's
--     `ι : J ∪ V ↪ J_{\doit(I_W)} ∪ V_{\doit(I_W)}`.*  The
--     canonical tex's set-theoretic inclusion `v ↦ v` is realised
--     constructor-wise as `.unsplit`; the body
--     `fun v1 v2 => lt' (.unsplit v1) (.unsplit v2)` is the
--     literal Lean rendering of the LN's `ι(v_1) ≺ ι(v_2)`.
--   · *Subtlety-2 resolution (`extend_meaning_unspecified`),
--     strict reading.*  Together with the strict-extension
--     property `restrictOrder (extOrder lt) =
--     lt` (true definitionally by case 4 of `extOrder`),
--     this helper realises the standard "the extension
--     restricted to the smaller carrier equals the original"
--     reading of "extend" that the LN leaves implicit.
--   · *Subtlety-3 resolution (`top_order_node_set_mismatch`),
--     type level.*  The two `IsTopologicalOrder`
--     predicates live on different relation types
--     (`IntExtNode Node → IntExtNode Node → Prop` vs.
--     `Node → Node → Prop`); `restrictOrder` is the
--     bridge.  The LN's loose "is also one for `G`" reads
--     correctly at the type level only via this restriction.
--   · *Body is `fun`, not `match`.*  Only the
--     `(.unsplit, .unsplit)` slot ever arises in restriction; a
--     one-line lambda is the most direct transcription.
--   · *`Prop`-valued, not typeclass.*  Same rationale as
--     `extOrder`: matches `def_3_8`'s refactor twin's
--     universal-quantification-over-`lt'` argument shape.
--
-- *Refactor-specific note.*  No `Sym2` boilerplate is introduced
--   because the helper has no `L` dependency.  The body reads
--   identically pre/post-refactor; only the surrounding namespace
--   (`CDMG`) and the helper's own identifier differ.

-- claim_3_13 --- start helper
def restrictOrder (lt' : IntExtNode Node → IntExtNode Node → Prop) :
    Node → Node → Prop :=
  fun v1 v2 => lt' (.unsplit v1) (.unsplit v2)
-- claim_3_13 --- end helper

-- ## Proof-only helpers (refactor twins; private, live above the
-- theorems)
--
-- The lemmas below are infrastructure for the proofs of
-- `extAcyclic`, `extRestrictsTopologicalOrder`,
-- and `extExtendsTopologicalOrder`.  They are deliberately
-- private, carry no marker comments inside (each wrapped in its own
-- REPLACEMENT marker), and do not appear in the rendered statement.
-- Mirrors the analogous block in the pre-refactor `namespace CDMG`
-- above and in `SwigAcyclic.lean`'s refactor twin.  Each is a
-- structural port of its pre-refactor counterpart — only the
-- upstream identifiers change from `<name>` → `refactor_<name>`
-- (and `CDMG` → `CDMG`).  `IntExtNode` is *shared* between
-- the two namespaces (defined once in `ExtendingCDMGsWith.lean` and
-- not refactored), so the constructor pattern-matches on
-- `.unsplit` / `.intCopy` and the `IntExtNode.unsplit.inj` /
-- `IntExtNode.unsplit` references read identically here.
--
-- *Independent of the bidirected-edge channel `L`.*  None of the
-- nine helpers below inspects the `L` field of any `CDMG`;
-- every helper reads only `J` / `V` / `E` or the constructor tag of
-- `IntExtNode`.  The `Finset (Sym2 Node)` retyping of `L` at root
-- `def_3_1` does not reach any helper — the entire file-level
-- refactor delta is a name-bump from `CDMG` / `IsAcyclic` /
-- `IsTopologicalOrder` / `extendingCDMGsWith` / `extOrder` /
-- `restrictOrder` / privates to their `refactor_<name>` twins.

-- *Role.*  Constructor-tag projection onto the underlying base
-- node.  Carved out so the lex characterisation
-- (`extOrder_iff`) and the trichotomy / transitivity /
-- irreflexivity branches of `aux_extTopologicalOrder` can
-- refer to "the underlying `Node`" without re-doing the two-case
-- match each time.  Inlining would balloon every base-node read in
-- those four branches into a `cases x` block.  Same shape as the
-- pre-refactor `baseOf`.
private def baseOf : IntExtNode Node → Node
  | .unsplit u => u
  | .intCopy w => w

-- *Role.*  Constructor-tag projection onto `{0, 1} ⊂ ℕ`, encoding
-- the LN's "fresh `I_w` nodes first" lex orientation
-- (`.intCopy ↦ 0 < .unsplit ↦ 1`).  Paired with `baseOf`,
-- this gives the (tag, base) lex key that
-- `extOrder_iff` characterises.  Lives separately from
-- `baseOf` so each projection can be unfolded / `simp`-ed
-- independently in the proof branches.  Discrete `ℕ` codomain
-- rules out consecutive-`W` collisions by construction (the
-- analog of `SwigAcyclic`'s `δ`-arithmetic concern raised in its
-- `one_third_offset_is_load_bearing_not_arbitrary` subtlety).
private def tagOf : IntExtNode Node → ℕ
  | .intCopy _ => 0
  | .unsplit _ => 1

-- *Role.*  The lex-on-(tag, base) characterisation of
-- `extOrder` —
-- `extOrder lt x y ↔ tag x < tag y ∨ (tag x = tag y ∧ lt
-- (base x) (base y))`.  Carved out so the 4-way constructor case
-- analysis (`cases x <;> cases y`) is done *once* here, and the
-- four proof branches of `aux_extTopologicalOrder`
-- (irreflexivity, transitivity, trichotomy, parent-precedence)
-- can each rewrite to the lex form and reason at the (tag, base)
-- level rather than re-introducing the 4 / 16 / 16 case splits.
-- `omit [DecidableEq Node]` is safe because the proof is pure
-- `simp` on the definitions; no kernel equality checks fire.
omit [DecidableEq Node] in
private lemma extOrder_iff (lt : Node → Node → Prop) (x y : IntExtNode Node) :
    extOrder lt x y ↔
      tagOf x < tagOf y ∨
        (tagOf x = tagOf y ∧ lt (baseOf x) (baseOf y)) := by
  cases x <;> cases y <;> simp [extOrder, baseOf, tagOf]

-- *Role.*  Extensionality on `IntExtNode Node`: equality on the
-- (tag, base) pair forces constructor equality.  Used in the
-- trichotomy branch of `aux_extTopologicalOrder` to lift
-- `lt`'s `base x = base y` clause back up to `x = y` (after
-- adjoining `tag x = tag y`).  Carved out because the `cases x
-- <;> cases y <;> simp_all` reasoning is uniform across all four
-- constructor pairs but reads badly inline.  `omit [DecidableEq
-- Node]` is safe — the proof is pure constructor reduction.
omit [DecidableEq Node] in
private lemma intExtNode_ext {x y : IntExtNode Node}
    (hbase : baseOf x = baseOf y)
    (htag : tagOf x = tagOf y) : x = y := by
  cases x <;> cases y <;> simp_all [baseOf, tagOf]

-- *Role.*  Membership lift: if `x` is in the extended carrier
-- `J' ∪ V'` of `extendingCDMGsWith G W hW`, then its base
-- node lives in `G.J ∪ G.V` (= `G` qua `Membership`).  Used in
-- *all four* clauses of `aux_extTopologicalOrder` to feed
-- the original topological-order hypotheses (which quantify over
-- `Node ∈ G`) the base of any `IntExtNode` they are asked about.
-- The case analysis traces the four set-builders of
-- `extendingCDMGsWith`'s `J'` and `V'`
-- (`G.J.image .unsplit`, `(W \ G.J).image .intCopy`,
-- `G.V.image .unsplit`); the `(W \ G.J).image .intCopy` arm is
-- where `hW : W ⊆ G.J ∪ G.V` is consumed (to land the fresh
-- node's base back in `G.V`).
private lemma baseOf_mem_ext {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {x : IntExtNode Node}
    (hx : x ∈ extendingCDMGsWith G W hW) :
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

-- *Role.*  The reverse lift of `baseOf_mem_ext`: from
-- `v ∈ G` (i.e. `v ∈ G.J ∪ G.V`) to `.unsplit v` in the extended
-- carrier.  Used in *all four* clauses of
-- `extRestrictsTopologicalOrder` (sub-claim (b)) to feed
-- the extension's topological-order hypotheses (which quantify
-- over `IntExtNode Node` in the extended carrier) the `.unsplit
-- v` of any base node they are asked about.  Case-splits on
-- `v ∈ G.J` vs. `v ∈ G.V`, each routed to the corresponding
-- `.unsplit`-image set-builder of `J'` and `V'`.
private lemma unsplit_mem_ext {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {v : Node} (hv : v ∈ G) :
    IntExtNode.unsplit v ∈ extendingCDMGsWith G W hW := by
  change IntExtNode.unsplit v ∈
    (extendingCDMGsWith G W hW).J ∪ (extendingCDMGsWith G W hW).V
  rcases Finset.mem_union.mp hv with hJ | hV
  · refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · refine Finset.mem_union_right _ ?_
    exact Finset.mem_image.mpr ⟨v, hV, rfl⟩

-- *Role.*  Case-4-of-`extOrder` corollary: `lt v1 v2`
-- transports to `extOrder lt (.unsplit v1) (.unsplit v2)`
-- definitionally (`extOrder` returns `lt u1 u2` in the
-- `(.unsplit u1, .unsplit u2)` branch).  Used in the *lifted-edge
-- sub-case* of `aux_extTopologicalOrder`'s parent-
-- precedence branch.  Carved out as a named lemma rather than
-- inlined to mirror the pre-refactor `extOrder_lifted_edge` and
-- to keep the proof of `aux_extTopologicalOrder`
-- readable as four matching one-liners (irreflexive / transitive
-- / trichotomous / parent-precedence).
omit [DecidableEq Node] in
private lemma extOrder_lifted_edge {lt : Node → Node → Prop}
    {v1 v2 : Node} (h : lt v1 v2) :
    extOrder lt (IntExtNode.unsplit v1) (IntExtNode.unsplit v2) :=
  h

-- *Role.*  Case-2-of-`extOrder` corollary:
-- `extOrder lt (.intCopy w) (.unsplit w)` is `True` by
-- construction (no `lt` hypothesis needed — the `.intCopy <
-- .unsplit` lex orientation discharges fresh edges unconditionally).
-- Used in the *fresh-edge sub-case* of
-- `aux_extTopologicalOrder`'s parent-precedence branch,
-- corresponding to `def_3_13`'s refactor twin item iii fresh
-- edges `(.intCopy w, .unsplit w)` for `w ∈ W \ G.J`.  Named for
-- symmetry with `extOrder_lifted_edge`.
omit [DecidableEq Node] in
private lemma extOrder_intCopy_edge {lt : Node → Node → Prop} {w : Node} :
    extOrder lt (IntExtNode.intCopy w) (IntExtNode.unsplit w) :=
  trivial

-- *Role.*  The shared workhorse: proves
-- `(extendingCDMGsWith G W hW).IsTopologicalOrder
-- (extOrder lt)` directly under the hypotheses of
-- sub-claim (c), consumed by both `extExtendsTopologicalOrder`
-- (as a one-liner wrapper) and `extAcyclic` (where the
-- topological-order witness is fed to the `⇐` direction of
-- `claim_3_2`'s refactor twin `acyclic_iff_topological_order`
-- to derive acyclicity).  Mirrors `SwigAcyclic.lean`'s
-- `aux_swigTopologicalOrder`.  Carved out because both
-- (a) and (c) need the same topological-order content — without
-- this shared lemma, the (c) proof would have to be inlined into
-- (a)'s body or duplicated.  Litmus: removing any of the eight
-- private helpers above would break this lemma, and removing
-- this lemma would break both (a) and (c).
private lemma aux_extTopologicalOrder (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.J ∪ G.V)
    (lt : Node → Node → Prop) (hlt : G.IsTopologicalOrder lt) :
    (extendingCDMGsWith G W hW).IsTopologicalOrder
      (extOrder lt) := by
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

-- ref: claim_3_13 (sub-claim (a), acyclicity preservation) — refactor twin
--
-- One-sentence summary: for a CDMG `G`, a subset `W ⊆ G.J ∪ G.V`,
-- and the assumption that `G` is acyclic (`def_3_6` refactor twin
-- `IsAcyclic`), the extended CDMG
-- `extendingCDMGsWith G W hW` (`def_3_13` refactor twin)
-- is itself acyclic.
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
-- *Mechanical name-bump from the pre-refactor `extAcyclic`.*
--   Identifier substitution `CDMG → CDMG`,
--   `IsAcyclic → IsAcyclic`,
--   `extendingCDMGsWith → extendingCDMGsWith`,
--   `extOrder → extOrder`,
--   `acyclic_iff_topological_order →
--    acyclic_iff_topological_order`,
--   `aux_extTopologicalOrder → aux_extTopologicalOrder`.
--   The body is a verbatim two-line proof: extract a topological
--   order via the `⇒` direction of `claim_3_2`'s refactor twin,
--   lift it via `aux_extTopologicalOrder`, conclude via
--   the `⇐` direction.  Mirrors `swigAcyclic` in
--   `SwigAcyclic.lean`.
--
-- *Pre-refactor rationales that carry over verbatim:*
--
--   · *Corollary route from (c) via `claim_3_2`.*  The proof
--     reduces acyclicity-of-extension to existence-of-topological-
--     order-on-extension, which (c) provides.  This route is
--     chosen over a direct induction on cycles because (c)'s
--     existence proof already does the cycle-by-cycle bookkeeping
--     via the lex order, and `claim_3_2`'s biconditional makes
--     the corollary one line.
--   · *Load-bearing role of `hAcyc` only for sub-claim (a).*
--     Without `G.IsAcyclic`, the route via (c) fails
--     because `lt` (the topological order on `G`) does not exist
--     in the first place.  (b) and (c) are content-free in the
--     "cyclic but admits a topological order" edge case
--     (vacuously true).
--   · *LN-faithful single-theorem split from (b)/(c).*  Same
--     "three theorems vs.\ one bundle" rationale recorded under
--     `extExtendsTopologicalOrder` below — different
--     hypotheses (`hAcyc` vs. `lt`/`lt'`) and different carriers
--     in the conclusion type force three separate theorems.
--   · *Hypothesis ordering `(G, W, hW, hAcyc)`.*  Matches the
--     refactor twin of `extendingCDMGsWith`'s binder
--     order `(G, W, hW)` and appends `hAcyc` at the end.
--   · *`IsAcyclic`, not `IsCADMG`.*  Unlike
--     `swigAcyclic`, this row does NOT take an
--     `IsCADMG` hypothesis because `extendingCDMGsWith`'s
--     signature does not require one (contrast with
--     `nodeSplittingHard`).  Keeps the signature
--     LN-faithful — the LN reads "If a CDMG `G` is acyclic", not
--     "If a CADMG `G`".
--
-- *Refactor-specific note (no `L`-channel reach).*  The
--   `Finset (Node × Node) → Finset (Sym2 Node)` retyping of `L`
--   at root `def_3_1` does not propagate into this theorem:
--   `IsAcyclic` quantifies over directed walks built from
--   `.forwardE` steps reading `G.E` alone; the extension's
--   `L`-channel — populated by
--   `L' := G.L.image (Sym2.map IntExtNode.unsplit)` per
--   `extendingCDMGsWith` — never enters the cycle
--   reasoning.  Sub-claim (a) is robust under any future change
--   to the `L`-channel encoding.
--
-- *Downstream consumers (unchanged from pre-refactor).*  ch.\ 5
--   do-calculus and ch.\ 8+ iSCM intervention algebra rely on the
--   extension being a CADMG; this theorem provides the
--   `IsAcyclic` witness that is the precondition for that
--   lift.
-- claim_3_13 -- start statement
theorem extAcyclic (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V) (hAcyc : G.IsAcyclic) :
    (extendingCDMGsWith G W hW).IsAcyclic
-- claim_3_13 -- end statement
  := by
  obtain ⟨lt, hlt⟩ := (acyclic_iff_topological_order G).mp hAcyc
  exact (acyclic_iff_topological_order
      (extendingCDMGsWith G W hW)).mpr
    ⟨extOrder lt, aux_extTopologicalOrder G W hW lt hlt⟩

-- ref: claim_3_13 (sub-claim (b), restriction direction) — refactor twin
--
-- One-sentence summary: for a CDMG `G`, a subset `W ⊆ G.J ∪ G.V`,
-- and a topological order `lt'` on the extension
-- `extendingCDMGsWith G W hW` (carrier `IntExtNode Node`),
-- the restricted relation `restrictOrder lt'` on `Node`
-- (pulling `lt'` back through `.unsplit`) is a topological order
-- on the original CDMG `G`.
--
-- Unfolded, the conclusion asserts:
--   · `restrictOrder lt'` is a strict total order on
--     `J ∪ V` (irreflexive, transitive, trichotomous; via the
--     nested `IsTotalOrder` projection);
--   · for every parent-child pair `v ∈ G.Pa w`, we have
--     `restrictOrder lt' v w`, i.e.
--     `lt' (.unsplit v) (.unsplit w)`.
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
-- *Mechanical name-bump from the pre-refactor
--   `extRestrictsTopologicalOrder`.*  Identifier substitution
--   `CDMG → CDMG`,
--   `IsTopologicalOrder → IsTopologicalOrder`,
--   `extendingCDMGsWith → extendingCDMGsWith`,
--   `restrictOrder → restrictOrder` (and the private
--   `unsplit_mem_ext → unsplit_mem_ext`).  The proof body
--   is a verbatim port of the pre-refactor four-clause case-split
--   (irreflexivity, transitivity, trichotomy, parent-precedence),
--   each clause lifting the corresponding clause of `lt'` back
--   along `.unsplit` via `unsplit_mem_ext`.
--
-- *Pre-refactor rationales that carry over verbatim:*
--
--   · *Separate theorem from (a) and (c).*  See the shared "three
--     theorems vs.\ one bundled conjunction" rationale on
--     `extExtendsTopologicalOrder` below — different
--     carriers in the hypothesis (`lt'` on `IntExtNode Node`) and
--     conclusion (relation on `Node`) versus (c)'s opposite
--     directionality force separate theorems.
--   · *No `hAcyclic` hypothesis.*  Acyclicity of `G` is unnecessary
--     for the restriction direction — the parent-precedence /
--     total-order properties transport pointwise via `.unsplit`'s
--     constructor injectivity (`IntExtNode.unsplit.inj`).  Mirrors
--     `claim_3_3` sub-claim (b)'s structure: topological-order
--     preservation does not require acyclicity on `G`.
--   · *Subtlety-2 / Subtlety-3 resolution carry-over.*  See the
--     `restrictOrder` design block above — strict reading
--     of "extend" (subtlety-2) and type-level fix for the LN's
--     loose "is also one for `G`" prose (subtlety-3) are both
--     inherited verbatim through the same `restrictOrder`
--     helper.
--   · *Hypothesis ordering `(G, W, hW, lt', hlt')`.*  Shared prefix
--     `(G, W, hW)` with `extAcyclic`, appends the
--     additional `(lt', hlt')` that sub-claim (b) needs.
--   · *`lt'` as a bare relation, not a typeclass.*  Universal
--     quantification over `lt'` is exposed at the binder level —
--     matches `def_3_8`'s refactor twin's argument shape.
--   · *Conclusion via `G.IsTopologicalOrder
--     (restrictOrder lt')`.*  The helper carries the
--     carrier translation `IntExtNode Node → Node` (via
--     `.unsplit`) explicitly; the LN's `ι(v_1) ≺ ι(v_2)` is
--     literal at the type level.
--
-- *Refactor-specific note (no `L`-channel reach).*  The
--   `Finset (Sym2 Node)` retyping of `L` at root `def_3_1` does not
--   propagate into this theorem: `IsTopologicalOrder` is
--   the conjunction of `IsTotalOrder` on `J ∪ V` (no `L`
--   reference) and the parent-precedence clause routed through
--   `Pa` (reads `G.E` only).  Neither this theorem's
--   statement nor any branch of its proof inspects `G.L`.
--
-- *Refactor-specific note (`set_option linter.style.longLine
--   false`).*  Retained from the pre-refactor block; the refactor
--   identifier prefixes push some signature lines past the
--   long-line threshold.
--
-- *Downstream consumers (unchanged from pre-refactor).*  ch.\ 5
--   do-calculus identification arguments that move from a
--   topological order on the extension back to a topological
--   order on the original CDMG consume this theorem.
set_option linter.style.longLine false in
-- claim_3_13 -- start statement
theorem extRestrictsTopologicalOrder (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V)
    (lt' : IntExtNode Node → IntExtNode Node → Prop)
    (hlt' : (extendingCDMGsWith G W hW).IsTopologicalOrder lt') :
    G.IsTopologicalOrder (restrictOrder lt')
-- claim_3_13 -- end statement
  := by
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
    refine h_pa' (.unsplit v) (.unsplit w)
      ⟨unsplit_mem_ext (hW := hW) hv_mem, ?_⟩
    -- goal: (.unsplit v, .unsplit w) ∈ (extension).E
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨(v, w), hvw_E, rfl⟩

-- ref: claim_3_13 (sub-claim (c), extension direction) — refactor twin
--
-- One-sentence summary: for a CDMG `G`, a subset `W ⊆ G.J ∪ G.V`,
-- and a topological order `lt` on `G`, the lifted relation
-- `extOrder lt` on `IntExtNode Node` is a topological
-- order on the extension `extendingCDMGsWith G W hW`.
--
-- Unfolded, the conclusion asserts:
--   · `extOrder lt` is a strict total order on
--     `J_{\doit(I_W)} ∪ V_{\doit(I_W)}`;
--   · for every parent-child pair
--     `v ∈ (extendingCDMGsWith G W hW).Pa w`,
--     we have `extOrder lt v w`.
--
-- The parent-precedence clause splits into two sub-cases on
-- `def_3_13`'s two edge-set-builders: (i) lifted edges
-- `(.unsplit v1, .unsplit v2)` for `(v1, v2) ∈ G.E`, discharged by
-- `extOrder_lifted_edge`; (ii) fresh edges
-- `(.intCopy w, .unsplit w)` for `w ∈ W \ G.J`, discharged by
-- `extOrder_intCopy_edge`.
--
-- *Strict-extension property is built in by construction.*  Case 4
-- of `extOrder` (`(.unsplit u1, .unsplit u2) ↦ lt u1 u2`)
-- gives `restrictOrder (extOrder lt) = lt`
-- definitionally — closing the LN's strict reading of "extend"
-- (subtlety-2) on the nose, paired with the topological-order
-- conclusion of this theorem.
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
-- *Mechanical name-bump from the pre-refactor
--   `extExtendsTopologicalOrder`.*  Identifier substitution
--   `CDMG → CDMG`,
--   `IsTopologicalOrder → IsTopologicalOrder`,
--   `extendingCDMGsWith → extendingCDMGsWith`,
--   `extOrder → extOrder`,
--   `aux_extTopologicalOrder → aux_extTopologicalOrder`.
--   The body is a one-line wrapper around
--   `aux_extTopologicalOrder`, identical in shape to the
--   pre-refactor `extExtendsTopologicalOrder` wrapper.
--
-- *Pre-refactor rationales that carry over verbatim:*
--
--   · *Three theorems vs.\ one bundled conjunction — picked three.*
--     The LN bundles (a)/(b)/(c) under one `\begin{Rem}`, but the
--     three sub-claims have *different hypotheses and carriers*:
--       · (a) takes `hAcyc : G.IsAcyclic` and concludes
--         a property of the extension (no order argument);
--       · (b) takes `lt' : IntExtNode Node → ... → Prop` and
--         produces a relation on `Node`;
--       · (c) takes `lt : Node → ... → Prop` and produces a
--         relation on `IntExtNode Node`.
--     Bundling them would force every consumer to take all three
--     arguments it does not need.  Matches the
--     `swigAcyclic / swigTopologicalOrder` and
--     `splAcyclic / splTopologicalOrder` precedents.
--   · *Conclusion-only existence witness, not separate
--     "extends-`lt`" theorem.*  The strict-extension property
--     `restrictOrder (extOrder lt) = lt` is true
--     definitionally by case 4 of `extOrder`; a separate
--     theorem would be a one-step `rfl` / `funext` with no
--     content.
--   · *No `hAcyclic` hypothesis.*  Same as (b): the extension
--     direction does not require `G` acyclic.  In practice no
--     cyclic `G` admits a topological order (`claim_3_2`), so
--     this is mostly a clean-signature win.
--   · *Hypothesis ordering `(G, W, hW, lt, hlt)`.*  Shared prefix
--     with `extAcyclic` and
--     `extRestrictsTopologicalOrder`; appends
--     `(lt, hlt)`.
--   · *`lt` typed as a bare relation, outermost positional
--     binder.*  Matches `def_3_8`'s refactor twin argument shape.
--   · *Conclusion via `extOrder` carrying the carrier
--     translation `Node → IntExtNode Node`.*  The LN's "put all
--     `I_w` first" prose is realised structurally by the four-
--     case definition.
--   · *Subtlety-1 / Subtlety-4 resolution carry-over via shared
--     `IntExtNode`.*  See the `extOrder` design block —
--     `def_3_13`'s refactor twin constructs `.intCopy w` only for
--     `w ∈ W \ G.J`, and the `(.intCopy w₁, .intCopy w₂) ↦ lt w₁
--     w₂` clause picks the canonical lift on the fresh nodes.
--
-- *Refactor-specific note (no `L`-channel reach).*  Same as (b):
--   `IsTopologicalOrder` reads only `J ∪ V` (totality)
--   and `G.E` (via `Pa`); `extOrder` reads only
--   the constructor tag and the underlying `lt`.  Neither this
--   theorem's statement nor any branch of its proof inspects
--   `G.L`.
--
-- *Refactor-specific note (`set_option linter.style.longLine
--   false`).*  Retained from the pre-refactor block; refactor
--   identifier prefixes push the conclusion line past the long-
--   line threshold.
--
-- *Downstream consumers (unchanged from pre-refactor).*  ch.\ 5
--   do-calculus and counterfactual identification chapters that
--   need an explicit topological order on the extension consume
--   this theorem.  Also consumed internally by
--   `extAcyclic`'s proof (via
--   `acyclic_iff_topological_order`).
set_option linter.style.longLine false in
-- claim_3_13 -- start statement
theorem extExtendsTopologicalOrder (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V)
    (lt : Node → Node → Prop) (hlt : G.IsTopologicalOrder lt) :
    (extendingCDMGsWith G W hW).IsTopologicalOrder (extOrder lt)
-- claim_3_13 -- end statement
  := by
  exact aux_extTopologicalOrder G W hW lt hlt

end CDMG

end Causality
