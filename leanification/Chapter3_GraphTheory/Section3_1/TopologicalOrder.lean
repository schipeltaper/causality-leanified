import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.FamilyRelationships

namespace Causality

/-!
# Topological order of a CDMG (`def_3_8`)

This file formalises the LN definition block `def_3_8`
(`\label{def-topological-order}` in `graphs.tex`):

> Let `G = (J, V, E, L)` be a CDMG.  A *topological order* of `G` is a
> total order `<` of `J ∪ V` such that for all `v, w ∈ G`:
> `v ∈ Pa^G(w) ⟹ v < w`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/def_3_8_TopologicalOrder.tex`,
verified equivalent to the LN block.  No `addition_to_the_LN` clauses
were attached in `data.json`; the rewrite folded the two wording-check
subtleties `equivalent_indexing_assumes_finite_node_set` and
`quantifier_domain_v_w_in_G_is_tuple_not_set` directly into the
canonical tex as non-load-bearing clarifications.  Both
`verify_tex_statement_only` (structural) and
`verify_tex_statement_equivalence` (semantic) passed.

The rewrite's clarifications, for the record:

* `<` is read *strictly*: irreflexive (`¬ v < v`), transitive
  (`v < w` and `w < x` imply `v < x`), and trichotomous
  (`v < w`, `v = w`, or `w < v` for every `v, w ∈ J ∪ V`).
* The order's domain is `J ∪ V` (the LN's "for all `v, w ∈ G`"
  shorthand) — finite, by `def_3_1`'s `J, V : Finset Node`.
* The parent implication `v ∈ Pa^G(w) ⟹ v < w` is well-typed
  because `Pa^G(w) ⊆ J ∪ V` by `def_3_5` item~i (the parent-set
  body includes `w ∈ G`); see `Pa`'s design block in
  `FamilyRelationships.lean`.
* The "equivalent indexing form" `J ∪ V = {v_1, ..., v_K}` with
  `v_1 < ... < v_K` is *logically equivalent* to the primary
  (strict-total-order) form *because* `J ∪ V` is finite (any strict
  total order on a finite set has order type a finite ordinal and so
  can be presented as an enumeration).  We do NOT formalise the
  indexed form as a separate predicate — see the "Scope choice"
  bullet in the design block below.

The predicate `IsTopologicalOrder` below is a *property of an external
ordering*: it takes a strict relation `lt : Node → Node → Prop` as an
explicit argument and asserts that this particular `lt` is a topological
order of `G`.  The existence claim "a topological order of `G` exists"
is what `claim_3_2` ("acyclic iff a topological order exists") will
quantify over.

-/

namespace CDMG

-- ## Design choice — statement context (refactor twin)
--
-- Three-dash `--- start helper` markers match the convention used
-- across `CDMG.lean`, `CDMGNotation.lean`, `Walks.lean`,
-- `EdgeRelations.lean`, `CDMGRestrictions.lean`, `Acyclicity.lean`,
-- `CDMGTypes.lean`, and `FamilyRelationships.lean` for the
-- `variable` line that binds the implicit parameters into the
-- predicates wrapped below.  Both `Node : Type*` and
-- `[DecidableEq Node]` are inherited verbatim from `def_3_1`'s
-- refactor twin (`CDMG`): the `Membership Node
-- (CDMG Node)` instance from `def_3_2`'s refactor twin
-- (`instMembership` in `CDMGNotation.lean`) — driving the
-- `v ∈ G` quantifier scope below — reduces to `Finset.mem` on
-- `G.J ∪ G.V`, which needs `DecidableEq Node`; the
-- `G.Pa w : Set Node` reference in
-- `IsTopologicalOrder` reaches back to `def_3_5`'s
-- refactor twin (`Pa` in `FamilyRelationships.lean`)
-- whose body `{u | u ∈ G ∧ (u, w) ∈ G.E}` likewise depends on
-- `DecidableEq` through `Finset` membership.
-- def_3_8 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_8 --- end helper

-- ref: def_3_8 — refactor twin
-- `G.IsTotalOrder lt` asserts that the strict binary
-- relation `lt : Node → Node → Prop` restricts to a *strict total
-- order* on the vertex set `J ∪ V` of `G`, i.e.\ (i) irreflexive on
-- `J ∪ V` (`¬ lt v v` for `v ∈ G`), (ii) transitive on `J ∪ V`, and
-- (iii) trichotomous on `J ∪ V`.  See the `IsTotalOrder` design
-- block above (`namespace CDMG`) for the full rationale — the helper-
-- predicate-vs-`IsTopologicalOrder` separation, the Mathlib-typeclass
-- rejection, the trichotomy disjunct ordering matching Mathlib's
-- `Trichotomous`, the `Prop`-valued-`def`-not-`structure` choice, and
-- the downstream-consumer survey (`def_3_9`'s `Pred` / `PredLE`,
-- `claim_3_2`'s nested projection, ch.\ 4–10's order-slicing
-- arguments).  All carry over verbatim.
/-
LN tex fragment (unchanged by refactor — extracted from the
rewritten canonical statement file `def_3_8_TopologicalOrder.tex`):

  ... a *strict* total order `<` on `J ∪ V` -- i.e.\ a binary relation
  `<` on `J ∪ V` that is irreflexive, transitive, and satisfies
  trichotomy (`v < w`, `v = w`, or `w < v` for every `v, w ∈ J ∪ V`) ...
-/
-- ## Design choice (refactor twin)
--
-- *Structural port of the original `IsTotalOrder`* (`namespace
-- CDMG`, lines above) onto the `cdmg_typed_edges` refactor's new
-- upstream type (DEPENDENT row; root `def_3_1`).  The mathematical
-- design — strict reading of `<`, domain restricted to `J ∪ V` via
-- `∀ v ∈ G`, trichotomy disjunct order matching Mathlib's
-- `Trichotomous`, `Prop`-valued `def` rather than a typeclass /
-- structure — is **unchanged**.  Both wording-check subtleties
-- carried by this row remain resolved exactly as before:
-- `quantifier_domain_v_w_in_G_is_tuple_not_set` is handled by the
-- `instMembership` instance reducing `v ∈ G` to
-- `v ∈ G.J ∪ G.V`, and `equivalent_indexing_assumes_finite_node_set`
-- is unaffected (finiteness still holds via `def_3_1`'s
-- `Finset`-valued `J, V` — both fields are unchanged on
-- `CDMG`).
--
-- *Upstream-type shifts (and only those).*
--   `CDMG Node → CDMG Node`
-- No other change.  In particular, the `∀ v ∈ G, …` quantifier
-- ports verbatim because the `instMembership` instance
-- (`CDMGNotation.lean`'s refactor twin of `def_3_2`) gives the same
-- `v ∈ G.J ∪ G.V` reduction on `CDMG Node` as the original
-- `instMembership` does on `CDMG Node`.  This predicate does not
-- touch the `L` field, so the `Finset (Node × Node) → Finset (Sym2
-- Node)` retyping at root `def_3_1` does not propagate here.
-- def_3_8 --- start helper
def IsTotalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  (∀ v ∈ G, ¬ lt v v) ∧
  (∀ u ∈ G, ∀ v ∈ G, ∀ w ∈ G, lt u v → lt v w → lt u w) ∧
  (∀ v ∈ G, ∀ w ∈ G, lt v w ∨ v = w ∨ lt w v)
-- def_3_8 --- end helper

-- ref: def_3_8 — refactor twin
-- `G.IsTopologicalOrder lt` asserts that the strict binary
-- relation `lt : Node → Node → Prop` is a *topological order* of
-- the CDMG `G`, i.e.\ (i) `G.IsTotalOrder lt` — a strict
-- total order on `J ∪ V` (irreflexive, transitive, trichotomous;
-- see the `IsTotalOrder` block above) — and (ii) for every
-- parent-child pair `v ∈ Pa^G(w)` we have `lt v w`: parents precede
-- their children under `<`.  See the `IsTopologicalOrder` design
-- block above (`namespace CDMG`) for the full rationale — the
-- nested 2-conjunct shape mirroring the LN's two-tier reading, the
-- predicate-vs-existence-claim choice (`claim_3_2` quantifies
-- existence at the use site), the explicit-`lt`-argument-vs-`[LT
-- Node]`-typeclass rejection, the deliberate omission of `v ≠ w`
-- and `v ∈ G` / `w ∈ G` guards on the parent implication, the
-- `Set Node`-valued `Pa` reuse, and the primary-form-only scope
-- choice (no parallel `IsTopologicalOrderIndexed`).  All carry
-- over verbatim.
/-
LN tex (rewritten canonical statement for `def_3_8`, unchanged by
the refactor):

  A *topological order* of `G` is a *strict* total order `<` on
  `J ∪ V` -- i.e.\ a binary relation `<` on `J ∪ V` that is
  irreflexive, transitive, and satisfies trichotomy (`v < w`,
  `v = w`, or `w < v` for every `v, w ∈ J ∪ V`) -- such that
    ∀ v, w ∈ J ∪ V :  v ∈ Pa^G(w)  ⟹  v < w.
-/
-- ## Design choice (refactor twin)
--
-- *Structural port of the original `IsTopologicalOrder`*
-- (`namespace CDMG`, lines above) onto the `cdmg_typed_edges`
-- refactor's new upstream types (DEPENDENT row; roots `def_3_1`,
-- via `def_3_5`'s `Pa`).  The mathematical design — the
-- nested 2-conjunct shape `IsTotalOrder ∧ parent-precedence`, the
-- predicate-not-existence shape, the explicit-`lt`-argument
-- choice, the deliberate no-guard form of the parent implication
-- (load-bearing for `claim_3_2`'s `⇐` direction: a directed
-- self-loop `(v, v) ∈ G.E` would force `lt v v`, contradicting
-- irreflexivity), and the primary-form-only scope (no parallel
-- indexed predicate) — is **unchanged**.  Both wording-check
-- subtleties remain resolved exactly as before
-- (`quantifier_domain_v_w_in_G_is_tuple_not_set` via the
-- `instMembership` instance,
-- `equivalent_indexing_assumes_finite_node_set` via
-- `CDMG`'s unchanged `Finset`-valued `J, V`).
--
-- *Upstream-type shifts (and only those).*
--   `CDMG Node       → CDMG Node`
--   `G.IsTotalOrder  → G.IsTotalOrder`  (the cross-call
--                      to the helper above, retyped onto the
--                      refactor namespace)
--   `G.Pa            → G.Pa`  (the per-vertex parent set
--                      from `def_3_5`'s refactor twin in
--                      `FamilyRelationships.lean`; its body
--                      `{u | u ∈ G ∧ (u, w) ∈ G.E}` is unchanged
--                      because `G.E`'s carrier
--                      `Finset (Node × Node)` is unchanged by the
--                      refactor — only the `L`-side of `def_3_1`
--                      retyped to `Finset (Sym2 Node)`).
-- No other change.  The unrestricted `∀ v w, v ∈ G.Pa w
-- → lt v w` quantifier reads identically to the original: the
-- inner `v ∈ G` and `w ∈ G` witnesses still come from
-- `Pa`'s set-builder body / `CDMG.hE_subset`,
-- and the LN's "for all `v, w ∈ G`" is again shorthand for
-- `v, w ∈ J ∪ V`.  Neither this predicate nor its constituents
-- `IsTotalOrder` and `Pa` reach into the `L`
-- field, so the `Finset (Node × Node) → Finset (Sym2 Node)`
-- retyping at root `def_3_1` does not propagate here.
-- def_3_8 -- start statement
def IsTopologicalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  G.IsTotalOrder lt ∧ (∀ v w, v ∈ G.Pa w → lt v w)
-- def_3_8 -- end statement

end CDMG

end Causality
