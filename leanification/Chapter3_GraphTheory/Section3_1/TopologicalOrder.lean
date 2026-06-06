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

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  Both fixtures are load-bearing for this
--   row's statement: (i) the `Membership Node (CDMG Node)` instance
--   from `def_3_2` (`CDMGNotation.lean`) — driving the `v ∈ G`
--   quantifier scope below — reduces to `Finset.mem` on
--   `G.J ∪ G.V`, which needs `DecidableEq Node`; (ii) the
--   `G.Pa w : Set Node` reference in the parent-implication conjunct
--   reaches back to `def_3_5`'s `Pa` whose body
--   `{u | u ∈ G ∧ (u, w) ∈ G.E}` likewise depends on `DecidableEq`
--   through `Finset` membership.  Dropping either fixture would make
--   this statement fail to type-check.  Stronger instances
--   (`Fintype`, `LinearOrder`) are not needed and are deferred to use
--   sites that consume them (e.g.\ `claim_3_2`'s constructive
--   topological-sort proof may need them at the algorithmic step).
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  The two-dash marker is reserved for
--   declarations whose body is the formalised LN content of the row.
--   This `variable` line is *statement-typing infrastructure* — it
--   binds the implicit parameters that the `IsTopologicalOrder` def
--   below relies on, but is not itself part of the LN definition.
--   Matches the convention in `CDMG.lean`, `CDMGNotation.lean`,
--   `Walks.lean`, `EdgeRelations.lean`, `CDMGRestrictions.lean`,
--   `Acyclicity.lean`, `CDMGTypes.lean`.
-- def_3_8 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_8 --- end helper

-- ref: def_3_8
-- `G.IsTopologicalOrder lt` asserts that the strict binary relation
-- `lt : Node → Node → Prop` is a *topological order* of the CDMG `G`,
-- i.e. (i) `lt` restricted to the vertex set `J ∪ V` is a strict total
-- order (irreflexive, transitive, trichotomous), and (ii) for every
-- parent–child pair `v ∈ Pa^G(w)` we have `lt v w` — parents precede
-- their children under `<`.
/-
LN tex (rewritten canonical statement for `def_3_8`):

  A *topological order* of `G` is a *strict* total order `<` on
  `J ∪ V` — i.e. a binary relation `<` on `J ∪ V` that is irreflexive,
  transitive, and satisfies trichotomy (`v < w`, `v = w`, or `w < v`
  for every `v, w ∈ J ∪ V`) — such that
    ∀ v, w ∈ J ∪ V :  v ∈ Pa^G(w)  ⟹  v < w.
-/
-- ## Design choice
--
-- *Predicate over an external ordering, not an existence claim.*
--   The LN reads "a topological order of `G` is a total order `<`
--   of `J ∪ V` such that …" — i.e. it characterises *which* orders
--   qualify, not whether one exists.  Mirroring this, the Lean
--   declaration is a `Prop`-valued predicate on `(G, lt)`:
--     `IsTopologicalOrder : CDMG Node → (Node → Node → Prop) → Prop`.
--   The downstream existence claim "an acyclic CDMG admits a
--   topological order" (`claim_3_2`) will be stated as
--   `G.IsAcyclic → ∃ lt, G.IsTopologicalOrder lt` — the existential is
--   *not* baked into this row's definition.  An alternative
--   "bundled" shape `structure TopologicalOrder (G) where lt + props`
--   was rejected on three grounds: (a) it would conflate the
--   *property* this row defines with the *witness data* that
--   `claim_3_2` will quantify over, breaking the LN's
--   property-vs-existence layering; (b) every consumer that just
--   wanted to *check* a candidate `lt` would have to package it into
--   a structure first, fighting the LN's reading; (c) a bundled
--   structure encourages downstream code to thread "the canonical
--   topological order" through a graph, but the LN never picks one —
--   multiple topological orders generally exist and the theory does
--   not privilege one.
--
-- *`lt : Node → Node → Prop` as an external argument, not a
--   typeclass `[LT Node]` or a structure field.*  Mathlib's
--   `[LT Node]` instance would force *exactly one* canonical `<` per
--   `Node` type — but a single `Node` type underlies *every* CDMG in
--   the codebase, and each CDMG may admit many different topological
--   orders; locking `<` to the type level would make the existence
--   claim of `claim_3_2` vacuous or false depending on the chosen
--   instance.  A typeclass `[CDMG.TopologicalOrder G]` would face the
--   same problem on the structure level (Lean's resolution forces
--   uniqueness).  An explicit `lt : Node → Node → Prop` argument
--   exposes the choice and lets `claim_3_2` quantify over it
--   existentially.
--
-- *Strict-total-order conjuncts unfolded inline, not Mathlib's
--   `IsStrictTotalOrder lt`.*  Mathlib's `IsStrictTotalOrder` class
--   asserts irreflexivity / transitivity / trichotomy *on the entire
--   ambient type `Node`*; ours must be restricted to `J ∪ V`.  Using
--   the typeclass would either (a) force `lt` to behave as a strict
--   total order on the *full* `Node` type — a stronger requirement
--   than the LN, ruling out perfectly valid orders that happen to
--   leave nodes outside `J ∪ V` unrelated — or (b) require a
--   restriction wrapper (a fresh subtype `↥(G.J ∪ G.V)` and a derived
--   relation), which would force every downstream use to coerce nodes
--   and relations across the subtype boundary.  Unfolding the three
--   conjuncts inline with `∀ v ∈ G, …` is the cleanest LN-faithful
--   form: the LN literally writes "for every `v, w ∈ J ∪ V`", and
--   `∀ v ∈ G, …` is the standard Lean rendering (via the
--   `Membership Node (CDMG Node)` instance from `def_3_2`).  A custom
--   helper `IsStrictTotalOrderOn (S : Finset Node) (lt) : Prop` was
--   considered and rejected as scope creep — no other row in the
--   chapter currently needs it, and bundling the three conjuncts
--   under a fresh name would obscure the LN's plain reading "strict
--   total order on `J ∪ V`".
--
-- *Three properties of `<` *plus* the parent-precedes conjunct —
--   four conjuncts in LN order.*  The LN's prose enumerates: (1)
--   irreflexive, (2) transitive, (3) trichotomous, (4) parents
--   precede.  We encode it as a four-fold `∧` in the same order.
--   Mirroring LN order keeps `obtain ⟨hi, htr, htri, hp⟩ := h`
--   downstream destructuring syntactically aligned with the LN
--   reading.  Lean's `∧` is right-associative, so this parses as
--   `h_irrefl ∧ (h_trans ∧ (h_tri ∧ h_parent))`; the
--   anonymous-constructor pattern `⟨_, _, _, _⟩` unpacks all four
--   on one line.
--
-- *Trichotomy disjunct order: `lt v w ∨ v = w ∨ lt w v` (Mathlib's
--   `Trichotomous` convention).*  Mathlib defines
--   `Trichotomous (r : α → α → Prop)` as `∀ a b, r a b ∨ a = b ∨ r b a`
--   — the equality case sits in the *middle* slot.  Adopting the
--   alternative order `lt v w ∨ lt w v ∨ v = w` would (i) force every
--   downstream destructure that mirrors Mathlib's
--   `rcases h with hlt | heq | hlt'` shape to flip alternatives, and
--   (ii) if a later proof ever lifts this predicate to a Mathlib
--   `Trichotomous` instance on a subtype `↥(G.J ∪ G.V)` (to reuse
--   strict-total-order lemmas), the disjunct shape would need
--   translating.  The LN's "`v < w`, `v = w`, or `w < v`" is
--   symmetric in disjunct order, so this is a free choice we spend
--   on Mathlib alignment.
--
-- *Parent implication: no explicit `v ∈ G`/`w ∈ G` guard.*  The
--   universal `∀ v w, v ∈ G.Pa w → lt v w` is well-typed without
--   guards because `def_3_5`'s `Pa G w := {u | u ∈ G ∧ (u, w) ∈ G.E}`
--   *already* forces (i) `v ∈ G` (= `v ∈ J ∪ V`) directly from the
--   `u ∈ G` conjunct of the set-builder body, and (ii) `w ∈ G` from
--   `def_3_1`'s `hE_subset : (u, w) ∈ G.E → u ∈ J ∪ V ∧ w ∈ V` (so
--   `w ∈ V ⊆ J ∪ V`).  Adding `v ∈ G → w ∈ G →` guards would be
--   redundant.  The LN's "for all `v, w ∈ J ∪ V`" prefix is what the
--   `Pa`-body already encodes, so the universal `∀ v w` form is both
--   LN-faithful in conclusion and stronger-looking in quantifier
--   scope; logically the two are equivalent.  Wording-check subtlety
--   `quantifier_domain_v_w_in_G_is_tuple_not_set` (the LN's literal
--   "for all `v, w ∈ G`" with `G` a 4-tuple) is resolved by reading
--   `v ∈ G` via `def_3_2` item~1 as `v ∈ J ∪ V`; the redundancy
--   above means the Lean encoding can drop the prefix without
--   semantic loss.
--
-- *No `v ≠ w` precondition on the parent implication, even though
--   `lt v v` is forbidden by irreflexivity.*  The LN's implication
--   reads `v ∈ Pa^G(w) ⟹ v < w` without case-splitting on `v = w`.
--   When `v = w` and `(v, v) ∈ G.E` (i.e.\ a directed self-loop is
--   present), the implication would force `lt v v` — which
--   contradicts irreflexivity.  So the existence of *any*
--   topological order entails the absence of directed self-loops on
--   nodes of `J ∪ V`, which is exactly the consequence
--   `def_3_6`'s `IsAcyclic` encodes (see `Acyclicity.lean`'s
--   "Consequence: no directed self-loops" paragraph).  This
--   matching constraint is *load-bearing* for `claim_3_2`'s "acyclic
--   iff topological order exists" direction: a topological order
--   exists ⟹ the graph is acyclic (via, among other things, no
--   self-loops).  Inserting a `v ≠ w` guard here would silently
--   weaken the predicate and break that direction of `claim_3_2`.
--
-- *`Pa G w` (`Set Node`), not `Finset Node` or a `(w, v) ∈ G.E`
--   spelling.*  Reuse of `def_3_5`'s `G.Pa w` keeps the chapter's
--   parent vocabulary uniform; downstream proofs of `claim_3_2` can
--   unfold `Pa` (one `unfold CDMG.Pa` step lands on
--   `{u | u ∈ G ∧ (u, w) ∈ G.E}`) when they need the literal edge
--   form, but the named `Pa` form keeps the LN-grep correspondence
--   intact.  Spelling the implication as `(v, w) ∈ G.E → lt v w`
--   would lose the `v ∈ G` witness baked into `Pa`'s body and would
--   require either re-deriving `v ∈ J ∪ V` from `hE_subset` at every
--   use site or weakening the LN-faithful parent reading.
--
-- *Scope choice: only the primary (strict-total-order) form is
--   formalised; the "Equivalent indexing form"
--   `J ∪ V = {v_1, …, v_K}` with `v_1 < … < v_K` is NOT a separate
--   declaration.*  The rewritten canonical tex spells out *both*
--   forms and proves them equivalent under finiteness; per the
--   manager-brief's "Design considerations" §4, we encode the primary
--   form only and leave the indexed form to a *separate downstream
--   theorem* (roughly `∃ K : ℕ, ∃ idx : Fin K → Node, …` shape) any
--   consumer can derive on demand — a finite strict total order is
--   `Equiv`-able to `Fin K` ordered by `<`, and `J ∪ V` is finite by
--   `def_3_1`'s `Finset`-valued `J, V`.  A future reader hunting for
--   the indexing form should look for that derived theorem, not for
--   a parallel predicate here.  Two
--   reasons: (a) introducing an `IsTopologicalOrderIndexed` parallel
--   predicate would invite spurious case-splits at every downstream
--   site over which form is in scope, while the LN treats the two as
--   logically identical "presentations" of one notion; (b) the
--   indexed form is essentially a `(Fin K → Node)` bijection plus an
--   order-respecting condition, and constructing the bijection
--   requires picking a specific enumeration — but the LN never picks
--   one, so any choice we make in Lean would be arbitrary and
--   inherited by every downstream consumer of the indexed form.
--   Sticking to the primary predicate keeps the API minimal.
--
-- *Mathlib re-use.*  `Membership Node (CDMG Node)` instance from
--   `def_3_2` (used by `∀ v ∈ G, …`).  `Set` and `∈` on `G.Pa w` come
--   from `def_3_5`.  No mathlib `IsStrictTotalOrder` / `LinearOrder`
--   / `Preorder` machinery: those are type-level, not
--   domain-restricted, and would over-commit `lt` on nodes outside
--   `J ∪ V` (see the typeclass discussion above).
--
-- *Downstream consumers.*  `claim_3_2` (the very next row in the LN)
--   states `G.IsAcyclic ↔ ∃ lt, G.IsTopologicalOrder lt`; its proof
--   destructures this four-conjunct shape both ways
--   (`obtain ⟨hi, htr, htri, hp⟩` for the ⟸ direction, anonymous
--   constructor for the ⟹ direction's witness construction).
--   Chapter 4 onwards (CBN factorisation, do-calculus, iSCMs) will
--   index over a topological order chosen from `claim_3_2`'s
--   existential, taking a single `(h : G.IsTopologicalOrder lt)`
--   hypothesis and destructuring the parent conjunct `hp` at the
--   point where the factorisation needs "every parent comes earlier
--   in the order".
-- def_3_8 -- start statement
def IsTopologicalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  (∀ v ∈ G, ¬ lt v v) ∧
  (∀ u ∈ G, ∀ v ∈ G, ∀ w ∈ G, lt u v → lt v w → lt u w) ∧
  (∀ v ∈ G, ∀ w ∈ G, lt v w ∨ v = w ∨ lt w v) ∧
  (∀ v w, v ∈ G.Pa w → lt v w)
-- def_3_8 -- end statement

end CDMG

end Causality
