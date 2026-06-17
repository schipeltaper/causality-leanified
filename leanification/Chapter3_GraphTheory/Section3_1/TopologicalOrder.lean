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
-- `G.IsTotalOrder lt` asserts that the strict binary relation
-- `lt : Node → Node → Prop` restricts to a *strict total order* on the
-- vertex set `J ∪ V` of `G`, i.e.\ (i) irreflexive on `J ∪ V`
-- (`¬ lt v v` for `v ∈ G`), (ii) transitive on `J ∪ V`
-- (`lt u v` and `lt v w` imply `lt u w` for `u, v, w ∈ G`), and (iii)
-- trichotomous on `J ∪ V` (`lt v w`, `v = w`, or `lt w v` for every
-- `v, w ∈ G`).  This is the LN's substantive sub-concept
-- "*total order of `J ∪ V`*" pulled out as its own named predicate so
-- downstream rows can carry it as an explicit type-level hypothesis.
/-
LN tex fragment (extracted from the rewritten canonical statement
file `def_3_8_TopologicalOrder.tex`):

  ... a *strict* total order `<` on `J ∪ V` -- i.e.\ a binary relation
  `<` on `J ∪ V` that is irreflexive, transitive, and satisfies
  trichotomy (`v < w`, `v = w`, or `w < v` for every `v, w ∈ J ∪ V`) ...
-/
-- ## Design choice
--
-- *Why a named helper predicate, separate from
--   `IsTopologicalOrder`.*  The LN reads "Let `<` be a *total order*
--   of `J ∪ V` such that ..." -- it treats "total order on `J ∪ V`"
--   as a named substantive sub-concept, mentioned in prose rather
--   than defined in its own `defmark` block.  Pulling the
--   total-order content out as its own predicate exposes the LN's
--   two-tier reading at the type level and gives downstream rows a
--   handle to refer to "just the total-order premise".  All three
--   signals from `formalize_definition_in_lean.md` §"Helper
--   predicates for substantive sub-concepts" are met:
--   (a) **referenced by spec** -- the rewritten canonical tex literally
--   writes "a *strict* total order `<` on `J ∪ V`" (see the LN tex
--   fragment above);
--   (b) **substantive content** -- three atomic conditions
--   (irreflexive, transitive, trichotomous), not a single one-liner;
--   (c) **reused by a downstream row** -- `def_3_9`'s `Pred` and
--   `PredLE` (`Predecessors.lean`) consume
--   `Pred^G_<(v) = {w ∈ J ∪ V ∣ w < v}`, which is meaningful for
--   *any* total order on `J ∪ V` (no parent-precedence required); ch.\
--   5's ID-algorithm chapter (id-algorithm.tex §"preceding Markov
--   blanket", lines 227-240) likewise slices `J ∪ V` into
--   `{w | w < v}`, `{v}`, `{w | v < w}` purely via the total-order
--   content, and ch.\ 5's factorisation step (id-algorithm.tex line
--   466) takes "the reverse topological order" -- an order-reversal
--   operation on the total-order content alone.  Without the helper,
--   every such consumer would either re-spell the three atomic
--   conditions or import the whole `IsTopologicalOrder` (silently
--   over-committing on the parent-precedence clause).
--
-- *Type-level home for `def_3_9`'s domain hypothesis.*  The LN's
--   `Pred^G_<(v)` is only well-defined when `<` is a total order on
--   `J ∪ V` -- without a named predicate to point at, `def_3_9` would
--   have to either re-spell the three atomic conditions in its own
--   signature or document the assumption only in prose.  Exposing
--   `IsTotalOrder` here lets `def_3_9` take
--   `(h : G.IsTotalOrder lt)` as an explicit hypothesis on
--   `Pred` / `PredLE`, anchoring the LN's domain restriction in
--   Lean's type contract rather than in side commentary.
--
-- *Strict reading of `<`: irreflexive, transitive, trichotomous.*
--   The LN's order symbol `<` is read strictly throughout, so the
--   three properties pin down a strict total
--   order rather than a `≤`-style order.  The rewritten canonical
--   tex makes this explicit by writing "*strict* total order" and
--   spelling out the trichotomy disjunct.  Wording-check subtlety
--   `equivalent_indexing_assumes_finite_node_set` is unaffected
--   (finiteness still holds via `def_3_1`'s `Finset`-valued
--   `J, V`); `quantifier_domain_v_w_in_G_is_tuple_not_set` is
--   resolved exactly as before via the `Membership Node (CDMG Node)`
--   instance from `def_3_2`.
--
-- *Domain `J ∪ V`, encoded via `∀ v ∈ G, …`.*  The
--   `Membership Node (CDMG Node)` instance from `def_3_2`
--   (`CDMGNotation.lean`) makes `v ∈ G` reduce to
--   `v ∈ G.J ∪ G.V`, so the three conjuncts quantify over the LN's
--   node set on the nose.  Restricting to `J ∪ V` (rather than the
--   ambient `Node` type) is load-bearing: the LN never asks `<` to
--   relate nodes outside `J ∪ V`, and Mathlib's
--   `IsStrictTotalOrder` typeclass would over-commit `lt` on the
--   whole `Node` type -- ruling out perfectly valid orders that
--   happen to leave non-`G` nodes unrelated, and tying the canonical
--   `<` to the type-level (the same uniqueness problem the
--   typeclass-rejection bullet below addresses).  A custom
--   `IsStrictTotalOrderOn (S : Finset Node) (lt) : Prop` was
--   considered and rejected: bundling the three conjuncts under a
--   fresh name would obscure the LN's plain "strict total order on
--   `J ∪ V`" reading without offering anything `∀ v ∈ G, …` does not
--   already.
--
-- *Trichotomy disjunct order: `lt v w ∨ v = w ∨ lt w v` (Mathlib's
--   `Trichotomous` convention).*  Mathlib's
--   `Trichotomous (r : α → α → Prop)` places the equality case in
--   the middle slot; we adopt that order so any future lift to a
--   `Trichotomous` instance on the subtype `↥(G.J ∪ G.V)` (or any
--   `rcases h with hlt | heq | hlt'` destructure mirroring Mathlib
--   convention) lines up without alternative-flipping.  The LN's
--   "`v < w`, `v = w`, or `w < v`" is symmetric in disjunct order,
--   so this is a free choice we spend on Mathlib alignment.
--
-- *Three-dash `--- start helper` markers, not the two-dash
--   `-- start statement`.*  `IsTotalOrder` is a *helper-for-statement*
--   in the row-worker sense: the row's primary LN content is
--   `IsTopologicalOrder` (which gets the two-dash statement markers
--   below); `IsTotalOrder` exists to support its definition and to
--   carry the LN's "let `<` be a total order" hypothesis through
--   downstream consumers.  The website builder pulls helper-marked
--   declarations alongside the main statement so the rendered
--   statement is self-contained.  Matches the helper-vs-statement
--   convention used throughout the chapter.
--
-- *`Prop`-valued predicate, not a `structure` / `class`.*
--   Multiple total orders may coexist on a fixed `G`, and an
--   `lt : Node → Node → Prop` plus `(h : G.IsTotalOrder lt)`
--   hypothesis lets the existence quantifier of `claim_3_2` (and
--   the chosen-order parameter of ch.\ 4 CBN factorisation, ch.\ 5
--   ID-algorithm) range over relations freely.  A bundled
--   `structure TotalOrder G where lt + h_irrefl + h_trans + h_total`
--   was rejected on three grounds: (a) it conflates the
--   *property* (`G.IsTotalOrder lt`) with *witness data* (`lt`
--   itself), (b) consumers wanting to *check* a candidate `lt`
--   would have to package it into a structure first, (c) it tempts
--   downstream code to single out "the canonical total order" the
--   LN never picks.  The same rationale rules out a bundled
--   `structure TopologicalOrder G` shape for `IsTopologicalOrder`
--   below.
--
-- *`def : Prop`, not a typeclass or structure.*  Beyond the
--   domain-restriction argument above, three further reasons rule
--   out a `class IsTotalOrderOn ...` or `instance : IsTotalOrder
--   ...` shape.  (a) **LN-faithfulness**: the LN's "total order of
--   `J ∪ V`" is a *property of a chosen relation*, not a typeclass
--   instance the type system resolves silently; a `def` returning
--   `Prop` is the closest Lean rendering of that prose reading.
--   (b) **No instance plumbing at every use site**: a class would
--   force every consumer (`def_3_9`'s `Pred`, ch.\ 4's CBN
--   factorisation, ch.\ 5's ID-algorithm, ch.\ 7's acyclification)
--   to either thread `[G.IsTotalOrder lt]` brackets through every
--   signature or rely on Lean's resolver to surface the witness --
--   neither matches the LN's pattern of *naming* the order
--   explicitly and quantifying over it.  (c) **No need to invent a
--   wrapper relation**: `lt` is already the bare `Node → Node →
--   Prop` the LN writes -- there is no subtype `↥(G.J ∪ G.V)` or
--   `Restricted lt` to define and pass around.  Reusing a Mathlib
--   typeclass would have required first manufacturing such a
--   wrapper, then proving an instance for it, then peeling the
--   wrapper back off at every use site that wants the raw `lt v w`
--   form the LN uses.  A `def : Prop` skips that round-trip.
--
-- *Mathlib re-use.*  `Membership Node (CDMG Node)` instance from
--   `def_3_2`.  No mathlib `IsStrictTotalOrder` / `LinearOrder` /
--   `Preorder` -- those are type-level, not domain-restricted, and
--   would over-commit `lt` on the whole `Node` type (see the domain
--   and typeclass-rejection discussions above).
--
-- *Downstream consumers.*  `def_3_9` (`Predecessors.lean`) takes
--   `(h : G.IsTotalOrder lt)` as an explicit hypothesis on
--   `Pred` / `PredLE`.  `claim_3_2`
--   (`AcyclicIffTopologicalOrder.lean`) accesses the total-order
--   content via the first projection of the nested
--   `IsTopologicalOrder` shape (`(h_topo : G.IsTopologicalOrder
--   lt).1 : G.IsTotalOrder lt`); its proof body destructures
--   further as `⟨h_irrefl, h_trans, h_total⟩`.  Ch.\ 4-10 consumers
--   that take a topological-order hypothesis and reach into the
--   total-order content (e.g.\ ch.\ 5's `Pred^G_<(v)` slicing,
--   ch.\ 5's factorisation reverse-ordering, ch.\ 7's
--   acyclification ordering on SCCs) all reuse this projection
--   pattern.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsTotalOrder
-- def_3_8 --- start helper
def IsTotalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  (∀ v ∈ G, ¬ lt v v) ∧
  (∀ u ∈ G, ∀ v ∈ G, ∀ w ∈ G, lt u v → lt v w → lt u w) ∧
  (∀ v ∈ G, ∀ w ∈ G, lt v w ∨ v = w ∨ lt w v)
-- def_3_8 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: IsTotalOrder

-- ref: def_3_8
-- `G.IsTopologicalOrder lt` asserts that the strict binary relation
-- `lt : Node → Node → Prop` is a *topological order* of the CDMG
-- `G`, i.e.\ (i) `G.IsTotalOrder lt` -- a strict total order on
-- `J ∪ V` (irreflexive, transitive, trichotomous; see the
-- `IsTotalOrder` block above) -- and (ii) for every parent-child
-- pair `v ∈ Pa^G(w)` we have `lt v w`: parents precede their
-- children under `<`.
/-
LN tex (rewritten canonical statement for `def_3_8`):

  A *topological order* of `G` is a *strict* total order `<` on
  `J ∪ V` -- i.e.\ a binary relation `<` on `J ∪ V` that is
  irreflexive, transitive, and satisfies trichotomy (`v < w`,
  `v = w`, or `w < v` for every `v, w ∈ J ∪ V`) -- such that
    ∀ v, w ∈ J ∪ V :  v ∈ Pa^G(w)  ⟹  v < w.
-/
-- ## Design choice
--
-- *Nested 2-conjunct shape: `IsTotalOrder ∧ parent-precedence`.*
--   The body packages the total-order conditions (irreflexive,
--   transitive, trichotomous on `J ∪ V`) into the helper predicate
--   `IsTotalOrder` above, and pairs that with the parent-precedence
--   clause.  This mirrors the LN's two-tier reading "Let `<` be a
--   *total order* of `J ∪ V` *such that* ... whenever
--   `v ∈ Pa^G(w)` we have `v < w`" (graphs.tex around the
--   topological-order `defmark` block): the LN names the
--   total-order premise as a substantive sub-concept and only then
--   layers the parent-precedence clause on top.  Destructure
--   patterns: `⟨⟨h_irrefl, h_trans, h_total⟩, h_topo⟩` in one step
--   or `⟨h_to, h_topo⟩` followed by destructuring `h_to`;
--   constructors mirror.  See the `IsTotalOrder` block above for
--   why the helper earns its own name.
--
-- *Predicate over an external ordering, not an existence claim.*
--   The LN reads "a topological order of `G` is a total order `<`
--   of `J ∪ V` such that ...", i.e.\ it characterises *which*
--   orders qualify, not whether one exists.  The Lean is a
--   `Prop`-valued predicate on `(G, lt)`, and `claim_3_2` (the very
--   next row) states `G.IsAcyclic ↔ ∃ lt, G.IsTopologicalOrder lt`
--   -- existence is at the use site, not baked into this definition.
--   Bundled-structure alternatives (`structure TopologicalOrder (G)
--   where lt + props`) were rejected on three grounds: (a)
--   conflates property with witness data; (b) forces consumers to
--   package a candidate `lt` into a structure just to *check* it
--   (fighting the LN's reading); (c) tempts downstream code to
--   single out "the canonical topological order" the LN never picks
--   (multiple typically coexist).
--
-- *`lt : Node → Node → Prop` as an explicit external argument, not
--   a typeclass `[LT Node]` or a structure field.*  Mathlib's
--   `[LT Node]` would force exactly one canonical `<` per `Node`
--   type -- but a single `Node` underlies every CDMG in the
--   codebase and each CDMG may admit many topological orders;
--   locking `<` to the type level would make `claim_3_2`'s
--   existential vacuous or false depending on the chosen instance.
--   A typeclass `[CDMG.TopologicalOrder G]` would face the same
--   Lean-resolution-forces-uniqueness problem on the structure
--   level.  An explicit relation argument exposes the choice and
--   lets `claim_3_2` quantify over it.
--
-- *Parent implication: no `v ≠ w` guard, no `v ∈ G` / `w ∈ G`
--   guard.*  (i) `def_3_5`'s
--   `Pa G w := {u | u ∈ G ∧ (u, w) ∈ G.E}` already forces
--   `v ∈ G` from the set-builder body and `w ∈ G` from `def_3_1`'s
--   `hE_subset`, so `v ∈ G → w ∈ G →` guards would be redundant.
--   This is the working-phase wording-check subtlety
--   `quantifier_domain_v_w_in_G_is_tuple_not_set`: the LN's literal
--   "for all `v, w ∈ G`" with `G` a 4-tuple is shorthand for
--   `v, w ∈ J ∪ V`, and parenthood already entails that membership
--   for both endpoints -- so the unrestricted `∀ v w, v ∈ G.Pa w
--   → lt v w` is both LN-faithful in conclusion and *stronger-looking*
--   only in quantifier scope (logically the two forms agree).
--   (ii) Omitting the `v ≠ w` guard is *load-bearing* for
--   `claim_3_2`: when `v = w` and a directed self-loop
--   `(v, v) ∈ G.E` is present, the parent implication forces
--   `lt v v`, contradicting irreflexivity (the first conjunct of
--   `IsTotalOrder`).  So the existence of any topological order
--   entails the absence of directed self-loops on `J ∪ V`, which
--   is exactly what `def_3_6`'s `IsAcyclic` encodes; this matching
--   constraint drives the `⇐` direction of `claim_3_2`.  Inserting
--   a `v ≠ w` guard here would silently weaken the predicate and
--   break that direction.
--
-- *`Pa G w` (`Set Node`), not `Finset Node` or `(w, v) ∈ G.E`.*
--   Reuse of `def_3_5`'s parent vocabulary keeps the chapter
--   uniform; downstream proofs can `unfold CDMG.Pa` when they need
--   the literal edge form.
--   Spelling the implication as `(v, w) ∈ G.E → lt v w` would lose
--   the `v ∈ G` witness baked into `Pa`'s body and would require
--   re-deriving `v ∈ J ∪ V` from `hE_subset` at every use site, or
--   weaken the LN-faithful parent reading.
--
-- *Scope choice: primary form only; indexed form is a downstream
--   theorem.*  The rewritten canonical tex spells out both the
--   strict-total-order form and
--   the "`J ∪ V = {v_1, …, v_K}` with `v_1 < … < v_K`" indexed
--   form, and proves them equivalent under finiteness.  We encode
--   the primary form only; any consumer that needs the indexed
--   form derives it on demand (a finite strict total order is
--   `Equiv`-able to `Fin K` ordered by `<`, and `J ∪ V` is finite
--   by `def_3_1`'s `Finset`-valued `J, V`).  This is exactly the
--   working-phase wording-check subtlety
--   `equivalent_indexing_assumes_finite_node_set`: the LN's
--   "Equivalently ..." clause is *only* an equivalence under
--   finiteness (any strict total order on a finite set has order
--   type a finite ordinal and so can be presented as
--   `v_1 < ... < v_K`); on an infinite node set the primary form
--   is still meaningful but the indexing form would either fail or
--   need extra conditions.  Formalising the primary form keeps
--   `IsTopologicalOrder` general (no implicit finiteness baked
--   into its type contract); finiteness for the indexed
--   reformulation is available *when needed* via `def_3_1`'s
--   `Finset`-valued `J, V`, so no consumer is shut out.  A parallel
--   `IsTopologicalOrderIndexed` predicate would invite spurious
--   case-splits at every downstream site over which form is in
--   scope, while the LN treats the two as logically identical
--   "presentations" of one notion (under finiteness).
--
-- *Mathlib re-use.*  `Membership Node (CDMG Node)` instance from
--   `def_3_2` (used inside `G.IsTotalOrder lt`'s conjuncts), `Set`
--   and `∈` on `G.Pa w` from `def_3_5`.  No mathlib
--   `IsStrictTotalOrder` / `LinearOrder` / `Preorder` for the
--   reasons spelled out in the `IsTotalOrder` block above.
--
-- *Downstream consumers.*  `def_3_9`
--   (`Predecessors.lean`) takes `(h : G.IsTotalOrder lt)` as an
--   explicit type-level hypothesis on `Pred` / `PredLE`; from a
--   topological-order witness this is reached via the first
--   projection `(h_topo : G.IsTopologicalOrder lt).1`.  `claim_3_2`
--   (`AcyclicIffTopologicalOrder.lean`) destructures the nested
--   2-conjunct shape both ways (`⟨⟨h_irrefl, h_trans, h_total⟩,
--   h_topo⟩` on inputs; the symmetric nested anonymous constructor
--   on outputs).  Ch.\ 4 onwards (CBN factorisation, ID-algorithm,
--   σ / d-separation, iSCMs) typically takes
--   `(h : G.IsTopologicalOrder lt)` and projects either via `.1`
--   for the total-order content (e.g.\ to feed
--   `Pred^G_<(v) := {w ∈ G | lt w v}` to `def_3_9` or to slice
--   `J ∪ V` into `{w | w < v}`, `{v}`, `{w | v < w}` for an
--   id-separation argument) or via `.2` for the parent-precedence
--   clause (e.g.\ when factorising a joint kernel into mechanism
--   conditionals).
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsTopologicalOrder
-- def_3_8 -- start statement
def IsTopologicalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  G.IsTotalOrder lt ∧ (∀ v w, v ∈ G.Pa w → lt v w)
-- def_3_8 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsTopologicalOrder

end CDMG

namespace refactor_CDMG

-- ## Design choice — statement context (refactor twin)
--
-- Three-dash `--- start helper` markers match the convention used
-- across `CDMG.lean`, `CDMGNotation.lean`, `Walks.lean`,
-- `EdgeRelations.lean`, `CDMGRestrictions.lean`, `Acyclicity.lean`,
-- `CDMGTypes.lean`, and `FamilyRelationships.lean` for the
-- `variable` line that binds the implicit parameters into the
-- predicates wrapped below.  Both `Node : Type*` and
-- `[DecidableEq Node]` are inherited verbatim from `def_3_1`'s
-- refactor twin (`refactor_CDMG`): the `Membership Node
-- (refactor_CDMG Node)` instance from `def_3_2`'s refactor twin
-- (`refactor_instMembership` in `CDMGNotation.lean`) — driving the
-- `v ∈ G` quantifier scope below — reduces to `Finset.mem` on
-- `G.J ∪ G.V`, which needs `DecidableEq Node`; the
-- `G.refactor_Pa w : Set Node` reference in
-- `refactor_IsTopologicalOrder` reaches back to `def_3_5`'s
-- refactor twin (`refactor_Pa` in `FamilyRelationships.lean`)
-- whose body `{u | u ∈ G ∧ (u, w) ∈ G.E}` likewise depends on
-- `DecidableEq` through `Finset` membership.
-- def_3_8 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_8 --- end helper

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsTotalOrder (was: refactor_IsTotalOrder)
-- ref: def_3_8 — refactor twin
-- `G.refactor_IsTotalOrder lt` asserts that the strict binary
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
-- `refactor_instMembership` instance reducing `v ∈ G` to
-- `v ∈ G.J ∪ G.V`, and `equivalent_indexing_assumes_finite_node_set`
-- is unaffected (finiteness still holds via `def_3_1`'s
-- `Finset`-valued `J, V` — both fields are unchanged on
-- `refactor_CDMG`).
--
-- *Upstream-type shifts (and only those).*
--   `CDMG Node → refactor_CDMG Node`
-- No other change.  In particular, the `∀ v ∈ G, …` quantifier
-- ports verbatim because the `refactor_instMembership` instance
-- (`CDMGNotation.lean`'s refactor twin of `def_3_2`) gives the same
-- `v ∈ G.J ∪ G.V` reduction on `refactor_CDMG Node` as the original
-- `instMembership` does on `CDMG Node`.  This predicate does not
-- touch the `L` field, so the `Finset (Node × Node) → Finset (Sym2
-- Node)` retyping at root `def_3_1` does not propagate here.
-- def_3_8 --- start helper
def refactor_IsTotalOrder (G : refactor_CDMG Node) (lt : Node → Node → Prop) : Prop :=
  (∀ v ∈ G, ¬ lt v v) ∧
  (∀ u ∈ G, ∀ v ∈ G, ∀ w ∈ G, lt u v → lt v w → lt u w) ∧
  (∀ v ∈ G, ∀ w ∈ G, lt v w ∨ v = w ∨ lt w v)
-- def_3_8 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: IsTotalOrder

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsTopologicalOrder (was: refactor_IsTopologicalOrder)
-- ref: def_3_8 — refactor twin
-- `G.refactor_IsTopologicalOrder lt` asserts that the strict binary
-- relation `lt : Node → Node → Prop` is a *topological order* of
-- the CDMG `G`, i.e.\ (i) `G.refactor_IsTotalOrder lt` — a strict
-- total order on `J ∪ V` (irreflexive, transitive, trichotomous;
-- see the `refactor_IsTotalOrder` block above) — and (ii) for every
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
-- via `def_3_5`'s `refactor_Pa`).  The mathematical design — the
-- nested 2-conjunct shape `IsTotalOrder ∧ parent-precedence`, the
-- predicate-not-existence shape, the explicit-`lt`-argument
-- choice, the deliberate no-guard form of the parent implication
-- (load-bearing for `claim_3_2`'s `⇐` direction: a directed
-- self-loop `(v, v) ∈ G.E` would force `lt v v`, contradicting
-- irreflexivity), and the primary-form-only scope (no parallel
-- indexed predicate) — is **unchanged**.  Both wording-check
-- subtleties remain resolved exactly as before
-- (`quantifier_domain_v_w_in_G_is_tuple_not_set` via the
-- `refactor_instMembership` instance,
-- `equivalent_indexing_assumes_finite_node_set` via
-- `refactor_CDMG`'s unchanged `Finset`-valued `J, V`).
--
-- *Upstream-type shifts (and only those).*
--   `CDMG Node       → refactor_CDMG Node`
--   `G.IsTotalOrder  → G.refactor_IsTotalOrder`  (the cross-call
--                      to the helper above, retyped onto the
--                      refactor namespace)
--   `G.Pa            → G.refactor_Pa`  (the per-vertex parent set
--                      from `def_3_5`'s refactor twin in
--                      `FamilyRelationships.lean`; its body
--                      `{u | u ∈ G ∧ (u, w) ∈ G.E}` is unchanged
--                      because `G.E`'s carrier
--                      `Finset (Node × Node)` is unchanged by the
--                      refactor — only the `L`-side of `def_3_1`
--                      retyped to `Finset (Sym2 Node)`).
-- No other change.  The unrestricted `∀ v w, v ∈ G.refactor_Pa w
-- → lt v w` quantifier reads identically to the original: the
-- inner `v ∈ G` and `w ∈ G` witnesses still come from
-- `refactor_Pa`'s set-builder body / `refactor_CDMG.hE_subset`,
-- and the LN's "for all `v, w ∈ G`" is again shorthand for
-- `v, w ∈ J ∪ V`.  Neither this predicate nor its constituents
-- `refactor_IsTotalOrder` and `refactor_Pa` reach into the `L`
-- field, so the `Finset (Node × Node) → Finset (Sym2 Node)`
-- retyping at root `def_3_1` does not propagate here.
-- def_3_8 -- start statement
def refactor_IsTopologicalOrder (G : refactor_CDMG Node) (lt : Node → Node → Prop) : Prop :=
  G.refactor_IsTotalOrder lt ∧ (∀ v w, v ∈ G.refactor_Pa w → lt v w)
-- def_3_8 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsTopologicalOrder

end refactor_CDMG

end Causality
