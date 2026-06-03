import Chapter3_GraphTheory.Section3_1.FamilyRelationships

namespace Causality

/-!
# Topological order of a CDMG: `def_3_8`

This file formalises the foundational notion of a *topological order*
of a CDMG.  Together with `def_3_6`'s acyclicity, topological order is
the single most load-bearing chapter-3 concept for the rest of the
lecture notes: `claim_3_2` (the very next claim in this section) proves
the fundamental "acyclic ⟺ admits a topological order" equivalence;
`def_3_9` (predecessors) takes a topological order as an explicit
parameter to define `Pred^G_<(v) := {w ∈ G | w < v}`; the intervention-
on-graphs operations of `def_3_10 / def_3_11 / def_3_14 / def_3_15`
each carry an "extend / refine / restrict the topological order"
companion lemma; and chapter 8's iSCM solution-uniqueness proposition
`Prp:acyclic_scms_are_simple` runs by induction on a topological order
extracted from acyclicity, with the solution function at `v` depending
on the values at `Pred^G_<(v)`.

## LN block (verbatim)

```
Let G=(J,V,E,L) be a CDMG.
A *topological order* of G is a total order < of J ∪ V such that for
all v,w ∈ G:
  v ∈ Pa^G(w) ⟹ v < w.
Equivalently, it can be described as an indexing of the nodes
J ∪ V = {v_1, ..., v_K} where parents always precede their children.
```

The "Equivalently, … indexing" sentence is a *theorem*, not an
alternative primary definition: any strict total order on a finite
carrier admits a unique increasing enumeration (the standard
Mathlib-derivable correspondence between `Finset.sort` and a
`LinearOrder`).  We encode only the primary form (relation `<`);
the indexing form is recoverable on demand by sorting `G.J ∪ G.V`
under `<` and is therefore not given its own definition here.

## LN wording-check (working phase): `NO_SUBTLETIES`

The working-phase wording-check returned `NO_SUBTLETIES` — the
definition is clean and standard, with no ambiguities, corner cases,
internal inconsistencies, or arbitrariness worth registering globally.
The four candidates the wording-check considered (all dismissed) were:

1. "$v, w \in G$" as sloppy notation for `v, w ∈ J ∪ V` (the LN
   conflates the tuple `G` with the carrier `J ∪ V`).  Standard graph-
   theory abuse-of-notation; we use the `Membership` instance of
   `def_3_2` item 1 (`CDMGNotation.lean`) so `v ∈ G` unfolds to
   `v ∈ G.J ∪ G.V` literally.
2. Corner cases (empty `J ∪ V` vacuously satisfied; singleton trivial;
   cyclic graph admits *no* topological order; self-loops on
   `v ∈ V` force `v < v` violating irreflexivity — i.e. cyclic graphs
   correctly have no topological order under our encoding).
3. Equivalence with the indexing form requires finiteness of
   `J ∪ V` — standard, already enforced by `CDMG.J / V : Finset Node`
   (def_3_1).
4. Bidirected edges (`L`) impose NO ordering constraint; only `Pa^G`
   (directed parents) appears in the implication.  Intentional and
   standard.

## Core encoding choices (load-bearing across this file)

* **Predicate shape, NOT a bundled structure.**
  `IsTopologicalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop`
  is parametric in the relation `lt`, not a record bundling
  `(lt, irrefl, trans, trichotomy, parents_precede)` as fields.
  Justification: every downstream consumer of this row
  (`def_3_9` Predecessors `Pred^G_<(v)`, `claim_3_2`, `def_3_13`-style
  "extend the topological order" intervention lemmas, the chapter-8
  iSCM solution-uniqueness proof) takes the relation `<` as an
  explicit parameter, NOT a structure.  In particular, `def_3_9`'s
  literal LN reads "Let G be a CDMG and `<` a total order of J ∪ V";
  parametricity is part of the LN's surface form.  A bundled
  `structure TopologicalOrder G` would force every consumer to write
  `.lt`-field projections at each use site.  Detailed comparison in
  the per-declaration design blocks below; the workspace scratchpad
  `workspace_def_3_8.md` records the worker's decision rationale.

* **Carrier: `lt : Node → Node → Prop` on the whole `Node` type,
  axioms restricted to `v ∈ G`.**  Per the manager's brief and parallel
  to how `def_3_5` family relations let out-of-graph vertices fall
  through to empty / vacuous behaviour, the relation is unconstrained
  outside the carrier `G.J ∪ G.V`; only inside the carrier do
  irreflexivity, transitivity, and trichotomy fire.  Subtype encoding
  `{v // v ∈ G.J ∪ G.V}` was rejected: every consumer would pay a
  subtype-coercion overhead at every walk-step / Pred lookup, and
  Mathlib's `LinearOrder` typeclass machinery is not the natural fit
  here (we want LN-faithful constraints over a *graph carrier*, not
  a free-standing type).

* **Helper `IsTotalOrderOn G lt` (three-dash helper marker) factors
  out the "total order of J ∪ V" clause.**  The LN reads "is a total
  order < of J ∪ V *such that* parents precede children" — two
  distinct constraints joined by "such that".  Factoring the
  total-order half into its own predicate (`G.IsTotalOrderOn lt`)
  matches that surface structure, lets `def_3_9` reuse the same
  helper for its "Let `<` be a total order of J ∪ V" hypothesis
  (the same notion appears in both rows), and keeps each conjunct
  small enough to be understood / rewritten / unfolded independently.

* **Strict order `<`, not `≤`.**  The LN uses strict `<`.  Encoded
  as `lt : Node → Node → Prop`; the connection to a non-strict
  `≤` (if ever needed) is the standard `lt ⊔ Eq` derivation.

* **Three-axiom total order (irrefl + trans + trichotomy).**
  Asymmetry (`lt v w → ¬ lt w v`) is derivable from irrefl + trans
  and not stated as a separate axiom.  Trichotomy uses Mathlib's
  `IsTrichotomous` form `lt v w ∨ v = w ∨ lt w v` (inclusive
  disjunction); exclusivity follows from irrefl + asymmetry, so the
  three-axiom form is logically equivalent to the four-axiom
  "irrefl + asym + trans + connex" form but more compact.
-/

namespace CDMG

variable {Node : Type*} [DecidableEq Node]

-- ref: def_3_8 (supporting helper — "total order of J ∪ V")
--
-- `G.IsTotalOrderOn lt` says that the relation `lt : Node → Node → Prop`
-- is a *strict total order* when restricted to the carrier `G.J ∪ G.V`
-- (i.e. the vertices `v ∈ G` per the `Membership` instance from
-- `def_3_2` item 1, `CDMGNotation.lean`).  Three axioms:
--
-- (a) irreflexivity on the carrier: `∀ v ∈ G, ¬ lt v v`;
-- (b) transitivity on the carrier: `lt u v → lt v w → lt u w` for
--     `u, v, w ∈ G`;
-- (c) trichotomy on the carrier: for any `v, w ∈ G`,
--     `lt v w ∨ v = w ∨ lt w v`.
--
-- This is the LN's literal "a total order `<` of `J ∪ V`" — the first
-- of the two clauses in the topological-order definition (`def_3_8`).
-- Outside the carrier (vertices not in `G.J ∪ G.V`) `lt` is
-- unconstrained, parallel to how `def_3_5`'s family-relation sets
-- treat out-of-graph vertices vacuously.
/-
LN tex (`def_3_8`, first clause):

  A *topological order* of $G$ is a total order $<$ of $J \cup V$ such
  that for all $v,w \in G$ … [parents-precede-children clause].

The literal "total order of $J \cup V$" is what this helper formalises;
the parents-precede-children clause is folded into the main
`IsTopologicalOrder` below.

The same notion is used parametrically by `def_3_9` (Predecessors),
which states "Let G be a CDMG and `<` a total order of J ∪ V" as its
hypothesis.  Factoring out `IsTotalOrderOn` here lets `def_3_9` reuse
it directly.
-/
-- ## Design choice
--
-- *Why a separate helper, not inlined into `IsTopologicalOrder`.*  The
--   LN explicitly separates the two clauses ("a total order … *such
--   that* parents precede children"), and `def_3_9` will need the
--   total-order clause *without* the parents-precede-children
--   clause (its hypothesis is just "let `<` be a total order of
--   J ∪ V").  A named helper keeps the two notions composable.  The
--   alternative — inlining the three axioms into `IsTopologicalOrder`
--   as four `∧`-conjuncts (three for the total-order part plus the
--   parents-precede-children clause) — was rejected on two grounds:
--   (i) it duplicates the three axioms when `def_3_9` is written,
--   forcing a refactor at that row; (ii) it loses the LN's literal
--   surface decomposition.
--
-- *Helper-marker (`--- start helper`, three dashes).*  Per the worker
--   prompt: `IsTotalOrderOn` is required for `IsTopologicalOrder`'s
--   statement to type-check, so it is a "statement support" helper
--   and gets the three-dash marker.  The website builder pulls it
--   alongside the main statement so the rendered statement is
--   self-contained.
--
-- *Why `∀ v ∈ G, ¬ lt v v` for irreflexivity, not `∀ v, ¬ lt v v`.*
--   The LN's "total order *of J ∪ V*" restricts every order axiom to
--   the carrier `J ∪ V`.  Imposing irreflexivity outside the carrier
--   would over-constrain the relation: `lt j₁ j₂` for nodes
--   `j₁, j₂ ∉ G.J ∪ G.V` is vacuous data — `IsTopologicalOrder` does
--   not look at it — but the bounded-forall form makes that vacuity
--   explicit.  Same pattern as `def_3_6`'s `∀ v ∈ G, ¬ ∃ p, …`.
--
-- *Why `∀ ⦃u v w⦄, u ∈ G → v ∈ G → w ∈ G → …` for transitivity.*
--   Three explicit membership hypotheses, instance-implicit binders
--   on the vertices.  The instance-implicit `⦃⦄` lets consumers
--   write `h.trans hu hv hw hluv hlvw` without spelling out
--   `u v w` at every call site (Lean unifies them from the
--   membership / `lt`-applied hypotheses).  Same shape as Mathlib's
--   `Trans.trans` instance-implicit binders.  An alternative
--   `∀ u v w ∈ G, lt u v → lt v w → lt u w` (triple bounded-forall)
--   was considered and rejected: the triple desugaring through
--   `∀ u, u ∈ G → ∀ v, v ∈ G → …` reads awkwardly and the three
--   membership hypotheses are *un-binnable* between the lt-applied
--   premises and the binder — splitting them out as separate
--   `→`-arrows makes the destructuring direct.
--
-- *Why trichotomy spelled `lt v w ∨ v = w ∨ lt w v`.*  Mirrors
--   Mathlib's `IsTrichotomous` form (`Mathlib/Order/RelClasses`).
--   Three explicit disjuncts; exclusivity (mutual exclusion of the
--   disjuncts) follows from irrefl + asymmetry, derivable but not
--   stated.  The "connex" alternative `∀ v w, v ≠ w → lt v w ∨ lt w v`
--   is logically equivalent to "trichotomy + irrefl" but requires
--   an extra `v ≠ w` hypothesis at every use site; we pick
--   trichotomy for ergonomics.  No `Decidable lt` instance is
--   assumed — trichotomy is a *constructive* disjunction at the
--   `Prop` level, and downstream proofs that need decidability
--   (chapter 8 iSCM iteration to extract a concrete enumeration) get
--   it via `Classical.dec` or via the indexing form
--   recoverable from `claim_3_2`'s forward direction.
--
-- *Asymmetry is not stated.*  `lt v w → ¬ lt w v` follows from
--   `irrefl` + `trans`: from `lt v w` and `lt w v` we get
--   `lt v v` via `trans hu hv hu hluv hlwv`, contradicting `irrefl
--   hu`.  Stating asymmetry as a fourth axiom would be redundant.
--
-- *Mathlib re-use.*  No direct fit.  `IsStrictTotalOrder lt`
--   (`Mathlib.Order.RelClasses`) is the closest match — it bundles
--   `IsTrichotomous`, `IsTrans`, `IsIrrefl` — but those typeclasses
--   are *unrestricted* (quantify over the whole `Node` type).  We
--   want axioms restricted to the carrier `G.J ∪ G.V`, so we roll
--   our own three-conjunct predicate.  An alternative encoding
--   "package `lt` as `LinearOrder` on the subtype `{v // v ∈ G.J ∪
--   G.V}`" was rejected — it would let Mathlib's typeclass machinery
--   fire, but every downstream consumer (`Pred^G_<`, walk-on-an-
--   order arguments, intervention-extends-the-order lemmas) would
--   have to coerce vertices to/from the subtype.  The
--   `Node → Node → Prop` carrier-axiom shape is the right surface
--   for chapter-3's downstream graph-theoretic / walk-level
--   reasoning.
-- def_3_8 --- start helper
def IsTotalOrderOn (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  (∀ v ∈ G, ¬ lt v v) ∧
  (∀ ⦃u v w : Node⦄, u ∈ G → v ∈ G → w ∈ G → lt u v → lt v w → lt u w) ∧
  (∀ ⦃v w : Node⦄, v ∈ G → w ∈ G → lt v w ∨ v = w ∨ lt w v)
-- def_3_8 --- end helper

-- ref: def_3_8
--
-- `G.IsTopologicalOrder lt` holds when the relation `lt` is a strict
-- total order on the carrier `G.J ∪ G.V` (the first clause —
-- `IsTotalOrderOn G lt`) AND every directed-parent pair `v ∈ Pa^G(w)`
-- is ordered `lt v w` (the second clause — parents precede children).
--
-- Encoded literally as the LN's two-clause conjunction.  The LN's
-- equivalent "indexing" formulation
--   `J ∪ V = {v_1, ..., v_K}` with parents preceding children
-- is a *theorem* about strict total orders on finite carriers (it
-- is just the sort enumeration of `G.J ∪ G.V` under `lt`), not an
-- alternative primary definition — see the file-level docstring.
/-
LN tex (verbatim, `def_3_8`):

  Let $G=(J,V,E,L)$ be a CDMG.
  A *topological order* of $G$ is a total order $<$ of $J \cup V$ such
  that for all $v,w \in G$:
  \[ v \in \Pa^G(w) \; \implies \; v < w.\]
  Equivalently, it can be described as an indexing of the nodes
  $J \cup V = \{v_1,\dots,v_K\}$ where parents always precede their
  children.
-/
-- ## Design choice
--
-- *Why a predicate `IsTopologicalOrder G lt`, not a bundled structure
--   `TopologicalOrder G`.*  The single most consequential decision in
--   this file.  The manager flagged both shapes as defensible and asked
--   the worker to weigh them; the downstream-usage survey (chapters
--   3 + 5 + 8 + 11) tipped the balance toward the predicate form.
--   Concretely:
--   1. *`def_3_9` (Predecessors) is parametric in `<` directly.*  The
--      next definition row after this one reads "Let G be a CDMG and
--      `<` a total order of J ∪ V.  Pred^G_<(v) := {w ∈ G | w < v}"
--      — `<` is a parameter to `Pred`, NOT a structure projection
--      `topo.lt`.  Matching this paradigm requires `IsTopologicalOrder`
--      to be parametric in `lt`.
--   2. *Downstream operations work on the relation level.*
--      `claim_3_13`: "Any topological order of G can be extended to
--      one for `G_{do(I_W)}`, e.g. by putting all the `I_w` nodes
--      first" — extension *of the relation*.  `claim_3_6 / claim_3_11`
--      (node splitting): re-indexes via fractional indices `v_j^0 :=
--      j - 1/3`, `v_j^1 := j + 1/3`, then re-sorts — *operates on the
--      indexing reading of the relation*.  `claim_3_16`
--      (marginalisation): "a topological order of G induces one on
--      G^{∖W} by just ignoring the nodes from W" — *restriction of
--      the relation*.  All three are natural under the predicate
--      form (construct a new relation, prove the predicate holds);
--      the structure form would force unpack / repack ceremony.
--   3. *Chapter-8 iSCM solution-uniqueness destructures `lt`
--      parametrically.*  `Prp:acyclic_scms_are_simple` unpacks
--      `∃ <, IsTopologicalOrder G <`, binds `<`, then iterates: for
--      each `v`, `f_v` depends on `Pred^G_<(v)`.  The bound `<` is
--      used parametrically through `Pred`; a structure encoding
--      would force a `.lt`-field projection at every `Pred` call
--      site.
--   4. *Parallel to existing Section 3.1 paradigm.*  `IsAcyclic`
--      (`def_3_6`, Acyclicity.lean), `IsCADMG / IsDMG / IsADMG / IsCDG
--      / IsDG / IsCDAG / IsDAG` (`def_3_7`, CDMGTypes.lean) are all
--      `Prop`-valued predicates on `G` (or `G` plus extra
--      arguments).  Encoding `IsTopologicalOrder` as a predicate
--      parametric in `lt` mirrors that paradigm, with `lt` as the
--      "extra argument" beyond `G`.
--   5. *The LN's noun phrasing is honoured by the existential.*  The
--      LN's "a topological order of G" reads as
--      `∃ lt, G.IsTopologicalOrder lt` (which is exactly the form
--      `claim_3_2` will use: `G.IsAcyclic ↔ ∃ lt, G.IsTopologicalOrder
--      lt`).  No expressive power lost vs the structure form's
--      `Nonempty (TopologicalOrder G)`.
--   The manager's three arguments *for* the structure form were:
--   (a) "the LN calls it 'a topological order' as a noun"; but the
--   same is true for "an acyclic CDMG" and we used a predicate
--   there.  (b) "the existential `∃ topo : TopologicalOrder G` reads
--   more naturally"; but `∃ lt, G.IsTopologicalOrder lt` reads
--   identically and is more LN-faithful (the LN's `<` is a
--   *relation*, not a record).  (c) "the iSCM destructure benefits
--   from named fields"; but the *data* is just `lt : Node → Node →
--   Prop`, and `obtain ⟨lt, hlt⟩ := h_exists_topo` is the destructure
--   — no named-fields gain.  The decision was therefore the
--   predicate form.
--
-- *Why parametric in `lt : Node → Node → Prop`, not the subtype
--   `{v // v ∈ G.J ∪ G.V}` with a `LinearOrder` instance.*  Three
--   reasons.
--   1. *LN-faithfulness.*  The LN writes "a total order `<` of `J ∪ V`"
--      — i.e. `<` is read as a relation on the ambient `Node` type
--      with constraints restricted to `J ∪ V`, not a relation on a
--      separate subtype.  Subtype coercion at every use site (every
--      `Pa^G(v)` lookup, every walk-step, every `Pred^G_<` call)
--      would be visible noise vs the LN.
--   2. *Composition with `def_3_5` family relations.*  `Pa^G(v) :
--      Finset Node` lives in `Finset Node`, not `Finset {v // v ∈ G.J
--      ∪ G.V}`.  The parents-precede-children clause uses `Pa^G(w)`
--      directly; making `lt` live on a subtype would force a
--      subtype-`Finset` lift at every use of `Pa`.
--   3. *Mathlib's `LinearOrder` typeclass machinery doesn't compose.*
--      `LinearOrder {v // v ∈ G.J ∪ G.V}` would require the subtype
--      to be inhabited (otherwise `LinearOrder` on empty is trivial
--      but the inhabited assumption breaks the empty-CDMG case
--      which `def_3_1` admits).  Encoding axioms restricted to the
--      carrier on `Node → Node → Prop` sidesteps this and keeps the
--      empty CDMG vacuously satisfying any topological order
--      predicate (with `lt` arbitrary).
--   The manager's brief reached the same conclusion ("I think the
--   `Node → Node → Prop` shape wins; check that conclusion against
--   the actual downstream usage you find") — the downstream survey
--   confirmed it.
--
-- *Why the helper `IsTotalOrderOn G lt`, not three inline conjuncts.*
--   Discussed above the helper declaration; the LN's surface form
--   ("a total order ... such that parents precede children") is a
--   two-clause split, and `def_3_9` will reuse the
--   total-order-half independently.
--
-- *Why `∀ ⦃v w⦄, v ∈ G.Pa w → lt v w`, not
--   `∀ v w, v ∈ G → w ∈ G → v ∈ G.Pa w → lt v w`.*  The membership
--   preconditions are automatic from `v ∈ G.Pa w`:
--   - `v ∈ G.Pa w` unfolds to `v ∈ (G.J ∪ G.V).filter (·, w) ∈ G.E`,
--     so `v ∈ G.J ∪ G.V`, i.e. `v ∈ G`.
--   - `(v, w) ∈ G.E` forces `w ∈ G.V` via `G.hE_subset`, so `w ∈ G`.
--   Restating `v ∈ G` and `w ∈ G` as separate hypotheses would
--   duplicate information the `Pa` antecedent already carries.  The
--   `IsTotalOrderOn` axioms *do* need explicit `v ∈ G` hypotheses
--   because they quantify over arbitrary `lt`-related pairs, not
--   over edge endpoints; here, the LN's "v ∈ Pa^G(w)" already
--   restricts to the carrier.
--
-- *Why `∀ ⦃v w⦄` instance-implicit, not `∀ {v w}` or `∀ v w`.*  Same
--   as the `IsTotalOrderOn` axioms: instance-implicit lets consumers
--   write `htop.2 hPa` without specifying `v` and `w` explicitly
--   (Lean unifies them from the `Pa`-applied premise).  Regular
--   implicit `{}` would behave similarly in most use cases but is
--   more eager to elaborate, occasionally causing unification
--   failures at use sites that pass `hPa` through `simp` /
--   `rcases` machinery; the instance-implicit `⦃⦄` defers
--   elaboration to the actual call.
--
-- *Why strict `<` (`lt v w`), not non-strict `≤`.*  LN uses strict.
--   The non-strict form `∀ v ∈ G, lt v v` would be reflexive (the
--   LN's `<` is irreflexive); the strict form is the literal
--   reading and downstream proofs (`claim_3_2`'s "no directed cycle
--   under the order" argument, the iSCM solution-uniqueness's
--   "depends only on strictly-earlier nodes" induction) all
--   pattern-match on strict `<`.  A non-strict variant is a
--   one-line corollary (`fun v w => lt v w ∨ v = w`) and can be
--   introduced on demand.
--
-- *Why the "indexing" reformulation is NOT a second definition.*
--   The LN's "Equivalently, it can be described as an indexing of
--   the nodes `J ∪ V = {v_1, ..., v_K}` where parents always
--   precede their children" is a *theorem*: any strict total order
--   on a finite carrier has a unique increasing enumeration, and
--   the parents-precede-children clause translates as "for every
--   directed edge `(v_i, v_k) ∈ E`, `i < k`".  Mathlib provides the
--   sort: `Finset.sort lt (G.J ∪ G.V) : List Node` is the
--   enumeration `(v_1, ..., v_K)`.  Finiteness is what makes the
--   reformulation a theorem, and it holds here because `G.J / G.V
--   : Finset Node` (def_3_1) are finite by construction.  Encoding
--   the indexing as a separate primary definition was rejected
--   because it would force a sort enumeration at every use site
--   that wanted the relation form (most of them: `claim_3_2`'s
--   backward direction builds the order by repeatedly selecting a
--   parentless node and wants the *relation* `lt v_i v_j ↔ i < j`;
--   `def_3_9` `Pred^G_<` takes the relation).  Provide the
--   indexing equivalence as a downstream lemma on
--   `IsTopologicalOrder` if any later chapter needs it.  *Both
--   formulations are non-unique in the same way*: any CDMG with
--   two `Pa`-incomparable vertices admits several distinct valid
--   orders (any topological linearisation of an antichain works),
--   so the LN's "a topological order" and our `∃ lt,
--   G.IsTopologicalOrder lt` are existence claims, NOT uniqueness
--   claims.  `claim_3_2`'s forward direction merely produces
--   *some* witness; chapter-8 iSCM proofs that destructure
--   `∃ lt, …` bind *a chosen* `lt` and reason parametrically in
--   it.  The strict-equivalence verifier confirmed the
--   relation-form ↔ LN total-order-of-`J ∪ V` correspondence is
--   PRESENTATION (off-carrier `lt` is freely extendable / freely
--   restrictable), not CONTENT.
--
-- *Why not a `Decidable` instance.*  The relation `lt` is a bare
--   `Node → Node → Prop`; decidability is the consumer's call (some
--   downstream chapters may want a constructive enumeration for
--   computability, in which case they add `[DecidableRel lt]`
--   locally; chapter 8's iSCM iteration uses the indexing form
--   from `claim_3_2`'s constructive proof, recovering decidability
--   that way).  Imposing `DecidableRel lt` here would over-constrain
--   the predicate and prevent classical-style existence statements
--   from going through.
--
-- *Mathlib re-use.*  No direct fit for the combined predicate.
--   `IsStrictTotalOrder` (`Mathlib.Order.RelClasses`) bundles the
--   three total-order axioms unrestricted; ours restricts them to
--   `v ∈ G`.  `LinearOrder.lift` / `LinearOrder.preimage` would
--   give a linear order on a subtype but force coercion (see the
--   carrier discussion above).  Mathlib's `SimpleGraph.IsAcyclic`
--   and friends do not provide a topological-order analogue
--   (Mathlib's general-graph framework lacks the J/V split and
--   bidirected channel).  We compose `Pa` (def_3_5) with our
--   carrier-restricted total-order helper; the resulting predicate
--   is the natural chapter-3 idiom.
--
-- *Downstream consumers (load-bearing for ten chapters).*
--   * `claim_3_2` (very next claim, same section).  Forward:
--     `G.IsAcyclic → ∃ lt, G.IsTopologicalOrder lt`.  Backward:
--     `(∃ lt, G.IsTopologicalOrder lt) → G.IsAcyclic`.  Both
--     directions pattern-match on `G.IsTopologicalOrder lt`'s two
--     conjuncts directly.
--   * `def_3_9` (Predecessors).  Defines `Pred^G_<(v) := (G.J ∪
--     G.V).filter (fun w => lt w v)`, parametric in `lt`.  The
--     same `lt : Node → Node → Prop` shape feeds in.
--   * `def_3_10` hard intervention preservation lemma (claim_3_3
--     and friends): "if `G` has a topological order, so does
--     `G_{do(W)}`, obtained by [extension rule]".  Pattern-matches
--     on the relation and proves the new relation satisfies the
--     predicate.
--   * `def_3_11` node-splitting preservation (claim_3_6, claim_3_11)
--     and `def_3_14` marginalisation preservation (claim_3_16):
--     similar.  Each takes a topological order, constructs a new
--     relation (via re-indexing or restriction), and proves the
--     predicate for the new relation.
--   * `def_3_15` acyclification: refines a topological order on the
--     SCC-DAG to a full order on the acyclified causal graph.
--     Predicate-level construction.
--   * Chapter 8 iSCMs (`def:scm_acyclic`,
--     `Prp:acyclic_scms_are_simple`).  Solution uniqueness: extract
--     a topological order from acyclicity (via `claim_3_2`), then
--     iterate node-by-node — `f_v` depends on values at
--     `Pred^G_<(v)`.  The relation `lt` is the iteration index.
--   * Chapter 11+ FCI: completeness arguments in the acyclic regime
--     use a topological order to linearise the d-/m-separation
--     constraint enumeration.
--
-- *Constraints / known limitations.*
--   1. **No reflexive variant.**  Some downstream chapters may
--      want a non-strict topological order (e.g. defining
--      `Pred^G_≤(v) := {w ∈ G | w ≤ v} = {w ∈ G | w < v} ∪ {v}`).
--      This is recoverable: `fun v w => lt v w ∨ v = w` is a
--      reflexive total order satisfying the same parents-precede
--      property (with the LN inclusion swapped: `v ∈ Pa^G(w) → v ≤
--      w` follows from `<` strictness).  No separate Lean def
--      required.
--   2. **The empty CDMG vacuously admits any `lt`.**  When
--      `G.J = ∅` and `G.V = ∅`, every relation `lt : Node → Node →
--      Prop` satisfies `G.IsTopologicalOrder lt` vacuously.
--      Consistent with the empty CDMG being trivially acyclic;
--      `claim_3_2`'s equivalence holds in this degenerate case.
--   3. **No `Decidable` instance** (see design block above).
--   4. **Trichotomy is at the `Prop` level, not `Decidable`.**
--      Downstream proofs that want a constructive enumeration get
--      it via `Classical.dec`; the LN's "indexing" reformulation
--      assumes finiteness (which we have) but is silent on
--      decidability.
--   5. **The "indexing" equivalence is not provided as a separate
--      definition** (see design block above) but is a theorem any
--      later chapter can prove on demand.
-- def_3_8 -- start statement
def IsTopologicalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  G.IsTotalOrderOn lt ∧ ∀ ⦃v w : Node⦄, v ∈ G.Pa w → lt v w
-- def_3_8 -- end statement

end CDMG

end Causality
