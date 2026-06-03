import Chapter3_GraphTheory.Section3_1.EdgeRelations

namespace Causality

/-!
# Walks on a CDMG: items 1–5 of `def_3_4`

This file formalises the foundational walk type for the rest of the
lecture notes.  Every separation argument from chapter 5 (`σ`/`d`-
separation, Markov properties), every do-calculus rewrite in chapter 5+,
every iSCM identification argument in chapters 8–10, and every FCI
discovery proof in chapter 11+ pattern-matches on the type `Walk`
defined here.  Getting the shape right is therefore load-bearing for
the entire book; the design-choice blocks immediately above each
declaration spell out the trade-offs — read them before deviating.

The LN block `def_3_4` `\label{def:walks}` introduces **six** named
concepts on top of `def_3_1`/`def_3_2`/`def_3_3`:

  1. Walk (with the closing "into / out of $v_0$ / $v_n$"
     classifications);
  2. Directed walk;
  3. Bidirected walk;
  4. Collider walk;
  5. Path;
  6. Bifurcation.

Items 1–5 live in **this file**.  Item 6 (`Bifurcation`) lives in the
sibling file `WalkBifurcation.lean`, written by a separate worker —
`Bifurcation` is the only one of the six that destructures the walk
*as data* (two directed sub-walks + a hinge edge + endpoint
constraints), so it sits one layer above and imports `Walks.lean` for
`Walk` and `Walk.IsDirectedWalk`.

## Core encoding choices (load-bearing across all six items)

* The LN's `a_k` — "the individual edge of a walk" — is a first-class
  object.  We encode it as an ADT `EdgeStep` with three constructors
  (`forward` / `backward` / `bidir`) carrying the underlying `G.tuh /
  G.hut / G.huh` existence proof.  This lets the into/out
  classifications and the three specialised walk predicates pattern-
  match on the constructor of the first / last / interior edge step —
  exactly the LN's `\hus / \tuh / \suh / \hut / \huh` distinctions.

* `Walk` is a Mathlib-style indexed inductive `Walk G u w` à la
  `SimpleGraph.Walk` — `nil` (the trivial walk) carrying an explicit
  membership proof `v ∈ G` (LN: "$v_0 \in G$"), and `cons` chaining an
  `EdgeStep` onto a tail walk.  The walk *direction* `Walk G u w` is
  the LN's walk-from-$u$-to-$w$; `cons` extends from the left
  (analogous to `List.cons`).

* The specialised LN walk variants (items 2/3/4) are **predicates** on
  `Walk`, not separate inductives — so `def_3_5`'s "$\exists$ directed
  walk: $w \tuh \cdots \tuh v$" maps verbatim to
  `∃ p : Walk G w v, p.IsDirectedWalk`, with no coercion needed and
  free reuse of `Walk.support / Walk.length` (and, later, concat /
  reverse / sub-walk).

* Items 1 (into/out of $v_0$, $v_n$) and 5 (`IsPath`) similarly stay
  as predicates on `Walk`.

* `Walk`, `EdgeStep`, and the walk-level predicates live **directly in
  the `Causality` namespace** — they are vertex-level concepts of
  walks *between* nodes, not field-style accessors on a CDMG (contrast
  the `CDMGNotation` items, which sit under `Causality.CDMG`).
  Downstream call sites use `p.IsDirectedWalk` / `p.support` / etc.,
  not `G.IsDirectedWalk p`.

## Subtleties surfaced by the working-phase wording check

The two informational ids cited below are registered globally in
`leanification/working_subtlety_register.json` by the manager:

* `trivial_walk_satisfies_all_specialized_walk_types` — `Walk.nil`
  satisfies `IsDirectedWalk`, `IsBidirectedWalk`, `IsColliderWalk`
  vacuously.  Literal LN `n ≥ 0` in items 2/3/4 + the commented-out
  exclusion line "% Directed walks exclude the trivial walk per
  definition." (visible in the LN tex source above item 2) shows the
  author considered and rejected exclusion.  Downstream consumers
  needing a *non-trivial* witness (e.g. `def_3_6` acyclicity says
  "non-trivial directed walk") add `0 < p.length` at the use site.

* `walk_into_out_classifications_undefined_for_trivial` — all four of
  `Walk.intoV0 / outOfV0 / intoVn / outOfVn` are `False` on the
  trivial walk.  The literal LN does not pin down the trivial case
  ("no $a_0$ / $a_{n-1}$ exists" ⇒ "no classification applies"); we
  choose the natural reading.

## Operator addition that fires here

`[collider_walk_n1_form_contradicts_inline_note]` (treated as part of
the LN) — for a length-1 collider walk, the form $v_0 \suh v_1$ +
$v_{n-1} \hus v_n$ collapses onto a single edge that must have
arrowheads at both endpoints, i.e. a *bidirected* edge.  The LN's
inline note "for $n=1$ this reads: $v \sus w \in G$" is read in the
stricter sense; pure directed edges $v \tuh w$ and $v \hut w$ do NOT
count as collider walks of length 1.  Encoded literally in
`Walk.IsColliderWalk`'s `n=1` cases below.
-/

variable {Node : Type*} [DecidableEq Node]

/-! ## Item 1 — `EdgeStep`, `Walk`, helpers, and the four into/out
classifications -/

-- ref: def_3_4 (item 1 — supporting helper)
--
-- An `EdgeStep G u v` is the LN's `a_k` symbol — "the individual edge
-- of a walk" — taking three forms keyed to the three CDMG edge
-- primitives `G.tuh / G.hut / G.huh`.  Reading: an `EdgeStep G u v`
-- IS a single step in a walk going *from `u` to `v`* (walk direction),
-- where the underlying edge is `(u, v) ∈ E` (`forward`),
-- `(v, u) ∈ E` (`backward` — same directed edge, traversed against its
-- direction), or `(u, v) ∈ L` (`bidir`).
/-
LN tex (extracted from item 1 of `\label{def:walks}`):

  A \emph{walk} from $v$ to $w$ in $G$ is a finite alternating
  sequence of adjacent nodes and edges $v = v_0, a_0, v_1, \dots,
  v_{n-1}, a_{n-1}, v_n = w$ in $G$ for some $n \ge 0$, i.e.\ such
  that for every $k = 0, \dots, n-1$ we have that
  $a_k = (v_k, v_{k+1}) \in E \cup L$ or $a_k = (v_{k+1}, v_k) \in E$.
-/
-- ## Design choice
--
-- *Why an ADT, not a `Sum` / three-way disjunctive `Prop` / a single
--   `G.sus` step.*  Three reasons.
--   1. The LN's `a_k` is a syntactic object — the *edge* between two
--      consecutive nodes of the walk — and the LN's into/out
--      classifications and specialised-walk forms inspect `a_k`'s
--      *shape* (`\tuh` vs `\hut` vs `\huh` vs `\suh` vs `\hus`).  A
--      first-class ADT preserves that.  A `Prop`-side disjunction
--      `(v_k, v_{k+1}) ∈ G.E ∨ (v_{k+1}, v_k) ∈ G.E ∨ (v_k, v_{k+1}) ∈
--      G.L` would erase which disjunct fired and force every
--      classification to peer through `Or.elim`.
--   2. The three constructors keep the three CDMG edge primitives
--      `tuh / hut / huh` visible side-by-side, matching the LN macros
--      one-for-one and surviving downstream pattern matches as
--      `.forward / .backward / .bidir`.
--   3. A single `G.sus` step ("any edge") would collapse the three
--      cases at the type level, after which the into/out
--      classifications and `IsDirectedWalk / IsBidirectedWalk /
--      IsColliderWalk` would all need to *re-derive* which kind of
--      edge fired — exactly the information the ADT preserves for
--      free.
--
-- *Why not bake the three cases into `Walk.cons` as three
--   constructors.*  An alternative was `Walk.consFwd / consBack /
--   consBidir` directly on `Walk`.  That would force every consumer
--   to triple-case-split at every cons (chapter 5–16 walk
--   manipulations: concat, reverse, sub-walks, support-list
--   operations), and would lose the "edge" abstraction entirely —
--   `Bifurcation`'s hinge edge `v_{k-1} \hus v_k` (in
--   `WalkBifurcation.lean`) is naturally typed as a single
--   `EdgeStep`, not a one-step walk.  Splitting `Walk.cons` would
--   make that hinge representation lopsided.
--
-- *Why `Type _` (data), not `Prop`.*  The constructor proof
--   `h : G.tuh u v` (etc.) is itself `Prop`, but the *choice of
--   constructor* (`forward` vs `backward` vs `bidir`) is data we
--   want to pattern-match on later (specialised walks; sub-walk
--   extraction at colliders in chapter 5+ separation proofs).  A
--   `Prop`-valued disjunction would not survive proof-irrelevance:
--   two different EdgeSteps with the same endpoints could be
--   identified, defeating "the walk has THIS pattern of edge types".
--   Living in `Type _` (data) preserves the distinction.
--
-- *Why `Node → Node → Type _` indexing.*  The two endpoint indices
--   (`u v : Node`) are exposed to the type system so that
--   `Walk.cons (e : EdgeStep G u v) (p : Walk G v w) : Walk G u w`
--   forces type-level chaining — the head of the tail walk must equal
--   the target of the edge step.  Packaging endpoints into a single
--   pair index `(Node × Node)` was rejected: every consumer would
--   then have to project `.1 / .2` to extract the endpoints, and
--   `cons`'s chaining condition would become an explicit proof
--   obligation instead of a free unification.
--
-- *Naming: `forward` / `backward` / `bidir`.*  `forward` reads as
--   "the step goes from `u` to `v`, in the same direction as the
--   underlying directed edge"; `backward` reads as "the step goes
--   from `u` to `v`, *against* the direction of the underlying
--   directed edge" — i.e. the underlying edge is `(v, u) ∈ E`
--   (LN: $u \hut v$, equivalently $v \tuh u$); `bidir` is the
--   symmetric bidirected case where the question of direction does
--   not arise.  The walk-from-`u`-to-`v` direction is the *walk*
--   direction, *not* necessarily the edge direction — `backward`
--   captures exactly this distinction.
--
-- *Mathlib re-use.*  No Mathlib edge type carries the LN's
--   `tuh / hut / huh` trichotomy — `SimpleGraph.Adj` is an undirected
--   symmetric relation, `Quiver.Hom` is single-directed with no
--   bidirected channel, and Mathlib has no mixed-directed-bidirected
--   "dart" or "edge" type at the time of writing.  We roll our own
--   ADT; the three constructors carry mathlib-provided `Finset`-
--   membership proofs (`G.tuh = (·,·) ∈ G.E` etc., see
--   `CDMGNotation.lean`), so we still re-use the underlying
--   `Finset` decidability machinery.
--
-- *Constraints / known limitations.*
--   1. **EdgeStep does not carry redundant membership proofs.**
--      The constructor's `h : G.tuh u v` already forces `u ∈ J ∪ V`
--      and `v ∈ V` via `CDMG.hE_subset` (and analogously for `.hut /
--      .bidir` via `hE_subset / hL_subset`).  We do not add separate
--      `(hu : u ∈ G) (hv : v ∈ G)` fields — they would be redundant
--      and would force every step constructor to discharge them.
--      Downstream consumers extract `u ∈ G` from the constructor's
--      proof when needed (a single `G.hE_subset h |>.1.2` /
--      `Finset.mem_union.mpr` derivation).
--   2. **EdgeStep is per-CDMG, not per-mathlib-graph.**  An
--      `EdgeStep G u v` only makes sense relative to a fixed `G :
--      CDMG Node`; we do not provide a coercion to / from
--      `SimpleGraph.Dart` (no Mathlib counterpart) or to a
--      `Quiver.Hom` (would erase the bidirected case).  Should later
--      chapters need an abstract "graph edge" notion (e.g. for
--      generic graph algorithms in chapter 11+ FCI), introduce the
--      abstraction at the use site rather than retrofitting it here.
--   3. **No `Decidable (EdgeStep G u v)`** — instance not provided
--      and not needed at this layer (downstream proofs reason about
--      specific constructors via pattern matching, not via
--      decidability of `EdgeStep`'s existence).  Should later need
--      it, the decidable instance reduces to deciding
--      `G.tuh u v ∨ G.hut u v ∨ G.huh u v`, each disjunct being
--      `Finset`-membership-decidable.
-- def_3_4 --- start helper
inductive EdgeStep (G : CDMG Node) : Node → Node → Type _ where
  | forward  {u v : Node} (h : G.tuh u v) : EdgeStep G u v
  | backward {u v : Node} (h : G.hut u v) : EdgeStep G u v
  | bidir    {u v : Node} (h : G.huh u v) : EdgeStep G u v
-- def_3_4 --- end helper

-- ref: def_3_4 (item 1 — main concept)
--
-- A `Walk G u w` is a finite chain of `EdgeStep`s from `u` to `w` in
-- `G`.  The `nil` constructor encodes the LN's "trivial walk
-- consisting of a single node $v_0 \in G$"; the `cons` constructor
-- prepends one `EdgeStep` from `u` to some intermediate vertex `v`,
-- chained onto a tail walk from `v` to `w`.
/-
LN tex (item 1 of `\label{def:walks}`):

  A \emph{walk} from $v$ to $w$ in $G$ is a finite alternating
  sequence of adjacent nodes and edges
    $v = v_0, a_0, v_1, \dots, v_{n-1}, a_{n-1}, v_n = w$
  in $G$ for some $n \ge 0$, i.e.\ such that for every
  $k = 0, \dots, n-1$ we have that
  $a_k = (v_k, v_{k+1}) \in E \cup L$ or $a_k = (v_{k+1}, v_k) \in E$,
  and with end nodes $v_0 = v$ and $v_n = w$.  The same node may
  appear multiple times in a walk.  Also the \emph{trivial walk}
  consisting of a single node $v_0 \in G$ is allowed (if $v = w$).
-/
-- ## Design choice
--
-- *Why an inductive type, not a list-based or function-based
--   encoding.*  Three encodings were on the table.
--   1. *Inductive* `nil | cons` (chosen).  Mirrors Mathlib's
--      `SimpleGraph.Walk` (whose lemmas — `support`, `length`, `Nil`
--      detection, concat, reverse, `IsPath` via `Nodup` — we adapt
--      below).  Recursion / induction on a walk is the natural
--      proof form for separation-style arguments downstream
--      (chapters 5+).
--   2. *Structure with parallel lists* `vs : List Node`,
--      `steps : List (EdgeStep …)`, plus invariants (`steps.length +
--      1 = vs.length`, every step's endpoints equal consecutive `vs`
--      entries).  Rejected: the parallel-list invariant is awkward,
--      and pattern matching to extract "the first step" or "the last
--      step" requires unpacking the invariant on every use.
--   3. *Function from `Fin (n+1)` to `Node` plus a step function*.
--      Rejected: pattern-matching on the first/last step (needed for
--      the into/out classifications and the collider-walk shape) is
--      finger-arithmetic over `Fin`, and concatenation requires
--      explicit index arithmetic — neither survives the chapter 5+
--      proof workload.
--
-- *Why `hv : v ∈ G` on `nil`, but no analogous membership proof on
--   `cons`.*  The LN explicitly says "the trivial walk consisting of
--   a single node $v_0 \in G$" — membership is part of the
--   definition, not bookkeeping.  We therefore make `hv : v ∈ G` an
--   explicit field of `nil`.  For `cons (e : EdgeStep G u v) (p : Walk
--   G v w)`, no membership proof is needed: the `EdgeStep`
--   constructor's underlying `G.tuh u v` / `G.hut u v` / `G.huh u v`
--   each force both endpoints `u` and `v` into `G.J ∪ G.V` via
--   `CDMG.hE_subset` / `CDMG.hL_subset` (see `CDMG.lean`).  Adding a
--   redundant `hv : v ∈ G` field on `cons` would force consumers to
--   propagate it manually at every step.
--
-- *Why parameterise on `G : CDMG Node` (explicit), not bundle the
--   graph inside.*  The graph is fixed for any given walk; making
--   `G` an explicit type parameter (as Mathlib does for
--   `SimpleGraph.Walk`) keeps the type-level dependence on `G`
--   visible and lets downstream defs (`IsDirectedWalk` etc.) take
--   `G` implicitly via unification from the walk's type.
--
-- *The cons-builds-from-the-left convention.*  Pictorially,
--   `Walk.cons e p` reads as "step `e` (from `u` to `v`), then walk
--   `p` (from `v` to `w`)", building the walk one step at a time
--   from the left endpoint — analogous to `List.cons`.  This
--   convention is exposed in `support` (head of the support list =
--   start of the walk) and `length` (counts cons constructors), and
--   propagates to the into/out classifications:
--   `intoV0 / outOfV0` inspect the *first* `cons`'s `EdgeStep`, and
--   `intoVn / outOfVn` recurse down to the *last* `cons`'s
--   `EdgeStep`.
--
-- *Downstream consumers (load-bearing).*  Every walk-existential and
--   every walk-recursion in chapter 3+ runs through this type:
--   `def_3_5` builds `Anc^G / Desc^G / Dist^G` as walk-existentials;
--   `def_3_6` acyclicity quantifies over `Walk G v v` with
--   `0 < p.length`; `def_3_4` item 6 (`Bifurcation`) packages two
--   directed sub-walks into a structure;  chapters 5+ use `Walk` as
--   the central object of `σ`/`d`-separation arguments;  FCI and
--   discovery algorithms in chapter 11+ pattern-match on walk shape
--   to characterise `m`-connection.
--
-- *Subtlety `trivial_walk_satisfies_all_specialized_walk_types`.*
--   `nil` is a valid `Walk G v v`, and the LN allows this case
--   ("trivial walk … is allowed if $v = w$").  All three specialised
--   walk predicates (`IsDirectedWalk` etc.) hold vacuously on `nil`
--   — see their design blocks below for the LN tie-back.
--
-- *Mathlib re-use.*  Directly modelled on Mathlib's
--   `SimpleGraph.Walk` (`Mathlib/Combinatorics/SimpleGraph/Walks/
--   Basic.lean`): same `nil` / `cons` shape, same `Nat`-valued
--   `length`, same `List Node`-valued `support`, same
--   `IsPath := support.Nodup` formulation downstream.  The departure
--   from Mathlib is the EdgeStep ADT, which carries the LN's
--   `tuh / hut / huh` trichotomy — Mathlib's `SimpleGraph.Walk` cons
--   takes an `h : G.Adj u v` (an undirected adjacency proof), whereas
--   we take an `EdgeStep G u v` (a typed *step*, not just an
--   adjacency).  This is the necessary extension for mixed graphs.
--
-- *Constraints / known limitations.*
--   1. **Walks are finite by type.**  `Walk G u w` is an inductive
--      with finite-arity constructors, so every walk has finite
--      length.  This matches the LN ("finite alternating sequence")
--      and is fine for chapter 3+ purposes.  Should later chapters
--      need "infinite walks" (countably infinite directed paths in
--      acyclic-graph counterexamples, say), one would need a
--      separate `coinductive` analogue — flagged here but not
--      needed.
--   2. **Walks do not memoise membership at intermediate vertices.**
--      `Walk G u w` carries `u ∈ G` only at the `nil` constructor (or
--      via the EdgeStep's underlying `G.tuh / G.hut / G.huh`).  The
--      intermediate vertex `v` in a `cons (e : EdgeStep G u v)
--      (p : Walk G v w)` has membership derivable from `e` (via
--      `hE_subset / hL_subset`), not stored directly.  Should a
--      downstream proof want `∀ x ∈ p.support, x ∈ G`, it follows by
--      structural recursion using `hE_subset / hL_subset`, but the
--      lemma itself isn't stated here — introduce on demand.
--   3. **Two walks with the same support but different EdgeStep
--      pattern are not equal.**  `Walk G u w` lives in `Type _`, not
--      `Prop`, so the *choice* of EdgeStep at each cons is part of
--      the walk's identity.  Two walks `p1 p2 : Walk G u w` with
--      `p1.support = p2.support` but different EdgeStep sequences
--      (e.g.  `(.forward h1)` vs `(.bidir h2)` at the first step,
--      where both edges exist) are distinct walks.  This matches the
--      LN — the LN's `a_k` symbol distinguishes which kind of edge
--      is being traversed — but downstream consumers reasoning about
--      walks "up to vertex sequence" need to introduce that
--      equivalence themselves.
--   4. **Reversal is not free.**  Mathlib's `SimpleGraph.Walk.reverse`
--      uses the underlying adjacency's symmetry; here, reversing a
--      `Walk G u w` to a `Walk G w u` requires flipping each EdgeStep
--      (`.forward h ↔ .backward h'` where `h' : G.hut v u` from
--      `h : G.tuh u v`; `.bidir h ↔ .bidir h'` via `hL_symm`).  A
--      `Walk.reverse` operation can be defined on demand;
--      `WalkBifurcation.lean` doesn't need it (the LN already gives
--      the left arm in reversed reading), so we don't define it here.
-- def_3_4 -- start statement
inductive Walk (G : CDMG Node) : Node → Node → Type _ where
  | nil  {v : Node} (hv : v ∈ G) : Walk G v v
  | cons {u v w : Node} (e : EdgeStep G u v) (p : Walk G v w) : Walk G u w
-- def_3_4 -- end statement

-- ref: def_3_4 (item 1 — supporting helper)
--
-- `Walk.support p` is the list of vertices traversed by the walk `p`,
-- in walk order, including both endpoints.  Length of the support
-- list equals `p.length + 1`.
/-
LN tex (item 1 of `\label{def:walks}`, surrounding context):

  A \emph{walk} from $v$ to $w$ in $G$ is a finite alternating
  sequence … $v = v_0, a_0, v_1, \dots, v_{n-1}, a_{n-1}, v_n = w$ …
  The same node may appear multiple times in a walk.
-/
-- ## Design choice
--
-- *Why a `List Node` of vertices, not a `Multiset` / `Finset`.*  The
--   LN reads "$v = v_0, a_0, v_1, \dots, v_{n-1}, a_{n-1}, v_n = w$"
--   as an *ordered* sequence; multiset / finset would erase order
--   (and, for finset, also multiplicity — the LN explicitly notes
--   "the same node may appear multiple times").  `List Node`
--   preserves both.
--
-- *Why not include the EdgeSteps in the support.*  The LN's "support"
--   is the vertex sequence only; the edge sequence is a parallel
--   object.  Should a chapter 5+ proof need both, the EdgeStep
--   sequence can be reconstructed by a separate `Walk.steps` recursor
--   (not declared here; introduce on demand).  Mathlib's
--   `SimpleGraph.Walk` follows the same split (`support` vs `darts`
--   vs `edges`); we adopt the same shape.
--
-- *Why `[u]` for `nil`, `u :: p.support` for `cons`.*  Identical
--   recursion shape to Mathlib's `SimpleGraph.Walk.support`.  The
--   start vertex `u` is the implicit binder of the def's signature;
--   for `nil`, the constructor forces the walk's endpoints to
--   coincide so `[u]` is the singleton vertex; for `cons`, prepend
--   the current start vertex to the tail's support.
--
-- *Downstream consumers.*  `Walk.IsPath` (item 5 below) is
--   `p.support.Nodup`; `Bifurcation` (in `WalkBifurcation.lean`)
--   constrains endpoint counts via `support.count`; chapter 5+
--   separation arguments traverse `support` to identify colliders
--   / non-colliders along the walk; chapter 11+ FCI inspects
--   support membership.
-- def_3_4 --- start helper
def Walk.support {G : CDMG Node} {u w : Node} : Walk G u w → List Node
  | .nil _ => [u]
  | .cons _ p => u :: p.support
-- def_3_4 --- end helper

-- ref: def_3_4 (item 1 — supporting helper)
--
-- `Walk.length p` is the LN's `n` — the number of edges (= number of
-- `cons` constructors).  Equals `0` exactly when `p = .nil _`
-- (the trivial walk).
/-
LN tex (item 1 of `\label{def:walks}`, surrounding context):

  … for some $n \ge 0$ …
-/
-- ## Design choice
--
-- *Why count edges, not vertices.*  The LN's `n` is the number of
--   edges; the vertex count is `n + 1` (handled by
--   `support.length`).  Distinguishing the two avoids the off-by-one
--   confusion that ad-hoc proofs slip into.
--
-- *Why `Nat`-valued, not `WithTop ℕ` / `ℕ∞`.*  Walks are finite by
--   LN definition ("finite alternating sequence"); no infinite walks
--   are admissible.  `Nat` is the right codomain.
--
-- *Why a plain `def`, not `@[simp]`.*  Adding `@[simp]` would unfold
--   `length` eagerly on every `simp` call, but downstream proofs
--   sometimes want to reason about `length` as a primitive (e.g.
--   `def_3_6` acyclicity says "non-trivial directed walk", i.e.
--   `0 < p.length`, without wanting to peer inside).  Mathlib's
--   `SimpleGraph.Walk.length` is also a plain `def`; the
--   `@[simp]`-tagged equations (`length_nil`, `length_cons`) are
--   stated as separate lemmas there.  We do not need those lemmas
--   here — defequal unfolding handles the cases that come up — and
--   keep `length` un-`simp`ed.
--
-- *Downstream consumers.*  `def_3_6` acyclicity ("non-trivial
--   directed walk from `v` to itself") = `∃ p, p.IsDirectedWalk ∧
--   0 < p.length`; chapter 5+ `m`-connection arguments do induction
--   on `p.length`; FCI in chapter 11+ uses length-bounded walk
--   enumeration.
-- def_3_4 --- start helper
def Walk.length {G : CDMG Node} {u w : Node} : Walk G u w → ℕ
  | .nil _ => 0
  | .cons _ p => p.length + 1
-- def_3_4 --- end helper

-- ref: def_3_4 (item 1 — closing prose, four into/out classifications)
--
-- The four predicates `intoV0 / outOfV0 / intoVn / outOfVn` formalise
-- the closing prose of LN item 1 ("the walk is called *into* $v_0$
-- if $a_0 = v_0 \hus v_1$, …").  Each inspects either the *first*
-- `cons`'s `EdgeStep` (for the `V0` versions) or the *last* `cons`'s
-- `EdgeStep` (for the `Vn` versions), and asks whether that step has
-- an arrowhead at the focal endpoint (`into`) or a tail at the focal
-- endpoint (`outOf`).
--
-- The single design block below covers all four; the four `def`s
-- follow in sequence with markers around each.
/-
LN tex (item 1 of `\label{def:walks}`, closing prose):

  The walk is called \emph{into $v_0$} if $a_0 = v_0 \hus v_1$, and
  \emph{out of $v_0$} if $a_0 = v_0 \tuh v_1$.  Similarly, it is
  called \emph{into $v_n$} if $a_{n-1} = v_{n-1} \suh v_n$ and
  \emph{out of $v_n$} if $a_{n-1} = v_{n-1} \hut v_n$.
-/
-- ## Design choice (consolidated for `intoV0 / outOfV0 / intoVn / outOfVn`)
--
-- *Pattern-matching shape: direct for V0, auxiliary for Vn.*  Two
--   candidate shapes were considered.
--   1. *All four direct* — V0 directly inspects the first cons's
--      `EdgeStep` (`| .cons (.forward _) _ => …`); Vn does the
--      analogous "peel cons until `.nil` tail" recursion with an
--      as-pattern `| .cons _ p@(.cons _ _) => p.intoVn`.  This was
--      the initial attempt: it elaborates and `lake build` is
--      clean, BUT the equation lemmas for the trivial-walk case do
--      not fire by `rfl` (the as-pattern + nested matches push the
--      compiler into well-founded-recursion mode, which blocks
--      definitional reduction on `(Walk.nil _).intoVn = False`).
--   2. *V0 direct, Vn via auxiliary* (chosen).  `intoV0 / outOfV0`
--      stay direct (single-level cons match, reduces by rfl).  For
--      Vn, introduce a 3-dash helper
--      `Walk.lastHeadAtRight / lastTailAtRight : EdgeStep G u v →
--      Walk G v w → Prop` that takes a *current* edge step and a
--      remaining tail walk, recursing structurally on the tail.
--      `Walk.intoVn / outOfVn` is then a thin two-case wrapper:
--      `.nil _ => False`, `.cons e p => Walk.lastXAtY e p`.  Both
--      `(.nil _).intoVn` and `(.cons e (.nil _)).intoVn` reduce by
--      `rfl` under this shape (tested in /tmp before commit).
--
-- *Why the four predicates are all `False` on the trivial walk
--   (`Walk.nil`).*  The LN's prose presupposes the existence of
--   $a_0$ (for the V0 versions) and $a_{n-1}$ (for the Vn versions).
--   On the trivial walk, no $a_0$ / $a_{n-1}$ exists — the LN
--   literally does not classify the trivial walk as "into / out of"
--   either endpoint.  We resolve this gap by reading "no edge → no
--   classification" and returning `False` in all four cases.
--   Subtlety id `walk_into_out_classifications_undefined_for_trivial`
--   (registered globally) documents this choice for downstream
--   consumers; a chapter 5+ proof that wants "trivial walk OR walk
--   into $v$" can write `p.length = 0 ∨ p.intoV0` explicitly.
--
-- *Mapping LN `\hus / \tuh / \suh / \hut` to `EdgeStep` constructors.*
--   The LN's notation `v_0 \hus v_1` (an arrowhead at $v_0$ on the
--   `a_0` edge) corresponds at the `EdgeStep G v_0 v_1` level to
--   either `.backward _` (underlying $v_1 \tuh v_0$, i.e. directed
--   edge pointing at $v_0$) or `.bidir _` (bidirected, arrowhead at
--   both endpoints).  Analogously, `v_0 \tuh v_1` (tail at $v_0$,
--   only directed) maps to `.forward _` exclusively.  At the other
--   end, `v_{n-1} \suh v_n` (arrowhead at $v_n$) maps to `.forward
--   _` (directed pointing at $v_n$) or `.bidir _`; and `v_{n-1}
--   \hut v_n` (tail at $v_n$, only directed) maps to `.backward _`
--   exclusively.  The case tables below encode exactly these
--   mappings.
--
-- *Asymmetry between V0 and Vn classifications and the underlying
--   `EdgeStep` constructors.*  At `v_0` (the *start* of the walk's
--   first edge), an arrowhead-at-`v_0` ↔ the edge's head is at
--   *its* `u` endpoint (the EdgeStep's left index); at `v_n` (the
--   *end* of the walk's last edge), an arrowhead-at-`v_n` ↔ the
--   edge's head is at *its* `v` endpoint (the EdgeStep's right
--   index).  The EdgeStep constructors are oriented so that
--   `.forward _` ↔ head at right, `.backward _` ↔ head at left,
--   `.bidir _` ↔ heads at both — propagating these to the V0 / Vn
--   tables gives the asymmetric mapping displayed above.
--
-- *Naming.*  `intoV0 / outOfV0 / intoVn / outOfVn` directly read
--   off the LN's prose; the `V0` / `Vn` suffix names the LN's
--   $v_0$ / $v_n$ explicitly to avoid confusion with "into-an-
--   arbitrary-vertex" predicates that may appear later.
--
-- *Downstream consumers.*  `def_3_5`'s family relationships (`Pa /
--   Ch / Anc / Desc`) do *not* use `intoV0` etc. directly — they
--   build walk-existentials with `IsDirectedWalk`.  But chapter 5+
--   `m`-connection / `σ`-separation arguments pattern-match on
--   walks-into-$v$ vs walks-out-of-$v$ to characterise colliders at
--   walk endpoints, and FCI in chapter 11+ uses the classifications
--   to detect endpoint marks during structure learning.
--
-- *Cross-reference to `G.hus` / `G.suh` from `CDMGNotation.lean`.*
--   The LN's "$a_0 = v_0 \hus v_1$" and "$a_{n-1} = v_{n-1} \suh
--   v_n$" use the LN macros `\hus` and `\suh` respectively — and
--   crucially the focal vertex (the one with the arrowhead) sits on
--   *different sides* of the writing in each case (`\hus`: head at
--   LEFT, `\suh`: head at RIGHT).  Our four predicates inherit this
--   from the EdgeStep's `.forward / .backward` orientation:
--   `intoV0 ↔ first EdgeStep is .backward or .bidir` mirrors
--   `\hus v_0 v_1 = (G.hut ∨ G.huh) v_0 v_1` (head at the left
--   index = `v_0`); `intoVn ↔ last EdgeStep is .forward or .bidir`
--   mirrors `\suh v_{n-1} v_n = (G.tuh ∨ G.huh) v_{n-1} v_n` (head
--   at the right index = `v_n`).  Consult the design block above
--   `CDMG.hus / CDMG.suh` in `CDMGNotation.lean` for the underlying
--   primitive shape and the design block above `CDMG.edgeInto` in
--   `EdgeRelations.lean` for the same head-asymmetry used in
--   `def_3_3`.
--
-- *Constraints / known limitations.*
--   1. **Trivial walk falls outside every classification cell.**
--      For `p : Walk G v v` with `p = .nil hv`, none of `intoV0 /
--      outOfV0 / intoVn / outOfVn` holds — all four return `False`.
--      So if a downstream chapter-5+ proof partitions "walks from
--      $v$ to $w$" by their into/out-of-endpoint status, the trivial
--      walk (when $v = w$) is in no cell.  Subtlety id
--      `walk_into_out_classifications_undefined_for_trivial`
--      (registered globally in
--      `leanification/working_subtlety_register.json`) documents
--      this; consumers can recover the missing cell by adding
--      `p.length = 0` as a fifth case.
--   2. **`intoV0` and `outOfV0` are NOT exclusive across walk
--      lengths.**  For a length-0 walk both are `False`; for any
--      `cons e p` exactly one of `intoV0 / outOfV0` is `True` (the
--      `.forward` / `.backward / .bidir` split).  Symmetrically for
--      `intoVn / outOfVn`.  Should a chapter-5+ proof want "exactly
--      one of into/out-of holds at $v_0$", it pairs the predicates
--      with `0 < p.length`.
--   3. **`intoV0 / outOfV0` are NOT `Decidable` instances** —
--      we provide them as plain `Prop`s, not `Decidable`-bounded
--      computational tests.  Decidability follows from
--      pattern-matching on the EdgeStep, but the typeclass is not
--      threaded; downstream proofs reason by `cases p` rather than
--      `if h : p.intoV0 then …`.
-- def_3_4 -- start statement
def Walk.intoV0 {G : CDMG Node} {u w : Node} : Walk G u w → Prop
  | .nil _ => False
  | .cons (.forward _) _ => False
  | .cons (.backward _) _ => True
  | .cons (.bidir _) _ => True
-- def_3_4 -- end statement

-- def_3_4 -- start statement
def Walk.outOfV0 {G : CDMG Node} {u w : Node} : Walk G u w → Prop
  | .nil _ => False
  | .cons (.forward _) _ => True
  | .cons (.backward _) _ => False
  | .cons (.bidir _) _ => False
-- def_3_4 -- end statement

-- Auxiliary helper for `intoVn`: given a "current" edge step `e :
-- EdgeStep G u v` and a remaining tail walk `p : Walk G v w`, says
-- whether the *last* edge step in the combined `cons e p` walk has
-- an arrowhead at its right-side index.  Structural recursion on
-- `p`; reduces cleanly by `rfl` in all base cases (verified).
-- def_3_4 --- start helper
def Walk.lastHeadAtRight {G : CDMG Node}
    : ∀ {u v w : Node}, EdgeStep G u v → Walk G v w → Prop
  | _, _, _, .forward _, .nil _ => True
  | _, _, _, .backward _, .nil _ => False
  | _, _, _, .bidir _, .nil _ => True
  | _, _, _, _, .cons e' p => Walk.lastHeadAtRight e' p
-- def_3_4 --- end helper

-- def_3_4 -- start statement
def Walk.intoVn {G : CDMG Node} {u w : Node} : Walk G u w → Prop
  | .nil _ => False
  | .cons e p => Walk.lastHeadAtRight e p
-- def_3_4 -- end statement

-- Auxiliary helper for `outOfVn` — symmetric to `lastHeadAtRight`,
-- asking whether the *last* edge step in `cons e p` has a tail at
-- its right-side index (i.e. is `.backward _`).  Structural
-- recursion on `p`; reduces by `rfl` (verified).
-- def_3_4 --- start helper
def Walk.lastTailAtRight {G : CDMG Node}
    : ∀ {u v w : Node}, EdgeStep G u v → Walk G v w → Prop
  | _, _, _, .forward _, .nil _ => False
  | _, _, _, .backward _, .nil _ => True
  | _, _, _, .bidir _, .nil _ => False
  | _, _, _, _, .cons e' p => Walk.lastTailAtRight e' p
-- def_3_4 --- end helper

-- def_3_4 -- start statement
def Walk.outOfVn {G : CDMG Node} {u w : Node} : Walk G u w → Prop
  | .nil _ => False
  | .cons e p => Walk.lastTailAtRight e p
-- def_3_4 -- end statement

/-! ## Item 5 — `IsPath` -/

-- ref: def_3_4 (item 5)
--
-- `Walk.IsPath p` says the walk `p` is a *path* in the LN's sense:
-- no vertex is repeated.  Encoded as `Nodup` on the support list.
/-
LN tex (item 5 of `\label{def:walks}`):

  A walk is called \emph{path} if no node occurs more than once.
-/
-- ## Design choice
--
-- *Why a predicate `Walk.IsPath : Walk G u w → Prop`, not a separate
--   `inductive Path` / structure with a `nodup` field.*  Two reasons.
--   1. The LN's item 5 is one sentence layered on top of "walk", not
--      a fresh concept.  A separate `Path` type would force a
--      coercion `Path → Walk` and re-derivation of `support /
--      length / concat / reverse` on the new type.  Mathlib's
--      `SimpleGraph.Walk.IsPath` is a structure with a `nodup`
--      field; we use a plain `Prop` for brevity — the LN does not
--      distinguish "this is a path" from "this walk satisfies the
--      path property" linguistically, so we collapse the two.
--   2. Downstream usage in chapter 3+ (e.g. d-/σ-separation through
--      paths, ancestral walks that happen to be paths) phrases path-
--      hood as a side condition on an existing walk; a predicate is
--      the natural shape for that.
--
-- *Why `p.support.Nodup`, not a list-of-distinct-vertices
--   formulation.*  Mathlib's `List.Nodup` is the standard "no
--   duplicates" predicate on lists; it gives us `Decidable` instances
--   (`Nodup.decidable` via `DecidableEq Node`), permutation-stability
--   lemmas, and `Finset`-conversion (`List.toFinset_card_eq_card` for
--   support-cardinality reasoning) for free.  A bespoke
--   "all-pairs-distinct" formulation would replicate this
--   infrastructure.
--
-- *Trivial walk is a path.*  The trivial walk `Walk.nil hv : Walk G
--   v v` has `support = [v]`, which is `Nodup` (a one-element list
--   has no duplicates).  This matches the LN's literal reading:
--   "no node occurs more than once" is vacuously true for a single-
--   node walk.
--
-- *Walks containing a cycle are not paths.*  Any walk visiting a
--   vertex twice (e.g.  `nil`-loop-prepended-walks, or the
--   `v_0 \tuh v_1 \hut v_0` shape from the LN's example) fails
--   `Nodup` by definition.  This matches the LN's intent.
--
-- *Downstream consumers.*  Chapter 5+ d-/σ-separation arguments
--   sometimes promote walks to paths (any walk between two vertices
--   can be shortened to a path by cutting out cycles); the standard
--   form of the argument is "let `p` be a walk, then `∃ q,
--   q.IsPath ∧ q.support ⊆ p.support`".  `Bifurcation` (in
--   `WalkBifurcation.lean`) uses `support.count = 1` constraints at
--   endpoints, not `IsPath` globally — the LN's bifurcation
--   condition is "both endnodes exactly once", weaker than full
--   `Nodup`.
-- def_3_4 -- start statement
def Walk.IsPath {G : CDMG Node} {u w : Node} (p : Walk G u w) : Prop :=
  p.support.Nodup
-- def_3_4 -- end statement

/-! ## Items 2, 3, 4 — `IsDirectedWalk`, `IsBidirectedWalk`,
`IsColliderWalk` -/

-- ref: def_3_4 (item 2)
--
-- `Walk.IsDirectedWalk p` says every `EdgeStep` in `p` is `.forward`
-- — the LN's "all arrowheads point in the direction of $w$ and there
-- are no arrowheads pointing back".  Vacuously true for the trivial
-- walk.
/-
LN tex (item 2 of `\label{def:walks}`):

  A \emph{directed walk} from $v$ to $w$ in $G$ is of the form:
    $v = v_0 \tuh v_1 \tuh \cdots \tuh v_{n-1} \tuh v_n = w$,
  for some $n \ge 0$, where all arrowheads point in the direction
  of $w$ and there are no arrowheads pointing back.
  % \item[] Directed walks exclude the trivial walk per definition.
-/
-- ## Design choice
--
-- *Why a predicate on `Walk`, not a fresh `inductive DirectedWalk`.*
--   Three reasons.
--   1. `def_3_5`'s `Anc^G(v) := {w \in G | \exists \text{ directed
--      walk: } w \tuh \cdots \tuh v \in G}` maps verbatim to
--      `∃ p : Walk G w v, p.IsDirectedWalk`.  A separate
--      `DirectedWalk` type would require a coercion at every such
--      existential.
--   2. A fresh inductive would re-derive `support`, `length`, and
--      all walk-level lemmas on a new type; the predicate form
--      reuses `Walk.support` / `Walk.length` directly.
--   3. Concatenation and sub-walk operations (used heavily in
--      chapter 5+ separation proofs and FCI in chapter 11+) are
--      written once on `Walk` and lifted to "directed walks" by
--      preserving `IsDirectedWalk`.  A separate inductive would
--      force per-type concat / sub-walk definitions.
--
-- *Pattern shape.*  `.nil _ => True` (vacuous);
--   `.cons (.forward _) p => p.IsDirectedWalk` (forward step,
--   recurse); both `.cons (.backward _) _` and `.cons (.bidir _) _`
--   return `False` (any non-forward step kills the directed
--   property).  Structural recursion on the tail walk; terminates.
--
-- *Trivial walk is a directed walk: subtlety
--   `trivial_walk_satisfies_all_specialized_walk_types`.*  Literal LN
--   "for some $n \ge 0$" admits $n = 0$, and the LN source even
--   shows a *commented-out* exclusion line ("% Directed walks
--   exclude the trivial walk per definition.") — the author actively
--   considered excluding the trivial walk and chose not to.  We
--   follow the literal LN: `(Walk.nil hv).IsDirectedWalk = True`.
--   Downstream consumers that need the *non-trivial* directed walk
--   (e.g.  `def_3_6` acyclicity: "non-trivial directed walk from
--   $v$ to itself") add `0 < p.length` at the use site.  Same
--   convention applies to `IsBidirectedWalk` / `IsColliderWalk`
--   below.
--
-- *Downstream consumers.*  `def_3_5` `Pa / Ch / Anc / Desc` (the
--   parent / child / ancestor / descendant sets are walk-
--   existentials with `IsDirectedWalk`); `def_3_5` `Sc^G` (strongly
--   connected components, via `Anc ∩ Desc`); `def_3_6` acyclicity
--   (`¬ ∃ p : Walk G v v, p.IsDirectedWalk ∧ 0 < p.length`);
--   `WalkBifurcation.lean` (the two arms of a `Bifurcation` are
--   both `IsDirectedWalk`); chapter 5+ identification / do-calculus
--   uses directed-walk reachability everywhere.
--
-- *Mathlib re-use.*  No direct analogue — Mathlib's
--   `SimpleGraph.Walk` lives on undirected graphs, so "directed
--   walk" is not a concept there.  We re-use `Walk` (which itself
--   is modelled on `SimpleGraph.Walk`) and the EdgeStep ADT to
--   construct the predicate from scratch.
--
-- *Constraints / known limitations.*
--   1. **No `Decidable (p.IsDirectedWalk)` instance.**  Decidability
--      follows from a straightforward structural recursion on `p`
--      (using `DecidableEq Node` to decide `Finset` membership at
--      each EdgeStep), but we do not provide the instance here;
--      downstream proofs reason via `cases p` / pattern matching on
--      EdgeStep constructors.  Add the instance on demand.
--   2. **`IsDirectedWalk` is preserved by sub-walks but not by
--      concatenation in general** — see `WalkBifurcation.lean`'s
--      design comments for an explicit case where two directed
--      arms are joined by a non-directed hinge edge.  A `concat`
--      operation for `Walk` (not yet defined) would preserve
--      `IsDirectedWalk` exactly when both operands are directed
--      walks; the bifurcation arms exploit this only at the per-arm
--      level, not across the hinge.
-- def_3_4 -- start statement
def Walk.IsDirectedWalk {G : CDMG Node} {u w : Node} : Walk G u w → Prop
  | .nil _ => True
  | .cons (.forward _) p => p.IsDirectedWalk
  | .cons (.backward _) _ => False
  | .cons (.bidir _) _ => False
-- def_3_4 -- end statement

-- ref: def_3_4 (item 3)
--
-- `Walk.IsBidirectedWalk p` says every `EdgeStep` in `p` is `.bidir`
-- — the LN's "where all edges are bidirected".  Vacuously true for
-- the trivial walk.
/-
LN tex (item 3 of `\label{def:walks}`):

  A \emph{bidirected walk} from $v$ to $w$ in $G$ is of the form:
    $v = v_0 \huh v_1 \huh \cdots \huh v_{n-1} \huh v_n = w$,
  for some $n \ge 0$, where all edges are bidirected.
-/
-- ## Design choice
--
-- *Direct analogue of `IsDirectedWalk` with `.bidir` in place of
--   `.forward`.*  Same predicate-on-`Walk` rationale as
--   `IsDirectedWalk`; same `nil = True` (vacuous) / `cons (.bidir
--   _) p = recurse` / otherwise `False` shape.
--
-- *Trivial walk is a bidirected walk: subtlety
--   `trivial_walk_satisfies_all_specialized_walk_types`.*  The LN
--   does *not* include a commented-out exclusion line for item 3
--   (unlike item 2), but the literal `n \ge 0` admits $n = 0$ and
--   the registered subtlety propagates the same reading: silent
--   inclusion of the trivial walk by uniformity with item 2.
--   Downstream consumers requiring a non-trivial bidirected walk
--   add `0 < p.length` at the use site.
--
-- *Downstream consumers.*  `def_3_5` `Sib^G` (siblings, walk-length-
--   1 bidirected walks) and `Dist^G` (district = bidirected-walk
--   reachable set) are the two primary consumers; the latter
--   builds `Dist^G(v) := {w | \exists \text{ bidirected walk: } v
--   \huh v_1 \huh \cdots \huh v_{n-1} \huh w}` directly.  Chapter
--   5+ `m`-connection arguments use bidirected walks as a building
--   block in collider analysis.
-- def_3_4 -- start statement
def Walk.IsBidirectedWalk {G : CDMG Node} {u w : Node} : Walk G u w → Prop
  | .nil _ => True
  | .cons (.bidir _) p => p.IsBidirectedWalk
  | .cons (.forward _) _ => False
  | .cons (.backward _) _ => False
-- def_3_4 -- end statement

-- ref: def_3_4 (item 4 — supporting helper)
--
-- `Walk.IsColliderTail e p` is the "tail half" of the collider-walk
-- form, used for the recursive case `n ≥ 2` of `IsColliderWalk`.
-- The helper takes a *current* edge step `e : EdgeStep G u v` (= the
-- next `a_k` to inspect) and the *remaining* tail walk `p : Walk G v
-- w`.  It encodes the constraints "all remaining middle steps are
-- `.bidir` and the last step has its head at its LEFT-side index (=
-- head at $v_{n-1}$, which equals `.backward _` or `.bidir _`)".
/-
LN tex (item 4 of `\label{def:walks}`, recurring context — see the
`IsColliderWalk` block below for the full LN quote):

  A \emph{collider walk} from $v$ to $w$ in $G$ is of the form:
    $v = v_0 \suh v_1 \huh \cdots \huh v_{n-1} \hus v_n = w$,
  for some $n \ge 0$, where all nodes in between $v$ and $w$ have
  two arrowheads pointing towards them …
-/
-- ## Design choice
--
-- *Helper because the `IsColliderWalk` recursion is "stateful".*
--   The collider-walk form distinguishes the *first* edge (head at
--   $v_1$ = `.forward` or `.bidir`), the *middle* edges (all
--   `.bidir`), and the *last* edge (head at $v_{n-1}$ = `.backward`
--   or `.bidir`).  After `IsColliderWalk` consumes the first edge,
--   the rest of the walk needs a different recursion shape than the
--   first step — "middle then last" rather than "first then rest".
--   Encapsulating that as `IsColliderTail` keeps `IsColliderWalk`
--   readable.
--
-- *Why the `EdgeStep G u v → Walk G v w → Prop` signature (rather
--   than `Walk G u w → Prop`).*  An earlier draft had
--   `IsColliderTail : Walk G u w → Prop` matching on the first cons
--   of the walk, with `p@(.cons _ _)` as-pattern on the recursive
--   branch.  That shape compiles (`lake build` clean) but the
--   as-pattern pushes the compiler into well-founded-recursion mode,
--   which BLOCKS definitional `rfl` reduction on the base cases
--   (`(Walk.nil _).IsColliderTail = True` was not `rfl`-equal).
--   Lifting the "current step" into an explicit `EdgeStep` parameter
--   eliminates the as-pattern and restores `rfl`-reduction in every
--   base case (verified against /tmp test files before commit).
--   This is the same trick used by `lastHeadAtRight / lastTailAtRight`
--   above.
--
-- *Pattern table (six cases, all exhaustive).*
--   1.  `e = .bidir _, p = .nil _ => True`         — last step `.bidir`, head at left of `e` ✓.
--   2.  `e = .backward _, p = .nil _ => True`      — last step `.backward`, head at left ✓.
--   3.  `e = .forward _, p = .nil _ => False`      — last step `.forward`, no head at left ✗.
--   4.  `e = .bidir _, p = .cons e' p' =>
--           IsColliderTail e' p'`                   — middle `.bidir`, recurse on `(e', p')`.
--   5.  `e = .forward _, p = .cons _ _ => False`   — middle `.forward` ≠ `.bidir` ✗.
--   6.  `e = .backward _, p = .cons _ _ => False`  — middle `.backward` ≠ `.bidir` ✗.
--
-- *Naming.*  `IsColliderTail` reads "the *tail* of a candidate
--   collider walk, anchored at the current edge step `e`, satisfies
--   the middle / last constraints".  Internal-use helper;
--   downstream consumers should reach for `IsColliderWalk`.
-- def_3_4 --- start helper
def Walk.IsColliderTail {G : CDMG Node}
    : ∀ {u v w : Node}, EdgeStep G u v → Walk G v w → Prop
  | _, _, _, .bidir _, .nil _ => True
  | _, _, _, .backward _, .nil _ => True
  | _, _, _, .forward _, .nil _ => False
  | _, _, _, .bidir _, .cons e' p => Walk.IsColliderTail e' p
  | _, _, _, .forward _, .cons _ _ => False
  | _, _, _, .backward _, .cons _ _ => False
-- def_3_4 --- end helper

-- ref: def_3_4 (item 4)
--
-- `Walk.IsColliderWalk p` says `p` is a *collider walk* in the LN's
-- sense: the alternation `v_0 \suh v_1 \huh \cdots \huh v_{n-1} \hus
-- v_n` holds.  Three regimes by length:
--   * `n = 0` (trivial walk): vacuous, `True`.
--   * `n = 1` (single edge): the edge MUST be `.bidir` per LN
--     addition `[collider_walk_n1_form_contradicts_inline_note]`.
--   * `n ≥ 2`: first step is `.forward` or `.bidir` (head at $v_1$);
--     interior steps are all `.bidir`; last step is `.backward` or
--     `.bidir` (head at $v_{n-1}$).
/-
LN tex (item 4 of `\label{def:walks}`):

  A \emph{collider walk} from $v$ to $w$ in $G$ is of the form:
    $v = v_0 \suh v_1 \huh \cdots \huh v_{n-1} \hus v_n = w$,
  for some $n \ge 0$, where all nodes in between $v$ and $w$ have
  two arrowheads pointing towards them (a.k.a.\ collider).
  Note that for $n = 1$ this reads: $v \sus w \in G$.

LN addition `[collider_walk_n1_form_contradicts_inline_note]` (treated
as part of the LN):

  For $n = 1$, a collider walk from $v$ to $w$ requires a bidirected
  edge $v \huh w \in E$ (arrowheads at both endpoints), as dictated
  by the form $v_0 \suh v_1$ combined with $v_{n-1} \hus v_n$
  collapsing onto the single edge.  The inline note
  "$v \sus w \in G$" is to be read in this stricter sense and does
  *not* admit purely directed edges $v \tuh w$ or $v \hut w$ as
  collider walks of length 1.
-/
-- ## Design choice
--
-- *Resolution of the n=1 form-vs-note inconsistency.*  The LN's
--   formal pattern $v_0 \suh v_1 \huh \cdots \huh v_{n-1} \hus v_n$
--   for $n = 1$ collapses the first segment ($v_0 \suh v_1$) and
--   the last segment ($v_{n-1} \hus v_n$) onto the *same* edge.
--   That single edge must simultaneously satisfy `\suh` (head at
--   $v_1$) AND `\hus` (head at $v_0$), i.e. arrowheads at both
--   endpoints — a bidirected edge.  The LN's inline note "for
--   $n = 1$ this reads: $v \sus w \in G$" appears to admit *any*
--   edge (`\sus` ranges over directed and bidirected), which
--   contradicts the formal pattern.  Working-phase wording-check
--   subtlety `collider_walk_n1_pattern_contradicts_note` flagged
--   the contradiction; the operator's addition
--   `[collider_walk_n1_form_contradicts_inline_note]` resolves it
--   in favor of the *form* — the inline note is read in the
--   stricter "bidirected only" sense.  Cases 2/3/4 of the pattern
--   table below encode this:
--     `.cons (.bidir _) (.nil _) => True`,
--     `.cons (.forward _) (.nil _) => False`,
--     `.cons (.backward _) (.nil _) => False`.
--
-- *Worked example for `n = 1`.*
--   * `Walk.cons (.bidir hL) (Walk.nil hv)` where `hL : G.huh v_0 v_1`
--     is `IsColliderWalk` ✓.
--   * `Walk.cons (.forward hE) (Walk.nil hv)` where `hE : G.tuh v_0
--     v_1` is NOT `IsColliderWalk` ✗ — even though `v_0 \sus v_1 \in
--     G` holds, the strict form requires the bidirected edge.
--   * `Walk.cons (.backward hE) (Walk.nil hv)` where `hE : G.hut v_0
--     v_1` is NOT `IsColliderWalk` ✗ — same reason.
--
-- *The "all interior nodes are colliders" prose is a *consequence*,
--   not an additional constraint.*  The LN says "all nodes in
--   between $v$ and $w$ have two arrowheads pointing towards them
--   (a.k.a. collider)".  In our shape: for $n \ge 2$, every
--   interior node $v_k$ (with $1 \le k \le n-1$) sits between two
--   `EdgeStep`s.  The interior `.bidir`-only constraint forces both
--   incident edges to have heads at $v_k$ → collider.  The first
--   interior node $v_1$ gets its left arrowhead from the first
--   `EdgeStep` (`.forward` head-at-right OR `.bidir` head-at-both);
--   the last interior node $v_{n-1}$ gets its right arrowhead from
--   the last `EdgeStep` (`.backward` head-at-left OR `.bidir`
--   head-at-both).  So the prose IS the form's structural content
--   re-described — no extra check needed.
--
-- *Trivial walk is a collider walk: subtlety
--   `trivial_walk_satisfies_all_specialized_walk_types`.*  $n = 0$
--   admits the trivial walk vacuously; the form's interior-collider
--   condition is empty.  Same reading as `IsDirectedWalk` /
--   `IsBidirectedWalk` — silent inclusion of `nil`.  Downstream
--   consumers needing a non-trivial witness add `0 < p.length`.
--
-- *Pattern table (seven cases, all exhaustive).*
--   1.  `.nil _ => True`                            — $n = 0$.
--   2.  `.cons (.bidir _) (.nil _) => True`         — $n = 1$, bidirected ✓.
--   3.  `.cons (.forward _) (.nil _) => False`      — $n = 1$, directed; head only at $v_1$.
--   4.  `.cons (.backward _) (.nil _) => False`     — $n = 1$, directed; head only at $v_0$.
--   5.  `.cons (.forward _) (.cons e' p) =>
--           Walk.IsColliderTail e' p`                — $n \ge 2$; first `.forward` (head at $v_1$).
--   6.  `.cons (.bidir _) (.cons e' p) =>
--           Walk.IsColliderTail e' p`                — $n \ge 2$; first `.bidir` (head at $v_1$).
--   7.  `.cons (.backward _) (.cons _ _) => False`  — $n \ge 2$; `.backward` (no head at $v_1$).
--
-- *Why explicit `(.cons e' p) => IsColliderTail e' p`, not
--   `p@(.cons _ _) => p.IsColliderTail`.*  Same rationale as for
--   `intoVn / outOfVn` and `IsColliderTail` itself: the as-pattern
--   shape blocks `rfl`-reduction on the base cases of the helper.
--   Decomposing the inner cons and threading `(e', p)` through to
--   `IsColliderTail` keeps the whole stack reducing definitionally.
--
-- *Downstream consumers.*  Every `m`-connection / `σ`-separation /
--   `d`-separation argument in chapters 5+ (and notably the
--   commented-out `MBl^G_d / MBl^G_σ` definitions in `def_3_5`)
--   inspects collider walks; FCI in chapter 11+ uses collider
--   walks as the structural building block for orienting edges
--   during discovery.  The n=1 bidirected-only reading is the
--   load-bearing case for "an edge between two siblings is a
--   collider walk of length 1" — chapter 5+ proofs rely on this.
--
-- *Addition enforced here (load-bearing).*  The pattern table
--   above is *where the operator addition
--   `[collider_walk_n1_form_contradicts_inline_note]` is honoured*
--   on the type.  Cases 2/3/4 (the three `n = 1` patterns) jointly
--   encode the addition: only `.bidir` survives.  This is the
--   contractual link between the LN addition (which is part of the
--   authoritative LN per the project's `addition_to_the_LN`
--   convention) and the formalisation; should a future refactor
--   touch this definition, the addition's encoding must be
--   preserved or the row's verifier-PASS status invalidated.
--
-- *Mathlib re-use.*  No Mathlib analogue: Mathlib has no notion of
--   "collider walk" — colliders are a graphical-causality concept
--   specific to mixed graphs.  We roll our own, building on the
--   `Walk` / `EdgeStep` inductives above.
--
-- *Constraints / known limitations.*
--   1. **Length-0 (trivial walk) is vacuously a collider walk.**
--      As documented, this follows literal LN ($n \ge 0$).  No
--      downstream caller seems to want this behaviour (the LN
--      writes "all nodes in between" presupposing $n \ge 2$ or so),
--      but the literal-LN reading is what we encode; consumers
--      needing $n \ge 1$ or $n \ge 2$ add the length hypothesis
--      explicitly.
--   2. **The recursive `IsColliderTail` helper is internal.**
--      Callers should always invoke `IsColliderWalk` on a full
--      walk; the helper is exposed only because Lean cannot inline
--      it without breaking `rfl`-reduction.  A future cleanup
--      could `private`-namespace the helper, but it currently
--      sits at the public `Walk.` level for simplicity.
--   3. **No `Decidable` instance.**  `IsColliderWalk p` is
--      definitionally a `Prop`; decidability would follow from a
--      structural recursion on `p` but is not currently provided.
--      Should chapter-5+ proofs need `if p.IsColliderWalk then …`,
--      add the instance on demand (a straightforward induction
--      using the seven-case table).
-- def_3_4 -- start statement
def Walk.IsColliderWalk {G : CDMG Node} {u w : Node} : Walk G u w → Prop
  | .nil _ => True
  | .cons (.bidir _) (.nil _) => True
  | .cons (.forward _) (.nil _) => False
  | .cons (.backward _) (.nil _) => False
  | .cons (.forward _) (.cons e' p) => Walk.IsColliderTail e' p
  | .cons (.bidir _) (.cons e' p) => Walk.IsColliderTail e' p
  | .cons (.backward _) (.cons _ _) => False
-- def_3_4 -- end statement

end Causality
