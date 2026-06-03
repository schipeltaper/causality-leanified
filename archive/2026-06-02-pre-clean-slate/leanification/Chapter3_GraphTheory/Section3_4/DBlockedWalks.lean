import Chapter3_GraphTheory.Section3_1.FamilyReachability
import Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks

/-!
# $d$-blocked walks (def 3.19)

This file formalises *definition 3.19* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`),
which opens section 3.4 ($id$-Separation): the classification
of a walk $\pi$ in a CDMG $G$, relative to a conditioning set
$C \subseteq J \cup V$, as either *$C$-$d$-blocked* or
*$C$-$d$-open*.

## Predicates exposed (under `Causality.Walk`)

* `IsDBlocked (π : Walk G v w) (C : Set α) : Prop` -- LN's
  "$\pi$ is $C$-$d$-blocked": either an endpoint of $\pi$
  lies in $C$, or some interior non-collider on $\pi$ lies
  in $C$, or some collider on $\pi$ lies outside
  $\Anc^G(C)$.
* `IsDOpen (π : Walk G v w) (C : Set α) : Prop` -- LN's
  "$\pi$ is $C$-$d$-open": the literal negation of
  `π.IsDBlocked C`, exactly as the LN states.

Plus defining-equation lemmas `isDBlocked_iff` and
`isDOpen_iff_not_isDBlocked`, both `Iff.rfl`.

## LN-clause structure preserved literally

The LN's clause (i) is "$v_0 \in C$ or $v_n \in C$"
(endpoint clause). Its clause (ii) enumerates four
sub-patterns at an interior position $k$:
$v_{k-1} \hut v_k \hus v_{k+1}$ (left chain),
$v_{k-1} \suh v_k \tuh v_{k+1}$ (right chain), and
$v_{k-1} \hut v_k \tuh v_{k+1}$ (fork) -- each with
$v_k \in C$ -- followed by
$v_{k-1} \suh v_k \hus v_{k+1}$ (collider) with
$v_k \notin \Anc^G(C)$. The first three sub-patterns of
clause (ii) together exhaust "interior non-collider in $C$";
the fourth is "interior collider not in $\Anc^G(C)$".

`IsDBlocked` is therefore the four-way disjunction
(endpoint $v_0$, endpoint $v_n$, interior non-collider,
collider), in the LN's exact reading order.

The `0 < k ∧ k < π.length` interior bound on the
non-collider disjunct is essential to keep the four
disjuncts *disjoint at the literal LN reading*: without it,
the non-collider clause would absorb the two endpoint
clauses (since `isNonColliderAt_zero` and
`isNonColliderAt_length` from `Section3_3.CollidersAndNon`
hold unconditionally on any walk). The collider disjunct
needs no bound: `IsColliderAt` is `False` at $k = 0$,
$k = \pi.\text{length}$ and at out-of-range positions, so
any witness is automatically interior.

## Downstream usage

* **def_3_20** ($i$-$d$-separation / $id$-separation):
  consumes `IsDBlocked` directly as the per-walk blocking
  predicate, mirroring how def_3_18 consumes
  `IsSigmaBlocked` for $i$-$\sigma$-separation.
* **claim_3_28** (Non-collider characterisation): proves
  the LN's *collapsed* form, "$\pi$ is $C$-$d$-blocked iff
  some non-collider position is in $C$ or some collider
  position is not in $\Anc^G(C)$" -- i.e. the four-disjunct
  shape collapses to a two-disjunct shape because the
  endpoint clauses are absorbed by the non-collider clause
  once the interior bound is dropped. The equivalence is
  *non-trivial* precisely because we keep the literal LN
  shape here; it would be vacuous (`Iff.rfl`) if we baked
  the collapse into `IsDBlocked`.
* **claim_3_29** ($d$-separation symmetry): pivots between
  `IsDBlocked` (or `IsDOpen`) and its analogue on the
  reversed walk.
* **claim_3_30** ($id$-separation properties:
  marginalisation stability and the structural
  preservation analogous to claim_3_16's marginalisation
  invariance for the family-reachability operator).
* Chapters 4 onwards (Markov properties, do-calculus,
  identification, iSCMs) consume `IsDBlocked` and
  `IsDOpen` through $d$-separation; this row is the
  *foundational* per-walk graphical condition for that
  whole downstream chain.

## How this differs from $\sigma$-blocked walks (def 3.17,
`Section3_3.SigmaBlockedWalks`)

1. **Endpoint clause.** $d$-blocked has an explicit
   endpoint clause (LN clause (i): $v_0 \in C$ or
   $v_n \in C$). $\sigma$-blocked has none -- every
   position in def_3_17 is examined under either
   `IsColliderAt` or `IsBlockableNonColliderAt`, and the
   LN's $\sigma$-clauses neither single out nor exclude
   endpoints.

2. **All non-colliders, not just blockable.** $d$-blocked
   uses `IsNonColliderAt` (every non-collider position).
   $\sigma$-blocked uses `IsBlockableNonColliderAt` (only
   the def_3_16 sub-classification of non-colliders that
   can be "blocked" by the coreflexive-edge boundary).
   Under acyclicity, claim_3_20
   (`AcyclicNonCollidersBlockable.lean`) proves the two
   collapse to the same family of walks; but as
   foundational definitions they differ, and the
   difference is precisely the
   `IsBlockableNonColliderAt`-vs-`IsNonColliderAt`
   distinction.

3. **Open is the negation, not a parallel positive
   predicate.** In `IsSigmaOpen` / `IsSigmaBlocked`, the
   LN supplies *two parallel positive definitions* (a
   conjunction of two universals for open, a disjunction
   of two existentials for blocked), and the De-Morgan
   dual `isSigmaBlocked_iff_not_isSigmaOpen` is proven as
   a sanity lemma using classical reasoning. In
   `IsDBlocked` / `IsDOpen`, the LN supplies *only* the
   blocked clause as a positive definition and *defines*
   open as its literal negation. We mirror that: `IsDOpen
   := ¬ IsDBlocked` syntactically, no separate positive
   definition.

## Style precedents

* `Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks`
  (def_3_17) -- closest analogue; same module shape,
  per-declaration design-choice block convention,
  per-LN-clause $\to$ Lean disjunct correspondence,
  `Walk.nodeAt` / position-indexing convention.
* `Chapter3_GraphTheory.Section3_3.CollidersAndNon`
  (def_3_15) -- source of `IsColliderAt`,
  `IsNonColliderAt`, the endpoint lemmas
  `isNonColliderAt_zero` and `isNonColliderAt_length`
  used here as design-choice justifications.
* `Chapter3_GraphTheory.Section3_1.FamilyReachability`
  (def_3_5) -- source of `AncSet G C`, the LN's
  $\Anc^G(C)$.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

/-! ### IsDBlocked (LN def 3.19, item 1) -/

-- def_3_19 (item 1)
-- title: Walks -- d-blocked walk predicate
--
-- `π.IsDBlocked C` says the walk $\pi$ is $C$-$d$-blocked,
-- per the LN's literal four-clause shape:
--   (i)  $v_0 \in C$ or $v_n \in C$, or
--   (ii) some interior non-collider $v_k$ is in $C$
--        (the left-chain / right-chain / fork sub-patterns
--        together), or some collider $v_k$ is not in
--        $\Anc^G(C)$.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.19,
item 1):

  Let $G=(J,V,E,L)$ be a CDMG and $C \ins J \cup V$ a subset of
  nodes and $\pi$ a walk in $G$:
    $\pi =\lp v_0 \sus \cdots \sus v_n \rp.$
  We say that the walk $\pi$ is \emph{$C$-$d$-blocked} or
  \emph{$d$-blocked by $C$} ... if either:
    i.)  $v_0 \in C$ or $v_n \in C$ or:
    ii.) there are two adjacent edges in $\pi$ of one of the
         following forms:
           left chain:  $v_{k-1} \hut v_k \hus v_{k+1}$, with $v_k \in C$,
           right chain: $v_{k-1} \suh v_k \tuh v_{k+1}$, with $v_k \in C$,
           fork:        $v_{k-1} \hut v_k \tuh v_{k+1}$, with $v_k \in C$,
           collider:    $v_{k-1} \suh v_k \hus v_{k+1}$, with
                        $v_k \notin \Anc^G(C).$
-/
--
-- ## Design choice
--
-- * **`Prop`-valued four-way disjunction, in the LN's exact
--   reading order: $v_0$ endpoint, $v_n$ endpoint, interior
--   non-collider, collider.** The LN's clauses (i) and (ii)
--   are joined by "if either ... or"; clause (ii) enumerates
--   four sub-patterns (left/right chain, fork, collider)
--   joined by "of one of the following forms". The first
--   three sub-patterns of (ii) all read "$v_k \in C$" under a
--   *non-collider* shape (at most one arrowhead at $v_k$);
--   together they exhaust "$v_k$ is an interior non-collider
--   in $C$". At the Lean level clause (ii) therefore splits
--   into two disjuncts:
--     `∃ k, 0 < k ∧ k < π.length ∧ π.IsNonColliderAt k ∧
--           π.nodeAt k ∈ C`
--   (the three chain/fork sub-patterns) and
--     `∃ k, π.IsColliderAt k ∧ π.nodeAt k ∉ G.AncSet C`
--   (the fourth sub-pattern). Together with the two
--   endpoint clauses from (i) we land on four disjuncts in
--   the LN's order.
--
-- * **Why preserve the literal 4-disjunct shape rather than
--   the collapsed 2-disjunct form.** With our
--   `IsNonColliderAt` definition, $v_0$ and $v_n$ are
--   *always* non-colliders (`isNonColliderAt_zero` and
--   `isNonColliderAt_length` from
--   `Section3_3.CollidersAndNon` are unconditional). So a
--   single "$\exists k, π.\text{IsNonColliderAt}\ k \land
--   π.\text{nodeAt}\ k \in C$" disjunct -- *with no interior
--   bound* -- already subsumes the two endpoint clauses. The
--   LN's clause-(i) endpoints + clause-(ii) interior
--   non-collider then collapse to the two-disjunct form
--   "some non-collider is in $C$, or some collider is not in
--   $\Anc^G(C)$". That collapsed form is the *content* of
--   the very next row -- claim_3_28, the LN's remark right
--   after def_3_19. Baking the collapse into `IsDBlocked`
--   would make claim_3_28 vacuous (`Iff.rfl`), which would
--   silently delete a theorem-statement the LN explicitly
--   articulates. We therefore keep the LN's literal
--   four-disjunct shape here, and let claim_3_28 carry the
--   equivalence as a real lemma.
--
-- * **Interior bound `0 < k ∧ k < π.length` on the
--   non-collider disjunct; no bound on the collider
--   disjunct.** The non-collider disjunct *needs* the
--   interior bound for the same reason it preserves the LN
--   shape: without it, the unconditional
--   `π.IsNonColliderAt 0` and
--   `π.IsNonColliderAt π.length` would let any walk with
--   $v_0 \in C$ (resp. $v_n \in C$) trigger the
--   non-collider disjunct, collapsing the four-disjunct
--   structure. The collider disjunct, by contrast, needs no
--   bound because `IsColliderAt` is already `False` at
--   $k = 0$, $k = \pi.\text{length}$ and at out-of-range
--   positions -- per the
--   `cons _ (nil _), _ ↦ False` exit case and the
--   `cons _ (cons _ _), 0 ↦ False` end-node case of
--   `CollidersAndNon.IsColliderAt`. Any witness $k$ in the
--   collider disjunct is therefore *automatically* interior,
--   without us writing a bound. Adding a redundant
--   `0 < k ∧ k < π.length` to the collider disjunct would
--   only force every downstream proof to discharge a bound
--   the per-position predicate already implies.
--
-- * **`IsNonColliderAt` (every non-collider), *not*
--   `IsBlockableNonColliderAt`.** This is the principal
--   shape-level difference between $d$-blocking (def_3_19)
--   and $\sigma$-blocking (def_3_17, see
--   `Section3_3.SigmaBlockedWalks`). $\sigma$-blocking
--   restricts attention to *blockable* non-colliders -- a
--   def_3_16 sub-classification rooted in the
--   coreflexive-edge boundary of the CDMG; non-blockable
--   non-colliders are "$\sigma$-open for free" per
--   claim_3_21. $d$-blocking makes no such restriction:
--   *every* non-collider position is a potential blocker.
--   Under acyclicity, claim_3_20
--   (`AcyclicNonCollidersBlockable.lean`) reconciles the
--   two by proving "non-collider = blockable non-collider",
--   but at the foundational level the predicates differ,
--   and the difference is exactly the
--   `IsBlockableNonColliderAt`-vs-`IsNonColliderAt`
--   distinction. Using `IsBlockableNonColliderAt` here
--   would silently make def_3_19 *equal* to def_3_17 (in
--   the absence of the endpoint clause), which is wrong:
--   claim_3_20 would then be vacuous, and the chapters
--   $\ge 4$ that distinguish $d$- from $\sigma$-separation
--   would lose their foundational difference.
--
-- * **`AncSet G C`, not `⋃ v ∈ C, Anc G v` inlined.** Same
--   rationale as in def_3_17
--   (`Section3_3.SigmaBlockedWalks`): reuse the operator
--   from def_3_5 (`Section3_1.FamilyReachability`) together
--   with its `mem_AncSet` simp lemma, set-reflexivity, and
--   downstream API. Keeps def_3_19 aligned with how the LN
--   composes the LN's $\Anc^G(C)$ on top of def_3_5, and
--   keeps the next claims' proofs working through the same
--   API rather than re-deriving the big-union structure
--   each time.
--
-- * **`C : Set α`, not a `{ C // C ⊆ G.J ∪ G.V }`
--   subtype.** Same rationale as in def_3_17. The LN's
--   "$C \ins J \cup V$" preamble is a side-condition stated
--   in standard set-theoretic prose, not a type-level
--   restriction; `AncSet G C` already silently ignores
--   members outside `G.J ∪ G.V`. Carrying a subtype would
--   pollute every downstream signature (def_3_20, the
--   claim_3_28 / 29 / 30 chain, chapter $\ge 4$ Markov
--   properties and do-calculus) for no proof ergonomic
--   gain. *Known limitation*: the LN's
--   "$C \subseteq J \cup V$" preamble therefore lives
--   *off-type* -- the predicate itself accepts any
--   `C : Set α` and is well-defined on nodes outside
--   `G.J ∪ G.V` via `AncSet`'s "ignore-out-of-graph"
--   convention. Any downstream consumer that genuinely
--   depends on the side-condition (def_3_20 pinning
--   $A$ / $B$ / $C$ inside the graph, chapter $\ge 4$
--   Markov / do-calculus reasoning that quantifies over
--   "all conditioning sets in the graph") must state it
--   as a separate hypothesis at the call site; the
--   predicate cannot enforce it.
--
-- * **`π` first, `C` second.** Lean's dot-notation
--   `π.IsDBlocked C` works iff `π` is the first explicit
--   argument; we follow the same convention as every other
--   walk predicate in chapter 3 (`π.IsColliderAt k`,
--   `π.IsNonColliderAt k`, `π.IsSigmaOpen C`,
--   `π.IsSigmaBlocked C`, ...).
--
-- * **No structural recursion, no per-constructor `@[simp]`
--   characterisation lemmas.** `IsDBlocked` is a one-line
--   composition of already-recursively-defined per-position
--   predicates (`IsColliderAt`, `IsNonColliderAt`,
--   `nodeAt`); there are no walk-shape case splits to
--   characterise here. Downstream proofs simply unfold
--   `IsDBlocked` once and dispatch the four disjuncts via
--   the underlying simp lemmas from `CollidersAndNon` and
--   `SigmaBlockedWalks`. *Known limitation*: because
--   `IsDBlocked` is not an `inductive` predicate over walk
--   constructors, a proof of "$\pi$ is $C$-$d$-blocked
--   $\implies P\ \pi$" cannot walk-induct in a single step
--   (there is no `case IsDBlocked.cons` to peel one step
--   off the head and recurse on the tail). Such proofs
--   instead unfold to the four-disjunct shape and then
--   walk-induct on the per-position predicates -- the
--   pattern claim_3_28's collapsed-form equivalence and
--   claim_3_29's symmetry pivot both follow. An
--   `inductive IsDBlocked` shape would buy a one-step
--   `cons`-induction but at the cost of hiding the
--   existential witnesses behind constructors, which the
--   four-disjunct form keeps directly accessible.

/-- The walk `π` is *$C$-$d$-blocked* (LN def 3.19, item 1):
either $v_0$ or $v_n$ lies in `C`, or some interior
non-collider position on `π` lies in `C`, or some collider
position on `π` lies outside $\Anc^G(C)$. -/
def IsDBlocked {v w : α} (π : Walk G v w) (C : Set α) : Prop :=
  (π.nodeAt 0 ∈ C) ∨
  (π.nodeAt π.length ∈ C) ∨
  (∃ k, 0 < k ∧ k < π.length ∧ π.IsNonColliderAt k ∧ π.nodeAt k ∈ C) ∨
  (∃ k, π.IsColliderAt k ∧ π.nodeAt k ∉ G.AncSet C)

/-- Defining equation for `IsDBlocked`. Useful when unfolding
the definition directly. -/
theorem isDBlocked_iff {v w : α} (π : Walk G v w) (C : Set α) :
    π.IsDBlocked C ↔
      (π.nodeAt 0 ∈ C) ∨
      (π.nodeAt π.length ∈ C) ∨
      (∃ k, 0 < k ∧ k < π.length ∧ π.IsNonColliderAt k ∧ π.nodeAt k ∈ C) ∨
      (∃ k, π.IsColliderAt k ∧ π.nodeAt k ∉ G.AncSet C) :=
  Iff.rfl

/-! ### IsDOpen (LN def 3.19, item 2) -/

-- def_3_19 (item 2)
-- title: Walks -- d-open walk predicate
--
-- `π.IsDOpen C` says the walk $\pi$ is $C$-$d$-open: it is
-- *not* $C$-$d$-blocked. The LN's clause "we say that the
-- walk $\pi$ is $C$-$d$-open if it is not $C$-$d$-blocked"
-- is, in our formalisation, the *definitional* shape of
-- `IsDOpen`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.19,
item 2):

  We say that the walk $\pi$ is \emph{$C$-$d$-open} if it is
  not $C$-$d$-blocked.
-/
--
-- ## Design choice
--
-- * **Defined as the literal negation of `IsDBlocked`, not
--   as a parallel positive predicate.** The LN supplies
--   *only* the $d$-blocked clause as a positive definition
--   (with four sub-cases for clause (ii)) and then defines
--   $d$-open as its negation in a single line: "we say that
--   the walk $\pi$ is $C$-$d$-open if it is not
--   $C$-$d$-blocked". This is structurally different from
--   def_3_17 ($\sigma$-blocked / open), where the LN
--   supplies *two parallel positive definitions* (a
--   conjunction of two universals for $\sigma$-open, a
--   disjunction of two existentials for $\sigma$-blocked)
--   and the De-Morgan dual
--   `isSigmaBlocked_iff_not_isSigmaOpen` has to be proven
--   as a separate sanity lemma using classical reasoning.
--   In def_3_19, the LN itself flips the asymmetry:
--   $d$-blocked is primary, $d$-open is the negation. We
--   mirror that.
--
--   Three consequences:
--   (a) There is no separate "$d$-open as a positive
--       conjunction of universals" definition exposed by
--       this module. A proof that wants the positive shape
--       unfolds `IsDOpen` to `¬ IsDBlocked`, applies De
--       Morgan to the four-way disjunction, and lands at
--       the dual conjunction of four universals. This
--       positive shape is *derived*, not the definition.
--   (b) There is no separate
--       `isDBlocked_iff_not_isDOpen` sanity lemma:
--       `IsDOpen ↔ ¬ IsDBlocked` is `Iff.rfl` by definition.
--       We expose `isDOpen_iff_not_isDBlocked` (below) for
--       discoverability and call-site readability, but its
--       proof is one `Iff.rfl` and there is no classical
--       reasoning anywhere in this file.
--   (c) Downstream consumers (claim_3_29 $d$-separation
--       symmetry, claim_3_30 marginalisation stability,
--       chapter $\ge 4$ Markov-property proofs) cite
--       `IsDBlocked` (the positive predicate with extractable
--       witnesses) far more often than `IsDOpen`; consumers
--       that want "open = no blocking witness anywhere"
--       pivot through `isDOpen_iff_not_isDBlocked` once and
--       then negate.
--
-- * **No `Classical.em` boilerplate.** Unlike
--   `isSigmaBlocked_iff_not_isSigmaOpen` -- which needs
--   classical reasoning to pull a witness out of
--   `¬ IsSigmaOpen` -- the definitional negation here is
--   syntactic; `isDOpen_iff_not_isDBlocked` is `Iff.rfl`.
--   *Known limitation*: the positive conjunctive shape of
--   $d$-open ("every endpoint not in $C$, every interior
--   non-collider not in $C$, every collider in $\Anc^G(C)$")
--   is *derived*, not the definition; a downstream consumer
--   that wants it must apply De Morgan +
--   `Classical.not_or` / `Classical.not_exists` /
--   `not_and` to the four-disjunct unfold of
--   `¬ IsDBlocked`. That classical cost is paid by callers
--   on-demand, not eagerly here, and is the price of
--   keeping the LN's "open = not blocked" framing as the
--   primitive shape.
--
-- * **Same `C : Set α` / `π`-first conventions as
--   `IsDBlocked`.** Keeps the two predicates in lockstep:
--   any rewrite of `IsDOpen` to `¬ IsDBlocked` reads
--   syntax-for-syntax, and downstream proofs that pivot
--   between the two predicates do so without
--   variable-naming drift.

/-- The walk `π` is *$C$-$d$-open* (LN def 3.19, item 2):
the literal negation of `π.IsDBlocked C`. -/
def IsDOpen {v w : α} (π : Walk G v w) (C : Set α) : Prop :=
  ¬ π.IsDBlocked C

/-- Defining equation for `IsDOpen`. The LN-original
characterisation: "$\pi$ is $C$-$d$-open iff it is not
$C$-$d$-blocked". Holds by definition. -/
theorem isDOpen_iff_not_isDBlocked {v w : α}
    (π : Walk G v w) (C : Set α) :
    π.IsDOpen C ↔ ¬ π.IsDBlocked C :=
  Iff.rfl

end Walk

end Causality
