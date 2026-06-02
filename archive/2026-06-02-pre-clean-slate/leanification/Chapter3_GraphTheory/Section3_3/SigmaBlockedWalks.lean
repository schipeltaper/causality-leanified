import Chapter3_GraphTheory.Section3_1.FamilyReachability
import Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable

/-!
# $\sigma$-blocked walks (def 3.17)

This file formalises *definition 3.17* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`): the
two-clause classification of a walk $\pi$ in a CDMG $G$,
relative to a conditioning set $C \subseteq J \cup V$, as
either *$C$-$\sigma$-open* or *$C$-$\sigma$-blocked*.

## Predicates exposed (under `Causality.Walk`)

* `nodeAt : Walk G v w → ℕ → α` -- helper returning the vertex
  $v_k$ at position $k$ on the walk
  $\pi = (v_0 \sus \cdots \sus v_n)$. Defined by structural
  recursion on the walk + pattern-match on `k`: the source
  vertex at `k = 0`, the tail's $k$-th vertex at `k + 1`, and
  (junk-totally-fine) the walk's *endpoint* `w` for
  `k > π.length`. See "Position-indexing convention" below for
  why the junk is never semantically observed.
* `IsSigmaOpen (π : Walk G v w) (C : Set α) : Prop` -- LN's
  "$\pi$ is $C$-$\sigma$-open": every collider on $\pi$ lies
  in $\Anc^G(C)$, *and* every blockable non-collider on $\pi$
  lies outside $C$.
* `IsSigmaBlocked (π : Walk G v w) (C : Set α) : Prop` -- LN's
  "$\pi$ is $C$-$\sigma$-blocked": there exists a collider on
  $\pi$ outside $\Anc^G(C)$, *or* there exists a blockable
  non-collider on $\pi$ inside $C$.

Plus the De-Morgan dual sanity lemma
`isSigmaBlocked_iff_not_isSigmaOpen`: classically (via
`Classical.em`), `π.IsSigmaBlocked C ↔ ¬ π.IsSigmaOpen C`.
The LN's two clauses are explicitly *complementary*
("$\sigma$-open *or* $\sigma$-blocked, never both, always at
least one"), and the dual is the natural sanity check.

## Position-indexing convention

Inherited from `Section3_3.CollidersAndNon` and
`Section3_3.BlockableAndUnblockable`:

* Positions are indexed by `ℕ` over `{0, …, π.length}`.
* `nodeAt` is *junk-on-out-of-range*: for `k > π.length` it
  returns the endpoint `w`. The junk is never semantically
  observed because:
  - In `IsSigmaOpen`, the two universal quantifiers are gated
    by `IsColliderAt` / `IsBlockableNonColliderAt`, both of
    which return `False` at out-of-range positions (the
    collider recursion exits via the `cons _ (nil _)` case
    and the blockable predicate carries `IsNonColliderAt`'s
    `k ≤ π.length` guard). The implication `False → P` is
    vacuous, so the body's value of `nodeAt` is irrelevant.
  - In `IsSigmaBlocked`, the existential witnesses must
    additionally satisfy `IsColliderAt` /
    `IsBlockableNonColliderAt`, which exclude out-of-range
    positions; no such witness can be produced
    out-of-range, so the junk value cannot be observed either.

## Downstream usage

* **def_3_18** ($i$-$\sigma$-separation,
  `graphs.tex` lines 1351 -- 1372): "every walk from $A$ to
  $J \cup B$ is $\sigma$-blocked by $C$". Consumes
  `IsSigmaBlocked` directly as the per-walk blocking
  predicate.
* **claim_3_21**
  (the trailing claimmark of this definition,
  `graphs.tex` lines 1343 -- 1346): "unblockable
  non-colliders are always $C$-$\sigma$-open" (regardless of
  $C$). Proves a property of an unblockable non-collider
  position vis-à-vis any `IsSigmaOpen` predicate.
* **claim_3_22** ($\sigma$-separation symmetry,
  `graphs.tex` lines 1366 -- 1369): pivots between
  `IsSigmaOpen` and `IsSigmaBlocked` via the De-Morgan dual.
* **claim_3_23 / claim_3_24** ($\sigma$-open path /
  $\sigma$-separation equivalences): rewrite $\sigma$-blocked
  walks in terms of $\sigma$-open paths and vice versa.
* Chapters 4 onwards (do-calculus, identification, iSCMs)
  consume `IsSigmaBlocked` and `IsSigmaOpen` through
  $\sigma$-separation.

## LN-faithfulness note

The LN's clauses (i) and (ii) under both *open* and *blocked*
single out *colliders* and *blockable non-colliders* -- a
distinction inherited from def_3_16, where non-colliders are
refined into *blockable* and *unblockable*. We faithfully
mirror that split: `IsSigmaOpen` and `IsSigmaBlocked`
reference `IsBlockableNonColliderAt`, *not* `IsNonColliderAt`.
Collapsing to "every non-collider" would mis-state the
definition: claim_3_21 (the trailing claimmark of def 3.17)
explicitly observes that *unblockable* non-colliders are
*always* $\sigma$-open and so play no role in the blocking
conditions. In the acyclic case claim_3_20 then collapses
"blockable non-collider" back to "non-collider", but this is
a *derived* equivalence (under acyclicity), not the LN's
definition.

The LN's preamble "$C \subseteq J \cup V$" is *not* a
type-level restriction here: the existing `AncSet G C` is
already `Set α → Set α` and silently ignores set members
outside `G` (same paradigm as `Anc G v`). So we keep
`C : Set α` and let the LN-precondition $C \subseteq J \cup V$
be propagated by callers (def_3_18 will state it as a
side-condition on $A$, $B$, $C$ when it consumes
`IsSigmaBlocked`).

## Style precedents

* `Chapter3_GraphTheory.Section3_3.CollidersAndNon` (def_3_15)
  and `Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable`
  (def_3_16) -- same module-docstring structure, same
  per-declaration design-choice block convention, same
  per-constructor `@[simp]` characterisation pattern.
* `Chapter3_GraphTheory.Section3_1.FamilyReachability` --
  source of `AncSet G C`, the LN's $\Anc^G(C)$.
* `Chapter3_GraphTheory.Section3_1.Walks` -- source of the
  `Walk` / `WalkStep` / `length` types whose `nil` / `cons`
  constructor pair structures the `nodeAt` recursion.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

/-! ### nodeAt (helper: vertex at position `k` on a walk) -/

-- def_3_17 (helper)
-- title: Walks -- vertex at position k on a walk
--
-- `π.nodeAt k` returns the vertex $v_k$ at position $k$ on the
-- walk $\pi = (v_0 \sus \cdots \sus v_n)$. Defined by structural
-- recursion on the walk + pattern-match on `k`: the source
-- vertex `v` at `k = 0` (any walk), the tail's $k$-th vertex
-- at `k + 1` on a `cons` walk, and -- junk-totally-fine -- the
-- walk's endpoint `w` for `k > π.length`.
--
-- This is the first row of section 3.3 that genuinely needs
-- such a helper: def_3_15 / def_3_16 are position-indexed but
-- their predicates only ever inspect the *joint of two
-- consecutive steps* at position $k$ (the head two steps of
-- the recursion), which the structural recursion exposes
-- directly without ever materialising "the vertex at $k$" as a
-- value of type `α`. def_3_17, by contrast, says "the *vertex*
-- $v_k$ is/is-not in $C$ / in $\Anc^G(C)$", which forces an
-- `α`-valued look-up. Hence this helper.
--
-- ## Design choice
--
-- * **Total `Walk G v w → ℕ → α`, no `Option`.** The LN
--   silently restricts the position $k$ to
--   $\{0, \dots, \pi.\text{length}\}$ and the syntactic
--   expressions "$v_k$ is/is-not in $C$" only ever appear
--   under the (i)/(ii) clauses' implicit "all colliders on
--   $\pi$" / "all blockable non-colliders on $\pi$"
--   quantifiers, which are themselves gated by
--   `IsColliderAt` / `IsBlockableNonColliderAt`. Both gating
--   predicates return `False` at out-of-range positions (the
--   collider recursion's `cons _ (nil _)` exit and the
--   blockable predicate's `IsNonColliderAt`-guard
--   respectively), so the out-of-range value of `nodeAt` is
--   *never semantically observed* by `IsSigmaOpen` /
--   `IsSigmaBlocked`. Returning the endpoint `w` as a junk
--   value keeps the helper total (no `Option` plumbing on
--   every call site), keeps every `@[simp]` characterisation
--   lemma `rfl`-reducible (no `some _` / `none` boilerplate),
--   and matches the precedent set by `length` /
--   `IsColliderAt` / `IsUnblockableNonColliderAt` -- each of
--   which is total on `ℕ` and silently returns a vacuous
--   value (`0`, `False`, `False`) on out-of-range positions.
--   A `Walk G v w → Fin (π.length + 1) → α` total signature
--   would also be junk-free, but it forces every downstream
--   caller to carry the dependent bound through every
--   quantifier (`Fin.val` / `Fin.mk` plumbing) -- the same
--   anti-pattern we ruled out for `IsColliderAt`'s position
--   index, and rejected for the same reasons. Concretely, the
--   length bound would have to thread through every collider /
--   blockable-non-collider quantifier in the API
--   downstream of this row: claim_3_21's "σ-open ⇒ every
--   collider on $\pi$ is in $\Anc^G(C)$ and every blockable
--   non-collider is not in $C$", claim_3_22's σ-symmetry pivot
--   between `IsSigmaOpen` and `IsSigmaBlocked`, def_3_18's
--   $i$-σ-separation universal over walks, and every
--   chapter-$\ge 4$ consumer that reasons about
--   $\sigma$-separation (do-calculus, identification, iSCMs).
--   Symmetrically, an `Option α`-return shape would push
--   `some _` / `none` pattern-matching into every one of those
--   call sites for zero gain over the gating-predicate
--   convention.
--
-- * **Source vertex at `k = 0`, tail recursion at `k + 1`.**
--   The LN's notation $v_0 \sus \cdots \sus v_n$ pins down
--   $v_0$ as the source endpoint of the walk; `cons` walks
--   have that source as the start vertex of the *head step*,
--   which the pattern `cons _ _, 0 => v` (with `v` bound to
--   the source via the implicit-index match) returns
--   directly. At `k + 1`, the LN's $v_{k+1}$ is the $k$-th
--   vertex of the tail walk (which starts at the joint after
--   the head step), so recursion shifts by exactly one: the
--   head step is consumed, the tail's position index
--   decrements. This is the same index shift that
--   `IsColliderAt` and `IsUnblockableNonColliderAt` use for
--   their `cons _ (cons _ _), k + 2 ↦ ..., k + 1` rule -- one
--   `cons` consumed, one position index shifted left.
--
-- * **Junk value is the walk's endpoint `w`, not "some
--   uninhabited fallback".** At `k > π.length` the recursion
--   eventually exits at a `nil w' , _ ↦ w'` case (every
--   `cons` recursion peels one step off the front and one
--   position index off the back until the tail is `nil`,
--   whose junk return is *its own* `nil`-vertex). On the
--   full walk that final `nil`-vertex is `w` -- the walk's
--   destination endpoint. Concretely, `(cons s p).nodeAt 5`
--   on a length-2 walk reduces
--   `cons s p, 5 ↦ p.nodeAt 4 ↦ (tail's nil).nodeAt 3 ↦ w`,
--   so out-of-range positions all collapse to `w`. This is
--   well-defined (any `α` would do, but `w` is the locally
--   available "default"), reproducible (the same `k` always
--   returns the same value), and matches the LN's silent
--   "$v_k$ is undefined for $k > n$" convention by being
--   semantically un-observable through the gating predicates.
--
-- * **Per-constructor `@[simp]` characterisation lemmas, all
--   `rfl`-reducible.** Matches the
--   `CollidersAndNon` / `BlockableAndUnblockable` precedent:
--   each pattern case of the definition is mirrored by an
--   explicit simp lemma -- `nodeAt_nil` (any `k` on `nil _`),
--   `nodeAt_cons_zero` (`k = 0` on `cons _ _`),
--   `nodeAt_cons_succ` (`k + 1` shifts into the tail).
--   Downstream proofs reduce `nodeAt` to its body case-by-case
--   via `simp`, without needing to unfold the recursion
--   manually.
--
-- * **Named endpoint lemmas `nodeAt_zero` and
--   `nodeAt_length`.** $v_0$ = source and $v_n$ = endpoint
--   are the LN's explicit endpoints in the walk notation;
--   they show up everywhere in `i`-$\sigma$-separation
--   reasoning (the two endpoints of a blocking-witness walk
--   play distinguished roles -- they sit in the "$A$" and
--   "$J \cup B$" sets). The two lemmas expose those endpoint
--   values for callers without forcing them to unfold
--   `nodeAt` against the walk's constructor.

/-- `π.nodeAt k` -- the vertex $v_k$ at position $k$ on the
walk $\pi$. Returns the source vertex `v` at `k = 0` (any
walk), the tail's $k$-th vertex at `k + 1` on a `cons` walk,
and -- junk-totally-fine, never semantically observed by
`IsSigmaOpen` / `IsSigmaBlocked` -- the walk's endpoint `w`
for `k > π.length`. -/
def nodeAt : {v w : α} → Walk G v w → ℕ → α
  | v, _, .nil _,    _     => v
  | v, _, .cons _ _, 0     => v
  | _, _, .cons _ p, k + 1 => p.nodeAt k

@[simp] theorem nodeAt_nil (v : α) (k : ℕ) :
    (Walk.nil v : Walk G v v).nodeAt k = v := by
  cases k <;> rfl

@[simp] theorem nodeAt_cons_zero {v w u : α}
    (s : WalkStep G v w) (p : Walk G w u) :
    (Walk.cons s p).nodeAt 0 = v := rfl

@[simp] theorem nodeAt_cons_succ {v w u : α}
    (s : WalkStep G v w) (p : Walk G w u) (k : ℕ) :
    (Walk.cons s p).nodeAt (k + 1) = p.nodeAt k := rfl

/-- The first vertex on any walk (LN's $v_0$) is the source
endpoint `v`. -/
theorem nodeAt_zero {v w : α} (π : Walk G v w) :
    π.nodeAt 0 = v := by
  cases π with
  | nil _    => rfl
  | cons _ _ => rfl

/-- The last vertex on any walk (LN's $v_n$, with
$n = \pi.\text{length}$) is the destination endpoint `w`. -/
theorem nodeAt_length {v w : α} (π : Walk G v w) :
    π.nodeAt π.length = w := by
  induction π with
  | nil _      => rfl
  | cons _ _ ih => simpa [Walk.length_cons] using ih

/-! ### IsSigmaOpen (LN def 3.17, item 1) -/

-- def_3_17 (item 1)
-- title: Walks -- σ-open walk predicate
--
-- `π.IsSigmaOpen C` says the walk $\pi$ is $C$-$\sigma$-open:
-- *every* collider position $v_k$ on $\pi$ lies in
-- $\Anc^G(C)$, *and* *every* blockable non-collider position
-- $v_k$ on $\pi$ lies *outside* $C$.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.17,
item 1):

  Let $G=(J,V,E,L)$ be a CDMG and $C \ins J \cup V$ a subset of
  nodes and $\pi$ a walk in $G$:
    $\pi =\lp v_0 \sus \cdots \sus v_n \rp.$
  We say that the walk $\pi$ is:
  (1) \emph{$C$-$\sigma$-open} (or \emph{$\sigma$-open given
      $C$}) if and only if:
        i.)  all colliders $v_k$ on $\pi$ are in $\Anc^G(C)$,
             and:
        ii.) all blockable non-colliders $v_k$ on $\pi$ are
             not in $C$.
-/
--
-- ## Design choice
--
-- * **`Prop`-valued conjunction of two universal
--   quantifiers, in the LN's exact order.** The LN's clauses
--   (i) and (ii) are joined by "and"; we mirror that with `∧`
--   between the two `∀ k, ...` universals. Clause (i) reads
--   "all colliders ... are in $\Anc^G(C)$", which becomes
--   `∀ k, π.IsColliderAt k → π.nodeAt k ∈ G.AncSet C` -- the
--   gating `IsColliderAt k` is the LN's "$v_k$ on $\pi$ is a
--   collider", the conclusion is the LN's "$v_k \in
--   \Anc^G(C)$". Clause (ii) is the dual, mutatis mutandis,
--   with `IsBlockableNonColliderAt` and `∉ C`.
--
-- * **Standalone `def`, not bundled into a `WalkStatus`
--   inductive or a single `Iff`-shaped definition.**
--   Alternatives considered:
--   (a) a `inductive WalkStatus | sigmaOpen | sigmaBlocked`
--       indexed by `(π, C)`, with the two predicates derived
--       by membership;
--   (b) one definition packaging both clauses behind a single
--       `Iff` (`IsSigmaOpen ↔ ¬ IsSigmaBlocked`) as its
--       defining equation.
--   Both rejected because downstream rows quantify over
--   *one* of the two predicates at a time, not the pair:
--   def_3_18 ($i$-σ-separation) consumes `IsSigmaBlocked`
--   only; claim_3_21 reasons about `IsSigmaOpen` only;
--   claim_3_22 (σ-symmetry) needs both *separately* to pivot
--   between them. Two definitionally-separate `def`s let each
--   consumer cite the predicate it actually needs without
--   destructuring an inductive or unfolding a bundled `Iff`,
--   and they make `isSigmaBlocked_iff_not_isSigmaOpen` below
--   a *theorem about two pre-existing predicates* rather than
--   a tautology over a single bundled definition.
--
-- * **Composes directly with the chapter-3 vocabulary
--   (`IsColliderAt`, `IsBlockableNonColliderAt`,
--   `G.AncSet`).** Every downstream Section 3.3 consumer
--   (claim_3_20, claim_3_21, claim_3_22, def_3_18) can
--   `unfold IsSigmaOpen` once and reason in the same
--   per-position primitives that def_3_15 / def_3_16
--   established -- no translation lemmas, no parallel
--   re-derivations.
--
-- * **`IsBlockableNonColliderAt`, not `IsNonColliderAt`.**
--   The LN explicitly singles out *blockable* non-colliders
--   in clause (ii) -- not all non-colliders. The distinction
--   is load-bearing: the trailing claimmark of def 3.17
--   (claim_3_21) is precisely "unblockable non-colliders are
--   always $C$-$\sigma$-open, regardless of $C$", which is
--   tautological under our `IsBlockableNonColliderAt`-only
--   reading (the universal vacuously skips unblockable
--   positions) and false under a "every non-collider" reading
--   (it would force unblockable non-colliders out of $C$ for
--   the walk to be open, which is exactly what claim_3_21
--   denies). In the acyclic case claim_3_20 then proves
--   "blockable non-collider = non-collider"
--   (`isBlockableNonColliderAt_of_isNonColliderAt_of_isAcyclic`
--   in `AcyclicNonCollidersBlockable.lean`), making the two
--   readings equivalent *under acyclicity*; but this is a
--   *derived* equivalence, not the LN's definition.
--
-- * **`AncSet G C`, not `⋃ v ∈ C, Anc G v` inlined.** The
--   LN's $\Anc^G(C)$ is the family-relationship operator from
--   def_3_5, formalised in `FamilyReachability.lean` as
--   `AncSet G C`. Reusing the existing operator (with its
--   `mem_AncSet` simp lemma, set reflexivity
--   `subset_Anc_set`, etc.) keeps `IsSigmaOpen` aligned with
--   how the LN composes def 3.17 on top of def 3.5, and lets
--   downstream proofs (`claim_3_22` symmetry,
--   `claim_3_23 / claim_3_24` equivalences) reason about
--   $\Anc^G(C)$ membership via the established API rather
--   than re-deriving the bigunion structure each time.
--
-- * **`C : Set α`, not `C : { C : Set α // C ⊆ G.J ∪ G.V }`.**
--   The LN's "$C \ins J \cup V$" is a side-condition on the
--   conditioning set, *not* a type-level restriction: it is
--   stated in the preamble of the def in standard
--   set-theoretic prose. The existing `AncSet G C` is
--   `Set α → Set α` and silently ignores members outside
--   `G.J ∪ G.V` (since `Anc G v` is empty for `v ∉ G`); so
--   `IsSigmaOpen` -- which is downstream of `AncSet` --
--   inherits the same convention. Carrying a subtype around
--   would pollute every downstream signature
--   (`IsSigmaBlocked`, def_3_18's `i`-$\sigma$-separation,
--   every claim's quantifier over $C$) for no proof
--   ergonomic gain. Callers that genuinely need
--   $C \subseteq J \cup V$ (e.g. def_3_18 will need it to
--   pin $A$ / $B$ into the graph) state that as a separate
--   hypothesis.
--
-- * **`π` first, `C` second.** Lean's dot-notation
--   `π.IsSigmaOpen C` works iff `π` is the first explicit
--   argument; we follow that. Matches every other walk
--   predicate in section 3.3 (`π.IsColliderAt k`,
--   `π.IsBlockableNonColliderAt k`, ...).
--
-- * **No structural recursion, no `@[simp]` characterisation
--   lemmas.** Unlike `IsColliderAt` / `IsUnblockableNonColliderAt`,
--   `IsSigmaOpen` is *not* defined by recursion on the walk;
--   it is a one-line composition of two universal
--   quantifiers over already-recursively-defined per-position
--   predicates. So there are no per-constructor cases to
--   characterise. Downstream proofs that need to inspect
--   `IsSigmaOpen` simply unfold the definition (or apply
--   `.1` / `.2` for the two conjuncts and dispatch the gated
--   quantifier).

/-- The walk `π` is *$C$-$\sigma$-open* (LN def 3.17, item 1):
every collider position on `π` is in $\Anc^G(C)$, *and* every
blockable non-collider position on `π` is *not* in `C`. -/
def IsSigmaOpen {v w : α} (π : Walk G v w) (C : Set α) : Prop :=
  (∀ k, π.IsColliderAt k → π.nodeAt k ∈ G.AncSet C) ∧
  (∀ k, π.IsBlockableNonColliderAt k → π.nodeAt k ∉ C)

/-- Defining equation for `IsSigmaOpen`. Useful when unfolding
the definition directly. -/
theorem isSigmaOpen_iff {v w : α} (π : Walk G v w) (C : Set α) :
    π.IsSigmaOpen C ↔
      (∀ k, π.IsColliderAt k → π.nodeAt k ∈ G.AncSet C) ∧
      (∀ k, π.IsBlockableNonColliderAt k → π.nodeAt k ∉ C) :=
  Iff.rfl

/-! ### IsSigmaBlocked (LN def 3.17, item 2) -/

-- def_3_17 (item 2)
-- title: Walks -- σ-blocked walk predicate
--
-- `π.IsSigmaBlocked C` says the walk $\pi$ is
-- $C$-$\sigma$-blocked: *there exists* a collider position
-- $v_k$ on $\pi$ outside $\Anc^G(C)$, *or* *there exists* a
-- blockable non-collider position $v_k$ on $\pi$ inside $C$.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.17,
item 2):

  ...
  (2) \emph{$C$-$\sigma$-blocked} (or \emph{$\sigma$-blocked
      given $C$}) if and only if:
        i.)  there exists a collider $v_k$ on $\pi$ that is
             not in $\Anc^G(C)$, or:
        ii.) there exists a blockable non-collider $v_k$ on
             $\pi$ in $C$.
-/
--
-- ## Design choice
--
-- * **`Prop`-valued disjunction of two existentials, in the
--   LN's exact order.** The LN's clauses (i) and (ii) are
--   joined by "or"; we mirror that with `∨`. Clause (i) reads
--   "there exists a collider ... not in $\Anc^G(C)$", which
--   becomes `∃ k, π.IsColliderAt k ∧ π.nodeAt k ∉ G.AncSet C`
--   -- the existential carries both the "$v_k$ is a collider"
--   witness and the "$v_k \notin \Anc^G(C)$" witness as a
--   conjunction. Clause (ii) is the dual.
--
-- * **Standalone `def`, mirroring `IsSigmaOpen`'s standalone
--   shape -- not folded into a single `WalkStatus` inductive
--   or derived from `¬ IsSigmaOpen`.** Same reasoning as on
--   `IsSigmaOpen` (separate consumers want separate
--   predicates), but with two `IsSigmaBlocked`-specific
--   sharpenings:
--   (a) def_3_18 ($i$-σ-separation) consumes
--       `IsSigmaBlocked` as the *primary* blocking condition
--       ("every walk from $A$ to $J \cup B$ is σ-blocked by
--       $C$") -- a derived-from-`¬ IsSigmaOpen` shape would
--       force the universal quantifier in def_3_18 to unfold
--       a negation at every use, where the literal
--       `∃-of-∃` shape lets witnesses be produced directly;
--   (b) the existential witnesses (collider $k$ in clause
--       (i), blockable non-collider $k$ in clause (ii)) are
--       the LN's actual "what blocks the walk?" certificates,
--       which downstream proofs need to *extract* (claim_3_20
--       in particular constructs such witnesses for acyclic
--       walks); a `¬ IsSigmaOpen` shape would hide those
--       witnesses behind classical reasoning at every
--       extraction.
--   The De-Morgan dual `isSigmaBlocked_iff_not_isSigmaOpen`
--   below stays available for the proof-direction that does
--   want to negate `IsSigmaOpen` instead.
--
-- * **Composes with the same chapter-3 primitives as
--   `IsSigmaOpen`.** Downstream consumers (claim_3_20,
--   claim_3_22, def_3_18) `unfold IsSigmaBlocked` once and
--   then work in `IsColliderAt` / `IsBlockableNonColliderAt`
--   / `G.AncSet` -- the exact vocabulary def_3_15, def_3_16,
--   def_3_5 already provide simp lemmas and characterisations
--   for.
--
-- * **De-Morgan dual of `IsSigmaOpen`, established by
--   `isSigmaBlocked_iff_not_isSigmaOpen` below.** The LN's
--   two clauses are explicitly *complementary*: the (1) /
--   (2) bullet structure of def 3.17 reads "$\pi$ is either
--   (1) $C$-$\sigma$-open or (2) $C$-$\sigma$-blocked",
--   never both, always exactly one. The dual lemma encodes
--   the "never both, always exactly one" half formally
--   (using classical reasoning to push $\neg \forall$
--   through to $\exists \neg$); see its design block below
--   for why it ships co-located with these two predicates.
--
-- * **Same `IsBlockableNonColliderAt` (not
--   `IsNonColliderAt`) reading.** See the design block on
--   `IsSigmaOpen`. Mirroring matters: the (1)/(2) clauses
--   are exact duals, so they reference the *same* pair of
--   per-position predicates (colliders + blockable
--   non-colliders) under exactly opposite quantifiers
--   ($\forall$ vs.\ $\exists$).
--
-- * **Same `AncSet G C` / `C : Set α` / `π`-first
--   conventions as `IsSigmaOpen`.** See the design block on
--   `IsSigmaOpen` for the rationale; we keep both predicates
--   in lockstep so the dual lemma below reads cleanly and
--   downstream proofs can pivot between them
--   syntax-for-syntax.

/-- The walk `π` is *$C$-$\sigma$-blocked* (LN def 3.17,
item 2): there exists a collider position on `π` not in
$\Anc^G(C)$, *or* there exists a blockable non-collider
position on `π` in `C`. -/
def IsSigmaBlocked {v w : α} (π : Walk G v w) (C : Set α) : Prop :=
  (∃ k, π.IsColliderAt k ∧ π.nodeAt k ∉ G.AncSet C) ∨
  (∃ k, π.IsBlockableNonColliderAt k ∧ π.nodeAt k ∈ C)

/-- Defining equation for `IsSigmaBlocked`. Useful when
unfolding the definition directly. -/
theorem isSigmaBlocked_iff {v w : α} (π : Walk G v w) (C : Set α) :
    π.IsSigmaBlocked C ↔
      (∃ k, π.IsColliderAt k ∧ π.nodeAt k ∉ G.AncSet C) ∨
      (∃ k, π.IsBlockableNonColliderAt k ∧ π.nodeAt k ∈ C) :=
  Iff.rfl

/-! ### σ-blocked is the De-Morgan dual of σ-open -/

-- def_3_17 (sanity lemma)
-- title: Walks -- σ-blocked iff not σ-open (classical De-Morgan dual)
--
-- The LN's two clauses (1) $C$-$\sigma$-open and (2)
-- $C$-$\sigma$-blocked are explicitly *complementary*: every
-- walk is exactly one of the two, never both. Formally, on
-- the conjunctions / disjunctions of universals /
-- existentials we picked, this is the De-Morgan dual:
--   ¬ (P ∧ Q) = ¬P ∨ ¬Q,    ¬(∀ k, R k) = ∃ k, ¬ R k.
-- The proof uses classical reasoning (`by_contra` to pull a
-- non-block witness from `¬ IsSigmaOpen`), which is fine
-- because we are in `Prop` and Lean+mathlib install classical
-- logic by default.
--
-- ## Design choice
--
-- * **Ships co-located with the two predicates.** The LN's
--   "(1) ... or (2) ..." structure is a *definitional* pair;
--   the dual identity ties the pair together formally and is
--   exactly the rewrite that every downstream consumer
--   reaches for ("a walk is not $\sigma$-blocked iff it is
--   $\sigma$-open", and vice versa). Stating it here -- next
--   to the two predicates -- means downstream rows
--   (def_3_18, claim_3_21, claim_3_22, claim_3_23 / 24) can
--   pivot between the two predicates by *citation*, without
--   re-deriving the De-Morgan dual each time.
--
-- * **`Iff`, not two separate `→`s.** The forward direction
--   (`IsSigmaBlocked → ¬ IsSigmaOpen`) is the "incompatible
--   with $\sigma$-open" half; the backward direction
--   (`¬ IsSigmaOpen → IsSigmaBlocked`) is the "exhaustive"
--   half ("if the walk fails $\sigma$-open, it must be
--   $\sigma$-blocked"). Both are equally consumed downstream,
--   so packing them into a single `Iff` is the natural API.
--
-- * **Classical proof via `by_contra` + `push_neg`-style
--   manual case construction, no `Classical.em` boilerplate
--   at call sites.** The backward direction needs to extract
--   a counterexample to a universal, which is classical. We
--   absorb the classical reasoning inside the proof; callers
--   apply `isSigmaBlocked_iff_not_isSigmaOpen.mp` /
--   `.mpr` without ever touching `Classical.em` themselves.

/-- LN def 3.17 sanity: a walk is $C$-$\sigma$-blocked iff it
fails to be $C$-$\sigma$-open. The two LN clauses
(1) $C$-$\sigma$-open and (2) $C$-$\sigma$-blocked are
explicitly *complementary* ("either (1) or (2), never both,
always exactly one"); this lemma is the De-Morgan dual making
that complementarity formal. -/
theorem isSigmaBlocked_iff_not_isSigmaOpen
    {v w : α} (π : Walk G v w) (C : Set α) :
    π.IsSigmaBlocked C ↔ ¬ π.IsSigmaOpen C := by
  constructor
  · rintro (⟨k, hcoll, hout⟩ | ⟨k, hblock, hin⟩) ⟨hOpenColl, hOpenBlock⟩
    · exact hout (hOpenColl k hcoll)
    · exact hOpenBlock k hblock hin
  · intro hNotOpen
    by_contra hNotBlock
    apply hNotOpen
    refine ⟨?_, ?_⟩
    · intro k hcoll
      by_contra hout
      exact hNotBlock (Or.inl ⟨k, hcoll, hout⟩)
    · intro k hblock hin
      exact hNotBlock (Or.inr ⟨k, hblock, hin⟩)

end Walk

end Causality
