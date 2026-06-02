import Chapter3_GraphTheory.Section3_1.FamilyReachability
import Chapter3_GraphTheory.Section3_3.CollidersAndNon

/-!
# Blockable and unblockable non-colliders (def 3.16)

This file formalises *definition 3.16* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`): the
refinement of *non-collider* positions on a walk into *blockable*
and *unblockable* ones, gated by whether every strict outgoing
arrow at the position lands in the same strongly connected
component of the graph.

## Predicates exposed

Under `Causality.WalkStep`:

* `IsForward` -- the step is the `forward` (`v ⟶ w`) constructor
  (LN's `\tuh`).
* `IsBackward` -- the step is the `backward` (`v ⟵ w`)
  constructor (LN's `\hut`).
* `IsUnblockableJoint` -- given two consecutive steps
  `s : WalkStep G a b` and `s' : WalkStep G b c`, the joint vertex
  `b` is an "unblockable non-collider joint": (i) not a collider
  joint, and (ii) every *strict* outgoing arrow from `b` along
  `s` or `s'` lands in `Sc^G(b)`.

Under `Causality.Walk`:

* `IsUnblockableNonColliderAt : Walk G v w → ℕ → Prop` -- "position
  `k` on `π` is an *unblockable* non-collider" (LN def 3.16). The
  position is interior (`0 < k < π.length`), not a collider, and
  every strict outgoing arrow from `v_k` on `π` lands in
  `Sc^G(v_k)`. Defined by structural recursion on the walk +
  pattern-match on `k`, paralleling
  `Walk.IsColliderAt` in
  `Section3_3.CollidersAndNon` -- the joint of two consecutive
  steps is exposed at the `k = 1` head position and shifted into
  the tail by recursion at `k + 2`.
* `IsBlockableNonColliderAt : Walk G v w → ℕ → Prop` --
  "position `k` on `π` is a *blockable* non-collider": defined as
  `π.IsNonColliderAt k ∧ ¬ π.IsUnblockableNonColliderAt k`. Dual to
  unblockable, captures the LN's "end-node OR at least one
  outgoing arrow `v_k \tuh v_{k\pm1}` outside `Sc^G(v_k)`".

## Strict outgoing-arrow reading (LN-critical)

The LN's "outgoing arrow" $v_k \tuh v_{k\pm 1}$ is the *strict*
`\tuh`-directed reading: bidirected steps `\huh` are NOT outgoing
arrows from either endpoint. This is enforced by the three
sub-patterns in the LN body, whose "non-outgoing" sides allow
`\suh` / `\hus` (which include `\huh`) while the strict outgoing
sides demand `\tuh` / `\hut`. Hence the new per-step predicates
`IsForward` and `IsBackward` -- which match `forward` and
`backward` constructors *exclusively*, excluding `bidir` -- rather
than reusing `HasArrowheadAtTarget` / `HasArrowheadAtSource` from
`Section3_1.WalkPredicates` (which would include the bidir case
and so over-constrain the SCC condition).

## Position-indexing convention

Inherited from `Section3_3.CollidersAndNon` (def 3.15):

* Positions are indexed by `ℕ` over `{0, …, π.length}`.
* End-nodes (`k = 0` or `k = π.length`) and out-of-range positions
  return `False` for `IsUnblockableNonColliderAt` (matching LN's
  "$k \notin \{0,n\}$" requirement).
* `IsBlockableNonColliderAt` returns `True` exactly at non-collider
  positions that fail unblockability -- which includes both
  end-nodes (always blockable, as captured by
  `isBlockableNonColliderAt_zero` and
  `isBlockableNonColliderAt_length`) and interior non-colliders
  with at least one offending outgoing arrow.

## Downstream usage

Section 3.3 rows that consume this classification:
def_3_17 ($\sigma$-blocked walks, where blocking conditions on
non-colliders quantify over "blockable" positions), and
claims 3.20 / 3.21 / 3.22 onwards (relating $\sigma$-separation
to the existence of unblocked walks).

## Style precedents

* `Chapter3_GraphTheory.Section3_3.CollidersAndNon` -- same
  paradigm of `Prop`-valued, position-indexed walk predicates with
  per-constructor `@[simp]` characterisation lemmas. The recursion
  shape of `IsUnblockableNonColliderAt` mirrors that of
  `IsColliderAt`: `nil` / `cons _ (nil _)` / `cons _ (cons _ _), 0`
  exit cases, `cons s (cons s' _), 1` joint-condition case, and
  `cons _ (cons s' p), k + 2 ↦ recurse on (cons s' p), k + 1`
  index shift.
* `Chapter3_GraphTheory.Section3_1.WalkPredicates` -- precedent for
  `IsForward` / `IsBackward` as per-step single-constructor
  predicates, analogous to the existing `IsBidir`.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace WalkStep

variable {G : CDMG α}

/-! ### Per-step strict-direction predicates -/

-- def_3_16 (helper)
-- title: WalkStep -- step is a forward directed edge (LN's `\tuh`)
--
-- `IsForward s` holds iff `s = .forward _`. Mirrors LN's strict
-- forward arrow `v \tuh w` -- the *only* step constructor that
-- represents a strict outgoing arrow from the step's source vertex
-- `v` to its target `w`. Used by `IsUnblockableJoint` below to
-- encode the LN's strict outgoing-arrow reading at a joint
-- (bidirected steps `\huh`, despite having arrowheads at both
-- endpoints, are *not* outgoing arrows from either endpoint).
--
-- ## Design choice
--
-- * **Distinct from `HasArrowheadAtTarget`.** The existing
--   `HasArrowheadAtTarget` from `Section3_1.WalkPredicates`
--   matches LN's `\suh`, which is the union of `forward` (`\tuh`)
--   and `bidir` (`\huh`). LN def 3.16 explicitly wants the strict
--   `\tuh`-only reading for "outgoing arrows", and using
--   `HasArrowheadAtTarget` would conflate `\huh` with `\tuh` and
--   incorrectly impose SCC constraints on bidirected
--   configurations.
--
-- * **Defined in this file, not in `Section3_1.WalkPredicates`.**
--   Per the worker scope rule, `WalkPredicates.lean` is in a
--   different subsection and out of scope for this row; the
--   predicate is introduced where it is first needed.
/-- The step is a *forward* directed edge `v ⟶ w` (LN's `\tuh`).
The unique step constructor representing a strict outgoing arrow
from the step's source vertex `v` to its target `w` -- in
particular, *not* a bidirected edge. -/
def IsForward : {v w : α} → WalkStep G v w → Prop
  | _, _, .forward _  => True
  | _, _, .backward _ => False
  | _, _, .bidir _    => False

@[simp] theorem isForward_forward {v w : α} (h : v ⟶[G] w) :
    (WalkStep.forward h).IsForward ↔ True := Iff.rfl

@[simp] theorem isForward_backward {v w : α} (h : v ⟵[G] w) :
    (WalkStep.backward h).IsForward ↔ False := Iff.rfl

@[simp] theorem isForward_bidir {v w : α} (h : v ⟷[G] w) :
    (WalkStep.bidir h).IsForward ↔ False := Iff.rfl

-- def_3_16 (helper)
-- title: WalkStep -- step is a backward directed edge (LN's `\hut`)
--
-- `IsBackward s` holds iff `s = .backward _`. Mirrors LN's strict
-- backward arrow `v \hut w` -- the *only* step constructor that
-- represents a strict outgoing arrow from the step's *target*
-- vertex `w` back to its source `v`.
--
-- ## Design choice
--
-- Same rationale as `IsForward`: strict `\hut`-only reading, no
-- bidir contamination. Used in `IsUnblockableJoint` to encode
-- "if the left step out of the joint is `\hut`, then the source
-- of the left step lies in `Sc^G(joint)`".
/-- The step is a *backward* directed edge `v ⟵ w` (LN's `\hut`).
The unique step constructor representing a strict outgoing arrow
from the step's target vertex `w` back to its source `v` -- in
particular, *not* a bidirected edge. -/
def IsBackward : {v w : α} → WalkStep G v w → Prop
  | _, _, .forward _  => False
  | _, _, .backward _ => True
  | _, _, .bidir _    => False

@[simp] theorem isBackward_forward {v w : α} (h : v ⟶[G] w) :
    (WalkStep.forward h).IsBackward ↔ False := Iff.rfl

@[simp] theorem isBackward_backward {v w : α} (h : v ⟵[G] w) :
    (WalkStep.backward h).IsBackward ↔ True := Iff.rfl

@[simp] theorem isBackward_bidir {v w : α} (h : v ⟷[G] w) :
    (WalkStep.bidir h).IsBackward ↔ False := Iff.rfl

/-! ### Joint condition for an unblockable non-collider -/

-- def_3_16 (helper, joint condition)
-- title: WalkStep -- the joint vertex of two consecutive steps is an
-- unblockable non-collider
--
-- `s.IsUnblockableJoint s'` packages the LN's "unblockable
-- non-collider at $v_k$" check at the joint of two consecutive
-- steps `s : WalkStep G a b` (the step into $v_k = b$) and
-- `s' : WalkStep G b c` (the step out of $v_k = b$):
--   (1) the joint is *not* a collider, i.e. *not* (`s` has an
--       arrowhead at `b` AND `s'` has an arrowhead at `b`);
--   (2) if `s` is a strict outgoing arrow from `b` (i.e.
--       `s = backward _`, LN's `\hut`), then $a \in \Sc^G(b)$;
--   (3) if `s'` is a strict outgoing arrow from `b` (i.e.
--       `s' = forward _`, LN's `\tuh`), then $c \in \Sc^G(b)$.
--
-- The three LN sub-patterns of def 3.16 are then exactly the
-- non-vacuous cases of (2) and (3):
--   * left chain ($v_{k-1} \hut v_k \hus v_{k+1}$): `s = backward`,
--     `s' ∈ {backward, bidir}`. Clause (2) bites: $a \in \Sc^G(b)$.
--   * right chain ($v_{k-1} \suh v_k \tuh v_{k+1}$): `s' = forward`,
--     `s ∈ {forward, bidir}`. Clause (3) bites: $c \in \Sc^G(b)$.
--   * fork ($v_{k-1} \hut v_k \tuh v_{k+1}$): `s = backward`,
--     `s' = forward`. Both clauses bite.
-- Each of the four collider configurations of `(s, s')` -- (fwd,
-- bwd), (fwd, bid), (bid, bwd), (bid, bid) -- is rejected by
-- clause (1).
--
-- ## Design choice
--
-- * **Single uniform predicate, not three case-specific
--   disjuncts.** The LN spells out three sub-patterns explicitly,
--   but they are an enumeration of the abstract condition
--   "non-collider AND every strict outgoing arrow from the joint
--   in `Sc^G(joint)`". Encoding the abstract condition uniformly
--   (clauses (1) -- (3)) lets one lemma cover all three LN cases,
--   keeps downstream proofs from doing nine-way constructor case
--   analyses, and makes the equivalence with the three LN
--   sub-patterns easy to verify by direct unfolding (the
--   per-step simp lemmas reduce `IsForward` / `IsBackward` /
--   `HasArrowheadAt*` on each constructor of `s, s'`).
--
-- * **`HasArrowheadAtTarget` / `HasArrowheadAtSource` for the
--   collider conjunct, but `IsForward` / `IsBackward` for the SCC
--   conjuncts.** This is the precise LN reading: the "collider"
--   condition is the disjunction `\suh ∧ \hus` (where each side
--   includes the bidir case), while the "outgoing arrow"
--   condition is the strict `\tuh` / `\hut` reading (excluding
--   bidir). Conflating either way would break LN-equivalence.
--
-- * **The collider conjunct mirrors def_3_15's vocabulary
--   verbatim.** `IsNonColliderAt` (def_3_15) checks `¬ (s.HasArrowheadAtTarget
--   ∧ s'.HasArrowheadAtSource)` at each interior position; clause
--   (1) here is exactly that, taken at the joint of two specific
--   consecutive steps. As a result, the bridge
--   `IsNonColliderAt_of_isUnblockableNonColliderAt` below is a
--   near-one-step proof (extract `.1` from the conjunction), and
--   downstream code can lift between joint-level and walk-level
--   non-collider reasoning without translation lemmas.
--
-- * **Predicate, not boolean.** Same rationale as in
--   `CollidersAndNon`'s `IsColliderAt`: foundational and only
--   ever used logically, not computationally.
--
-- * **Joint-level abstraction reusable for future shapes.**
--   Section 3.3's downstream rows (def 3.17 σ-blocked walks,
--   claims 3.20--3.22) and likely further joint-shape predicates
--   in later chapters benefit from having "joint condition"
--   isolated at the per-step pair level: any future "joint with
--   property X" predicate can be introduced alongside
--   `IsUnblockableJoint` with the same shape and immediately slot
--   into a `Walk.IsXAt`-style position-indexed predicate by
--   structural recursion.
/-- The joint vertex `b` of two consecutive walk steps
`s : WalkStep G a b` and `s' : WalkStep G b c` is an *unblockable
non-collider joint*: the joint is not a collider, and every strict
outgoing arrow from `b` (i.e. backward via `s`, or forward via
`s'`) lands in `Sc^G(b)`. -/
def IsUnblockableJoint {a b c : α}
    (s : WalkStep G a b) (s' : WalkStep G b c) : Prop :=
  (¬ (s.HasArrowheadAtTarget ∧ s'.HasArrowheadAtSource)) ∧
  (s.IsBackward → a ∈ G.Sc b) ∧
  (s'.IsForward → c ∈ G.Sc b)

end WalkStep

namespace Walk

variable {G : CDMG α}

/-! ### IsUnblockableNonColliderAt (LN def 3.16, unblockable) -/

-- def_3_16
-- title: Walks -- unblockable non-collider position predicate
--
-- `π.IsUnblockableNonColliderAt k` says position $k$ on $\pi$ is
-- an unblockable non-collider: $0 < k < \pi.\text{length}$ (not an
-- end-node), not a collider, and every strict outgoing arrow from
-- $v_k$ along $\pi$ lands in $\Sc^G(v_k)$.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.16):

  Let $G=(J,V,E,L)$ be a CDMG and $\pi$ a walk in $G$:
    $\pi =\lp  v_0 \sus \cdots \sus v_n \rp.$
  We call a non-collider $v_k$ on $\pi$ an \emph{unblockable
  non-collider} on $\pi$ if it is not an end-node
  ($k \notin \{0,n\}$) and it only has outgoing edges on $\pi$ to
  nodes in the same strongly connected component of $G$. That is,
  it is one of the following patterns:
    left chain:  $v_{k-1} \hut v_k \hus v_{k+1}$
       with $v_{k-1} \in \Sc^G(v_k)$
    right chain: $v_{k-1} \suh v_k \tuh v_{k+1}$
       with $v_{k+1} \in \Sc^G(v_k)$
    fork:        $v_{k-1} \hut v_k \tuh v_{k+1}$
       with $v_{k-1} \in \Sc^G(v_k) \land v_{k+1} \in \Sc^G(v_k)$
  Otherwise, $v_k$ is called a \emph{blockable non-collider} on
  $\pi$. This means that $v_k$ is either an end-node
  ($k \in \{0,n\}$) or it has at least one outgoing arrow
  $v_k \tuh v_{k\pm1}$ pointing to a node $v_{k\pm1}$ that lies in
  a different strongly connected component than $v_k$, i.e.
  $v_{k\pm1} \notin \Sc^G(v_k)$.
-/
--
-- ## Design choice
--
-- * **Structural recursion on the walk, mirror of
--   `IsColliderAt`.** The five recursion cases (`nil`,
--   `cons _ (nil _)`, `cons _ (cons _ _), 0`,
--   `cons s (cons s' _), 1`, `cons _ (cons s' p), k + 2`) are the
--   same shape as `IsColliderAt` in `CollidersAndNon`. The
--   joint of two consecutive steps -- the syntactic locus of the
--   LN's per-position check -- is exposed at the `k = 1` head
--   position by pattern-matching on `cons s (cons s' _)`, and
--   shifted into the tail by recursion at `k + 2`. Choosing this
--   shape (rather than a `nodeAt`-based reformulation that scans
--   the walk for position `k` and then inspects neighbours) keeps
--   the simp normal form aligned with `IsColliderAt`'s and lets
--   downstream lemmas case-analyse both predicates uniformly on
--   the same walk constructors.
--
-- * **End-node and out-of-range cases return `False`.** The LN
--   explicitly forbids $k \in \{0, n\}$ for unblockability ("if it
--   is not an end-node"). The `nil` and `cons _ (nil _)` walks
--   have no interior position; the `cons _ (cons _ _), 0` case is
--   the head end-node. For positions `k = n` and larger, the
--   recursion eventually hits a `cons _ (nil _)` exit and returns
--   `False`. So the LN's "interior" requirement falls out of the
--   recursion shape, without an explicit `0 < k ∧ k < π.length`
--   guard cluttering the definition. (Compare the dual choice in
--   `IsColliderAt`: that predicate has no interior requirement at
--   the LN level either -- a collider must be interior anyway --
--   so the recursion returning `False` on end-node patterns is
--   the right convention for both.)
--
-- * **The `k = 1` joint case delegates to
--   `WalkStep.IsUnblockableJoint`.** The LN's three sub-patterns
--   (left chain, right chain, fork) and the underlying abstract
--   condition "non-collider AND every strict outgoing arrow in
--   `Sc^G(joint)`" are packaged uniformly in
--   `IsUnblockableJoint`. Inlining the three LN sub-patterns
--   here as a disjunction would be equivalent but more verbose
--   and would duplicate the per-step constructor case analysis
--   already encoded in `IsForward` / `IsBackward` /
--   `HasArrowheadAt*`. Delegating to `IsUnblockableJoint` is
--   strictly LN-equivalent (proven by unfolding on the four
--   non-collider constructor combinations of `(s, s')`) and lets
--   the joint condition be reused independently downstream.
--
-- * **Strict outgoing-arrow reading enforced via
--   `IsForward` / `IsBackward`, not
--   `HasArrowheadAtTarget` / `HasArrowheadAtSource`.** See the
--   module docstring's "Strict outgoing-arrow reading" section
--   and the design block on `IsUnblockableJoint`. The LN's
--   $v_k \tuh v_{k\pm 1}$ is strict-`\tuh`, so bidirected steps
--   do not count as outgoing arrows from either endpoint and so
--   impose no SCC constraint.
--
-- * **Per-constructor `@[simp]` characterisation lemmas, all
--   `Iff.rfl`-reducible.** Matches the `CollidersAndNon`
--   precedent: each pattern case of the definition is mirrored
--   by an explicit simp lemma. Downstream proofs reduce
--   `IsUnblockableNonColliderAt` to its body case-by-case via
--   `simp`, without needing to unfold the recursion manually.
/-- The position `k` on the walk `π` is an *unblockable
non-collider*: not an end-node, not a collider, and every strict
outgoing arrow from $v_k$ on $\pi$ lands in `Sc^G(v_k)` (LN def
3.16). Returns `False` on end-node positions ($k = 0$ on any
non-trivial walk, both positions on a length-$\le 1$ walk) and on
out-of-range positions. -/
def IsUnblockableNonColliderAt : {v w : α} → Walk G v w → ℕ → Prop
  | _, _, .nil _, _              => False
  | _, _, .cons _ (.nil _), _    => False
  | _, _, .cons _ (.cons _ _), 0 => False
  | _, _, .cons s (.cons s' _), 1 => s.IsUnblockableJoint s'
  | _, _, .cons _ (.cons s' p), k + 2 =>
      IsUnblockableNonColliderAt (.cons s' p) (k + 1)

@[simp] theorem isUnblockableNonColliderAt_nil (v : α) (k : ℕ) :
    (Walk.nil v : Walk G v v).IsUnblockableNonColliderAt k ↔ False := Iff.rfl

@[simp] theorem isUnblockableNonColliderAt_cons_nil {v w : α}
    (s : WalkStep G v w) (k : ℕ) :
    (Walk.cons s (Walk.nil w) : Walk G v w).IsUnblockableNonColliderAt k ↔
      False := Iff.rfl

@[simp] theorem isUnblockableNonColliderAt_cons_cons_zero {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) :
    (Walk.cons s (Walk.cons s' p)).IsUnblockableNonColliderAt 0 ↔
      False := Iff.rfl

@[simp] theorem isUnblockableNonColliderAt_cons_cons_one {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) :
    (Walk.cons s (Walk.cons s' p)).IsUnblockableNonColliderAt 1 ↔
      s.IsUnblockableJoint s' := Iff.rfl

@[simp] theorem isUnblockableNonColliderAt_cons_cons_succ_succ {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) (k : ℕ) :
    (Walk.cons s (Walk.cons s' p)).IsUnblockableNonColliderAt (k + 2) ↔
      (Walk.cons s' p).IsUnblockableNonColliderAt (k + 1) := Iff.rfl

/-! ### Unblockable implies non-collider (LN sanity) -/

-- def_3_16 (helper lemma)
-- title: Walks -- unblockable non-collider positions are non-colliders
--
-- The LN's wording "We call a *non-collider* $v_k$ on $\pi$ an
-- unblockable non-collider..." makes it tautological that
-- unblockable ⇒ non-collider. The recursive definition encodes
-- this via the `IsUnblockableJoint` clause `¬ (HasArrowheadAtTarget
-- ∧ HasArrowheadAtSource)`, and the helper lemma below makes the
-- consequence available to downstream consumers (who can then
-- chain through `IsNonColliderAt`'s API without reaching for the
-- unblockable predicate's internals).

/-- An unblockable non-collider position is in particular a
non-collider position. -/
theorem IsNonColliderAt_of_isUnblockableNonColliderAt :
    ∀ {v w : α} (π : Walk G v w) (k : ℕ),
      π.IsUnblockableNonColliderAt k → π.IsNonColliderAt k
  | _, _, .nil _, _, h => (h).elim
  | _, _, .cons _ (.nil _), _, h => (h).elim
  | _, _, .cons _ (.cons _ _), 0, h => (h).elim
  | _, _, .cons s (.cons s' p), 1, h => by
      -- Unfold `IsUnblockableJoint` to extract the `¬ collider`
      -- conjunct, then assemble `IsNonColliderAt 1`.
      refine ⟨?_, ?_⟩
      · -- 1 ≤ length: `cons s (cons s' p)` has length ≥ 2.
        simp [Walk.length]
      · exact h.1
  | _, _, .cons _ (.cons s' p), k + 2, h => by
      -- Recurse on the tail.
      have ih := IsNonColliderAt_of_isUnblockableNonColliderAt
        (.cons s' p) (k + 1) h
      refine ⟨?_, ?_⟩
      · -- k + 2 ≤ length: shift via the tail's bound.
        have := ih.1
        simp [Walk.length] at this ⊢
        omega
      · -- ¬ collider at k + 2 ↔ ¬ collider at k + 1 on the tail.
        exact ih.2

/-! ### Unblockable positions are interior -/

-- def_3_16 (helper lemma)
-- title: Walks -- unblockable positions lie strictly inside the walk
--
-- The LN's "$k \notin \{0, n\}$" requirement is encoded by the
-- recursion (returning `False` at end-node patterns); this helper
-- surfaces both bounds explicitly for downstream callers.

/-- An unblockable non-collider position is strictly interior:
$0 < k < \pi.\text{length}$. -/
theorem zero_lt_and_lt_length_of_isUnblockableNonColliderAt :
    ∀ {v w : α} (π : Walk G v w) (k : ℕ),
      π.IsUnblockableNonColliderAt k → 0 < k ∧ k < π.length
  | _, _, .nil _, _, h => (h).elim
  | _, _, .cons _ (.nil _), _, h => (h).elim
  | _, _, .cons _ (.cons _ _), 0, h => (h).elim
  | _, _, .cons _ (.cons _ _), 1, _ => by
      refine ⟨Nat.zero_lt_one, ?_⟩
      simp [Walk.length]
  | _, _, .cons _ (.cons s' p), k + 2, h => by
      have ih := zero_lt_and_lt_length_of_isUnblockableNonColliderAt
        (.cons s' p) (k + 1) h
      refine ⟨Nat.succ_pos _, ?_⟩
      have := ih.2
      simp [Walk.length] at this ⊢
      omega

/-- An unblockable non-collider position is not the start endpoint. -/
theorem not_isUnblockableNonColliderAt_zero {v w : α} (π : Walk G v w) :
    ¬ π.IsUnblockableNonColliderAt 0 := by
  intro h
  have := zero_lt_and_lt_length_of_isUnblockableNonColliderAt π 0 h
  exact (Nat.lt_irrefl _) this.1

/-- An unblockable non-collider position is not the end endpoint. -/
theorem not_isUnblockableNonColliderAt_length {v w : α} (π : Walk G v w) :
    ¬ π.IsUnblockableNonColliderAt π.length := by
  intro h
  have := zero_lt_and_lt_length_of_isUnblockableNonColliderAt π π.length h
  exact (Nat.lt_irrefl _) this.2

/-! ### IsBlockableNonColliderAt (LN def 3.16, blockable) -/

-- def_3_16 (blockable)
-- title: Walks -- blockable non-collider position predicate
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.16,
trailing clause):

  Otherwise, $v_k$ is called a \emph{blockable non-collider} on
  $\pi$. This means that $v_k$ is either an end-node
  ($k \in \{0,n\}$) or it has at least one outgoing arrow
  $v_k \tuh v_{k\pm1}$ pointing to a node $v_{k\pm1}$ that lies in
  a different strongly connected component than $v_k$, i.e.
  $v_{k\pm1} \notin \Sc^G(v_k)$.
-/
--
-- ## Design choice
--
-- * **Defined as `IsNonColliderAt k ∧ ¬ IsUnblockableNonColliderAt
--   k`, not by a parallel recursive predicate.** The LN's
--   "Otherwise, ..." is exactly the *complement* (within
--   non-colliders) of unblockability. Encoding blockable as
--   `non-collider ∧ ¬ unblockable` makes the two predicates
--   definitionally dual, reuses every `IsUnblockableNonColliderAt`
--   and `IsNonColliderAt` simp lemma for free, and means
--   downstream proofs that case-split on "blockable vs
--   unblockable non-collider" close by `Classical.em` or by
--   direct `Iff.intro` on the unfolded definitions. A parallel
--   recursive predicate would duplicate the joint-condition case
--   analysis and force every dual lemma to be proven twice.
--
-- * **The non-collider conjunct is kept.** The LN's "blockable
--   non-collider" is, by name, a non-collider; including the
--   `IsNonColliderAt` conjunct keeps `IsBlockableNonColliderAt`
--   restricted to valid non-collider positions (LN restriction
--   $k \in \{0, …, n\}$ plus "not a collider") and rules out
--   out-of-range positions and collider positions from blockable
--   universally and existentially. Without the conjunct,
--   out-of-range positions and collider positions would
--   spuriously satisfy `¬ unblockable` and be miscounted as
--   blockable.
--
-- * **No new structural recursion.** Downstream proofs that
--   "every non-collider on $\pi$ is blockable or unblockable"
--   become `simp` / `Classical.em` one-liners. The
--   convenience lemmas
--   `isBlockableNonColliderAt_zero` and
--   `isBlockableNonColliderAt_length` (the LN's "end-node"
--   sub-case of blockable) follow by composing the corresponding
--   non-collider endpoint lemmas with
--   `not_isUnblockableNonColliderAt_*`.
/-- The position `k` on the walk `π` is a *blockable non-collider*:
a non-collider position that is not unblockable. By LN def 3.16,
equivalent to "end-node OR ∃ outgoing arrow $v_k \tuh v_{k\pm 1}$
with $v_{k\pm 1} \notin \Sc^G(v_k)$". -/
def IsBlockableNonColliderAt {v w : α} (π : Walk G v w) (k : ℕ) : Prop :=
  π.IsNonColliderAt k ∧ ¬ π.IsUnblockableNonColliderAt k

/-- Defining equation for `IsBlockableNonColliderAt`. -/
theorem isBlockableNonColliderAt_iff {v w : α} (π : Walk G v w) (k : ℕ) :
    π.IsBlockableNonColliderAt k ↔
      π.IsNonColliderAt k ∧ ¬ π.IsUnblockableNonColliderAt k := Iff.rfl

/-- The first position ($k = 0$, i.e.\ $v_0$) on any walk is a
*blockable* non-collider. Matches the LN's "end-node:
$k \in \{0, n\}$" sub-case of *blockable*. -/
theorem isBlockableNonColliderAt_zero {v w : α} (π : Walk G v w) :
    π.IsBlockableNonColliderAt 0 :=
  ⟨isNonColliderAt_zero π, not_isUnblockableNonColliderAt_zero π⟩

/-- The last position ($k = \pi.\text{length}$, i.e.\ $v_n$) on
any walk is a *blockable* non-collider. Matches the LN's
"end-node: $k \in \{0, n\}$" sub-case of *blockable*. -/
theorem isBlockableNonColliderAt_length {v w : α} (π : Walk G v w) :
    π.IsBlockableNonColliderAt π.length :=
  ⟨isNonColliderAt_length π, not_isUnblockableNonColliderAt_length π⟩

end Walk

end Causality
