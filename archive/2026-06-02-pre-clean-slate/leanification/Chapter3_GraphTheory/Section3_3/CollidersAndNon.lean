import Chapter3_GraphTheory.Section3_1.WalkPredicates

/-!
# Colliders and non-colliders at positions on a walk (def 3.15)

This file formalises *definition 3.15* of the lecture notes (Forré
& Mooij, `lecture-notes/lecture_notes/graphs.tex`): the
classification of each *position* $k \in \{0, \dots, n\}$ on a walk
$\pi = (v_0 \sus \cdots \sus v_n)$ as either a *collider* or a
*non-collider*.

## Predicates exposed (under `Causality.Walk`)

* `IsColliderAt : Walk G v w → ℕ → Prop` -- "position $k$ on $\pi$
  is a collider": there are two arrowheads pointing towards $v_k$ on
  $\pi$ (the LN shape $v_{k-1} \suh v_k \hus v_{k+1}$). Defined by
  structural recursion on the walk, pattern-matching on $k$ at the
  joint of the head two steps.
* `IsNonColliderAt : Walk G v w → ℕ → Prop` -- "position $k$ on
  $\pi$ is a non-collider": defined as
  $k \le \pi.\text{length} \wedge \neg \pi.\text{IsColliderAt}\ k$,
  capturing the LN's "at most one arrowhead pointing towards $v_k$"
  prose plus the LN's restriction $k \in \{0, \dots, n\}$.

## Position-indexing convention

Positions are indexed by `ℕ`, ranging (semantically) over
$\{0, \dots, n\}$ where $n = \pi.\text{length}$.

* **End-nodes ($k = 0$ or $k = n$) are non-colliders.** The LN's
  list of non-collider sub-patterns includes the end-node case
  explicitly. In our definition this falls out because
  `IsColliderAt` returns `False` on the end-node cases of the
  recursion. The convenience lemmas `isNonColliderAt_zero` and
  `isNonColliderAt_length` make this explicit.
* **Out-of-range positions ($k > n$) are neither collider nor
  non-collider.** `IsColliderAt` returns `False` vacuously (the
  recursion eventually exits via the `cons _ (nil _), _ ↦ False`
  case for any oversized $k$), and `IsNonColliderAt` rules them out
  via the `k ≤ π.length` conjunct. Downstream universal quantifiers
  `∀ k, π.IsNonColliderAt k → P k` then correctly skip the
  out-of-range positions.

## Downstream usage

Section 3.3 rows that sit on top of this position-indexed
classification: def_3_16 (blockable / unblockable non-colliders),
def_3_17 ($\sigma$-blocked walks), and def_3_18
($\sigma$-separation). Each of those rows universally or
existentially quantifies over positions on a walk and asks whether
each position is a collider or a non-collider.

## Style precedents

* `Chapter3_GraphTheory.Section3_1.WalkPredicates` -- same paradigm
  of `Prop`-valued walk predicates with per-constructor `@[simp]`
  characterisation lemmas. Reuses
  `WalkStep.HasArrowheadAtTarget` (LN's `\suh`) and
  `WalkStep.HasArrowheadAtSource` (LN's `\hus`) from that file to
  phrase the per-step "arrowhead at $v_k$" conditions in LN
  vocabulary.
* `Chapter3_GraphTheory.Section3_1.Bifurcation` -- module-level
  docstring style.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

/-! ### IsColliderAt (LN def 3.15, item 2) -/

-- def_3_15 (item 2)
-- title: Colliders -- position-indexed collider predicate on a walk
--
-- `π.IsColliderAt k` holds iff position $k$ on $\pi$ has two
-- arrowheads pointing towards $v_k$ (the LN shape
-- $v_{k-1} \suh v_k \hus v_{k+1}$): the step into $v_k$ has an
-- arrowhead at its target (`HasArrowheadAtTarget`) AND the step
-- out of $v_k$ has an arrowhead at its source
-- (`HasArrowheadAtSource`).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.15,
item 2):

  Let $G=(J,V,E,L)$ be a CDMG and $\pi$ a walk in $G$:
    $\pi =\lp  v_0 \sus \cdots \sus v_n \rp.$
  A node $v_k$, or more precisely, the position
  $k \in \lC 0,\dots, n \rC$, on the walk $\pi$ is called:
  ...
  (2) a \emph{collider} on $\pi$, if it is of the form:
            $v_{k-1} \suh v_k \hus v_{k+1},$
            i.e.\ if there are two arrowheads pointing towards
            $v_k$ on the walk $\pi$.
-/
--
-- ## Design choice
--
-- * **`Prop`-valued, not `Bool`-valued.** Downstream
--   $\sigma$-blocking and $\sigma$-separation (def_3_17 /
--   def_3_18) quantify over positions on a walk:
--   `∀ k, π.IsColliderAt k → nodeAt π k ∈ Anc(C)` and dually
--   `∃ k, π.IsColliderAt k ∧ ...`. `Prop` composes cleanly with
--   `∀` / `∃` / `→` / `¬`; a `Bool`-valued classifier would force
--   `decide`-glue (`= true`) on every quantifier and is the wrong
--   default for a foundational predicate that is only ever *used*
--   logically, never *computed*.
--
-- * **Position-indexed by `ℕ`, not by `Fin (π.length + 1)`.** The
--   LN's "position $k \in \lC 0, \dots, n \rC$" naturally maps to
--   a bounded position type, but using `Fin (π.length + 1)` would
--   force every downstream quantifier and lemma to carry the
--   dependent bound, polluting statements with `Fin.val` /
--   `Fin.mk` plumbing on every position. Indexing by `ℕ` instead,
--   with out-of-range $k$ returning `False`, is the semantically
--   correct vacuous answer ("position $k$ of $\pi$ is not a
--   collider" when $k$ is past the end) and keeps statements like
--   `∀ k, π.IsColliderAt k → ...` first-order in `ℕ`.
--
-- * **Structural recursion on the walk, with explicit ℕ-pattern
--   cases for $k = 0$, $k = 1$, and $k + 2$.** A collider check at
--   position $k$ examines the *joint* of two consecutive steps --
--   the incoming step `a_{k-1}` (arrowhead-at-target test at
--   $v_k$) and the outgoing step `a_k` (arrowhead-at-source test
--   at $v_k$). Structural recursion on `cons s (cons s' p)` gives
--   direct access to those two consecutive steps `s, s'` at the
--   head of the recursion, which is exactly the data the joint
--   test needs; no other recursion shape exposes both edges
--   meeting at the head-side interior vertex simultaneously. For
--   $k = 0$ (end-node) we return `False`; for $k \ge 2$ we shift
--   the joint into the tail by recursing on `cons s' p` at
--   position $k - 1$ (the input position $k + 2$ shifts to
--   $k + 1$, mirroring how "removing the head step" moves every
--   interior position one index to the left -- walk-cons advances
--   the position index by one, so this is the natural index-shift
--   under cons). Walks of length $\le 1$ have no interior position
--   and return `False` on every $k$.
--
-- * **The body at $k = 1$ is exactly
--   `s.HasArrowheadAtTarget ∧ s'.HasArrowheadAtSource`.** This is
--   the direct Lean transcription of the LN's "two arrowheads
--   pointing towards $v_k$ on the walk $\pi$": the joint
--   condition is symmetric in the two edges meeting at $v_k$, and
--   the per-side arrowhead predicates `HasArrowheadAtTarget` /
--   `HasArrowheadAtSource` from `Section3_1.WalkPredicates`
--   already encode the LN's `\suh` and `\hus`. No new per-step
--   vocabulary is introduced; the collider test reads
--   word-for-word like the LN's shape
--   $v_{k-1} \suh v_k \hus v_{k+1}$. We deliberately do *not*
--   bottom this out at `EdgeInto` / `EdgeOutOf` (def_3_3) -- a
--   CDMG may host several parallel edges between the same
--   vertices, so the joint test must constrain the *walk's
--   specific steps* $a_{k-1}, a_k$, not the abstract edge
--   relations.
--
-- * **Out-of-range $k > \pi.\text{length}$ returns `False`** via
--   the `cons _ (nil _), _ ↦ False` exit case of the recursion.
--   Downstream `IsNonColliderAt` adds the `k ≤ length` guard to
--   rule these positions out of the non-collider relation too
--   (see the design-choice block on `IsNonColliderAt` below for
--   why the guard is needed there but not here).
--
-- * **Per-constructor `@[simp]` characterisation lemmas, all
--   `Iff.rfl`-reducible.** Matches the `WalkPredicates` paradigm:
--   each pattern case of the definition is mirrored by an
--   explicit simp lemma (`isColliderAt_nil`,
--   `isColliderAt_cons_nil`, `isColliderAt_cons_cons_zero`,
--   `isColliderAt_cons_cons_one`,
--   `isColliderAt_cons_cons_succ_succ`) that exposes the case to
--   downstream proofs *without* unfolding the recursive body.
--   Downstream walk-shape-specific reasoning (the end-node /
--   length-1 lemmas just below; def_3_17 / def_3_18 case analysis
--   on blocking-witness walks) then closes by `simp` on the walk
--   constructors plus the per-step `HasArrowheadAt*` simp lemmas
--   from `Section3_1`, never needing to inspect `IsColliderAt`'s
--   body directly.
/-- The position `k` on the walk `π` is a *collider*: there are two
arrowheads pointing towards $v_k$ on $\pi$ (the LN shape
$v_{k-1} \suh v_k \hus v_{k+1}$). Defined by structural recursion
on the walk, pattern-matching on `k` at the joint of the head two
steps. Returns `False` on the end-node cases ($k = 0$ on any walk,
both positions on a length-$\le 1$ walk) and on out-of-range
positions. -/
def IsColliderAt : {v w : α} → Walk G v w → ℕ → Prop
  | _, _, .nil _, _              => False
  | _, _, .cons _ (.nil _), _    => False
  | _, _, .cons _ (.cons _ _), 0 => False
  | _, _, .cons s (.cons s' _), 1 =>
      s.HasArrowheadAtTarget ∧ s'.HasArrowheadAtSource
  | _, _, .cons _ (.cons s' p), k + 2 => IsColliderAt (.cons s' p) (k + 1)

@[simp] theorem isColliderAt_nil (v : α) (k : ℕ) :
    (Walk.nil v : Walk G v v).IsColliderAt k ↔ False := Iff.rfl

@[simp] theorem isColliderAt_cons_nil {v w : α}
    (s : WalkStep G v w) (k : ℕ) :
    (Walk.cons s (Walk.nil w) : Walk G v w).IsColliderAt k ↔ False :=
  Iff.rfl

@[simp] theorem isColliderAt_cons_cons_zero {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) :
    (Walk.cons s (Walk.cons s' p)).IsColliderAt 0 ↔ False := Iff.rfl

@[simp] theorem isColliderAt_cons_cons_one {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) :
    (Walk.cons s (Walk.cons s' p)).IsColliderAt 1 ↔
      s.HasArrowheadAtTarget ∧ s'.HasArrowheadAtSource := Iff.rfl

@[simp] theorem isColliderAt_cons_cons_succ_succ {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) (k : ℕ) :
    (Walk.cons s (Walk.cons s' p)).IsColliderAt (k + 2) ↔
      (Walk.cons s' p).IsColliderAt (k + 1) := Iff.rfl

/-! ### IsNonColliderAt (LN def 3.15, item 1) -/

-- def_3_15 (item 1)
-- title: Non-colliders -- position-indexed non-collider predicate
--
-- `π.IsNonColliderAt k` holds iff $k$ is a valid position on $\pi$
-- ($0 \le k \le n$) and $\pi$ does *not* have a collider at $k$.
-- The LN lists four sub-patterns (end-node, left chain, right
-- chain, fork) that together characterise "at most one arrowhead
-- pointing towards $v_k$"; these exhaust the negation of the
-- collider pattern at valid positions, so defining the
-- non-collider predicate as the negation captures the LN's intent
-- in one line.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.15,
item 1):

  Let $G=(J,V,E,L)$ be a CDMG and $\pi$ a walk in $G$:
    $\pi =\lp  v_0 \sus \cdots \sus v_n \rp.$
  A node $v_k$, or more precisely, the position
  $k \in \lC 0,\dots, n \rC$, on the walk $\pi$ is called:
  (1) a \emph{non-collider} on $\pi$, if there is at most one
      arrowhead pointing towards $v_k$, i.e.\ if it falls into one
      of the following cases:
       end-node:    $k \in \lC 0, n \rC$,
       left chain:  $v_{k-1} \hut v_k \hus v_{k+1}$,
       right chain: $v_{k-1} \suh v_k \tuh v_{k+1}$,
       fork:        $v_{k-1} \hut v_k \tuh v_{k+1};$
-/
--
-- ## Design choice
--
-- * **Defined as `k ≤ π.length ∧ ¬ π.IsColliderAt k`, not by a
--   separate four-case recursion on (walk-pattern, k-pattern).**
--   The LN says "at most one arrowhead pointing towards $v_k$",
--   and the four sub-patterns (end-node, left chain, right chain,
--   fork) are an exhaustive enumeration of *that* condition --
--   equivalently, the negation of the collider sub-pattern ("two
--   arrowheads"). Defining the non-collider predicate as
--   `¬ IsColliderAt` (gated by validity) captures the LN's intent
--   in one line, makes the two predicates *definitionally dual*
--   (any proof that splits on collider vs.\ non-collider just
--   unfolds the `¬`), and reuses every `IsColliderAt` simp lemma
--   for free. A parallel four-case recursion on (walk-pattern,
--   k-pattern) would duplicate the per-step orientation case
--   analysis already done in
--   `Section3_1.WalkPredicates.HasArrowheadAt*` and would force
--   downstream lemmas to be proven twice -- once against the
--   collider recursion and once against the non-collider
--   recursion.
--
-- * **`k ≤ π.length` guard.** The LN restricts $k$ to
--   $\lC 0, \dots, n \rC$. Without the guard an out-of-range $k$
--   would make `IsNonColliderAt` *vacuously true*
--   (`¬ False = True`, from `IsColliderAt`'s out-of-range
--   `False`), which is semantically wrong: an out-of-range
--   position is not a node on the walk at all, so it is neither a
--   collider nor a non-collider. With the guard,
--   `π.IsNonColliderAt k` is faithful to the LN's
--   $\lC 0, \dots, n \rC$ precondition: it implies $k \le n$, so
--   downstream quantifiers `∀ k, π.IsNonColliderAt k → P k` are
--   automatically restricted to valid positions.
--
--   The asymmetry -- `IsColliderAt` does *not* need the guard but
--   `IsNonColliderAt` does -- is exactly what one would expect: a
--   positive condition (two arrowheads present) fails vacuously
--   off-walk and *should* be `False`; the complement would
--   succeed vacuously off-walk and so must be gated. The guard
--   restores the "neither / nor" status of out-of-range positions.
--
-- * **Named endpoint lemmas `isNonColliderAt_zero` and
--   `isNonColliderAt_length` (with helper
--   `not_isColliderAt_length`).** $k = 0$ and $k = \pi.\text{length}$
--   are the LN's "end-node: $k \in \lC 0, n \rC$" sub-pattern of
--   the non-collider definition: end-nodes are *always*
--   non-colliders. Downstream proofs about path endpoints -- which
--   show up everywhere in $\sigma$-blocking / $\sigma$-separation
--   (the two endpoints of a blocking-witness walk play
--   distinguished roles) -- close by direct application of these
--   named lemmas rather than unfolding `IsNonColliderAt` and then
--   doing case analysis on the walk's head and tail. They are
--   the natural "interface" to `IsNonColliderAt` at the endpoints
--   and avoid repeating the same end-node case split in every
--   downstream proof.
/-- The position `k` on the walk `π` is a *non-collider*: `k` is a
valid position on `π` (i.e.\ `k ≤ π.length`) and `π` does not have
a collider at `k`. Equivalent to the LN's "at most one arrowhead
pointing towards $v_k$" prose, which by case analysis on the head
two steps decomposes into the LN's four sub-patterns (end-node,
left chain, right chain, fork). -/
def IsNonColliderAt {v w : α} (π : Walk G v w) (k : ℕ) : Prop :=
  k ≤ π.length ∧ ¬ π.IsColliderAt k

/-- Defining equation for `IsNonColliderAt`. Useful when unfolding
the definition directly. -/
theorem isNonColliderAt_iff {v w : α} (π : Walk G v w) (k : ℕ) :
    π.IsNonColliderAt k ↔ k ≤ π.length ∧ ¬ π.IsColliderAt k := Iff.rfl

/-- The first position ($k = 0$, i.e.\ $v_0$) on any walk is a
non-collider. Matches the LN's "end-node: $k \in \{0, n\}$"
sub-pattern at $k = 0$. -/
theorem isNonColliderAt_zero {v w : α} (π : Walk G v w) :
    π.IsNonColliderAt 0 := by
  refine ⟨Nat.zero_le _, ?_⟩
  intro h
  cases π with
  | nil _ => exact h
  | cons _ p =>
    cases p with
    | nil _ => exact h
    | cons _ _ => exact h

/-- Position $k = \pi.\text{length}$ (i.e.\ $v_n$) is never a
collider, on any walk. Used internally to discharge the negation in
`isNonColliderAt_length`, but also useful in its own right. -/
theorem not_isColliderAt_length {v w : α} (π : Walk G v w) :
    ¬ π.IsColliderAt π.length := by
  induction π with
  | nil _ => intro h; exact h
  | cons _ p ih =>
    cases p with
    | nil _ => intro h; exact h
    | cons _ _ => exact ih

/-- The last position ($k = \pi.\text{length}$, i.e.\ $v_n$) on any
walk is a non-collider. Matches the LN's "end-node:
$k \in \{0, n\}$" sub-pattern at $k = n$. -/
theorem isNonColliderAt_length {v w : α} (π : Walk G v w) :
    π.IsNonColliderAt π.length :=
  ⟨le_refl _, not_isColliderAt_length π⟩

end Walk

end Causality
