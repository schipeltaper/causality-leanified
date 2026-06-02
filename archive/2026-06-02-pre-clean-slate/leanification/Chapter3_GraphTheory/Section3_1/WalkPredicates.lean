import Chapter3_GraphTheory.Section3_1.Walks
import Mathlib.Data.List.Nodup

/-!
# Walk-kind predicates (def 3.4, items 2--5; item 1's "into / out of" prose)

This file formalises *items 2--5* of definition 3.4 of the lecture
notes (Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`)
plus the four "into / out of $v_0$ / $v_n$" prose predicates of
item 1, all as `Prop`-valued predicates sitting on top of the
`Walk G v w` data layer from `Walks.lean`.

Item 6 of LN def 3.4 (bifurcations) lives in `Bifurcation.lean`.

## Predicates exposed (all under `Causality.Walk`)

* `IsDirected` -- LN item 2: every step is `forward` (`\tuh`).
* `IsBidirected` -- LN item 3: every step is `bidir` (`\huh`).
* `IsCollider` -- LN item 4: first step `\suh`, every internal step
  `\huh`, last step `\hus`. Trivial walk vacuously a collider walk;
  single-step walks reduce (by combining both endpoint constraints)
  to a single `\huh` step.
* `IsPath` -- LN item 5: no vertex appears more than once
  (defined via `support.Nodup`, mirroring Mathlib's
  `SimpleGraph.Walk.IsPath`).
* `IntoStart`, `OutOfStart`, `IntoEnd`, `OutOfEnd` -- LN item 1's
  "into / out of $v_0$ / $v_n$" prose predicates, reading off the
  first or last `WalkStep`'s constructor.

A handful of per-step helpers in `Causality.WalkStep`
(`IsBidir`, `HasArrowheadAtTarget`, `HasArrowheadAtSource`) make
the collider-walk recursion read cleanly and let downstream code
phrase per-step conditions in LN vocabulary.

## Design conventions adopted in this file

* **All eight Walk predicates are defined by structural recursion**
  on the underlying `Walk` (or on a step's constructor for the
  per-step helpers). Each definition is paired with `@[simp]`
  characterisation lemmas reducible by `Iff.rfl` (one lemma per
  constructor case), so downstream proofs unfold these predicates
  one step at a time without needing to mention the body.

* **`nil` (the trivial walk) is treated case-by-case** according
  to which reading the LN sentence actually supports:
  - For `IsDirected`, `IsBidirected`, `IsCollider`, `IsPath` we
    return `True` -- there are no edges to constrain and no vertex
    repeats are possible, so the conditions hold vacuously. The
    LN's "for some $n \ge 0$" in items 2 and 3 explicitly admits
    `n = 0`; item 4 (collider walk) is also written "for some
    $n \ge 0$" and so admits the trivial walk vacuously even
    though the LN's terse "for $n=1$ this reads $v \sus w \in G$"
    note is slightly looser than our strict reading (see the
    design-choice block on `IsCollider` below).
  - For the four `IntoStart` / `OutOfStart` / `IntoEnd` /
    `OutOfEnd` predicates we return `False`: the LN's sentences
    each pin down a specific "first edge $a_0$" or "last edge
    $a_{n-1}$", which the trivial walk does not have, and the
    LN's downstream uses of these predicates always assume a walk
    of length $\ge 1$.

* **Each into/out-of predicate is paired with a one-way bridge to
  `def_3_3`'s `EdgeInto` / `EdgeOutOf`** (`EdgeRelations.lean`),
  so callers reasoning about the LN's prose ("the walk is into
  $v_0$" $\Rightarrow$ "the first edge is into $v_0$") can land
  on the def_3_3 vocabulary without unfolding through the
  `WalkStep` constructors. The converse implication does *not*
  hold in general because a CDMG may host several parallel edges
  between the same pair of vertices, so the existence of an
  edge-into-$v_0$ does not pin down which edge the walk's first
  step witnesses; see `intoStart_implies_edgeInto` for the precise
  statement.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace WalkStep

variable {G : CDMG α}

/-! ### Per-step helper predicates

Tiny one-constructor classifiers on a `WalkStep`. They serve two
purposes: they let `Walk.IsCollider`'s recursion below state its
intermediate / endpoint conditions in LN vocabulary (`\huh`,
`\suh`, `\hus`), and they give the `Into*` / `OutOf*` simp lemmas
a uniform per-step right-hand side. Each is paired with three
`@[simp]` `rfl`-equations on the three constructors. -/

-- def_3_4 helpers (item 4 / item 1 prose)
-- title: WalkStep -- step is a bidirected edge
--
-- True only on the `bidir` constructor. Used in `Walk.IsBidirected`
-- (every step `\huh`) and `Walk.IsCollider` (every internal step
-- `\huh`).
/-- The step is a *bidirected* edge: `s = .bidir _`. Mirrors the
LN's `v \huh w`. -/
def IsBidir : {v w : α} → WalkStep G v w → Prop
  | _, _, .forward _  => False
  | _, _, .backward _ => False
  | _, _, .bidir _    => True

@[simp] theorem isBidir_forward {v w : α} (h : v ⟶[G] w) :
    (WalkStep.forward h).IsBidir ↔ False := Iff.rfl

@[simp] theorem isBidir_backward {v w : α} (h : v ⟵[G] w) :
    (WalkStep.backward h).IsBidir ↔ False := Iff.rfl

@[simp] theorem isBidir_bidir {v w : α} (h : v ⟷[G] w) :
    (WalkStep.bidir h).IsBidir ↔ True := Iff.rfl

-- def_3_4 helpers (item 4 / item 1 prose)
-- title: WalkStep -- step has arrowhead at its target endpoint (\suh)
--
-- Mirrors the LN's `\suh` relation: the edge between consecutive
-- vertices `(v_k, v_{k+1})` has an arrowhead at `v_{k+1}`. True for
-- `forward` (`\tuh`) and `bidir` (`\huh`); false for `backward`.
-- Used as the first-step constraint in `Walk.IsCollider` (LN: the
-- first edge is $v_0 \suh v_1$) and as the last-step constraint in
-- `Walk.IntoEnd` (LN: $a_{n-1} = v_{n-1} \suh v_n$).
/-- The step has an arrowhead at its *target* endpoint: `forward`
or `bidir`. Mirrors the LN's `v \suh w`. -/
def HasArrowheadAtTarget : {v w : α} → WalkStep G v w → Prop
  | _, _, .forward _  => True
  | _, _, .backward _ => False
  | _, _, .bidir _    => True

@[simp] theorem hasArrowheadAtTarget_forward {v w : α} (h : v ⟶[G] w) :
    (WalkStep.forward h).HasArrowheadAtTarget ↔ True := Iff.rfl

@[simp] theorem hasArrowheadAtTarget_backward {v w : α} (h : v ⟵[G] w) :
    (WalkStep.backward h).HasArrowheadAtTarget ↔ False := Iff.rfl

@[simp] theorem hasArrowheadAtTarget_bidir {v w : α} (h : v ⟷[G] w) :
    (WalkStep.bidir h).HasArrowheadAtTarget ↔ True := Iff.rfl

-- def_3_4 helpers (item 4 / item 1 prose)
-- title: WalkStep -- step has arrowhead at its source endpoint (\hus)
--
-- Mirrors the LN's `\hus` relation: the edge `(v_k, v_{k+1})` has
-- an arrowhead at `v_k`. True for `backward` (`\hut`) and `bidir`
-- (`\huh`); false for `forward`. Used as the last-step constraint
-- in `Walk.IsCollider` (LN: $v_{n-1} \hus v_n$) and as the
-- first-step constraint in `Walk.IntoStart` (LN: $a_0 = v_0 \hus
-- v_1$).
/-- The step has an arrowhead at its *source* endpoint: `backward`
or `bidir`. Mirrors the LN's `v \hus w`. -/
def HasArrowheadAtSource : {v w : α} → WalkStep G v w → Prop
  | _, _, .forward _  => False
  | _, _, .backward _ => True
  | _, _, .bidir _    => True

@[simp] theorem hasArrowheadAtSource_forward {v w : α} (h : v ⟶[G] w) :
    (WalkStep.forward h).HasArrowheadAtSource ↔ False := Iff.rfl

@[simp] theorem hasArrowheadAtSource_backward {v w : α} (h : v ⟵[G] w) :
    (WalkStep.backward h).HasArrowheadAtSource ↔ True := Iff.rfl

@[simp] theorem hasArrowheadAtSource_bidir {v w : α} (h : v ⟷[G] w) :
    (WalkStep.bidir h).HasArrowheadAtSource ↔ True := Iff.rfl

/-- A step with an arrowhead at its target endpoint witnesses
`EdgeInto G w v` (def_3_3, item 2: `\suh` reading): a `forward`
step `v ⟶[G] w` gives `(w ⟵[G] v) ∨ ...` and a `bidir` step gives
`... ∨ (w ⟷[G] v)`. Note the swap of argument order between the
walk-step's `(v, w)` and the LN-prose's "into $w$". -/
theorem edgeInto_target_of_hasArrowheadAtTarget {v w : α} {s : WalkStep G v w}
    (hs : s.HasArrowheadAtTarget) : CDMG.EdgeInto G w v := by
  cases s with
  | forward h  => exact Or.inl h
  | backward _ => simp at hs
  | bidir h    => exact Or.inr (G.L_symm h)

/-- A step with an arrowhead at its source endpoint witnesses
`EdgeInto G v w` (def_3_3, item 2): a `backward` step `v ⟵[G] w`
gives `(v ⟵[G] w) ∨ ...` and a `bidir` step gives `... ∨ (v ⟷[G]
w)`. -/
theorem edgeInto_source_of_hasArrowheadAtSource {v w : α} {s : WalkStep G v w}
    (hs : s.HasArrowheadAtSource) : CDMG.EdgeInto G v w := by
  cases s with
  | forward _  => simp at hs
  | backward h => exact Or.inl h
  | bidir h    => exact Or.inr h

end WalkStep

namespace Walk

variable {G : CDMG α}

/-! ### IsDirected (LN def 3.4, item 2) -/

-- def_3_4 (item 2)
-- title: Walks -- directed walks
--
-- A walk is *directed* if every one of its steps is a `forward`
-- step (LN's `\tuh`). The recursion: trivial walk is vacuously
-- directed (LN's "for some $n \ge 0$" admits $n = 0$); a
-- `forward`-then-`p` walk is directed iff `p` is directed; a
-- walk with any non-forward leading step is not directed.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4,
item 2):

  A \emph{directed walk} from $v$ to $w$ in $G$ is of the form:
    $v=v_0 \tuh v_1 \tuh  \cdots \tuh v_{n-1} \tuh v_n=w,$
  for some $n \ge 0$,
  where all arrowheads point in the direction of $w$ and there are
  no arrowheads pointing back.
-/
--
-- ## Design choice
--
-- * **`Prop`-valued predicate, not a separate `DirectedWalk` type.**
--   The plan §4 (`workspace_def_3_4.md`) argues against duplicating
--   the inductive structure of `Walk`: a separate inductive would
--   need its own `length` / `support` / `append` / `reverse` API
--   re-proved from scratch, whereas a predicate composes naturally
--   with the data layer ("a directed walk from $v$ to $w$" becomes
--   `∃ π : Walk G v w, π.IsDirected`, which is exactly the LN's
--   existential shape used in def 3.5 for ancestors and
--   descendants).
--
-- * **`nil` is `True`, not `False`.** The LN admits $n = 0$
--   explicitly. This is load-bearing for def 3.5
--   (Family Relationships): $v \in \Anc^G(v)$ requires the trivial
--   directed walk from $v$ to itself.
--
-- * **Recursive shape `cons (.forward _) p ↦ p.IsDirected`,
--   everything else `False`.** Each pattern case unfolds to an
--   `Iff.rfl` simp lemma below -- downstream proofs reduce
--   `IsDirected` by `simp` one step at a time, without ever
--   needing to mention the body.
/-- A *directed walk*: every step is a `forward` step. Equivalent
to the LN's "all arrowheads point in the direction of $w$ and
there are no arrowheads pointing back" condition. The trivial walk
is directed vacuously. -/
def IsDirected : {v w : α} → Walk G v w → Prop
  | _, _, .nil _              => True
  | _, _, .cons (.forward _) p => p.IsDirected
  | _, _, .cons (.backward _) _ => False
  | _, _, .cons (.bidir _) _    => False

@[simp] theorem isDirected_nil (v : α) :
    (Walk.nil v : Walk G v v).IsDirected ↔ True := Iff.rfl

@[simp] theorem isDirected_cons_forward {v w u : α}
    (h : v ⟶[G] w) (p : Walk G w u) :
    (Walk.cons (.forward h) p).IsDirected ↔ p.IsDirected := Iff.rfl

@[simp] theorem isDirected_cons_backward {v w u : α}
    (h : v ⟵[G] w) (p : Walk G w u) :
    (Walk.cons (.backward h) p).IsDirected ↔ False := Iff.rfl

@[simp] theorem isDirected_cons_bidir {v w u : α}
    (h : v ⟷[G] w) (p : Walk G w u) :
    (Walk.cons (.bidir h) p).IsDirected ↔ False := Iff.rfl

/-! ### IsBidirected (LN def 3.4, item 3) -/

-- def_3_4 (item 3)
-- title: Walks -- bidirected walks
--
-- Mirror image of `IsDirected`: every step is `bidir` (LN's
-- `\huh`). Trivial walk vacuously bidirected.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4,
item 3):

  A \emph{bidirected walk} from $v$ to $w$ in $G$ is of the form:
    $v=v_0 \huh v_1 \huh \cdots \huh v_{n-1} \huh v_n=w,$
  for some $n \ge 0$, where all edges are bidirected.
-/
--
-- ## Design choice
--
-- Same shape as `IsDirected`: recursive predicate, one constructor
-- match per case, `nil` returns `True` because LN's "for some
-- $n \ge 0$" admits the trivial walk. Used in def 3.5 to define
-- the *district* $\Dist^G(v) = \{w \in G \mid \exists \text{
-- bidirected walk } v \huh \cdots \huh w \in G\}$.
/-- A *bidirected walk*: every step is a `bidir` step. The trivial
walk is bidirected vacuously. -/
def IsBidirected : {v w : α} → Walk G v w → Prop
  | _, _, .nil _              => True
  | _, _, .cons (.bidir _) p   => p.IsBidirected
  | _, _, .cons (.forward _) _ => False
  | _, _, .cons (.backward _) _ => False

@[simp] theorem isBidirected_nil (v : α) :
    (Walk.nil v : Walk G v v).IsBidirected ↔ True := Iff.rfl

@[simp] theorem isBidirected_cons_bidir {v w u : α}
    (h : v ⟷[G] w) (p : Walk G w u) :
    (Walk.cons (.bidir h) p).IsBidirected ↔ p.IsBidirected := Iff.rfl

@[simp] theorem isBidirected_cons_forward {v w u : α}
    (h : v ⟶[G] w) (p : Walk G w u) :
    (Walk.cons (.forward h) p).IsBidirected ↔ False := Iff.rfl

@[simp] theorem isBidirected_cons_backward {v w u : α}
    (h : v ⟵[G] w) (p : Walk G w u) :
    (Walk.cons (.backward h) p).IsBidirected ↔ False := Iff.rfl

/-! ### IsCollider (LN def 3.4, item 4)

`IsCollider` recurses through a helper `IsColliderInner` that
captures the LN's "$v_1 \huh \cdots \huh v_{n-1} \hus v_n$" tail
shape (every step bidir except possibly the last, which may also be
backward). The split makes the two endpoint constraints visible
separately and avoids a single 7-case recursion. -/

-- def_3_4 (item 4, helper)
-- title: Walks -- collider-walk tail predicate
--
-- `IsColliderInner π` says that `π` -- viewed as the *suffix* of a
-- collider walk starting at $v_1$ -- has every step except the
-- last bidirected (LN's `\huh` middle), and the last step has an
-- arrowhead at its source endpoint (LN's `\hus` last edge). The
-- trivial walk case is unreachable from `IsCollider` but defined
-- as `True` for totality.
/-- Helper for `IsCollider`: a walk whose internal steps are all
bidir and whose final step has an arrowhead at its source endpoint
(LN's `\hus`). Encodes the "$v_1 \huh \cdots \huh v_{n-1} \hus
v_n$" suffix of a collider walk. -/
def IsColliderInner : {v w : α} → Walk G v w → Prop
  | _, _, .nil _              => True
  | _, _, .cons s (.nil _)    => s.HasArrowheadAtSource
  | _, _, .cons s (.cons s' p) => s.IsBidir ∧ IsColliderInner (.cons s' p)

@[simp] theorem isColliderInner_nil (v : α) :
    (Walk.nil v : Walk G v v).IsColliderInner ↔ True := Iff.rfl

@[simp] theorem isColliderInner_cons_nil {v w : α} (s : WalkStep G v w) :
    (Walk.cons s (Walk.nil w) : Walk G v w).IsColliderInner ↔
      s.HasArrowheadAtSource := Iff.rfl

@[simp] theorem isColliderInner_cons_cons {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) :
    (Walk.cons s (Walk.cons s' p)).IsColliderInner ↔
      s.IsBidir ∧ (Walk.cons s' p).IsColliderInner := Iff.rfl

-- def_3_4 (item 4)
-- title: Walks -- collider walks
--
-- A collider walk has the LN shape:
--   $v_0 \suh v_1 \huh \cdots \huh v_{n-1} \hus v_n$.
-- Three constraints encoded by structural recursion:
--   * first step has an arrowhead at $v_1$ (`HasArrowheadAtTarget`,
--     i.e. forward or bidir);
--   * internal steps are all bidir (the `IsBidir` conjunct in
--     `IsColliderInner`);
--   * last step has an arrowhead at $v_{n-1}$
--     (`HasArrowheadAtSource`, i.e. backward or bidir).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4,
item 4):

  A \emph{collider walk} from $v$ to $w$ in $G$ is of the form:
    $v=v_0 \suh v_1 \huh \cdots \huh v_{n-1} \hus v_n=w,$
  for some $n \ge 0$, where all nodes in between $v$ and $w$ have
  two arrowheads pointing towards them (a.k.a.\ collider).
  Note that for $n=1$ this reads: $v\sus w \in G$.
-/
--
-- ## Design choice
--
-- * **Trivial walk ($n = 0$) is `True`.** The LN's "for some
--   $n \ge 0$" admits $n = 0$ and there are no internal nodes to
--   constrain. The plan §4 endorses this choice.
--
-- * **Single-step walk ($n = 1$): strict reading.** The LN's
--   general formula
--   `v_0 \suh v_1 \huh \cdots \huh v_{n-1} \hus v_n` with $n = 1$
--   collapses to a single edge that is *simultaneously* `\suh`
--   (arrowhead at $v_1$) and `\hus` (arrowhead at $v_0$),
--   i.e. bidirected. We adopt this strict reading -- the only
--   single-step collider walks are bidirected ones -- and so
--   `IsCollider (cons s (nil _))` reduces to `s.IsBidir`.
--
--   The LN's note "for $n = 1$ this reads: $v \sus w$" is *slightly
--   looser* (it admits any orientation), but the looser reading is
--   inconsistent with the simultaneous-`\suh`-and-`\hus`
--   instantiation of the general formula at $n = 1$, and the
--   downstream commented-out use in def 3.5
--   (`\MBl^G_d(v):=\{w \in G \mid \exists \text{ collider walk
--   } v \suh v_1 \huh \cdots \huh v_{n-1} \hus w\}`) and in
--   chapters 15 -- 16 only ever uses collider walks via the strict
--   general formula. Choosing the strict reading keeps the
--   predicate compositional with the rest of the LN's collider
--   reasoning and is the recommendation of the plan §4 / risks 2.
--
-- * **`HasArrowheadAtTarget` and `HasArrowheadAtSource`, not raw
--   constructors, in the simp characterisation.** The LN
--   vocabulary at this level is `\suh` and `\hus`; phrasing the
--   simp lemma in those terms (via the per-step helpers above)
--   keeps the downstream simp normal form aligned with the LN's
--   prose. The constructor-level simp lemmas on
--   `HasArrowheadAtTarget` etc. then collapse the per-step layer
--   in a separate simp step when needed.
--
-- * **Why the helper `IsColliderInner` and not a single 7-case
--   recursion?** Both work; the split mirrors the LN's two-clause
--   sentence ("first edge $\suh$, internal $\huh$, last edge
--   $\hus$") and gives three short simp lemmas on the outer
--   predicate plus three on the helper, instead of one big tangle.
/-- A *collider walk* in `G` from `v` to `w`: the LN shape
$v_0 \suh v_1 \huh \cdots \huh v_{n-1} \hus v_n$. The trivial walk
is a collider walk vacuously; a single-step walk is a collider
walk iff that step is bidirected (see the design-choice block
above for the $n = 1$ interpretation). -/
def IsCollider : {v w : α} → Walk G v w → Prop
  | _, _, .nil _              => True
  | _, _, .cons s (.nil _)    => s.IsBidir
  | _, _, .cons s (.cons s' p) =>
      s.HasArrowheadAtTarget ∧ (Walk.cons s' p).IsColliderInner

@[simp] theorem isCollider_nil (v : α) :
    (Walk.nil v : Walk G v v).IsCollider ↔ True := Iff.rfl

@[simp] theorem isCollider_cons_nil {v w : α} (s : WalkStep G v w) :
    (Walk.cons s (Walk.nil w) : Walk G v w).IsCollider ↔ s.IsBidir := Iff.rfl

@[simp] theorem isCollider_cons_cons {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) :
    (Walk.cons s (Walk.cons s' p)).IsCollider ↔
      s.HasArrowheadAtTarget ∧ (Walk.cons s' p).IsColliderInner := Iff.rfl

/-! ### IsPath (LN def 3.4, item 5) -/

-- def_3_4 (item 5)
-- title: Walks -- paths
--
-- A *path* is a walk with no repeated vertices. We define this
-- directly in terms of `Walk.support` (the visited-vertex list,
-- from `Walks.lean`) via `List.Nodup`. Mirrors Mathlib's
-- `SimpleGraph.Walk.IsPath`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4,
item 5):

  A walk is called \emph{path} if no node occurs more than once.
-/
--
-- ## Design choice
--
-- * **`support.Nodup`, not a bespoke per-step recursion.** The
--   support list already carries the vertex sequence in order; the
--   "no repeats" condition is exactly `List.Nodup`, which has a
--   full Mathlib API (`nodup_cons`, `nodup_append`, etc.) that
--   downstream chapters 15 -- 16 will use heavily when manipulating
--   paths. Defining `IsPath` recursively from scratch would be
--   strictly more work for no gain.
--
-- * **Trivial walk has `support = [v]` and `[v].Nodup` is `True`,**
--   so `(nil v).IsPath ↔ True` falls out -- the trivial walk is a
--   (degenerate) path. The LN's downstream uses of paths
--   (def 3.18, chapter 16) all admit this degeneracy, so no
--   special case is needed.
/-- A *path* in `G`: a walk whose visited-vertex sequence has no
repeats. Equivalent to `List.Nodup` on `Walk.support`. -/
def IsPath {v w : α} (π : Walk G v w) : Prop := π.support.Nodup

@[simp] theorem isPath_nil (v : α) :
    (Walk.nil v : Walk G v v).IsPath ↔ True := by
  simp [IsPath]

@[simp] theorem isPath_cons {v w u : α} (s : WalkStep G v w) (p : Walk G w u) :
    (Walk.cons s p).IsPath ↔ v ∉ p.support ∧ p.IsPath := by
  simp [IsPath]

/-- Reformulation of `IsPath` in terms of `support.Nodup`, the
defining equation. Useful when invoking Mathlib's `Nodup` lemmas
directly. -/
theorem isPath_iff_support_nodup {v w : α} (π : Walk G v w) :
    π.IsPath ↔ π.support.Nodup := Iff.rfl

/-! ### IntoStart / OutOfStart (LN def 3.4, item 1 prose) -/

-- def_3_4 (item 1 prose: "into / out of $v_0$")
-- title: Walks -- the walk's first edge enters $v_0$
--
-- The LN sentence (item 1): "The walk is called *into $v_0$* if
-- $a_0 = v_0 \hus v_1$". So `IntoStart π` says the walk's *first
-- step* has an arrowhead at the walk's start vertex -- equivalently,
-- the first `WalkStep` is `backward` (LN's `\hut`) or `bidir`
-- (LN's `\huh`).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4,
item 1, in-line):

  The walk is called \emph{into $v_0$} if $a_0 = v_0 \hus v_1$, ...
-/
--
-- ## Design choice
--
-- * **`nil` is `False`.** The LN sentence references a specific
--   edge $a_0$; the trivial walk has no edges, and every
--   downstream LN use of these prose predicates (def 3.15 / 3.17
--   collider predicates, chapter 16 path-vs-walk arguments) is on
--   walks of length $\ge 1$. Plan §7 endorses this choice.
--
-- * **Constructor-level recursion, not `EdgeInto`-level.** A CDMG
--   may host more than one edge between a vertex pair (e.g. both
--   a directed and a bidirected edge), so the abstract relation
--   `EdgeInto G v v'` does not pin down which edge `a_0` is. The
--   LN's sentence specifically constrains `a_0`; we match the LN
--   by pattern-matching on the constructor of the first step.
--   `intoStart_implies_edgeInto` below gives the one-way bridge to
--   `def_3_3.EdgeInto` for downstream callers who want to reason
--   in the LN's `\hus` vocabulary.
/-- The walk is *into $v_0$* (LN item 1 prose): the first
`WalkStep` is `backward` or `bidir`, i.e. it has an arrowhead at
the walk's start vertex. The trivial walk is *not* into its start
vertex (it has no first edge). -/
def IntoStart : {v w : α} → Walk G v w → Prop
  | _, _, .nil _              => False
  | _, _, .cons s _           => s.HasArrowheadAtSource

@[simp] theorem intoStart_nil (v : α) :
    (Walk.nil v : Walk G v v).IntoStart ↔ False := Iff.rfl

@[simp] theorem intoStart_cons {v w u : α}
    (s : WalkStep G v w) (p : Walk G w u) :
    (Walk.cons s p).IntoStart ↔ s.HasArrowheadAtSource := Iff.rfl

/-- LN prose bridge to `def_3_3`: a walk `into $v_0$` (whose first
step goes to some next vertex $v_1$) certifies that there is an
edge into $v_0$ from $v_1$ in `G`. The converse does *not* hold in
general (parallel edges between $v_0$ and $v_1$ may make
`EdgeInto G v v₁` true even when the walk's first step is
`forward`). -/
theorem intoStart_implies_edgeInto {v w u : α}
    {s : WalkStep G v w} {p : Walk G w u}
    (h : (Walk.cons s p).IntoStart) : CDMG.EdgeInto G v w :=
  WalkStep.edgeInto_source_of_hasArrowheadAtSource (by simpa using h)

-- def_3_4 (item 1 prose: "out of $v_0$")
-- title: Walks -- the walk's first edge leaves $v_0$
--
-- LN sentence: "out of $v_0$ if $a_0 = v_0 \tuh v_1$" -- the first
-- step is a *directed* edge from $v_0$. No bidir disjunct (a
-- bidirected edge is "into $v_0$", never "out of $v_0$" -- see
-- def_3_3 design discussion).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4,
item 1, in-line):

  ... and \emph{out of $v_0$} if $a_0 = v_0 \tuh v_1$.
-/
--
-- ## Design choice
--
-- * **`forward` only, no bidir.** Mirrors def_3_3's asymmetric
--   treatment of "out of": bidirected edges have arrowheads at
--   both endpoints, so they are *into* both vertices but *out of*
--   neither.
--
-- * **`nil` is `False`** for the same reason as `IntoStart`.
/-- The walk is *out of $v_0$* (LN item 1 prose): the first
`WalkStep` is `forward`, i.e. a directed edge originating at
$v_0$. The trivial walk is not out of its start vertex. -/
def OutOfStart : {v w : α} → Walk G v w → Prop
  | _, _, .nil _              => False
  | _, _, .cons (.forward _) _ => True
  | _, _, .cons (.backward _) _ => False
  | _, _, .cons (.bidir _) _    => False

@[simp] theorem outOfStart_nil (v : α) :
    (Walk.nil v : Walk G v v).OutOfStart ↔ False := Iff.rfl

@[simp] theorem outOfStart_cons_forward {v w u : α}
    (h : v ⟶[G] w) (p : Walk G w u) :
    (Walk.cons (.forward h) p).OutOfStart ↔ True := Iff.rfl

@[simp] theorem outOfStart_cons_backward {v w u : α}
    (h : v ⟵[G] w) (p : Walk G w u) :
    (Walk.cons (.backward h) p).OutOfStart ↔ False := Iff.rfl

@[simp] theorem outOfStart_cons_bidir {v w u : α}
    (h : v ⟷[G] w) (p : Walk G w u) :
    (Walk.cons (.bidir h) p).OutOfStart ↔ False := Iff.rfl

/-- LN prose bridge: a walk *out of $v_0$* certifies an
`EdgeOutOf G v_0 v_1` (def_3_3) -- the first step is a `forward`
step, which is exactly `EdgeOutOf`. The converse holds for
single-step walks but not in general (parallel edges). -/
theorem outOfStart_implies_edgeOutOf {v w u : α}
    {s : WalkStep G v w} {p : Walk G w u}
    (h : (Walk.cons s p).OutOfStart) : CDMG.EdgeOutOf G v w := by
  cases s with
  | forward hs => exact hs
  | backward _ => simp at h
  | bidir _    => simp at h

/-! ### IntoEnd / OutOfEnd (LN def 3.4, item 1 prose) -/

-- def_3_4 (item 1 prose: "into $v_n$")
-- title: Walks -- the walk's last edge enters $v_n$
--
-- LN sentence: "into $v_n$ if $a_{n-1} = v_{n-1} \suh v_n$" -- the
-- last step has an arrowhead at $v_n$, i.e. it is `forward` (`\tuh`)
-- or `bidir` (`\huh`). Recurses through the walk to reach the last
-- step (mirroring `Walks.lean`'s `lastStep?`).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4,
item 1, in-line):

  Similarly, it is called \emph{into $v_n$} if $a_{n-1} = v_{n-1}
  \suh v_n$ ...
-/
--
-- ## Design choice
--
-- * **Recursion structure parallel to `lastStep?` in
--   `Walks.lean`.** Three cases:
--   - `nil`: false (no last edge).
--   - `cons s (nil _)`: single-step walk; this step is the last,
--     check `s.HasArrowheadAtTarget`.
--   - `cons _ (cons s' p)`: at least two steps; recurse into the
--     tail (the leading step is not the last).
--
-- * **Uses `HasArrowheadAtTarget`** (forward or bidir), mirroring
--   the LN's `\suh`.
/-- The walk is *into $v_n$* (LN item 1 prose): the last
`WalkStep` has an arrowhead at the walk's end vertex
(`HasArrowheadAtTarget`). The trivial walk is not into its end
vertex (no last edge). -/
def IntoEnd : {v w : α} → Walk G v w → Prop
  | _, _, .nil _              => False
  | _, _, .cons s (.nil _)    => s.HasArrowheadAtTarget
  | _, _, .cons _ (.cons s p) => IntoEnd (.cons s p)

@[simp] theorem intoEnd_nil (v : α) :
    (Walk.nil v : Walk G v v).IntoEnd ↔ False := Iff.rfl

@[simp] theorem intoEnd_cons_nil {v w : α} (s : WalkStep G v w) :
    (Walk.cons s (Walk.nil w) : Walk G v w).IntoEnd ↔
      s.HasArrowheadAtTarget := Iff.rfl

@[simp] theorem intoEnd_cons_cons {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) :
    (Walk.cons s (Walk.cons s' p)).IntoEnd ↔ (Walk.cons s' p).IntoEnd := Iff.rfl

-- def_3_4 (item 1 prose: "out of $v_n$")
-- title: Walks -- the walk's last edge leaves $v_n$
--
-- LN sentence: "out of $v_n$ if $a_{n-1} = v_{n-1} \hut v_n$" --
-- the last step is `backward` (`\hut`), i.e. a directed edge from
-- $v_n$ to $v_{n-1}$ ($v_n$ is the tail).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4,
item 1, in-line):

  ... and \emph{out of $v_n$} if $a_{n-1} = v_{n-1} \hut v_n$.
-/
--
-- ## Design choice
--
-- * **`backward` only.** Just as `OutOfStart` excludes `bidir`,
--   `OutOfEnd` does too: a bidirected last edge is *into* $v_n$,
--   never *out of* $v_n$.
--
-- * **Same recursion shape as `IntoEnd`.**
/-- The walk is *out of $v_n$* (LN item 1 prose): the last
`WalkStep` is `backward`, i.e. a directed edge with $v_n$ as the
tail. The trivial walk is not out of its end vertex. -/
def OutOfEnd : {v w : α} → Walk G v w → Prop
  | _, _, .nil _              => False
  | _, _, .cons s (.nil _)    =>
      -- Single-step walk: this step is the last; it must be backward.
      match s with
      | .backward _ => True
      | _           => False
  | _, _, .cons _ (.cons s p) => OutOfEnd (.cons s p)

@[simp] theorem outOfEnd_nil (v : α) :
    (Walk.nil v : Walk G v v).OutOfEnd ↔ False := Iff.rfl

@[simp] theorem outOfEnd_cons_nil_forward {v w : α} (h : v ⟶[G] w) :
    (Walk.cons (.forward h) (Walk.nil w) : Walk G v w).OutOfEnd ↔ False := Iff.rfl

@[simp] theorem outOfEnd_cons_nil_backward {v w : α} (h : v ⟵[G] w) :
    (Walk.cons (.backward h) (Walk.nil w) : Walk G v w).OutOfEnd ↔ True := Iff.rfl

@[simp] theorem outOfEnd_cons_nil_bidir {v w : α} (h : v ⟷[G] w) :
    (Walk.cons (.bidir h) (Walk.nil w) : Walk G v w).OutOfEnd ↔ False := Iff.rfl

@[simp] theorem outOfEnd_cons_cons {v w x u : α}
    (s : WalkStep G v w) (s' : WalkStep G w x) (p : Walk G x u) :
    (Walk.cons s (Walk.cons s' p)).OutOfEnd ↔ (Walk.cons s' p).OutOfEnd := Iff.rfl

end Walk

end Causality
