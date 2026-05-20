import Chapter3_GraphTheory.Section3_1.WalkPredicates

/-!
# Bifurcations in a CDMG (def 3.4, item 6)

This file formalises *item 6* of definition 3.4 of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`): the
*bifurcation* concept in a Conditional Directed Mixed Graph (CDMG),
together with its *source* (when the hinge edge happens to be a
directed edge `\hut` rather than a bidirected edge `\huh`).

This is the structurally trickiest piece of LN def 3.4 because the
LN's prose decomposes a bifurcation at an existentially-quantified
hinge index $k$:
\[ v = v_0 \hut v_1 \hut \cdots \hut v_{k-1} \hus v_k
       \tuh \cdots \tuh v_n = w. \]
The left arm has $k-1$ steps (positions $0,\dots,k-2$, all `\hut`),
the hinge is a single edge at position $k-1$ (0-indexed; it is
either `\hut` or `\huh`, satisfying the LN's `\hus` reading), and
the right arm has $n-k$ steps (positions $k,\dots,n-1$, all
`\tuh`). The LN restricts to $1 \le k \le n$ and $v \ne w$, with
both endnodes appearing exactly once.

## Encoding sketch (for the design verifier)

We encode a bifurcation by a **`Type _`-valued witness structure**
`Walk.BifurcationWitness π` that explicitly names the three pieces:

* `m, m' : α` -- the LN's $v_{k-1}$ and $v_k$ (hinge endpoints);
* `leftArm : Walk G v m` -- the left subwalk $v_0 \hut \cdots
  \hut v_{k-1}$;
* `hinge : WalkStep G m m'` -- the hinge step $v_{k-1} \hus v_k$;
* `rightArm : Walk G m' w` -- the right subwalk $v_k \tuh \cdots
  \tuh v_n$;
* `decompose : π = leftArm.append (.cons hinge rightArm)` -- ties
  the three pieces back to `π`;
* `leftBackward : leftArm.IsAllBackward` -- every step of the
  left arm is `backward` (LN's `\hut`); equivalent to the LN's
  "the subwalk $v_0 \hut \cdots v_{k-1}$ is a directed walk from
  $v_{k-1}$ to $v_0$" reading;
* `hingeIntoSource : hinge.HasArrowheadAtSource` -- the hinge is
  `backward` or `bidir` (the LN's `\hus` reading);
* `rightDirected : rightArm.IsDirected` -- every step of the
  right arm is `forward` (LN's `\tuh`).

The **`Prop`-valued predicate** `Walk.IsBifurcation π` bundles the
LN's endpoint constraints ($v \ne w$, both endnodes appear exactly
once) with `Nonempty (BifurcationWitness π)`.

The **source extractor** `Walk.bifurcationSource (hb :
π.IsBifurcation) : Option α` picks any witness via
`Classical.choice` and returns:

* `some bw.m'` (the LN's $v_k$) if the chosen `bw.hinge` is
  `backward` (the LN's `\hut` case -- "the bifurcation has source
  $v_k$");
* `none` if the chosen `bw.hinge` is `bidir` (the LN's `\huh` case
  -- the bifurcation has no source).

(`bw.hinge` cannot be `forward` because the witness's
`hingeIntoSource` field rules that case out; the `match` in
`bifurcationSource` still includes a catch-all `_ => none` branch
for totality.)

## Design decisions

* **Decomposition-into-arms vs. indexed `takeSteps`/`dropSteps`.**
  The plan §6 outlines two options for capturing the existential
  hinge index $k$:
  - (a) define `Walk.takeSteps` / `Walk.dropSteps` and state the
    predicate as "$k$ such that takeSteps $(k-1)$ is all-backward,
    step $k-1$ is `\hus`, dropSteps $k$ is directed";
  - (b) introduce a separate inductive type whose constructors
    encode the three-piece shape directly.

  We pick a *third* option (closer to (a) than (b)): a
  `Type _`-valued **witness structure** that names the three
  pieces (left arm, hinge, right arm) directly, without going
  through a numeric index $k$. This (i) sidesteps the off-by-one
  indexing required by the index form (the LN's $k$ ranges over
  $1, \dots, n$ with the hinge at *position* $k-1$, which is
  fiddly), (ii) makes `Walk.bifurcationSource` a pure
  pattern-match on the hinge's constructor rather than an
  arithmetic-laden access via `dropSteps (k-1)`, and (iii)
  directly mirrors the LN's downstream usage pattern: claim_3_5's
  proof concatenates a left directed walk and a right directed
  walk; def_3_14 reads off the "intermediate nodes" of the arms;
  remark_3_16's marginalisation argument inducts on the arms
  separately. The LN never refers to the numeric index $k$ in any
  argument that survives into Lean, so we don't carry $k$
  forward.

  The LN's $k$ is still recoverable from a witness as
  $k = 1 + \text{leftArm}.\text{length}$; we have not exposed a
  lemma for this because no current downstream row asks for it.

* **`Walk.IsAllBackward` vs. `leftArm.reverse.IsDirected`.**
  The LN's left-arm condition is "the subwalk $v_0 \hut \cdots
  v_{k-1}$ is a directed walk from $v_{k-1}$ to $v_0$" -- i.e.
  the left arm read in reverse is a directed walk. Two equivalent
  Lean phrasings:
  - directly: `leftArm.IsAllBackward` (every step is `backward`);
  - via reversal: `leftArm.reverse.IsDirected`.

  We adopt the *direct* `IsAllBackward` predicate because it is
  structurally simpler (no `reverse` to unfold) and yields clean
  `simp` lemmas mirroring `IsDirected`. The equivalence
  `leftArm.IsAllBackward ↔ leftArm.reverse.IsDirected` is not
  proven here -- it requires a careful induction on `reverse` and
  `IsDirected` over `append`, and is not needed by any downstream
  row currently in scope. (If a downstream row wants the LN-prose
  reading "is a directed walk from $v_{k-1}$ to $v_0$", they can
  either work with `IsAllBackward` directly or prove the
  equivalence locally.)

* **Endpoints "exactly once" via `support.tail` / `support.dropLast`.**
  The LN's "the walk contains both endnodes exactly once" reads
  naturally as `support.count v = 1 ∧ support.count w = 1`, but
  `List.count` requires `[BEq α]` / `[DecidableEq α]`, an
  assumption we cannot make at this layer of the project (the
  vertex type ranges over arbitrary `α : Type*` in def_3_1's
  `CDMG α`; chapters 4+ use real-valued nodes). The
  decidability-free phrasing `v ∉ π.support.tail ∧
  w ∉ π.support.dropLast` captures the same content: $v$ does
  not appear after position 0 (where it always sits as the head
  of `support`), and $w$ does not appear before position $n$
  (where it always sits as the last element). Combined with those
  always-true endpoint placements, this gives "each endnode
  appears exactly once".

* **`v ≠ w` retained as a separate clause.** The LN spells out
  "$v \ne w$" *in addition* to "both endnodes exactly once". The
  two are partly redundant -- if $v = w$ then for any non-trivial
  walk `support` has the form `v :: ... :: v`, violating "exactly
  once"; for the trivial walk `nil v` the witness's existential
  fails anyway because there is no hinge step. We include
  $v \ne w$ verbatim for LN fidelity.

* **`bifurcationSource` is `noncomputable`.** `Nonempty.some`
  invokes the `Classical.choice` axiom. The LN does not claim the
  witness's hinge index is unique -- a walk with two candidate
  hinge positions could in principle yield two distinct witnesses
  with two distinct sources -- so `bifurcationSource` is
  well-defined only up to classical choice. In practice every
  downstream LN use of the source either (a) names $c$ via an
  outer existential ("there exists a bifurcation between $v$ and
  $w$ with source $c$", which Lean-faithfully reads as
  `∃ π, π.IsBifurcation ∧ π.bifurcationSource = some c`), or
  (b) tests bifurcation existence without inspecting the source.
  In neither case does the ambiguity surface.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

/-! ### Auxiliary: every step is a `backward` step -/

-- helper for def_3_4 (item 6)
-- title: Walks -- predicate "every step is a backward step"
--
-- Mirror image of `Walk.IsDirected` (LN item 2) but for the
-- `backward` constructor (LN's `\hut`) instead of `forward`
-- (LN's `\tuh`). Used inside `BifurcationWitness`'s `leftBackward`
-- field to express the LN's "the subwalk $v_0 \hut \cdots v_{k-1}$
-- is a directed walk from $v_{k-1}$ to $v_0$" condition: a walk
-- whose every step is `backward` reads in reverse as a directed
-- walk, which is exactly the LN's reading.
--
-- ## Design choice
--
-- * **Same shape as `IsDirected`.** One pattern case per
--   `WalkStep` constructor; the `backward` case recurses, the
--   other two return `False`, and `nil` returns `True`. Each
--   pattern yields an `Iff.rfl` simp lemma below, so callers
--   reduce `IsAllBackward` one step at a time without unfolding
--   the body.
--
-- * **Trivial walk: `True` (vacuous).** Matches the
--   `IsDirected_nil` design: the LN's left-arm sentence for
--   $k = 1$ reads "the subwalk is just $v_0$, which is the
--   trivial directed walk from $v_0$ to itself", and that
--   degenerate case must be admitted.
--
-- * **No equivalence to `reverse.IsDirected` proven here.** The
--   equivalence would require a non-trivial induction on
--   `reverse` and `IsDirected` over `append`, and no downstream
--   row currently needs it. See the module docstring's design
--   block for the trade-off.
/-- A walk in which *every step* is a `backward` step (the LN's
`\hut`). The trivial walk is vacuously `IsAllBackward`. The LN's
"the subwalk $v_0 \hut \cdots v_{k-1}$ is a directed walk from
$v_{k-1}$ to $v_0$" (def 3.4 item 6, left arm of a bifurcation)
is equivalent to this predicate on the left arm. -/
def IsAllBackward : {v w : α} → Walk G v w → Prop
  | _, _, .nil _               => True
  | _, _, .cons (.backward _) p => p.IsAllBackward
  | _, _, .cons (.forward _) _  => False
  | _, _, .cons (.bidir _) _    => False

@[simp] theorem isAllBackward_nil (v : α) :
    (Walk.nil v : Walk G v v).IsAllBackward ↔ True := Iff.rfl

@[simp] theorem isAllBackward_cons_backward {v w u : α}
    (h : v ⟵[G] w) (p : Walk G w u) :
    (Walk.cons (.backward h) p).IsAllBackward ↔ p.IsAllBackward := Iff.rfl

@[simp] theorem isAllBackward_cons_forward {v w u : α}
    (h : v ⟶[G] w) (p : Walk G w u) :
    (Walk.cons (.forward h) p).IsAllBackward ↔ False := Iff.rfl

@[simp] theorem isAllBackward_cons_bidir {v w u : α}
    (h : v ⟷[G] w) (p : Walk G w u) :
    (Walk.cons (.bidir h) p).IsAllBackward ↔ False := Iff.rfl

/-! ### Bifurcation witness structure -/

-- def_3_4 (item 6, witness structure)
-- title: Walks -- explicit decomposition witness for a bifurcation
--
-- A `BifurcationWitness π` is the explicit data of a decomposition
-- of `π` as a bifurcation, naming all three pieces (left arm,
-- hinge step, right arm) and packaging the LN's shape constraints
-- (left arm all `backward`, hinge `\hus`, right arm `IsDirected`)
-- as Prop-level fields.
--
-- The structure is `Type _`-valued because its `α`-, `Walk`-, and
-- `WalkStep`-valued fields cannot inhabit `Prop`. The
-- `Prop`-level "$\pi$ is a bifurcation" predicate (`IsBifurcation`,
-- below) lifts the structure to `Prop` via `Nonempty`.
--
-- See the module docstring for the design discussion of why a
-- witness structure was chosen over a numeric-index encoding.
/-- Witness that a walk `π : Walk G v w` is a bifurcation: an
explicit decomposition into a left arm (all `backward` steps), a
hinge step (with an arrowhead at its source, i.e. `backward` or
`bidir`), and a right arm (all `forward` steps), matching LN
def 3.4 item 6's shape
$v_0 \hut \cdots \hut v_{k-1} \hus v_k \tuh \cdots \tuh v_n$. -/
structure BifurcationWitness {v w : α} (π : Walk G v w) : Type _ where
  /-- The LN's $v_{k-1}$: end of the left arm, start of the hinge. -/
  m : α
  /-- The LN's $v_k$: end of the hinge, start of the right arm. -/
  m' : α
  /-- The left arm $v_0 \hut \cdots \hut v_{k-1}$. Has length
  $k - 1$; may be the trivial walk `nil v` if $k = 1$. -/
  leftArm : Walk G v m
  /-- The hinge step $v_{k-1} \hus v_k$ -- either `backward`
  (LN's `\hut`, giving a source) or `bidir` (LN's `\huh`, no
  source). -/
  hinge : WalkStep G m m'
  /-- The right arm $v_k \tuh \cdots \tuh v_n$. Has length
  $n - k$; may be the trivial walk `nil w` if $k = n$. -/
  rightArm : Walk G m' w
  /-- The walk `π` decomposes as `leftArm` followed by the hinge
  step followed by `rightArm`. -/
  decompose : π = leftArm.append (Walk.cons hinge rightArm)
  /-- Every step of the left arm is a `backward` step
  (LN: "$v_0 \hut \cdots \hut v_{k-1}$"). -/
  leftBackward : leftArm.IsAllBackward
  /-- The hinge step has an arrowhead at its source endpoint,
  i.e. it is `backward` or `bidir` (LN: "$v_{k-1} \hus v_k$"). -/
  hingeIntoSource : hinge.HasArrowheadAtSource
  /-- Every step of the right arm is a `forward` step
  (LN: "$v_k \tuh \cdots \tuh v_n$"). -/
  rightDirected : rightArm.IsDirected

/-! ### `IsBifurcation` predicate -/

-- def_3_4 (item 6, predicate)
-- title: Walks -- bifurcation predicate
--
-- A walk is a *bifurcation* (LN def 3.4 item 6) iff:
--   * `v ≠ w` (LN's "such that $v \ne w$");
--   * both endnodes appear exactly once in `support` (LN's "the
--     walk contains both endnodes exactly once"), encoded as
--     `v ∉ support.tail ∧ w ∉ support.dropLast` (see the design
--     block in the module docstring for why we avoid
--     `List.count`);
--   * there exists a witness of the LN's shape decomposition
--     (left arm + hinge + right arm), encoded as
--     `Nonempty (BifurcationWitness π)`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.4,
item 6):

  A \emph{bifurcation} between $v$ and $w$ in $G$ is a walk of the
  form:
    $v=v_0 \hut v_1 \hut  \cdots \hut v_{k-1} \hus v_k
       \tuh \cdots \tuh v_{n-1} \tuh v_n=w,$
  such that $v \ne w$, the walk contains both endnodes exactly
  once, the subwalk $v_0 \hut \cdots v_{k-1}$ is a directed walk
  from $v_{k-1}$ to $v_0$, and the subwalk $v_k \tuh \cdots v_n$
  is a directed walk from $v_k$ to $v_n$. If the edge
  $v_{k-1} \hus v_k$ is directed ($v_{k-1} \hut v_k$) then we say
  that the bifurcation has \emph{source} $v_k$.
-/
/-- A walk `π : Walk G v w` is a *bifurcation* between $v$ and $w$
in $G$ (LN def 3.4 item 6) iff $v \ne w$, both endnodes appear
exactly once in `π.support`, and `π` admits a witness
decomposition into a left arm (all `backward`), a hinge step
(`backward` or `bidir`), and a right arm (all `forward`). -/
def IsBifurcation {v w : α} (π : Walk G v w) : Prop :=
  v ≠ w ∧
  v ∉ π.support.tail ∧
  w ∉ π.support.dropLast ∧
  Nonempty (BifurcationWitness π)

/-! ### `bifurcationSource` extractor -/

-- def_3_4 (item 6, source extractor)
-- title: Walks -- the source of a bifurcation (Option-valued)
--
-- Picks any bifurcation witness via `Classical.choice` and returns
-- `some bw.m'` (the LN's $v_k$) if the chosen hinge is `backward`
-- (LN's $v_{k-1} \hut v_k$, directed), or `none` if the hinge is
-- `bidir` (LN's $v_{k-1} \huh v_k$, bidirected). The `forward`
-- case is impossible (ruled out by the witness's `hingeIntoSource`
-- field), but Lean's pattern-matcher still requires a branch for
-- exhaustiveness; we collapse it with the bidir case via a
-- catch-all `_ => none`.
--
-- ## Design choice
--
-- * **`Option α` return type, not a `Prop`-valued
--   `HasBifurcationSource` predicate.** Per the manager's
--   deliverable spec. The advantage is that downstream callers
--   can compare `π.bifurcationSource hb = some c` for a specific
--   candidate `c`, matching the LN's prose "the bifurcation has
--   source $v_k$".
--
-- * **`noncomputable`.** Classical.choice (used by
--   `Nonempty.some`) introduces axiomatic non-constructivity.
--   We accept this because the LN does not claim witness
--   uniqueness and downstream uses do not need a constructive
--   source extractor.
--
-- * **Catch-all `_ => none`.** Lean's `match` requires all
--   constructors of `WalkStep` to be matched. The witness's
--   `hingeIntoSource` field forbids `forward`, but the `match`
--   syntax doesn't see that; we use `_ => none` to handle the
--   `bidir` (legitimate "no source") and `forward` (impossible)
--   cases uniformly. The corner case is that if a stranger
--   constructed an invalid witness with hinge = `.forward _`,
--   `bifurcationSource` would return `none` -- the
--   `hingeIntoSource` field rules this out, so for any
--   well-formed witness the catch-all only fires on `bidir`.
/-- The *source* of a bifurcation in the LN def 3.4 item 6 sense:
`some bw.m'` if the chosen witness's hinge is `backward` (the
LN's "$v_{k-1} \hut v_k$" directed-hinge case, where the source
is $v_k$), or `none` if it is `bidir` (LN's "$v_{k-1} \huh v_k$"
bidirected-hinge case, where the LN does not assign a source).
The witness is selected by `Classical.choice` from the
`Nonempty (BifurcationWitness π)` clause of `IsBifurcation`; see
the module docstring for the well-definedness caveat. -/
noncomputable def bifurcationSource {v w : α} (π : Walk G v w)
    (hb : π.IsBifurcation) : Option α :=
  let bw := hb.2.2.2.some
  match bw.hinge with
  | .backward _ => some bw.m'
  | _           => none

/-! ### Basic lemmas -/

-- A bifurcation has $v \ne w$. Spelled out as a separate lemma
-- because the `IsBifurcation` predicate is a `def` (not an
-- `abbrev`) and so the conjunction does not unfold automatically.
/-- A bifurcation has distinct endpoints (the LN's "$v \ne w$"
clause, spelled out as a one-line consequence of
`IsBifurcation`). -/
theorem ne_of_isBifurcation {v w : α} {π : Walk G v w}
    (hb : π.IsBifurcation) : v ≠ w := hb.1

-- The trivial walk is not a bifurcation. Follows immediately from
-- the $v \ne w$ clause, since `nil v : Walk G v v`.
/-- The trivial walk `nil v` is not a bifurcation: its endpoints
coincide, violating the $v \ne w$ clause. -/
theorem nil_not_isBifurcation (v : α) :
    ¬ (Walk.nil v : Walk G v v).IsBifurcation :=
  fun hb => hb.1 rfl

-- A bifurcation has length at least 1. The witness's decomposition
-- `π = leftArm.append (.cons hinge rightArm)` exhibits at least
-- the hinge step, so `π.length ≥ 1`.
/-- A bifurcation has length at least 1. The witness's
decomposition `π = leftArm.append (.cons hinge rightArm)`
exhibits at least the hinge step, forcing $\pi.\text{length}
\ge 1$. -/
theorem length_pos_of_isBifurcation {v w : α} {π : Walk G v w}
    (hb : π.IsBifurcation) : 1 ≤ π.length := by
  obtain ⟨_, _, _, ⟨bw⟩⟩ := hb
  rw [bw.decompose, length_append, length_cons]
  omega

end Walk

end Causality
