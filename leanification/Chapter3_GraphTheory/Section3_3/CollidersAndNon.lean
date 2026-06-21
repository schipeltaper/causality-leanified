import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.EdgeRelations
import Chapter3_GraphTheory.Section3_1.Walks

namespace Causality

/-!
# Colliders and non-colliders on walks (`def_3_15`)

This file formalises `def_3_15` (`\label{def:collider_noncollider}`),
the first definition of Section 3.3 of the lecture notes.  Given a
walk `π = (v_0, a_0, v_1, …, a_{n-1}, v_n)` in a CDMG `G`, every
position `k ∈ {0, 1, …, n}` is classified as either a **collider** or
a **non-collider** on `π` according to the arrowhead-count
`ah_π(k) ∈ {0, 1, 2}` — the number of walk-incident edges
`a_{k - 1}, a_k` that are "edges into `v_k`" in the sense of `def_3_3`
item~ii.

* `Walk.IsCollider p k` — `ah_π(k) = 2`; both walk-incident edges
  exist (forcing `1 ≤ k` and `k < p.length`, i.e.\ an interior
  position) and both are edges into `v_k`.
* `Walk.IsNonCollider p k` — `ah_π(k) ≤ 1`; the position is in
  range (`k ≤ p.length`) and is *not* a collider.  End-positions
  `k ∈ {0, p.length}` automatically have at most one walk-incident
  edge in scope, so they are non-colliders by construction.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/def_3_15_CollidersAndNon.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:collider_noncollider}`).  The canonical tex's
`addition_to_the_LN` is empty — the only nontrivial transformation
was spelling out the bespoke visual edge-mark notation
(`\sus, \hut, \tuh, \suh, \hus, \huh`) as the set-theoretic
arrowhead-counting predicate
`ah_π(k) := |{i ∈ {k - 1, k} : 0 ≤ i ≤ n - 1 ∧ a_i edge into v_k}|`,
reusing `def_3_3` item~ii's "edge into `v_k`" predicate.

## Design pillars

1. **`Prop` predicates on `Walk` indexed by `(k : ℕ)`, mirroring
   `Walk.IsBifurcationWithSplit` (`def_3_4`).**  Natural-number
   positions match the LN's `k ∈ {0, …, n}` enumeration; out-of-
   range positions (`k > p.length`) make both predicates vacuously
   `False`, in line with the LN's "every position on `π`" scope.

2. **`IsCollider` as the primary predicate, `IsNonCollider` as the
   complement on in-range positions.**  Avoids a ℕ-valued counting
   helper `ahCount`, which would require decidability discharges at
   every elaboration site.  Mathematically the count lives in
   `{0, 1, 2}` (canonical tex, paragraph "Arrowhead count at a
   position"), so `ah_π(k) ≤ 1 ↔ ¬ (ah_π(k) = 2)` — the negation
   form is semantically equivalent to the LN's "at most one
   arrowhead" reading.

The substantive per-declaration design rationale lives in the
comment block immediately above each `-- def_3_15 -- start statement`
marker.
-/

end Causality

namespace Causality

namespace CDMG

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same chapter
--   convention used by every other `CDMG`-opening file in the chapter
--   (`Walks.lean:1201-1203`, `CDMG.lean`, `CDMGNotation.lean`,
--   `EdgeRelations.lean`).
--
-- *Three-dash `--- start helper` / `--- end helper`, not two-dash
--   `-- start statement`.*  Lean 4's `variable` auto-binding folds these
--   implicit binders into every declaration below.  The three-dash
--   flavour tags this as helper-level wrapping, consistent with how the
--   `CDMG` section-wide `variable` at `Walks.lean:1201-1203` is tagged.
-- def_3_15 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_15 --- end helper

namespace WalkStep

-- ## Design choice — WalkStep-namespace statement context
--
-- *Why a namespace-level `variable {G : CDMG Node}`.*  The
--   helper `IsInto` below takes a typed WalkStep
--   `s : WalkStep G u v` and asks whether it places an
--   arrowhead at a given node.  Without the namespace-wide `variable`,
--   the signature would carry an explicit `{G : CDMG Node}`
--   binder; the auto-binding keeps the signature readable and matches
--   the chapter-wide implicit-G convention used by every
--   `CDMG`-opening file in the chapter
--   (`Walks.lean:1201-1203`, `EdgeRelations.lean:357`, etc.).
--
-- *Three-dash helper marker, not two-dash statement marker.*  Same
--   rationale as the `Walk` namespace `variable` block below
--   and as the section-wide `variable` immediately above: this `{G}`
--   binder is load-bearing infrastructure that the tex/Lean
--   reconciliation tooling must recognise as helper-flavour.
-- def_3_15 --- start helper
variable {G : CDMG Node}
-- def_3_15 --- end helper

-- ref: def_3_15 (helper, "edge into a node" at a typed WalkStep)
--
-- `s.IsInto w` iff the typed WalkStep `s : WalkStep
-- G u v` places an arrowhead at the node `w` when traversed.  The
-- typed-WalkStep transcription of `def_3_3` item~ii's "edge into a
-- node" predicate, reading the channel and direction off the
-- WalkStep's constructor tag:
--
-- - `.forwardE _` (encoding `(u, v) ∈ G.E`, running `u → v`):
--   arrowhead at the target index `v`.  `IsInto w := (w = v)`.
-- - `.backwardE _` (encoding `(v, u) ∈ G.E`, running `v → u`):
--   arrowhead at the source index `u` (the target of the underlying
--   directed edge).  `IsInto w := (w = u)`.
-- - `.bidir _` (encoding `s(u, v) ∈ G.L`, bidirected): arrowheads at
--   BOTH endpoints simultaneously.  `IsInto w := (w = u ∨ w = v)`.
--
-- Consumed by the WalkStep-reversal symmetry lemma
-- `s.reverse.IsInto w ↔ s.IsInto w` in `SigmaSeparationSymmetric.lean`,
-- which exploits the node-equality framing's index-symmetry to
-- discharge the reversal invariance in one rewrite.
--
-- ## Design choice — IsInto
--
-- *Why a Prop-level "arrowhead-at-node" predicate at the WalkStep
--   level.*  The LN block phrases the collider case as "there are two
--   arrowheads pointing towards $v_k$ on the walk $\pi$" (canonical
--   tex `def_3_15`, item~ii of the Classification paragraph: collider
--   iff `ah_π(k) = 2`, with `ah_π(k)` defined as the count of walk-
--   incident edges `a_{k-1}, a_k` that are edges into $v_k$).
--   `def_3_3` item~ii ("edge into a node") is the per-edge primitive
--   the LN itself uses to build the collider count, so `IsInto` is the
--   typed-WalkStep transcription of that exact primitive — a literal,
--   node-equality-keyed reading of "edge into a node" that downstream
--   symmetry lemmas rely on.  The actual collider classification
--   (`IsCollider` below) instead uses the side-aware predicates
--   `HeadAtTarget` / `HeadAtSource`, which commit to the recorded
--   traversal channel and disambiguate self-loops; the two readings
--   coincide off the corner kinds documented on `IsCollider`'s design
--   block.
--
-- *Writing-mirror union semantics on directed branches.*  The LN's
--   `into v_k a_i` predicate at a walk-incident edge `a_i = (e_1, e_2)`
--   is a *union* over the two channels read off a SINGLE stored
--   ordered pair: `into v_k a_i ↔ (a_i ∈ E ∧ e_2 = v_k) ∨ (a_i ∈ L ∧
--   (e_1 = v_k ∨ e_2 = v_k))` (canonical tex `def_3_15` spelling out
--   `def_3_3` item~ii).  In the typed-WalkStep encoding here, the stored
--   pair is split into three constructor channels — `.forwardE` and
--   `.backwardE` hold an `(u, v) ∈ G.E` (resp.\ `(v, u) ∈ G.E`)
--   witness, `.bidir` holds an `s(u, v) ∈ G.L` witness — but `def_3_1`
--   *does not* enforce `E ∩ L = ∅` (see the "No `E ∩ L = ∅` field, by
--   intent" design pillar in `CDMG.lean`: the same vertex pair
--   `{u, v}` may simultaneously support an L-edge `s(u, v) ∈ G.L` AND
--   a directed edge `(u, v) ∈ G.E` or `(v, u) ∈ G.E`).  Such a
--   "writing-mirror" pair admits TWO equally-valid encodings of the
--   same underlying walk position: the walker may legitimately store
--   the step as either `.forwardE h_E` (carrying the E-channel
--   witness) or `.bidir h_L` (carrying the L-channel witness), and the
--   LN's `into v_k a_i` classification — being a UNION over the
--   stored pair's two channels — does not depend on which constructor
--   was chosen.  A constructor-tag-only reading
--   (`.forwardE → only test the E-target side`) would *drop* the
--   L-channel disjunct in writing-mirror cases and make `IsInto`'s
--   classification depend on the walker's encoding choice, diverging
--   from the LN.  The extra disjunct
--   `s(u, v) ∈ G.L ∧ (w = u ∨ w = v)` on the `.forwardE` /
--   `.backwardE` branches re-injects the LN's L-clause whenever the
--   stored pair also lives in `G.L`, restoring constructor-choice
--   invariance.  Equivalently: on the (large) sub-population of
--   non-writing-mirror CDMGs (`s(u, v) ∉ G.L`), the new disjunct is
--   vacuously false and the predicate collapses to the previous
--   per-channel reading — only writing-mirror cases are touched.
--   `.bidir`'s branch is unchanged (it already encodes the union
--   semantics built-in: `IsInto w := w = u ∨ w = v`, the LN's
--   L-clause).  Wording-check subtlety
--   `self_loop_makes_tuh_and_hut_simultaneously_true` (the literal-LN
--   constructor-tag reading is ambiguous for self-loops; the count-
--   based reading is unambiguous) is preserved verbatim: at a directed
--   self-loop `(v, v) ∈ G.E`, the new disjunct `s(v, v) ∈ G.L` is
--   *vacuously false* by `def_3_1`'s `hL_irrefl` (which forbids
--   `s.IsDiag ∈ G.L`), so the self-loop branch reduces to the
--   node-equality test `w = v` on the type indices alone.  No
--   special-casing is needed for self-loops; the writing-mirror union
--   and the self-loop reading coexist by `hL_irrefl`.
--
-- *Why `.bidir` does NOT carry a symmetric "writing-mirror E-disjunct".*
--   A reader noticing the writing-mirror union disjunct on
--   `.forwardE` / `.backwardE` might expect a symmetric disjunct on
--   `.bidir` of the form
--   `((u, v) ∈ G.E ∨ (v, u) ∈ G.E) ∧ (w = v ∨ w = u)` — "if the stored
--   `Sym2 Node` pair `s(u, v)` *also* lives in `G.E` under some
--   orientation, fall back to the E-channel reading at the directed-
--   edge's target".  This disjunct is unnecessary, and structurally
--   so.  The `.bidir` constructor carries *only* an `s(u, v) ∈ G.L`
--   witness — by `def_3_1`'s typing, it intentionally does NOT carry
--   any `(u, v) ∈ G.E` or `(v, u) ∈ G.E` witness — and the L-channel
--   reading `w = u ∨ w = v` already places an arrowhead at *both*
--   endpoints simultaneously.  Any conceivable E-channel disjunct
--   could at most add an arrowhead at one specific endpoint (the
--   target of the underlying directed edge), which is a *strict
--   sub-condition* of the L-clause's "arrowhead at both endpoints":
--   the L-reading already DOMINATES anything an E-disjunct could
--   contribute, so adding one would be vacuous on top of the existing
--   OR-clause (`P ∨ Q ↔ P` whenever `Q → P`).  This is the
--   structural-symmetry payoff of `def_3_1`'s `Sym2` encoding for
--   `G.L`: an L-edge is orientation-free, hence its arrowhead pattern
--   is maximally inclusive at both endpoints, and the writing-mirror
--   union semantics collapses on `.bidir` to the existing two-
--   disjunct.  Equivalently — and this is the constructor-choice-
--   invariance argument from the previous bullet read in reverse — at
--   a writing-mirror pair `s(u, v) ∈ G.L ∧ (u, v) ∈ G.E`, the walker
--   may encode a given walk step as either `.forwardE h_E` or
--   `.bidir h_L`; on the `.bidir` encoding, the L-clause already
--   fires arrowheads at both endpoints, so the E-channel information
--   is redundant at the constructor index and the writing-mirror
--   union is automatic.  This is what makes the
--   `.forwardE` / `.backwardE` writing-mirror disjuncts and the
--   `.bidir` no-extra-disjunct shape *jointly* constructor-choice-
--   invariant in the strict sense the verifier checks: a single LN
--   walk position evaluates `IsInto v_k` to the same Boolean under
--   every legal typifying encoding.
--
-- *Why test by node-equality (`w = u` / `w = v`) rather than by
--   constructor-tag "source vs target" labels.*  This is the load-
--   bearing semantic decision of the helper.  A naive constructor-tag
--   reading — "a `.forwardE` puts the arrowhead at the target side,
--   not the source side" — loses information at directed self-loops,
--   where the WalkStep's source and target type indices are *the same
--   node*.  Concretely: at a self-loop `(v, v) ∈ G.E` encoded as
--   `.forwardE _ : WalkStep G v v`, the source-vs-target
--   reading would label this as "arrowhead at v but not at v" — a
--   semantically empty statement that cannot distinguish "arrowhead at
--   the loop vertex" from "no arrowhead at the loop vertex".  The
--   node-equality test resolves this cleanly: `IsInto v` evaluates to
--   `(v = v) = True` for `.forwardE _ : WalkStep G v v`, matching the
--   literal `G.into v (v, v) = True` reading (via the E-clause's
--   `e.2 = v` condition).  Wording-check subtlety
--   `self_loop_makes_tuh_and_hut_simultaneously_true` flagged exactly
--   this corner: the literal-LN constructor-tag reading
--   (`v ⟵ v ⟶ v_{k+1}` vs. `v ⟶ v ⟶ v_{k+1}`) is ambiguous for
--   self-loops, but the count-based reading the canonical tex commits
--   to (preserved here via node-equality) is unambiguous and matches
--   the `G.into`-based semantics of `def_3_3` item~ii.
--
-- *Why a `Prop` predicate, not a `Bool` decidable.*  Walks live at
--   `Type _`, their per-position classification at `Prop`.  A `Bool`
--   form would require a `DecidableEq Node` discharge at every
--   elaboration site — possible in principle (we already have
--   `[DecidableEq Node]` from the section-wide variable), but adds
--   infrastructure with no payoff for the predicate's role as a
--   `Prop`-valued primitive consumed by symmetry lemmas downstream.
--
-- *Why the explicit `w : Node` argument, not curried via the
--   WalkStep's source/target indices.*  Keeping the queried node
--   separate from the WalkStep's type indices makes the helper
--   position-independent: any WalkStep can be queried "is your
--   arrowhead at `w`?" without the caller having to remember whether
--   `w` is the source or target index.  This is the shape downstream
--   symmetry lemmas exploit — `s.reverse.IsInto w ↔ s.IsInto w`
--   discharges in one rewrite precisely because the `w` argument is
--   index-symmetric across constructors.
--
-- *Why the pattern binds `u` / `v` from the implicit binders rather
--   than using `_`.*  The body references the WalkStep's type indices
--   (`v` for `.forwardE`; `u` for `.backwardE`; both for `.bidir`),
--   so the implicit binders must be brought into scope on the
--   corresponding branches.  Pattern positions 1 and 2 of the
--   `∀ {u v : Node}, ...` signature are the implicit binders; binding
--   them explicitly as `u, v` (or `_` where unused) is the standard
--   shape used by every existing pattern-match-on-implicits def in
--   `Walks.lean` (e.g.\ `vertices`, `IsBidirectedWalk`,
--   `intoStart`-via-`outOf` original).
-- def_3_15 --- start helper
def IsInto : ∀ {u v : Node}, WalkStep G u v → Node → Prop
  | u, v, .forwardE _,  w => w = v ∨ (s(u, v) ∈ G.L ∧ (w = u ∨ w = v))
  | u, v, .backwardE _, w => w = u ∨ (s(u, v) ∈ G.L ∧ (w = u ∨ w = v))
  | u, v, .bidir _,     w => w = u ∨ w = v
-- def_3_15 --- end helper

-- ref: def_3_15 (helper, side-aware "head at walk-traversal target")
--
-- `s.HeadAtTarget` iff the typed WalkStep
-- `s : WalkStep G u v` places an arrowhead at its walk-traversal target
-- end `v` (per the canonical-tex addition tag
-- `[collider_side_aware_walkstep_predicates]`, clause~(b)):
--
-- - `.forwardE _` encodes `(u, v) ∈ G.E`; the directed edge runs
--   `u → v`, so the walk-traversal target `v` is the arrowhead-
--   receiving end.  ↦ `True`.
-- - `.backwardE _` encodes `(v, u) ∈ G.E`; the directed edge runs
--   `v → u`, so the walk-traversal target `v` is the *tail* end of
--   the directed step — no arrowhead at `v`.  The side-aware reading
--   commits to the walk-step's recorded traversal channel as the
--   SOLE signal for arrowhead-presence; there is NO opposite-channel
--   L-disjunct on this branch, even when a coexisting
--   `s(u, v) ∈ G.L` would, under the literal stored-pair test,
--   contribute an arrowhead at `v` (writing-mirror case, addressed
--   in the design block below).  ↦ `False`.
-- - `.bidir _` encodes `s(u, v) ∈ G.L`; arrowheads at both endpoints
--   by the bidirected semantics.  ↦ `True`.
--
-- ## Design choice — HeadAtTarget
--
-- *Pure constructor-tag pattern, no `w : Node` argument, no opposite-
--   channel disjunct.*  The walk-step's typed source `u` and target
--   `v` already carry the "side" information at the type level, and
--   the body is a pure True / False pattern keyed off the constructor
--   tag alone: no node-equality test, no L-membership disjunct
--   anywhere.  This is the load-bearing design move: per clause~(b)
--   of the canonical-tex addition
--   `[collider_side_aware_walkstep_predicates]`, the per-step
--   contribution of `a_i` to `ah_π(k)` at each adjacent position is
--   determined SOLELY by the recorded traversal channel `c_i`,
--   "never consulting whether the underlying stored pair also sits
--   in the opposite channel of `G`".  A directed step (`.forwardE`
--   or `.backwardE`) commits to its E-side traversal even when a
--   coexisting `s(u, v) ∈ G.L` is present in `G`; symmetrically,
--   `.bidir` commits to the L-side bidirected reading even when a
--   coexisting E-edge is present.  The canonical tex states this
--   explicitly: "There is *no* additional opposite-channel
--   $L$-disjunct on the directed branches and *no* additional
--   $E$-disjunct on the bidirected branch -- the constructor tag
--   alone carries the side-aware commitment, exactly realising the
--   per-step contribution formula above."
--
-- *Strict deviation from the literal stored-pair test at two corner
--   kinds.*  Per clause~(c) of the canonical-tex addition, the
--   side-aware reading strictly deviates from the literal
--   `def-edge-relations` item~ii test at two corner configurations
--   admitted by `def_3_1`:
--   - **directed self-loop walk-steps** (`a_i ∈ G.E` with
--     `v_i = v_{i+1}`, no coexisting L-edge): the literal test fires
--     `e.2 = v` at both adjacent positions unconditionally
--     (contributing `1 + 1 = 2`); the side-aware reading commits via
--     the constructor tag to a single position (the walk-traversal
--     target) for the contribution, contributing `1` there and `0`
--     at the other adjacent position.  The L-channel cannot fire
--     here because `def_3_1`'s `hL_irrefl` rules out
--     `s(v, v) ∈ G.L` outright (so the writing-mirror self-loop
--     sibling `(v, v) ∈ G.E` AND `s(v, v) ∈ G.L` simultaneously is
--     structurally impossible).  This is the manager-accepted
--     deviation `collider_side_aware_at_self_loops` in
--     `leanification/deviations.json`.
--   - **writing-mirror walk-steps traversed via the E-channel**
--     (`(v_i, v_{i+1}) ∈ G.E` AND `s(v_i, v_{i+1}) ∈ G.L`, with
--     `v_i ≠ v_{i+1}`, encoded as `.forwardE` / `.backwardE`):
--     `def_3_1` does not impose `E ∩ L = ∅` (see `CDMG.lean`'s
--     "No `E ∩ L = ∅` field, by intent" design pillar), so the same
--     vertex pair may simultaneously support a directed edge and a
--     bidirected edge.  The literal stored-pair test's L-disjunct
--     fires at both adjacent positions regardless of which channel
--     the walk-step actually traverses; the side-aware reading
--     ignores the coexisting L-edge entirely when the recorded
--     traversal channel is `.forwardE` / `.backwardE`, contributing
--     only at the walk-traversal target of the directed channel.
--
-- *Scope of coincidence with the literal stored-pair test.*  The
--   side-aware contribution formula coincides pointwise with the
--   literal `def-edge-relations` item~ii test only on walks that
--   traverse NEITHER a directed self-loop step NOR a writing-mirror
--   walk-step via the E-channel.  A writing-mirror walk-step
--   traversed via the L-channel (`.bidir _`) agrees with the literal
--   test pointwise: the literal test's L-clause already fires
--   arrowheads at both endpoints, matching `.bidir`'s `↦ True` on
--   both sides.
--
-- Paired with `HeadAtSource`, the two zero-arg predicates
-- realise the addition's clause-(b) per-step contribution formula
-- exactly: forward `E`-step head at target only; backward `E`-step
-- head at source only; bidirected `L`-step head at both adjacent
-- positions.  See `tex/def_3_15_CollidersAndNon.tex`, the "Encoding
-- note: side-aware reading via a typed walk-step representation" and
-- "Treatment of directed self-loops and writing-mirror walk-steps"
-- paragraphs for the full canonical spec.
-- def_3_15 --- start helper
def HeadAtTarget : ∀ {u v : Node}, WalkStep G u v → Prop
  | _, _, .forwardE _  => True
  | _, _, .backwardE _ => False
  | _, _, .bidir _     => True
-- def_3_15 --- end helper

-- ref: def_3_15 (helper, side-aware "head at walk-traversal source")
--
-- `s.HeadAtSource` iff the typed WalkStep
-- `s : WalkStep G u v` places an arrowhead at its walk-traversal source
-- end `u` (per the canonical-tex addition tag
-- `[collider_side_aware_walkstep_predicates]`, clause~(b)):
--
-- - `.forwardE _` encodes `(u, v) ∈ G.E`; the directed edge runs
--   `u → v`, so the walk-traversal source `u` is the *tail* end of
--   the directed step — no arrowhead at `u`.  The side-aware reading
--   commits to the walk-step's recorded traversal channel as the
--   SOLE signal for arrowhead-presence; there is NO opposite-channel
--   L-disjunct on this branch, even when a coexisting
--   `s(u, v) ∈ G.L` would, under the literal stored-pair test,
--   contribute an arrowhead at `u` (writing-mirror case).
--   ↦ `False`.
-- - `.backwardE _` encodes `(v, u) ∈ G.E`; the directed edge runs
--   `v → u`, so the walk-traversal source `u` is the arrowhead-
--   receiving end.  ↦ `True`.
-- - `.bidir _` encodes `s(u, v) ∈ G.L`; arrowheads at both endpoints
--   by the bidirected semantics.  ↦ `True`.
--
-- The mirror of `HeadAtTarget`, asking the same per-step
-- arrowhead-contribution question on the walk-traversal *source*
-- side.  Same pure constructor-tag pattern: no node-equality test
-- and no opposite-channel L-disjunct anywhere in the body.  A
-- directed step commits to its E-side traversal even at a writing-
-- mirror pair, ignoring the coexisting `G.L` edge entirely (the
-- side-aware reading is the canonical disambiguation per clause~(c)
-- of the addition `[collider_side_aware_walkstep_predicates]`).
-- See the design block on `HeadAtTarget` above for the
-- full justification, in particular: the two corner kinds where the
-- side-aware reading strictly deviates from the literal stored-pair
-- test (directed self-loops AND writing-mirror walk-steps traversed
-- via the E-channel); the role of `def_3_1`'s `hL_irrefl` in ruling
-- out the writing-mirror self-loop sibling structurally; and the
-- scope of coincidence with the literal `def-edge-relations` item~ii
-- test (walks avoiding both corner kinds).  At a directed self-loop
-- step encoded as `.forwardE _ : WalkStep G v v`, the source-side
-- predicate at the loop vertex reads `False` — the manager-accepted
-- deviation `collider_side_aware_at_self_loops` is preserved
-- verbatim by the constructor-tag-only body.
-- def_3_15 --- start helper
def HeadAtSource : ∀ {u v : Node}, WalkStep G u v → Prop
  | _, _, .forwardE _  => False
  | _, _, .backwardE _ => True
  | _, _, .bidir _     => True
-- def_3_15 --- end helper

end WalkStep

namespace Walk

-- ## Design choice — Walk-namespace statement context
--
-- *Why a namespace-level `variable {G : CDMG Node}`.*  Both
--   `IsCollider` and `IsNonCollider` recurse over /
--   take a walk `p : Walk G u v`.  Without the namespace-wide
--   `variable`, every signature would carry an explicit
--   `{G : CDMG Node}` binder; the auto-binding keeps the
--   signatures readable and matches the LN's "Let $G = (J, V, E, L)$ be
--   a CDMG" once-at-the-top quantifier.  `{G}` is implicit because
--   downstream consumers reach into `G` via dot-notation on the walk
--   (`p.IsCollider k` rather than `Walk.IsCollider G p k`).
--
-- *Three-dash helper marker, not two-dash statement marker.*  Same
--   rationale as the `WalkStep` namespace `variable` block above and
--   as the section-wide `variable` near the top of the file: this
--   `{G}` binder is load-bearing infrastructure that the tex/Lean
--   reconciliation tooling must recognise as helper-flavour.
-- def_3_15 --- start helper
variable {G : CDMG Node}
-- def_3_15 --- end helper


-- ref: def_3_15 (item ii, collider)
--
-- `p.IsCollider k` iff position `k` on the walk `p` has
-- arrowhead count `ah_π(k) = 2` under the *side-aware* per-step
-- arrowhead-contribution reading.  Both walk-incident steps `s_{k-1}`
-- and `s_k` exist (forcing `1 ≤ k ≤ p.length - 1`, an interior
-- position) and:
--   - `s_{k-1} : WalkStep G _ v_k` has its walk-traversal *target* at
--     `v_k`, so it contributes an arrowhead at `v_k` iff
--     `s_{k-1}.HeadAtTarget`;
--   - `s_k : WalkStep G v_k _` has its walk-traversal *source* at
--     `v_k`, so it contributes an arrowhead at `v_k` iff
--     `s_k.HeadAtSource`.
-- The clause-1 body is therefore
-- `s₀.HeadAtTarget ∧ s₁.HeadAtSource` — no `v_k`
-- node binder is needed, because the typed `WalkStep` indices already
-- pin which end of each step is at `v_k`.
--
-- ## Design choice — IsCollider
--
-- *Why side-aware semantics rather than node-equality on `IsInto`.*
--   A node-equality reading `s₀.IsInto vk ∧ s₁.IsInto vk` collapses on
--   directed self-loops: a `.forwardE _ : WalkStep G b b` step has
--   `u = v = b`, so the `IsInto` test cannot distinguish "arrowhead at
--   `b` on the source side" from "arrowhead at `b` on the target side"
--   — both disjuncts of `IsInto`'s `.forwardE` branch (`w = v`,
--   `s(u, v) ∈ G.L ∧ …`) reduce to the single condition `w = b`.
--   Consequence: a position-1 walk `a → b → b` (with a directed
--   self-loop at `b` as the second step) would be spuriously classified
--   as a collider at `b`, even though the self-loop's source side at
--   `b` is a tail (no arrowhead), not a head.  The side-aware
--   predicates `HeadAtTarget` / `HeadAtSource` disambiguate via the
--   WalkStep's constructor tag alone (no node-equality test), making
--   the self-loop's source-side contribution unambiguously `False` for
--   `.forwardE` and `True` only for `.backwardE` / `.bidir`.
--
-- *Intended deviation at two corner kinds; restricted agreement
--   elsewhere.*  The side-aware reading is a strict refinement of the
--   literal stored-pair (`def-edge-relations` item~ii) test at two
--   corner configurations admitted by `def_3_1` but ambiguously
--   handled by the LN's pattern-macro writing.  Per clause~(c) of the
--   canonical-tex addition `[collider_side_aware_walkstep_predicates]`,
--   the two readings strictly diverge at:
--   - **directed self-loop walk-steps** (`a_i ∈ G.E` with
--     `v_i = v_{i+1}`, no coexisting L-edge): the literal test fires
--     `e.2 = v` at both adjacent positions unconditionally (the
--     literal-LN ambiguity flagged by wording-check subtlety
--     `self_loop_makes_tuh_and_hut_simultaneously_true`), whereas
--     the side-aware reading places the arrowhead on the walk-
--     traversal target side only -- the side recorded by the
--     `.forwardE` / `.backwardE` constructor tag.  The L-channel
--     cannot fire at a self-loop because `def_3_1`'s `hL_irrefl`
--     rules out `s(v, v) ∈ G.L` outright (so the writing-mirror
--     self-loop sibling `(v, v) ∈ G.E` AND `s(v, v) ∈ G.L` is
--     structurally impossible), so the strict refinement at self-
--     loops is preserved by construction (this is the manager-
--     accepted deviation `collider_side_aware_at_self_loops`).
--   - **writing-mirror walk-steps traversed via the E-channel**
--     (`(v_i, v_{i+1}) ∈ G.E` AND `s(v_i, v_{i+1}) ∈ G.L`, with
--     `v_i ≠ v_{i+1}`, encoded as `.forwardE` / `.backwardE`):
--     `def_3_1` does not impose `E ∩ L = ∅` (see `CDMG.lean`'s
--     "No `E ∩ L = ∅` field, by intent" design pillar), so the
--     same vertex pair may simultaneously support a directed edge
--     in `G.E` and a bidirected edge in `G.L`.  The literal
--     stored-pair test's L-disjunct fires at both adjacent
--     positions regardless of which channel the walk-step actually
--     traverses; the side-aware predicates
--     `HeadAtTarget` / `HeadAtSource` ignore the
--     coexisting L-edge entirely when the recorded traversal
--     channel is `.forwardE` / `.backwardE` (their bodies have NO
--     opposite-channel L-disjunct anywhere), contributing only at
--     the walk-traversal target of the directed channel.  Clause~(c)
--     of the addition explicitly extends the strict deviation to
--     this corner: "the strict deviation from the literal stored-
--     pair test is preserved at writing-mirror walk-steps traversed
--     via the E-channel as well as at directed self-loops".
--   The two readings coincide pointwise only on walks that avoid
--   BOTH a directed self-loop step AND a writing-mirror walk-step
--   traversed via the E-channel; a writing-mirror walk-step
--   traversed via the L-channel (`.bidir _`) agrees with the
--   literal test pointwise (the L-clause of the literal test
--   already fires arrowheads at both endpoints, matching `.bidir`'s
--   `↦ True` on both sides).  Both deviations are the *intended*
--   canonical disambiguation per the addition tag
--   `[collider_side_aware_walkstep_predicates]` (see
--   `tex/def_3_15_CollidersAndNon.tex`, "Treatment of directed
--   self-loops and writing-mirror walk-steps"), not accidental
--   divergences: the LN's `ah_π(k) = 2` count is itself ambiguous
--   at both corner kinds, so the encoding must commit to one of
--   the admissible counts, and the side-aware reading is the one
--   the canonical tex pins as taking precedence over the literal
--   stored-pair test.  As a concrete consequence: a position-1 walk
--   `a → b → b` (with a directed self-loop at `b` as the second
--   step) is *not* a collider at `b` under the side-aware reading,
--   because the self-loop's source side at `b` carries a tail, not
--   a head.
--
-- *No node-binder `vk` at the clause-1 pattern.*  Side information is
--   carried at the type level by the WalkStep's indices
--   (`s₀ : WalkStep G _ vk`, `s₁ : WalkStep G vk _`), so the middle
--   vertex's identity is not consulted at the runtime level — the
--   predicate reads off the constructor tag of each step alone.
--   The cons-cell's middle-vertex slot is therefore a wildcard `_`.
--
-- *Recursive pattern-match shape and end-position handling.*  The
--   five clauses encode the LN's "every position `k ∈ {0, …, n}`"
--   scope via structural case-analysis on the `Walk` cons-cell and
--   the `ℕ` index together.  `nil _ _` (trivial walk, `n = 0`) and
--   `cons _ _ (nil _ _)` (length-1 walk, `n = 1`) have no interior
--   position, so every `k` falls through to `False` — end-positions
--   are non-colliders by the LN's convention.  At a cons-cons head
--   `cons _ s₀ (cons _ s₁ _)`, position `0` is the walk's start
--   (end-position, `False`) and position `1` is the unique interior
--   position adjacent to the head pair — the slot where
--   `s₀.HeadAtTarget ∧ s₁.HeadAtSource` lives, the
--   side-aware encoding of the LN's `ah_π(1) = 2` condition.  Higher
--   positions `k + 2` recurse one cons-cell deep with index shift
--   `k + 2 → k + 1`, matching the LN's walk-tail re-indexing of
--   positions.  Pattern-match exhaustiveness on `Walk × ℕ` means
--   out-of-range positions (`k > p.length`) fall through to `False`
--   automatically without an explicit `1 ≤ k ≤ p.length - 1` bound
--   check — the structural shape encodes the LN's `n ≥ 2` lower
--   bound on the walk length for a collider position to even be
--   admissible.
-- def_3_15 -- start statement
def IsCollider : ∀ {u v : Node}, Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ _ (.nil _ _), _ => False
  | _, _, .cons _ _ (.cons _ _ _), 0 => False
  | _, _, .cons _ s₀ (.cons _ s₁ _), 1 =>
      s₀.HeadAtTarget ∧ s₁.HeadAtSource
  | _, _, .cons _ _ (p@(.cons _ _ _)), k + 2 =>
      p.IsCollider (k + 1)
-- def_3_15 -- end statement


-- ref: def_3_15 (item i, non-collider)
--
-- `p.IsNonCollider k` iff position `k` on the walk `p` is in
-- range (`k ≤ p.length`) and is *not* a `IsCollider`, i.e.\
-- has side-aware arrowhead count `ah_π(k) ≤ 1` under the canonical
-- side-aware reading committed to by the addition tag
-- `[collider_side_aware_walkstep_predicates]`.
--
-- ## Design choice — IsNonCollider
--
-- *De Morgan dual of `IsCollider` — partition must hold.*
--   The LN's "every position on `π` is exactly one of a non-collider
--   or a collider on `π`" mutual-exclusivity / joint-exhaustiveness
--   property (canonical tex `def_3_15`, "Classification" paragraph)
--   requires that the collider / non-collider predicate pair partition
--   the in-range index set `{0, 1, …, p.length}` exactly.  The
--   non-collider predicate is the de Morgan negation of the collider
--   predicate, restricted to the in-range fragment.
-- def_3_15 -- start statement
def IsNonCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  k ≤ p.length ∧ ¬ p.IsCollider k
-- def_3_15 -- end statement

end Walk

end CDMG

end Causality
