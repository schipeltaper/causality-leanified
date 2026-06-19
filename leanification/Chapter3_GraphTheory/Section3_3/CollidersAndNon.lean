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
   helper `ahCount`, which would need a `Decidable (G.into v e)`
   instance for the `if-then-else` reduction.  Mathematically the
   count lives in `{0, 1, 2}` (canonical tex, paragraph "Arrowhead
   count at a position"), so `ah_π(k) ≤ 1 ↔ ¬ (ah_π(k) = 2)` — the
   negation form is semantically equivalent to the LN's "at most
   one arrowhead" reading.

3. **Self-loop tie-breaking convention.**  A directed self-loop
   `a = (v, v) ∈ G.E` is "an edge into `v`" per `def_3_3` item~ii
   (the `E`-clause's `e.2 = v` fires with `e.2 = v = v`), so it
   contributes `1` (not `2`) to the count when the walk traverses
   it at a position where `v_k = v`.  This is the resolution the
   canonical tex commits to in its "Treatment of directed
   self-loops" paragraph, and matches `EdgeRelations.lean`'s
   `into` semantics: the count is over **walk-incident edges**, and
   each walk-edge contributes at most `1`.  The literal LN
   pattern-matching writings (`\tuh / \hut / \huh`) would otherwise
   ambiguously classify a position adjacent to a self-loop as both
   collider and non-collider; the count-based reading is
   unambiguous and is what `IsCollider` / `IsNonCollider` encode.

4. **`G.into` reused from `def_3_3` (`EdgeRelations.lean`).**  The
   canonical tex spells out "edge into `v_k`" by reference to
   `def_3_3` item~ii, and `CDMG.into` already encodes that exact
   set-theoretic predicate.  Re-inlining the two-clause disjunction
   here would duplicate `into`'s body and break the LN-macro-grep
   correspondence.

The substantive per-declaration design rationale lives in the
comment block immediately above each `-- def_3_15 -- start statement`
marker.
-/

namespace CDMG

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Matches
--   the chapter convention set by `CDMG.lean`, `CDMGNotation.lean`,
--   `EdgeRelations.lean`, `Walks.lean`.  Fixing `Node` to a concrete
--   carrier (`Fin n`, `ℕ`) here would force renumbering at every
--   downstream operation that rewrites the vertex set.
--
-- *Three-dash `--- start helper` / `--- end helper`, not two-dash
--   `-- start statement`.*  Lean 4's `variable` auto-binding folds
--   these implicit binders into every declaration below — they are
--   load-bearing infrastructure, not throwaway local sugar.  Matches
--   the wrapping used by every prior file in this chapter
--   (`CDMGNotation.lean`, `EdgeRelations.lean`, `Walks.lean`).
-- def_3_15 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_15 --- end helper

namespace Walk

-- ## Design choice — Walk-namespace statement context
--
-- *Namespace-level `variable {G : CDMG Node}`.*  Both `IsCollider`
--   and `IsNonCollider` take (or recurse over) a walk `p : Walk G u
--   v`.  Without the namespace-wide `variable`, every signature
--   would carry an explicit `{G : CDMG Node}` binder; the
--   auto-binding keeps the signatures readable and matches the LN's
--   "Let $G = (J, V, E, L)$ be a CDMG" once-at-the-top quantifier.
--   `{G}` is implicit because downstream consumers reach into `G`
--   via dot-notation on the walk (`p.IsCollider k` rather than
--   `Walk.IsCollider G p k`).
-- def_3_15 --- start helper
variable {G : CDMG Node}
-- def_3_15 --- end helper

-- ref: def_3_15 (item ii, collider)
--
-- `p.IsCollider k` iff position `k` on the walk `p` has arrowhead
-- count `ah_π(k) = 2`, i.e.\ both walk-incident edges `a_{k - 1}`
-- and `a_k` exist (forcing `1 ≤ k ≤ p.length - 1`, an interior
-- position) and both are edges into the vertex `v_k =
-- p.vertices[k]` in the sense of `def_3_3` item~ii (`G.into vk a`).
--
-- ## Design choice
--
-- *Direct existential characterisation, no `ahCount` helper.*  The
--   canonical tex defines `ah_π(k)` as a named cardinality and then
--   classifies positions by `ah_π(k) = 2` (collider) vs
--   `ah_π(k) ≤ 1` (non-collider).  In Lean, a ℕ-valued count via
--   `if G.into vk a then 1 else 0` would require a
--   `Decidable (G.into v e)` instance — extra infrastructure for no
--   semantic gain, since `ah_π(k) ∈ {0, 1, 2}` lets us classify
--   directly by "both edges into `v_k`" (collider) vs "at most one
--   edge into `v_k`" (non-collider).  Three signals checked: (a)
--   `ah_π(k)` is genuinely referenced — yes; (b) substantive
--   content — yes; (c) downstream consumers will name it — no,
--   `def_3_16`–`def_3_17` consume "collider" / "non-collider" by
--   name, not the count.  Litmus fails on (c); no count helper.
--
-- *Naming distinct from `Walk.IsColliderWalk` (`def_3_4` item~iv).*
--   The chapter already defines `Walk.IsColliderWalk` as the
--   *whole-walk* shape predicate (every interior position is a
--   collider, plus endpoint constraints fixed by the LN's symbolic
--   pattern, plus a bidirected-edge constraint at `n = 1`).  The
--   present `Walk.IsCollider` is the *single-position* predicate at
--   index `k`.  They are not interchangeable: even on the in-range
--   interior fragment `1 ≤ k ≤ p.length - 1`, the conjunction
--   `∀ k, 1 ≤ k → k < p.length → p.IsCollider k` is strictly
--   weaker than `p.IsColliderWalk` — the latter additionally
--   constrains the endpoints (`a_0` places an arrowhead at `v_1`,
--   `a_{n-1}` places an arrowhead at `v_{n-1}`) and treats `n = 1`
--   via a bidirected-edge constraint (see the `IsColliderWalk`
--   block in `Walks.lean`), neither of which appears in the
--   pointwise version.  The names intentionally diverge —
--   `IsColliderWalk` for the walk-level property, `IsCollider` for
--   the position-level one — so that pointwise consumers
--   downstream (`def_3_16` blockable / unblockable, `def_3_17`
--   $\sigma$-blocked walks) do not tacitly inherit
--   `IsColliderWalk`'s endpoint or `n = 1` constraints.  A reader
--   tempted to read `IsCollider` as sugar for `IsColliderWalk` (or
--   vice versa) will misclassify exactly those walks where the
--   distinction matters.
--
-- *`1 ≤ k` guard.*  Required because Lean's ℕ subtraction is
--   truncated: for `k = 0`, `k - 1 = 0`, so without the guard the
--   predicate would mistakenly inspect `p.edges[0]?` for the "left"
--   slot.  The LN's index set `{i ∈ {k - 1, k} : 0 ≤ i ≤ n - 1}`
--   excludes the `i = -1` slot at `k = 0`; the `1 ≤ k` guard is the
--   exact encoding of that exclusion.
--
-- *`p.vertices[k]? = some vk` (Option-membership) rather than
--   `k ≤ p.length`.*  Both characterise in-range positions, but the
--   Option-membership reads `v_k` out as a witness in the same
--   step, which the body needs to evaluate `G.into vk a₁` and
--   `G.into vk a₂`.  The bound check `k ≤ p.length` is implicit
--   (`p.vertices` has length `p.length + 1`, so the lookup returns
--   `some` exactly when the position is in range).
--
-- *End-positions never satisfy `IsCollider`.*  At `k = 0` the `1 ≤
--   k` guard fails.  At `k = p.length` the lookup `p.edges[k]? =
--   none` (since `p.edges` has length `p.length`), so the `a₂`
--   witness does not exist.  Either way `IsCollider` is `False`,
--   matching the LN's "end-positions are non-colliders by
--   construction".  Trivial walks (`n = 0`, `p.length = 0`) have
--   only the single position `k = 0 = p.length`, which is therefore
--   never a collider.
--
-- *Self-loops contribute `1`, not `2`, by the `G.into`-semantics.*
--   A walk-incident self-loop `a = (v, v) ∈ G.E` is **one** walk-
--   edge, and `G.into v (v, v)` holds via the `E`-clause's
--   `e.2 = v` condition — a single contribution to the count, not
--   two.  The canonical tex's "Treatment of directed self-loops"
--   paragraph commits to this resolution; the literal LN
--   pattern-match writings (`\tuh / \hut / \huh / \suh / \hus`)
--   would otherwise classify the same position as both collider
--   and non-collider for any walk that traverses a self-loop.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsCollider
-- def_3_15 -- start statement
def IsCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ (vk : Node) (a₁ a₂ : Node × Node),
    p.vertices[k]? = some vk ∧
    p.edges[k - 1]? = some a₁ ∧
    p.edges[k]? = some a₂ ∧
    G.into vk a₁ ∧
    G.into vk a₂
-- def_3_15 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsCollider

-- ref: def_3_15 (item i, non-collider)
--
-- `p.IsNonCollider k` iff position `k` on the walk `p` is in range
-- (`k ≤ p.length`) and has arrowhead count `ah_π(k) ≤ 1`,
-- equivalently `¬ p.IsCollider k`.  This makes the LN's mutual
-- exclusivity ("every position on `π` is exactly one of collider /
-- non-collider on `π`") definitional on the in-range fragment
-- `{0, …, p.length}`.
--
-- ## Design choice
--
-- *Encoded as `k ≤ p.length ∧ ¬ p.IsCollider k`.*  Since
--   `ah_π(k) ∈ {0, 1, 2}` (canonical tex paragraph "Arrowhead count
--   at a position"), `ah_π(k) ≤ 1 ↔ ah_π(k) ≠ 2 ↔ ¬ IsCollider`.
--   The `k ≤ p.length` bound enforces the LN's "position `k ∈ {0,
--   …, n}`" scope; without it, out-of-range positions
--   `k > p.length` would vacuously satisfy `¬ IsCollider` (since
--   `IsCollider` is `False` out of range) and be misclassified as
--   non-colliders, which the LN does not intend.
--
-- *Asymmetric encoding: positive existential for `IsCollider`,
--   negation-with-bound for `IsNonCollider`.*  `IsCollider` carries
--   its in-range condition implicitly through the Option-membership
--   conjuncts (`p.vertices[k]? = some _ ∧ p.edges[k - 1]? = some _
--   ∧ p.edges[k]? = some _`), which fire only at interior positions
--   `1 ≤ k ≤ p.length - 1`.  `IsNonCollider`, by contrast, has to
--   carry `k ≤ p.length` *explicitly* because `¬ p.IsCollider k` is
--   vacuously satisfied out of range and the Option-membership
--   trick is not available on the negation side.  The asymmetry is
--   the cost of using negation rather than a second positive
--   existential; the benefit is that mutual exclusivity on the
--   in-range fragment is *definitional* — one side is literally the
--   negation of the other, so for `k ≤ p.length` the statement
--   `p.IsNonCollider k ↔ ¬ p.IsCollider k` reduces by unfolding,
--   not by an external theorem.  Had we encoded both predicates
--   independently via a shared counting helper `ahCount p k : ℕ`,
--   we would owe a separate proof that
--   `ahCount p k ≤ 1 ↔ ¬ (ahCount p k = 2)` (true but not by
--   reduction) and would need a `Decidable (G.into v e)` instance
--   to define `ahCount` in the first place.
--
-- *End-positions are non-colliders automatically.*  Both `k = 0`
--   (`0 ≤ p.length` always holds) and `k = p.length` satisfy the
--   in-range bound, and both fail `IsCollider` (the `1 ≤ k` guard
--   for `k = 0`, the missing edge `p.edges[k]? = none` for
--   `k = p.length`), so `IsNonCollider` is `True` at both
--   end-positions.  This captures the LN's "end-node" pattern-case
--   definitionally.
--
-- *Why not a positive enumeration of the four LN pattern-cases
--   (end-node, left chain, right chain, fork).*  The canonical tex
--   takes the count-based classification as canonical, with the
--   four visual writings as a downstream "reconciliation".
--   Encoding the four pattern-cases directly would duplicate the
--   count logic and re-introduce the LN's literal visual-overlap
--   ambiguity at directed self-loops (which the canonical tex
--   explicitly resolves via the count semantics — see `IsCollider`
--   above).
--
-- *Why `Prop`, not `Bool` / decidable predicate.*  Walks live at
--   `Type _`, their classification at `Prop`.  A `Bool` form would
--   require deciding `G.into v e` at every elaboration site —
--   possible in principle but adds infrastructure with no payoff.
--   Downstream rows (`def_3_16` BlockableAndUnblockable,
--   `def_3_17` SigmaBlockedWalks) consume `IsNonCollider` as a
--   hypothesis-style `Prop` predicate; matching that shape keeps
--   the type-contract clean.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsNonCollider
-- def_3_15 -- start statement
def IsNonCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  k ≤ p.length ∧ ¬ p.IsCollider k
-- def_3_15 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsNonCollider

end Walk

end CDMG

end Causality

namespace Causality

namespace refactor_CDMG

-- ## Design choice — refactor section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same chapter
--   convention used by the original `CDMG` namespace above and by every
--   other `refactor_CDMG`-opening file in the chapter
--   (`Walks.lean:1201-1203`, `CDMG.lean`, `CDMGNotation.lean`,
--   `EdgeRelations.lean`).  The refactor does not alter the carrier-type
--   discipline — only (a) `def_3_1`'s `L`-field shape (`Finset (Sym2 Node)`
--   with `hL_irrefl : ∀ ⦃s⦄, s ∈ L → ¬ s.IsDiag`) and (b) `def_3_4`'s
--   per-step walk-edge data (typed `refactor_WalkStep` with three
--   constructors `.forwardE / .backwardE / .bidir`) and the `cons`-cell of
--   `refactor_Walk` — so the binders below are byte-identical to the
--   original `CDMG`-namespace variable line at the top of this file.
--
-- *Three-dash `--- start helper` / `--- end helper`, not two-dash
--   `-- start statement`.*  Lean 4's `variable` auto-binding folds these
--   implicit binders into every refactored declaration below exactly as
--   it does for the originals.  The three-dash flavour tags this as
--   helper-level wrapping, consistent with how the original `variable`
--   line at the top of this file and the `refactor_CDMG` section-wide
--   `variable` at `Walks.lean:1201-1203` are tagged.  The Phase 7
--   cleanup script's whole-word rename (`refactor_<Name>` → `<Name>`)
--   leaves the `def_3_15` marker text inside this block untouched (the
--   marker is a documentation comment, not a declaration name).
-- def_3_15 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_15 --- end helper

namespace refactor_WalkStep

-- ## Design choice — refactor_WalkStep-namespace statement context
--
-- *Why a namespace-level `variable {G : refactor_CDMG Node}`.*  The
--   helper `refactor_IsInto` below takes a typed WalkStep
--   `s : refactor_WalkStep G u v` and asks whether it places an
--   arrowhead at a given node.  Without the namespace-wide `variable`,
--   the signature would carry an explicit `{G : refactor_CDMG Node}`
--   binder; the auto-binding keeps the signature readable and matches
--   the chapter-wide implicit-G convention used by every
--   `refactor_CDMG`-opening file in the chapter
--   (`Walks.lean:1201-1203`, `EdgeRelations.lean:357`, etc.).
--
-- *Three-dash helper marker, not two-dash statement marker.*  Same
--   rationale as the `refactor_Walk` namespace `variable` block below
--   and as the refactor section's section-wide `variable` immediately
--   above: this `{G}` binder is load-bearing infrastructure that the
--   tex/Lean reconciliation tooling and the Phase 7 cleanup script
--   must recognise as helper-flavour.
-- def_3_15 --- start helper
variable {G : refactor_CDMG Node}
-- def_3_15 --- end helper

-- ref: def_3_15 (helper, "edge into a node" at a typed WalkStep) — refactor
--
-- `s.refactor_IsInto w` iff the typed WalkStep `s : refactor_WalkStep
-- G u v` places an arrowhead at the node `w` when traversed.  The
-- canonical per-WalkStep "arrowhead-at-node" predicate at the typed-
-- WalkStep level, reading the channel and direction off the WalkStep's
-- constructor tag instead of going through the original's
-- ordered-pair-plus-`G.into` machinery:
--
-- - `.forwardE _` (encoding `(u, v) ∈ G.E`, running `u → v`):
--   arrowhead at the target index `v`.  `IsInto w := (w = v)`.
-- - `.backwardE _` (encoding `(v, u) ∈ G.E`, running `v → u`):
--   arrowhead at the source index `u` (the target of the underlying
--   directed edge).  `IsInto w := (w = u)`.
-- - `.bidir _` (encoding `s(u, v) ∈ G.L`, bidirected): arrowheads at
--   BOTH endpoints simultaneously.  `IsInto w := (w = u ∨ w = v)`.
--
-- The sole consumer is `refactor_Walk.refactor_IsCollider` below, which
-- uses `s.refactor_IsInto vk` to test arrowhead-presence at the
-- position-`k` vertex on the walk.
--
-- ## Design choice — refactor_IsInto
--
-- *Why a helper at all, rather than inlining the per-WalkStep
--   classification directly into `refactor_IsCollider`'s pattern
--   match.*  The LN block phrases the collider case as "there are two
--   arrowheads pointing towards $v_k$ on the walk $\pi$" (canonical
--   tex `def_3_15`, item~ii of the Classification paragraph: collider
--   iff `ah_π(k) = 2`, with `ah_π(k)` defined as the count of walk-
--   incident edges `a_{k-1}, a_k` that are edges into $v_k$).
--   Factoring "this WalkStep contributes an arrowhead at node `w`"
--   out as `refactor_IsInto` lets the consumer
--   `refactor_IsCollider` mirror the LN's phrasing word-for-word at
--   its `k = 1` branch as the conjunction
--   `s₀.refactor_IsInto vk ∧ s₁.refactor_IsInto vk` — one conjunct
--   per "arrowhead pointing towards $v_k$".  Inlining would instead
--   force a 9-Cartesian-product branch (one per pair of constructor
--   tags) at the `k = 1` slot of `refactor_IsCollider`, breaking the
--   LN-mirroring reading and re-introducing the writing-mirror /
--   self-loop pathologies the helper is designed to absorb (see the
--   next bullet for the writing-mirror union fix, and the "Self-loop
--   semantics" bullet on `refactor_IsCollider` below for the self-
--   loop fix).  The helper's "arrowhead-at-node" framing is also the
--   LN-faithful one: `def_3_3` item~ii ("edge into a node") is the
--   per-edge primitive the LN itself uses to build the collider
--   count, so `refactor_IsInto` is the typed-WalkStep transcription
--   of that exact primitive.
--
-- *Writing-mirror union semantics on directed branches.*  The LN's
--   `into v_k a_i` predicate at a walk-incident edge `a_i = (e_1, e_2)`
--   is a *union* over the two channels read off a SINGLE stored
--   ordered pair: `into v_k a_i ↔ (a_i ∈ E ∧ e_2 = v_k) ∨ (a_i ∈ L ∧
--   (e_1 = v_k ∨ e_2 = v_k))` (canonical tex `def_3_15` spelling out
--   `def_3_3` item~ii).  Under the typed-WalkStep refactor, the stored
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
--   L-channel disjunct in writing-mirror cases and make the refactor's
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
--   node-equality test `w = v` on the type indices alone — the same
--   load-bearing self-loop fix the prior review committed to.  No
--   special-casing is needed for self-loops; the writing-mirror union
--   fix and the self-loop fix coexist by `hL_irrefl`.
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
-- *Net-new helper with no original counterpart.*  The original
--   `Walk.IsCollider` (`def_3_15` ORIGINAL block above in this file)
--   characterised "edge into `v_k`" by `G.into v_k a`, the `def_3_3`
--   item~ii membership disjunction over the stored ordered pair
--   `a : Node × Node`.  Under the typed-WalkStep refactor (a) the
--   stored pair is dissolved into the WalkStep's typed structure and
--   (b) the original `Walk.edges` projection that fed `G.into` no
--   longer exists (see `Walks.lean:1631-1685`'s "Why no `refactor_edges`"
--   block for the intentional omission).  A per-WalkStep
--   "arrowhead-at-w" predicate is therefore needed as new
--   infrastructure to translate "edge into `v_k`" through the refactor
--   shape — `refactor_IsInto` is that predicate.  Wrapped as a
--   REPLACEMENT block with no ORIGINAL counterpart per the manager's
--   net-new-helper marker convention.
--
-- *Why test by node-equality (`w = u` / `w = v`) rather than by
--   constructor-tag "source vs target" labels.*  This is the load-
--   bearing semantic decision of the helper.  A naive constructor-tag
--   reading — "a `.forwardE` puts the arrowhead at the target side,
--   not the source side" — loses information at directed self-loops,
--   where the WalkStep's source and target type indices are *the same
--   node*.  Concretely: at a self-loop `(v, v) ∈ G.E` encoded as
--   `.forwardE _ : refactor_WalkStep G v v`, the source-vs-target
--   reading would label this as "arrowhead at v but not at v" — a
--   semantically empty statement that cannot distinguish "arrowhead at
--   the loop vertex" from "no arrowhead at the loop vertex".  The
--   node-equality test resolves this cleanly: `IsInto v` evaluates to
--   `(v = v) = True` for `.forwardE _ : refactor_WalkStep G v v`,
--   matching the original's `G.into v (v, v) = True` (via the
--   E-clause's `e.2 = v` condition).  Wording-check subtlety
--   `self_loop_makes_tuh_and_hut_simultaneously_true` flagged exactly
--   this corner: the literal-LN constructor-tag reading
--   (`v ⟵ v ⟶ v_{k+1}` vs. `v ⟶ v ⟶ v_{k+1}`) is ambiguous for
--   self-loops, but the count-based reading the canonical tex commits
--   to (preserved here via node-equality) is unambiguous and matches
--   the original's `G.into`-based semantics.
--
-- *Why a `Prop` predicate, not a `Bool` decidable.*  Same rationale as
--   `refactor_IsCollider` below: walks live at `Type _`, their per-
--   position classification at `Prop`.  A `Bool` form would require a
--   `DecidableEq Node` discharge at every elaboration site — possible
--   in principle (we already have `[DecidableEq Node]` from the section-
--   wide variable), but adds infrastructure with no payoff for the
--   predicate's role as a `Prop`-conjunct inside `refactor_IsCollider`.
--
-- *Why the explicit `w : Node` argument, not curried via the
--   WalkStep's source/target indices.*  The two call sites in
--   `refactor_IsCollider` both pass the SAME node `vk` (the position-
--   `k` vertex on the walk) to two different WalkSteps `s_{k-1}` and
--   `s_k`, only one of which has `vk` as its type-level target index
--   (`s_{k-1}` has target `vk`; `s_k` has source `vk`).  The `w : Node`
--   argument keeps the helper position-independent: either WalkStep
--   can be queried "is your arrowhead at `vk`?" without the caller
--   having to remember whether `vk` is the source or target index.
--   This is exactly the call pattern `refactor_IsCollider` uses:
--   `s₀.refactor_IsInto vk` and `s₁.refactor_IsInto vk` where `vk` is
--   the cons-cell's middle vertex binder.
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
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsInto (was: refactor_IsInto)
-- def_3_15 --- start helper
def refactor_IsInto : ∀ {u v : Node}, refactor_WalkStep G u v → Node → Prop
  | u, v, .forwardE _,  w => w = v ∨ (s(u, v) ∈ G.L ∧ (w = u ∨ w = v))
  | u, v, .backwardE _, w => w = u ∨ (s(u, v) ∈ G.L ∧ (w = u ∨ w = v))
  | u, v, .bidir _,     w => w = u ∨ w = v
-- def_3_15 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: IsInto

end refactor_WalkStep

namespace refactor_Walk

-- ## Design choice — refactor_Walk-namespace statement context
--
-- *Why a namespace-level `variable {G : refactor_CDMG Node}`.*  Both
--   `refactor_IsCollider` and `refactor_IsNonCollider` recurse over /
--   take a walk `p : refactor_Walk G u v`.  Without the namespace-wide
--   `variable`, every signature would carry an explicit
--   `{G : refactor_CDMG Node}` binder; the auto-binding keeps the
--   signatures readable and matches the LN's "Let $G = (J, V, E, L)$ be
--   a CDMG" once-at-the-top quantifier.  Mirrors the original
--   `namespace Walk` opening earlier in this file and the refactor
--   `namespace refactor_Walk` opening at `Walks.lean:1514-1538`
--   byte-for-byte modulo the `CDMG → refactor_CDMG` type retarget.
--   `{G}` is implicit because downstream consumers reach into `G` via
--   dot-notation on the walk (`p.refactor_IsCollider k` rather than
--   `refactor_Walk.refactor_IsCollider G p k`).
--
-- *Three-dash helper marker, not two-dash statement marker.*  Same
--   rationale as the original (Walk-namespace block above) and as the
--   refactor section's section-wide `variable` immediately above: this
--   `{G}` binder is load-bearing infrastructure that the tex/Lean
--   reconciliation tooling and the Phase 7 cleanup script must
--   recognise as helper-flavour.
-- def_3_15 --- start helper
variable {G : refactor_CDMG Node}
-- def_3_15 --- end helper

-- ref: def_3_15 (item ii, collider) — refactor
--
-- `p.refactor_IsCollider k` iff position `k` on the walk `p` has
-- arrowhead count `ah_π(k) = 2`, i.e.\ both walk-incident edges
-- `s_{k - 1}` and `s_k` exist (forcing `1 ≤ k ≤ p.refactor_length - 1`,
-- an interior position) and both are "edges into the vertex `v_k`" in
-- the LN sense of `def_3_3` item~ii.  Under the typed-WalkStep refactor
-- this classification is delegated to the helper
-- `refactor_WalkStep.refactor_IsInto` (defined above), which tests
-- arrowhead-presence by *node-equality* on the WalkStep's type indices
-- rather than by a constructor-tag "source vs target" reading.  This
-- preserves the original's `G.into`-driven semantics including the
-- self-loop convention (a directed self-loop contributes exactly one
-- arrowhead at the loop vertex, matching `G.into v (v, v) = True` via
-- the original's E-clause's `e.2 = v` condition).
--
-- ## Design choice — refactor_IsCollider
--
-- *Mutual exclusivity pulls back along the forgetful map.*  No code
--   change is required in `refactor_IsCollider` itself for the
--   writing-mirror union-semantics fix (the entire fix is encapsulated
--   inside `refactor_IsInto` above), but the consequence at this level
--   is worth stating: the LN's "every position on `π` is exactly one
--   of a non-collider or a collider on `π`" mutual-exclusivity
--   property (canonical tex `def_3_15`, "Classification" paragraph)
--   now pulls back *cleanly* along the forgetful map
--   `refactor_Walk G u v → LN walk in G` even for writing-mirror
--   walks (those traversing a stored pair that lives in both `G.E`
--   and `G.L`).  Concretely, a single LN walk position has a
--   well-defined `ah_π(k) ∈ {0, 1, 2}` count independent of the
--   walker's constructor choice when typifying the underlying ordered
--   pair, and `refactor_IsCollider` / `refactor_IsNonCollider` agree
--   with the LN classification at every encoding — the writing-mirror
--   union fix in `refactor_IsInto` is the load-bearing piece that
--   makes this constructor-choice invariance hold.  Without that fix,
--   the same LN walk position could be classified differently
--   depending on whether the walker stored each step as `.forwardE`
--   versus `.bidir` at a writing-mirror pair, breaking pullback along
--   the forgetful map and producing a CONTENT-class strict-checker
--   divergence; the fix restores the LN's classification-by-`ah_π(k)`
--   reading verbatim.
--
-- *Why the refactor needs to touch this predicate.*  The original
--   `Walk.IsCollider` (ORIGINAL block above) characterised "edge into
--   `v_k`" by an `Option`-lookup into `p.edges : List (Node × Node)`
--   followed by a `G.into v (e : Node × Node)` membership-disjunction
--   over `G.E` and `G.L`.  Under the typed-WalkStep refactor (a)
--   `p.edges` no longer exists — the original's `Walk.edges` block has
--   been intentionally dropped under the refactor (see
--   `Walks.lean:1631-1685`'s "Why no `refactor_edges`" block), so any
--   port that goes through `p.edges`-style indexing is non-buildable;
--   and (b) the channel and direction information that the original
--   read off the ordered pair `a : Node × Node` plus `G.into` is now
--   carried by the WalkStep's *constructor tag* (channel) and *type
--   indices* (source/target endpoints).  The natural refactor port is
--   therefore a *recursive pattern-match* on the `refactor_Walk`
--   constructors that case-splits at the head cons-cell and recurses
--   on the tail — same recursion shape as
--   `refactor_IsBifurcationWithSplit` (`Walks.lean:2444-2455`) and
--   `refactor_IsColliderRest` (`Walks.lean:2186-2197`).  The per-step
--   "edge into `v_k`" test is delegated to
--   `refactor_WalkStep.refactor_IsInto` (defined above) — see the
--   next bullet for why a helper rather than inline pattern-matching.
--
-- *Why the helper `refactor_IsInto` rather than an inline constructor-
--   tag enumeration.*  The naive port — enumerate all 9 combinations
--   of (`s_{k-1}`'s tag) × (`s_k`'s tag) at position `k = 1` and ask
--   "does this pair of tags encode an arrowhead at `v_k` from both
--   sides?" — gives the wrong answer at directed self-loops.
--   Concretely: with `E = {(v_0, v_1), (v_1, v_1)}` and walk
--   `cons _ (.forwardE h₁) (cons _ (.forwardE h₂) (.nil _ hv))`, the
--   original's `Walk.IsCollider p 1` evaluates to `True` (both
--   `G.into v_1 (v_0, v_1)` and `G.into v_1 (v_1, v_1)` fire via the
--   E-clause's `e.2 = v_1` condition).  But a tag-enumeration that
--   reads `.forwardE` rigidly as "arrowhead at target, not source"
--   would classify the second step `s_k = .forwardE _` (encoding the
--   self-loop at `v_1`) as "no arrowhead at `v_1`" and return `False`
--   — a divergence from the original.  The root cause is that for a
--   self-loop, the WalkStep's source and target type indices are the
--   SAME node, so the "source vs target" reading of the constructor
--   tag loses the self-loop coincidence; both readings are
--   simultaneously valid for the same edge.  The fix is to test "is
--   there an arrowhead at `v_k`?" by *node-equality* on the type
--   indices instead — exactly what `refactor_IsInto` does.  Under the
--   helper, both `.forwardE _` and `.backwardE _` encodings of a
--   self-loop at `v_k` correctly fire `IsInto v_k = True`, recovering
--   the original's count.  Wording-check subtlety
--   `self_loop_makes_tuh_and_hut_simultaneously_true` flagged this
--   corner explicitly; the `IsInto`-helper-with-node-equality is the
--   resolution.
--
-- *Why the recursive pattern-match style rather than retaining the
--   original's existential-with-`vertices`/`edges`-indexing shape.*
--   Two converging reasons:
--   - **`refactor_edges` does not exist** (`Walks.lean:1631-1685`'s
--     "Why no `refactor_edges`" block documents the intentional
--     omission), so the original's `p.edges[k - 1]? = some a₁ ∧
--     p.edges[k]? = some a₂` indexing has no refactor counterpart at
--     all.  Without `refactor_edges`, every per-step classification
--     *must* be done by pattern-matching on the typed
--     `refactor_WalkStep` constructors directly off the
--     `refactor_Walk.cons` cell.
--   - **Pattern-match on constructors is structurally exclusive** —
--     `.forwardE`, `.backwardE`, `.bidir` are mutually disjoint
--     constructors, so the recursion bottoms out structurally rather
--     than by Option-membership failure as in the original.  The
--     `nil` / `cons-nil` / `cons-cons` shape of `refactor_Walk`
--     translates the original's in-range / out-of-range / end-position
--     case analysis into pattern-match exhaustiveness checked by Lean's
--     equation compiler.
--
-- *Self-loop semantics preserved via the `refactor_IsInto` helper.*
--   A directed self-loop `(v, v) ∈ G.E` at step `s_i` is encoded as
--   either `.forwardE h` (with `h : (u, v) ∈ G.E`, here `u = v`) or
--   `.backwardE h` (with `h : (v, u) ∈ G.E`, here `v = u`).  At a
--   self-loop position, the WalkStep's source and target type indices
--   are the SAME node, so the node-equality test inside
--   `refactor_IsInto` fires `True` for BOTH `.forwardE` and
--   `.backwardE` encodings of the self-loop — matching the original's
--   `G.into v_k (v_k, v_k) = True` via the E-clause's `e.2 = v_k`
--   condition.  Concretely: a `.forwardE _ : refactor_WalkStep G v_k
--   v_k` at slot `s_{k-1}` hits `IsInto`'s `w = v` branch with
--   `w = v_k` and `v = v_k`, returning `True`; a
--   `.backwardE _ : refactor_WalkStep G v_k v_k` at slot `s_k` hits
--   `IsInto`'s `w = u` branch with `w = v_k` and `u = v_k`, also
--   returning `True`.  `.bidir _` is *impossible* on a self-loop
--   because the refactor's `hL_irrefl : ∀ ⦃s⦄, s ∈ G.L → ¬ s.IsDiag`
--   rules out `s(v, v) ∈ G.L` outright, so the bidir disjunction never
--   fires at a self-loop.  No special-casing is needed in
--   `refactor_IsCollider` itself — the helper absorbs the self-loop
--   convention through its node-equality test.
--
-- *Why the cons-nil branch (length-1 walk) returns `False` uniformly
--   for every `k`.*  A collider position requires
--   `k ∈ {1, …, n − 1}` — i.e.\ an *interior* position — per the LN's
--   "Arrowhead count at a position" paragraph (canonical tex
--   `def_3_15`): at an end-position `k ∈ {0, n}` at most one walk-
--   incident index is admissible, so `ah_π(k) ≤ 1` automatically and
--   the position is a non-collider.  A length-1 walk
--   (`refactor_Walk.cons _ _ (.nil _ _)`, `n = 1`) has *only* end-
--   positions `k ∈ {0, 1}` — no interior positions exist — so
--   `ah_π(k) = 2` is impossible at every `k`, and the position is
--   *necessarily* a non-collider.  The `.cons _ _ (.nil _ _), _`
--   branch catches all `k` uniformly and returns `False`,
--   structurally encoding the LN's `n ≥ 2` lower bound on the walk's
--   length for a collider position to even be admissible.  The
--   trivial walk (`n = 0`, only position 0) is the length-0 sibling
--   case, caught by the `.nil _ _, _` branch with the same
--   `False`-return.  These two false-branches together encode the
--   "at most one walk-incident edge in scope" structural reading: a
--   walk's interior is non-empty only when its shape is at least
--   `.cons _ _ (.cons _ _ _)`, matching the LN's `n ≥ 2` requirement
--   word-for-word.  The original `Walk.IsCollider` (ORIGINAL block)
--   encoded the same content via the `p.edges[k - 1]? = some _ ∧
--   p.edges[k]? = some _` Option-membership conjuncts (which fail at
--   `k = 0` and at `k ≥ p.length`); the refactor port encodes it
--   structurally via the cons-pattern instead, since `refactor_edges`
--   does not exist (see "Why the recursive pattern-match style"
--   below).
--
-- *Why no explicit `1 ≤ k` end-position guard, and why no
--   `k ≤ p.refactor_length - 1` end-position guard.*  Both are
--   absorbed into the recursive structure of the pattern match itself.
--   - At `k = 0`: the only branches firing are `.nil _ _, _` (a trivial
--     walk has no interior, returns `False`),
--     `.cons _ _ (.nil _ _), _` (a length-1 walk has only endpoints,
--     returns `False`), and `.cons _ _ (.cons _ _ _), 0` (the
--     position-0 slot of a non-trivial walk, returns `False`).
--   - At `k = 1` with a length-1 walk: the `.cons _ _ (.nil _ _), _`
--     branch catches all `k`, returning `False` — correct since
--     position 1 is the end of a length-1 walk and the original's
--     `p.edges[1]? = none` would also return `False` here.
--   - At `k > p.refactor_length`: the recursion bottoms out by
--     descending through cons-cells with `k + 2` decrementing to
--     `k + 1`, until eventually the walk is `.nil _ _` or
--     `.cons _ _ (.nil _ _)`, both of which return `False`.  Out-of-
--     range positions therefore return `False` without an explicit
--     bound check, exactly as the original did via the
--     `p.edges[k]? = none` Option-membership failure.
--   This is the same recursion discipline used by
--   `refactor_IsBifurcationWithSplit`: the trivial walk and the
--   length-1 walk are explicit base cases; longer walks recurse via
--   `p.refactor_IsCollider (k + 1)` (index shift by 1 because the
--   tail walk starts at v_1, not v_0 — see the next bullet).
--
-- *Why the recursive call is on `p` at index `k + 1` (not at `k`).*
--   At an outer position `k + 2` of the walk `cons _ s_0 (cons _ s_1
--   p)`, the recursion descends one cons-cell into the tail (so the
--   tail walk starts at vertex `v_1`, not `v_0`).  The LN's position
--   `k + 2` on the outer walk corresponds to position `k + 1` on the
--   tail walk (vertex re-indexing shifts by 1).  Hence the call is
--   `p.refactor_IsCollider (k + 1)`, not `p.refactor_IsCollider k`.
--   Note that the tail walk here starts with the cons-cell containing
--   `s_1` (which becomes the new `s_0` of the tail), so position
--   `k + 1` on the tail corresponds correctly to position `k + 2` on
--   the outer.
--
-- *Why the recursion only fires at outer position `k + 2`, not at
--   outer position `k + 1`.*  The cons-cons-at-k=1 branch
--   (`.cons vk s₀ (.cons _ s₁ _), 1`) handles outer position 1
--   *directly* — without recursion — and necessarily so.  Testing
--   collider-ness at outer position 1 requires reading the two HEAD
--   walk-incident steps `s_0 = s₀` and `s_1 = s₁` simultaneously,
--   both of which are bound at the OUTER level of the cons-cons
--   pattern.  Recursing into the tail at outer position 1 would lose
--   access to the head step `s_0` (which lives at the outer head
--   cons-cell, not inside the tail), so the recursion structurally
--   cannot decrement past the cons-cons barrier without dropping the
--   LHS of the `IsInto ∧ IsInto` conjunction that position 1
--   requires.  The recursion's first opportunity to fire is therefore
--   at outer position `k + 2` (with `k ≥ 0`), where the head's
--   `(s_0, s_1)` pair is no longer the relevant pair to query —
--   instead the tail's first two steps `(s_1, s_2)` form the relevant
--   pair at the outer's position `k + 2 = (tail position) + 1`, and
--   the tail's position-1 query recovers
--   `tail.refactor_IsCollider 1 ↔ s_1.IsInto v_2 ∧ s_2.IsInto v_2`,
--   which is exactly the outer's position-2 query
--   `cons s_0 (cons s_1 …).IsCollider 2`.  Net effect: position 1 is
--   special-cased (dedicated branch); positions `2..n−1` are recursed
--   (`k + 2` outer descends to `k + 1` tail); the recursion bottoms
--   out one cons-level earlier than a naïve "shift-by-1 at every
--   outer position" pattern would, because the position-1 case has
--   its own dedicated branch above it.  A reader tempted to "unify"
--   the cons-cons-at-k=1 and the cons-cons-at-k+2 branches into a
--   single recursive case would have to either (a) introduce a
--   companion helper that carries `s_0` through the recursion, or
--   (b) reach into the tail's `cons` to recover `s_0` — both options
--   strictly more complex than the dedicated branch.
--
-- *Why the cons-cell middle-vertex binder `vk` (not a wildcard) at
--   the `k = 1` branch.*  The `IsInto` helper calls require `vk`
--   (= `v_1` of the walk) on the RHS as the node to test arrowhead-
--   presence for.  Binding `vk` in the pattern reads the cons-cell's
--   middle vertex out for use in both `s₀.refactor_IsInto vk` and
--   `s₁.refactor_IsInto vk`.  This is `refactor_Walk.cons`'s first
--   explicit constructor argument (the `(v : Node)` slot of
--   `cons {u w : Node} (v : Node) (s : refactor_WalkStep G u v) (p :
--   refactor_Walk G v w)`), so binding the first pattern position of
--   the cons reads exactly `v_1`.  No other branch references the
--   middle vertex (the `False`/recursion branches don't need it), so
--   they keep their `_` wildcard.
--
-- *Net-new declaration with no original counterpart at the markered
--   level beyond the wrapped ORIGINAL block above.*  The original
--   `Walk.IsCollider` (ORIGINAL block) remains under the original
--   `CDMG` namespace and continues to compile; the refactor's
--   `refactor_IsCollider` is a separate `def` under the
--   `refactor_CDMG.refactor_Walk` namespace.  The
--   `REFACTOR-BLOCK-REPLACEMENT` marker pair wraps the entire `def`;
--   Phase 7 cleanup will rename `refactor_IsCollider` to `IsCollider`
--   (whole-word) across every refactored file, leaving a `def IsCollider`
--   in the final tree — the LN's intended object name.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsCollider (was: refactor_IsCollider)
-- def_3_15 -- start statement
def refactor_IsCollider : ∀ {u v : Node}, refactor_Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ _ (.nil _ _), _ => False
  | _, _, .cons _ _ (.cons _ _ _), 0 => False
  | _, _, .cons vk s₀ (.cons _ s₁ _), 1 =>
      s₀.refactor_IsInto vk ∧ s₁.refactor_IsInto vk
  | _, _, .cons _ _ (p@(.cons _ _ _)), k + 2 => p.refactor_IsCollider (k + 1)
-- def_3_15 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsCollider

-- ref: def_3_15 (item i, non-collider) — refactor
--
-- `p.refactor_IsNonCollider k` iff position `k` on the walk `p` is in
-- range (`k ≤ p.refactor_length`) and has arrowhead count
-- `ah_π(k) ≤ 1`, equivalently `¬ p.refactor_IsCollider k`.  Body
-- identical to the original `Walk.IsNonCollider` (ORIGINAL block above)
-- modulo two mechanical retargets:
-- - `p.length` → `p.refactor_length` (the refactor-ported walk-length
--   helper at `Walks.lean:1590-1593`); and
-- - `p.IsCollider` → `p.refactor_IsCollider` (the REPLACEMENT def
--   immediately above).
--
-- ## Design choice — refactor_IsNonCollider
--
-- *Why the refactor needs to touch this predicate.*  Mechanically only,
--   not semantically.  The body references two walk-helpers that have
--   themselves been refactored (`p.length` and `p.IsCollider`), so the
--   def needs to be re-stated using the refactored helpers.  The
--   `Prop`-level conjunction `k ≤ … ∧ ¬ …`, the bound-via-natural-
--   number-comparison shape, the LN-correspondence to the canonical
--   tex's "non-collider iff `ah_π(k) ≤ 1`" reading — all unchanged.
--   Note that the `refactor_IsCollider` reference now resolves to the
--   `IsInto`-helper-based predicate immediately above, so the self-
--   loop convention (a self-loop contributes exactly one arrowhead at
--   the loop vertex) is preserved through this indirection — see the
--   `refactor_IsCollider` design block for the load-bearing
--   node-equality-based reading.
--
-- *Why `k ≤ p.refactor_length` rather than the Option-membership style
--   (`p.refactor_vertices[k]? = some _`).*  Same rationale as the
--   original (ORIGINAL block above's design notes): the LN's "every
--   position on `π`" scope is `{0, 1, …, n}`, and the bound
--   `k ≤ p.refactor_length` is the exact ℕ-comparison encoding of this
--   index set.  An Option-membership encoding would force every
--   downstream consumer to destructure the witness, which is not needed
--   here because the body's other conjunct (`¬ p.refactor_IsCollider k`)
--   does not consume a `v_k` witness.  Preserving the asymmetry between
--   the original's `IsCollider` (positive existential with Option-
--   membership) and `IsNonCollider` (bounded negation with explicit
--   range check) — the refactor preserves this asymmetry verbatim, only
--   the helper-level surface retargets to the typed-WalkStep API.
--
-- *Why mutual exclusivity on the in-range fragment stays definitional
--   after the port.*  `refactor_IsNonCollider p k` literally unfolds
--   to `k ≤ p.refactor_length ∧ ¬ p.refactor_IsCollider k`, so on the
--   in-range fragment `k ≤ p.refactor_length` the statement
--   `p.refactor_IsNonCollider k ↔ ¬ p.refactor_IsCollider k` reduces
--   by definitional unfolding alone — no external theorem needed.  The
--   original's symmetry property (ORIGINAL block above's design notes)
--   is preserved verbatim through the mechanical retarget; only the
--   referenced helpers change, not the logical shape of the predicate.
--
-- *End-positions are non-colliders automatically (preserved).*  Both
--   `k = 0` (`0 ≤ p.refactor_length` always holds) and
--   `k = p.refactor_length` satisfy the in-range bound.  At `k = 0`,
--   `refactor_IsCollider` fires the `.nil _ _, _` or `.cons _ _ _, 0`
--   branches, returning `False`.  At `k = p.refactor_length`, the
--   recursion eventually descends into a `.nil _ _` or
--   `.cons _ _ (.nil _ _)` tail at the indexed position, also returning
--   `False`.  Either way `refactor_IsNonCollider` evaluates to `True`,
--   preserving the LN's "end-positions are non-colliders by
--   construction" reading without modification.
--
-- *Net-new declaration with no original counterpart at the markered
--   level beyond the wrapped ORIGINAL block above.*  The original
--   `Walk.IsNonCollider` (ORIGINAL block) remains under the original
--   `CDMG` namespace and continues to compile; the refactor's
--   `refactor_IsNonCollider` is a separate `def` under the
--   `refactor_CDMG.refactor_Walk` namespace.  Phase 7 cleanup will
--   rename `refactor_IsNonCollider` to `IsNonCollider` (whole-word)
--   across every refactored file, leaving a `def IsNonCollider` in the
--   final tree — the LN's intended object name.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsNonCollider (was: refactor_IsNonCollider)
-- def_3_15 -- start statement
def refactor_IsNonCollider {u v : Node} (p : refactor_Walk G u v) (k : ℕ) : Prop :=
  k ≤ p.refactor_length ∧ ¬ p.refactor_IsCollider k
-- def_3_15 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsNonCollider

end refactor_Walk

end refactor_CDMG

end Causality
