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
-- def_3_15 -- start statement
def IsCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ (vk : Node) (a₁ a₂ : Node × Node),
    p.vertices[k]? = some vk ∧
    p.edges[k - 1]? = some a₁ ∧
    p.edges[k]? = some a₂ ∧
    G.into vk a₁ ∧
    G.into vk a₂
-- def_3_15 -- end statement

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
-- def_3_15 -- start statement
def IsNonCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  k ≤ p.length ∧ ¬ p.IsCollider k
-- def_3_15 -- end statement

end Walk

end CDMG

end Causality
