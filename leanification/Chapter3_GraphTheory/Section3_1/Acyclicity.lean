import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.Walks

namespace Causality

/-!
# Acyclicity of CDMGs (`def_3_6`)

This file formalises the LN definition block `def_3_6`
(`\label{def-acylic}` in `graphs.tex`):

> A CDMG `G = (J, V, E, L)` is called *acyclic* iff there does not exist
> any non-trivial directed walk from `v` to itself in `G` for any node
> `v ∈ J ∪ V`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/def_3_6_Acyclicity.tex`,
verified equivalent to the LN block augmented with one operator
clarification:

* `[nontrivial_directed_walk_not_defined_in_block]` — a "non-trivial"
  directed walk is one of length `n ≥ 1` (i.e.\ it traverses at least
  one edge); the length-`0` trivial walk `(v_0)` at a single vertex is
  excluded. Consequence: an acyclic CDMG contains no directed
  self-loops on any `v ∈ V`.

The predicate is built on `def_3_4`'s `Walk` inductive (`Walks.lean`)
together with its `Walk.IsDirectedWalk` predicate and `Walk.length`
function: a *directed walk* from `v` to `v` is a `Walk G v v` carrying
the `IsDirectedWalk` witness, and *non-trivial* is encoded as
`Walk.length p ≥ 1`.  The membership `v ∈ G` (`Membership Node (CDMG
Node)` instance from `CDMGNotation.lean`, `def_3_2`) supplies the
quantifier scope `v ∈ J ∪ V` from the LN.
-/

namespace CDMG

-- def_3_6 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_6 --- end helper

-- ref: def_3_6 (acyclicity) — refactor
--
-- *Structural port of the original `IsAcyclic`* (`namespace CDMG`,
-- lines ~39–187 above) onto the `cdmg_typed_edges` refactor's new
-- upstream types (DEPENDENT row; roots `def_3_1`, `def_3_4`). The
-- mathematical design — quantifier scope `∀ v ∈ G` resolved to
-- `J ∪ V`, "non-trivial" as `p.length ≥ 1`, predicate built on
-- `Walk + IsDirectedWalk` (not on a separate `Cycle` / `Path`
-- type), conjunction-under-`∃` instead of a subtype or bundled
-- `DirectedCycle`, the Mathlib `SimpleGraph.IsAcyclic` re-use
-- trade-off, and the three known-limitations notes — is
-- **unchanged**.  See the original block above for the full
-- rationale; the resolutions of wording-check subtleties
-- `node_quantifier_scope_v_in_G_unclear_J_versus_V` and
-- `non_trivial_walk_undefined_admits_self_loop_and_2cycle_ambiguity`
-- carry over verbatim.
--
-- *Upstream-type shifts (and only those).*
--   `CDMG Node          → CDMG Node`
--   `Walk G v v         → Walk G v v`
--   `p.IsDirectedWalk   → p.IsDirectedWalk`
--   `p.length           → p.length`
-- The `∀ v ∈ G` quantifier reads verbatim via the
-- `instMembership` instance in `CDMGNotation.lean`
-- (`def_3_2` refactor twin), and the structural argument that the
-- `J`-half of the quantifier is vacuous — relying on `hE_subset`
-- and `hJV_disj` — is unchanged: both fields exist on
-- `CDMG` with identical signatures.
--
-- ## Refactor-specific design deltas (choices made *against* the
-- new typed-edge shape)
--
-- *Predicate-on-walk, not structural recursion on typed
--   `WalkStep`.*  Because `Walk` now carries
--   each step's channel in the type
--   (`.forwardE` / `.backwardE` / `.bidir`), `IsAcyclic` *could*
--   have been re-encoded directly via the inductive — e.g.\ "no
--   `Walk G v v` of length ≥ 1 has every step
--   `.forwardE`", inlining `IsDirectedWalk` into the
--   predicate.  Rejected on two counts: (i) the LN speaks of
--   "directed walks" as a separate notion and the strict-
--   equivalence solved-gate compares against that LN text, so
--   collapsing the two would obscure the LN-to-Lean
--   correspondence at this row; (ii) downstream consumers
--   (`def_3_8` topological order, `claim_3_2`, chs.\ 6–7
--   d-/σ-separation) re-use `IsDirectedWalk`
--   independently of acyclicity, so layering `IsAcyclic` *on top
--   of* `IsDirectedWalk` shares the inversion / recursion
--   lemmas across rows rather than re-proving them per consumer.
--
-- *Non-triviality stays `length ≥ 1`, not baked into
--   `Walk` as a "non-empty walk" constructor split.*  The
--   `def_3_4` refactor preserved the `nil` / `cons` constructor
--   shape of `Walk` (only the per-step datum moved from an
--   untyped `Node × Node` pair to a typed `WalkStep`),
--   so the length-counting story is unchanged.  A constructor-
--   level non-triviality split on `Walk` would force
--   every walk-predicate recursion (`IsDirectedWalk`,
--   `IsColliderWalk`, `IsBidirectedWalk`,
--   `IsBifurcationWithSplit`, …) to branch on it,
--   propagating the change far beyond this row for no local
--   benefit.  `length ≥ 1` keeps the encoding local and
--   matches the LN's `n \ge 1` literally.
-- def_3_6 -- start statement
def IsAcyclic (G : CDMG Node) : Prop :=
  ∀ v ∈ G, ¬ ∃ p : Walk G v v, p.IsDirectedWalk ∧ p.length ≥ 1
-- def_3_6 -- end statement

end CDMG

end Causality
