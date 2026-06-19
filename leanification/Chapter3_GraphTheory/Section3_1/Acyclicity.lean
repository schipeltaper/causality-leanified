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

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  The typeclass is load-bearing for this
--   row's statement specifically because (i) `Walk.IsDirectedWalk`
--   (`Walks.lean`, `def_3_4` item~ii) recurses on per-edge
--   `a ∈ G.E` checks that need decidable pair equality on `Node`,
--   and (ii) the `Membership Node (CDMG Node)` instance from
--   `def_3_2` (`CDMGNotation.lean`) — the dispatch driving the
--   `v ∈ G` quantifier below — reduces to `Finset.mem` on
--   `G.J ∪ G.V`, which in turn requires `DecidableEq Node`.
--   Dropping either fixture would make this statement fail to
--   type-check.  Stronger instances (`Fintype`, `LinearOrder`) are
--   not needed and are deferred to use sites that consume them.
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  The two-dash marker is reserved for
--   declarations whose body is the formalised LN content of the row.
--   This `variable` line is *statement-typing infrastructure* — it
--   binds the implicit parameters that the `IsAcyclic` def below
--   relies on, but is not itself part of the LN definition.  The
--   three-dash flavour signals this to the tex/Lean reconciliation
--   tooling and the website extractor (both of which read by marker).
--   Matches the convention in `CDMG.lean`, `CDMGNotation.lean`,
--   `Walks.lean`, `EdgeRelations.lean`, `CDMGRestrictions.lean`.
-- def_3_6 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_6 --- end helper

-- ref: def_3_6
-- A CDMG `G = (J, V, E, L)` is *acyclic* iff there does not exist any
-- non-trivial directed walk from `v` to itself in `G`, for any node
-- `v ∈ J ∪ V`.  A non-trivial directed walk is one of length `n ≥ 1`
-- (i.e. it traverses at least one edge); equivalently, for `p : Walk G
-- v v` carrying `p.IsDirectedWalk` we require `p.length ≥ 1` for `p`
-- to be "non-trivial".  Quantifier scope `v ∈ G` is the LN's `v ∈ J ∪
-- V` via the `Membership Node (CDMG Node)` instance from `def_3_2`.
/-
LN tex (rewritten canonical statement for `def_3_6`):

  The CDMG $G$ is called *acyclic* iff
    for every $v \in J \cup V$,
    there does not exist any non-trivial directed walk from $v$ to
    itself in $G$.
-/
-- ## Design choice
--
-- *Quantifier scope `∀ v ∈ G`, mirroring the LN's literal "for any
--   node `v ∈ G`".*  Per `def_3_2`'s `Membership Node (CDMG Node)`
--   instance (`CDMGNotation.lean`), `v ∈ G` unfolds to `v ∈ G.J ∪
--   G.V`, so the LN phrasing transports onto the Lean text verbatim
--   — no notation macro, no helper function.  The LN-critic
--   wording-check flagged this scope as ambiguous (subtlety
--   `node_quantifier_scope_v_in_G_unclear_J_versus_V`: should `v`
--   range over `G.V` only, or `G.J ∪ G.V`?).  We resolve to the
--   wider scope `J ∪ V`, and the choice is *safe* because the
--   `J`-half is vacuous: `def_3_1`'s `hE_subset` forces every
--   directed edge's target into `G.V`, and `hJV_disj` makes
--   `J ∩ V = ∅`, so no length-≥ 1 directed walk can start and
--   return to any `j ∈ G.J` (it would require `j ∈ G.V`,
--   contradicting disjointness).  Restricting to `∀ v ∈ G.V` would
--   be logically equivalent but would no longer match the LN's
--   literal text and would force every downstream destructuring of
--   `v ∈ G` to carry an extra `J`-vs-`V` case split.
--
-- *"Non-trivial" encoded as `p.length ≥ 1`, per
--   `[nontrivial_directed_walk_not_defined_in_block]`.*  The LN
--   block uses "non-trivial" without defining it; the operator's
--   addition pins it to "length `n ≥ 1`" — i.e.\ the walk traverses
--   at least one edge — and explicitly admits a self-loop
--   `v ⇀ v` as a non-trivial walk of length 1.  `Walk.length`
--   (`Walks.lean`) counts edges via `nil ↦ 0` / `cons ↦ length p +
--   1`, so `p.length ≥ 1` is exactly "at least one `cons`
--   constructor" — i.e.\ at least one edge — matching the
--   addition's reading on the nose.  The wording-check subtlety
--   `non_trivial_walk_undefined_admits_self_loop_and_2cycle_ambiguity`
--   surfaced two plausible readings (length ≥ 1 vs.\ length ≥ 2 —
--   only the latter would let an acyclic CDMG carry self-loops);
--   the addition resolves to reading (a), and the rewritten tex
--   spec spells out the no-self-loop consequence in its
--   "Consequence" paragraph.  Alternative encodings `0 < p.length`,
--   `¬ p.length = 0`, or `p ≠ Walk.nil v hv` would all be
--   logically equivalent, but `p.length ≥ 1` reads most directly
--   off the LN's `$n \ge 1$`.
--
-- *`Walk G v v` rather than a fresh `Cycle` / `Path` type.*  The
--   upstream `def_3_4` `Walk` inductive (`Walks.lean`) indexes on
--   endpoints, so "from `v` to itself" lives in the *type*
--   `Walk G v v` — no side condition "`p` starts and ends at `v`"
--   needs to be threaded through.  Re-introducing a separate
--   `Cycle G v` type would force a forgetful `Cycle → Walk`
--   coercion at every downstream site that mixes acyclicity with
--   general-walk reasoning (`def_3_8` topological order,
--   `claim_3_2` acyclic-iff-topological-order, chapters 6–7
--   d-/σ-separation arguments that case-split on whether a sub-walk
--   is directed), duplicating `Walk`'s structural recursion for no
--   gain.  A `Path` type (Nodup vertex sequence) would *exclude*
--   the LN-admitted "non-trivial" self-loop case of length 1 —
--   wrong shape for this row's predicate.
--
-- *Conjunction `p.IsDirectedWalk ∧ p.length ≥ 1` under the
--   existential, not a subtype or bundled `DirectedCycle` struct.*
--   Mirrors the LN's prose "a non-trivial directed walk" — two
--   independent constraints on the same walk `p`.  A subtype
--   `{p : Walk G v v // p.IsDirectedWalk ∧ p.length ≥ 1}` would
--   force every consumer of `¬ ∃ p, …` to unpack `Subtype.mk` /
--   `Subtype.property` before reaching the underlying walk; a
--   bundled `DirectedCycle` structure would commit downstream rows
--   to a parallel walk-flavoured notion that does not otherwise
--   appear in the chapter.  A plain `∧` keeps inversion ergonomic:
--   a hypothesis `¬ ∃ p, p.IsDirectedWalk ∧ p.length ≥ 1` decomposes
--   by `rintro ⟨p, hp_dir, hp_len⟩` directly — exactly the shape
--   `claim_3_2` (acyclic ⟺ topological order) will pattern-match
--   against when constructing or rejecting witness cycles, and
--   exactly the shape `def_3_8`'s topological-order construction
--   needs when ruling out backward edges.
--
-- *Mathlib re-use.*  Built on our own `Walk` (`def_3_4`); mathlib's
--   `SimpleGraph.Walk` is for undirected single-channel graphs and
--   has no notion of directed-vs-bidirected edges or `J`/`V`
--   partition, so it cannot encode a CDMG walk.  Mathlib's
--   `SimpleGraph.IsAcyclic` forbids only undirected cycles of
--   length ≥ 3 — neither the LN's "directed walk" constraint nor
--   the self-loop case of length 1 fits.  Rolling our own
--   `IsAcyclic` on top of our own `Walk` is the only option that
--   stays close to the LN definition.
--
-- *Known limitations.*  (i) The rewritten tex spec's "Consequence:
--   no directed self-loops on output nodes" paragraph is *implied*
--   by `IsAcyclic` (a directed self-loop `(v, v) ∈ G.E` yields the
--   length-1 directed walk `Walk.cons v (v, v) _ (Walk.nil v _)`
--   from `v` to itself) but is not exposed as a separate field
--   here; it lives as a future lemma
--   `IsAcyclic G → ∀ v ∈ G.V, (v, v) ∉ G.E`.  Intentional:
--   `def_3_6` formalises the definition, not its corollaries.
--   (ii) Acyclicity is silent about *bidirected* self-loops
--   `(v, v) ∈ G.L`; those are already excluded by `def_3_1`'s
--   `hL_irrefl` at the foundational structure level, so no extra
--   constraint here is needed or wanted.  (iii) The predicate
--   lives in `Prop`, not as a `Decidable` instance — acyclicity is
--   decidable in principle (finite `G.J ∪ G.V`, finitely many
--   simple cycles to enumerate) but no current chapter consumes
--   such an instance, so the decidability plumbing is deferred to
--   the use site that needs it (e.g.\ causal-discovery algorithms
--   in chapters 11+).

end CDMG

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
