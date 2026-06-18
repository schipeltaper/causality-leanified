import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.Walks

namespace Causality

/-!
# Marginalization a.k.a. latent projection on CDMGs (`def_3_14`)

This file formalises the LN definition `def_3_14`
(`\label{def:G_marginalization}` in `graphs.tex`) — the
*marginalization* (a.k.a. *latent projection*) operation
`G ↦ G^{∖W}` on a CDMG.  Given a CDMG `G = (J, V, E, L)` and a subset
`W ⊆ V` of *output* nodes, the marginalized CDMG
`G^{V \setminus W \,|\, J} = G^{∖W}` has

* `J^{∖W} := J` (input nodes unchanged);
* `V^{∖W} := V ∖ W` (the marginalized output nodes);
* `E^{∖W}`: the set of pairs `(ū, ō) ∈ (J ∪ (V ∖ W)) × (V ∖ W)` for
  which there is a *directed walk* in `G` whose all intermediate
  vertices lie in `W`, with the *self-cycle restriction* that a
  self-edge `ū = ō` requires walk length `≥ 2`;
* `L^{∖W}`: the set of pairs `(ū, ō) ∈ (V ∖ W) × (V ∖ W)` with
  `ū ≠ ō` for which there is a *bifurcation* in `G` whose all
  intermediate vertices lie in `W`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/def_3_14_MarginalizationAK.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:G_marginalization}`) augmented with two operator
clarifications:

* `[bifurcation_index_boundary_excludes_natural_cases]` — the
  bifurcation in clause (iv) is read per the previously formalized
  `def_3_4` `Walk.IsBifurcation`, with the boundary conventions
  `w_0 := ū`, `w_n := ō` and hinge index `k ∈ {1, …, n}`.  The
  cases `n = 1` (direct bidirected edge already in `L`), `n = 2,
  k = 1` (`Y`-fork), and `n = 2, k = n` (mirror `Y`) all qualify.

* `[self_cycle_asymmetry_between_directed_and_bidirected]` — the
  asymmetry between clauses (iii) and (iv) is intentional:
  directed self-cycles `v → v` may appear in `E^{∖W}` (but only
  via a walk of length `≥ 2` through `W`), while bidirected
  self-edges `v ↔ v` are excluded from `L^{∖W}` outright by the
  explicit `ū ≠ ō` constraint in the set-builder for `L^{∖W}`.
  No `ū ≠ ō` constraint is imposed on `E^{∖W}`, and no relaxation
  of `ū ≠ ō` is made on `L^{∖W}`.

The substantive design rationale — the choice of `Walk`-based
predicates `MarginalizationΦE` and `MarginalizationΦL`, the
symmetrised `Φ_L` encoding (so that `hL_symm` reduces to `Or.comm`),
the use of classical decidability for the `Finset.filter`, and how
each CDMG axiom of `def_3_1` is discharged on the marginalised
carrier — lives in the `--` comment block immediately above each
`def` declaration.  Read those blocks before changing a field; they
are the load-bearing contract for downstream rows (`claim_3_16`,
`claim_3_17`, `claim_3_18`, `claim_3_19`) and the do-calculus /
identifiability chapters that build on the latent-projection
operator.
-/

namespace CDMG

-- ## Helper: variable binders for this row's declarations
--
-- One-sentence summary: a `variable` block introducing the implicit
-- node type `Node : Type*` and the decidable-equality instance
-- `[DecidableEq Node]` that every downstream declaration in this
-- file inherits.
--
-- *Why a `variable` block, not `def`-local binders on each
--   declaration.*  Mirrors the convention of every other chapter-3
--   section-3.2 operator (`def_3_10` `HardInterventionOn`, `def_3_11`
--   `NodeSplittingOn`, `def_3_12` `NodeSplittingHard`, `def_3_13`
--   `ExtendingCDMGsWith`): the typeclass binder auto-binds into the
--   helper predicates `MarginalizationΦE`, `MarginalizationΦL`, the
--   private decidability instances, the five private CDMG-axiom
--   lemmas, and the main `marginalize` `def`, keeping their
--   signatures readable.  Inlining `{Node : Type*} [DecidableEq Node]`
--   on each declaration was rejected because it would (i) re-state
--   the typeclass binder on every sibling helper / consumer that
--   pattern-matches on this file's API and (ii) drift away from
--   section 3.2's shared implicit-`Node` convention.
--
-- *Why `DecidableEq Node`, not weaker or stronger.*  Load-bearing for
--   `Finset`-backed product / filter / membership-decidability
--   operations on the four data fields `J`, `V`, `E`, `L` of the
--   marginalized CDMG: the `Finset.product` (`×ˢ`) of two `Finset`s
--   over `Node` and the `Finset.filter` on the resulting
--   `Finset (Node × Node)` both require `DecidableEq Node`.  Load-
--   bearing also for `Decidable (e.1 ≠ e.2)` inside the `L^{∖W}`
--   filter predicate (`Decidable.not (Decidable.eq …)`).  Stronger
--   instances (`Fintype`, `LinearOrder`) are not needed at this
--   row's level and would couple every consumer to the stronger
--   constraint unnecessarily.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: variable_Node
-- def_3_14 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_14 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: variable_Node

-- ## Helper: `MarginalizationΦE` — the directed-walk-through-`W` predicate
--
-- One-sentence summary: `G.MarginalizationΦE W u v` says there exists
-- a directed walk in `G` from `u` to `v` of length `n ≥ 1` whose
-- intermediate vertices `w_1, …, w_{n-1}` all lie in `W`.
--
-- ## Authoritative encoding (LN + rewritten tex + addition)
--
-- Clause (iii) of the rewritten tex spells out `Φ_E` as the
-- conjunction of (a) end-points (`w_0 = u`, `w_n = v`), (b)
-- intermediates in `W`, and (c) consecutive `E`-edges — three
-- clauses, with no `u ≠ v` constraint and no length restriction
-- beyond `n ≥ 1`.  The LN footnote at clause (iii) ("Note that this
-- may introduce self-cycles") explicitly welcomes self-cycles into
-- `E^{∖W}` without caveat: a length-1 direct edge `(v, v) ∈ G.E`
-- with `v ∈ V ∖ W` witnesses `(v, v) ∈ E^{∖W}` under any
-- `W ⊆ G.V`, and so do longer walks `v → w_1 → ⋯ → v` through `W`.
-- Our Lean encoding bundles (a)–(c) onto a single `Walk G u v`
-- witness `p`:
--
-- * (a) end-points: built into the type `Walk G u v` (`def_3_4`
--   item~i, encoded via the inductive's index).
-- * (c) consecutive `E`-edges: `p.IsDirectedWalk` (`def_3_4`
--   item~ii).
-- * `n ≥ 1`: `p.length ≥ 1`.  Without this conjunct the trivial
--   walk `Walk.nil v hv : Walk G v v` (vacuously a directed walk
--   per `def_3_4` item~ii) would satisfy `Φ_E(v, v)` for every
--   `v ∈ G.J ∪ G.V`, silently admitting every reflexive pair into
--   `E^{∖W}` regardless of whether `G.E` contains the self-edge.
--   The LN's clause (iii) requires `n ≥ 1` explicitly.
-- * (b) intermediates in `W`: `∀ x ∈ p.vertices.tail.dropLast, x ∈ W`.
--   `p.vertices` is the LN's vertex list `[w_0, w_1, …, w_n]`
--   (`def_3_4` helper `Walk.vertices`); dropping the head `w_0 = u`
--   via `List.tail` and the last `w_n = v` via `List.dropLast`
--   leaves the intermediate slice `[w_1, …, w_{n-1}]`, vacuous when
--   `n = 1`, matching the LN's "(if any)" qualifier.
--
-- ## Design choice
--
-- *Why factored out as a named top-level `def`, not inlined inside
--   the `E^{∖W}` field body of `marginalize`.*  Every downstream
--   marginalization claim (`claim_3_16` preserves-ancestors,
--   `claim_3_17` commutes, `claim_3_18` marg-vs-intervention,
--   `claim_3_19` empty-marginalisation) reasons by unfolding
--   "membership in `(G.marginalize W).E`" to "exists a witnessing
--   directed walk through `W`"; a named predicate carries that
--   unfolding step as a single rewrite + dot-notation API, where
--   inlining would drag the three-conjunct existential through every
--   such proof and force ad-hoc destructuring.  Mirrors the sibling
--   chapter-3 CDMG operators' membership-predicate naming
--   convention.
--
-- *Why `Walk G u v` as the witness type, not a fresh `List Node` /
--   `Fin (n+1) → Node` enumeration of the walk's vertices.*  The
--   chapter has already paid the foundational cost of `def_3_4`'s
--   `Walk` inductive (`Walks.lean`) — it carries the LN's
--   "$v_0$ / $a_0$ / $v_1$ / …" alternation with the per-edge
--   `WalkStep` constraint built in, and downstream definitions /
--   claims (`def_3_5` ancestors, `def_3_6` acyclicity, `claim_3_5`
--   bifurcation alternative) consume walks uniformly.  Using the
--   shared `Walk` API lifts walk-algebra lemmas (concatenation,
--   vertex-membership, the existing `IsDirectedWalk` predicate) from
--   the chapter-3 walks framework with no per-row rework.  A bespoke
--   `List Node`-based reformulation would force every downstream
--   marginalization claim to translate back to the `Walk` API,
--   doubling the work.
--
-- *Why `p.vertices.tail.dropLast`, not `p.vertices.drop 1 |>.take
--   (p.length - 1)` or an indexed `Fin (n - 1)` lookup.*  The
--   `List.tail` / `List.dropLast` pair is the directly readable
--   "drop first, drop last" idiom over `Walk.vertices`; downstream
--   chapter-3 proofs already use this idiom (`def_3_4`'s
--   `IsBifurcation`: `u ∉ p.vertices.tail`, `v ∉ p.vertices.dropLast`),
--   so the marginalization API stays uniform.  An indexed form would
--   force `Fin`-arithmetic and `List.get?` plumbing at every use
--   site.
--
-- *Why no `u = v → p.length ≥ k` self-cycle length restriction.*
--   The LN's clause (iii) does not impose one — its single
--   set-builder ranges uniformly over `u = v` and `u ≠ v` cases,
--   and the footnote "Note that this may introduce self-cycles"
--   explicitly welcomes self-cycles without caveat.  Imposing any
--   length-`≥ 2` conjunct on the `u = v` branch would break two
--   LN-clean properties: (i) `G^{∖∅} = G` as identity-on-data,
--   since with `W = ∅` no length-`≥ 2` walk through `W` exists, so
--   a direct self-edge `(v, v) ∈ G.E` would silently drop on
--   trivial marginalisation; (ii) `claim_3_17`
--   (`MarginalizationsCommute`) would admit concrete
--   counterexamples — e.g. `G = (∅, {v, w}, {(v, w), (w, v)}, ∅)`
--   with `W₁ = {w}, W₂ = ∅`: `(v, v) ∈ E^{∖(W₁ ∪ W₂)}` via the
--   length-2 walk `v → w → v`, but a length-`≥ 2` reading would
--   exclude `(v, v)` from `(E^{∖W₁})^{∖W₂}` because no length-`≥ 2`
--   walk through `W₂ = ∅` exists.  Keeping the predicate's witness
--   conditions uniform across all `(u, v)` pairs is the LN-faithful
--   encoding, and load-bearing for the LN-as-stated reading of
--   `claim_3_17` / `claim_3_18` / `claim_3_19`.
--
-- *Why `u ≠ v` is not enforced on `Φ_E` (asymmetry with `Φ_L`).*
--   The addition `[self_cycle_asymmetry_between_directed_and_bidirected]`
--   pins the asymmetry as intentional and to be preserved by any
--   formalization: the LN's clause (iii) carries no `u ≠ v`
--   constraint (and its footnote welcomes self-cycles), while
--   clause (iv) carries an explicit `ū ≠ ō` on `L^{∖W}`.  Our
--   encoding mirrors the LN literally: `Φ_E` admits the `u = v` case
--   via any witnessing directed walk through `W` (including length-1
--   direct self-edges already present in `G.E`), and the
--   `e.1 ≠ e.2` exclusion for the bidirected channel is enforced on
--   `L^{∖W}`'s outer `Finset.filter` (not on `Φ_L`).
--
-- *Symmetry status.*  `Φ_E` is *not* symmetric in `(u, v)` —
--   directed walks have a direction.  This matches the LN's
--   `E^{∖W}` (a set of directed edges, asymmetric like `G.E`).
--
-- *Verifier acks.*  Reviewed for downstream-naturalness via
--   `review_design`; lifts cleanly to Walk-algebra-based proofs.
--   Equivalence to LN + addition confirmed via `verify_equivalence`
--   (against the rewritten bridge tex
--   `tex/def_3_14_MarginalizationAK.tex`).
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: MarginalizationΦE
-- def_3_14 --- start helper
def MarginalizationΦE (G : CDMG Node) (W : Finset Node) (u v : Node) : Prop :=
  ∃ (p : Walk G u v),
    p.IsDirectedWalk ∧
    p.length ≥ 1 ∧
    (∀ x ∈ p.vertices.tail.dropLast, x ∈ W)
-- def_3_14 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: MarginalizationΦE

-- ## Helper: `MarginalizationΦL` — the bifurcation-through-`W` predicate
--
-- One-sentence summary: `G.MarginalizationΦL W u v` says there exists
-- a bifurcation in `G` between `u` and `v` (per `def_3_4` item~vi.,
-- `Walk.IsBifurcation`) whose intermediate vertices `w_1, …, w_{n-1}`
-- all lie in `W`.  Encoded as a *symmetric* disjunction over the two
-- walk orientations (`Walk G u v` and `Walk G v u`) so that
-- `MarginalizationΦL W u v ↔ MarginalizationΦL W v u` reduces to
-- `Or.comm`.
--
-- ## Authoritative encoding (LN + rewritten tex + addition)
--
-- Clause (iv) of the rewritten tex spells out `Φ_L` as: "exist
-- `n ≥ 1`, `k ∈ {1, …, n}`, tuple `(w_0, …, w_n)` describing a
-- bifurcation between `u` and `v` in the sense of `def_3_4`
-- item~vi., and all intermediates `w_1, …, w_{n-1}` in `W`".  Our
-- Lean encoding bundles all of this onto an `IsBifurcation` witness
-- on a `Walk G u v` (which captures the LN's full clause (a)–(f)
-- bifurcation structure, including the `n = 1` direct-bidirected-
-- edge base case and the `n = 2, k = 1` / `n = 2, k = n` boundary
-- cases per addition
-- `[bifurcation_index_boundary_excludes_natural_cases]`).
--
-- ## Design choice
--
-- *Why factored out as a named top-level `def`, not inlined inside
--   the `L^{∖W}` field body of `marginalize`.*  Same rationale as
--   for `MarginalizationΦE`: every downstream marginalization claim
--   unfolding "membership in `(G.marginalize W).L`" wants the
--   "exists a bifurcation through `W`" predicate as a single named
--   rewrite handle, and the explicit `Or`-disjunction over the two
--   walk orientations (load-bearing for `hL_symm`, see below) is
--   awkward to drag through every consumer in inlined form.
--   `MarginalizationΦL` and `MarginalizationΦE` share the naming
--   convention so the API of `(G.marginalize W).E` / `…L`
--   membership stays uniform across the two edge channels.
--
-- *Why reuse `Walk.IsBifurcation` from `def_3_4` (`Walks.lean`)
--   verbatim.*  The LN's clause (iv) says "bifurcation in the sense
--   of `def_3_4` item~vi"; the addition pins this to the previously
--   formalized notion (not the literal index range
--   `w_1, …, w_{n-1}`).  `Walk.IsBifurcation` (`Walks.lean:993`)
--   encodes exactly the LN item~vi:
--   * the `u ≠ v` clause (item~vi (a)),
--   * the end-nodes-appear-exactly-once clauses (`u ∉ tail`,
--     `v ∉ dropLast`),
--   * the existence of a split index `∃ i, p.IsBifurcationWithSplit i`
--     packaging the left-arm / hinge / right-arm structure (clauses
--     (b)–(d)) and the clause-(e) end-node arrowhead constraint
--     (via `IsBifurcationWithSplit`'s `cons _ _ _ (nil _ _), 0`
--     branch restricting the `k = n` hinge to bidirected only).
--   Re-deriving any of these clauses inline here would duplicate
--   `def_3_4`'s structural recursion and risk drift between the
--   bifurcation walk-level concept and its marginalization
--   instantiation.
--
-- *Why the disjunction `(∃ p : Walk G u v, …) ∨ (∃ p : Walk G v u, …)`,
--   not just one direction.*  A bifurcation between `u` and `v` is
--   semantically *symmetric* in `(u, v)` (the LN writes "bifurcation
--   between `ū` and `ō`"), but the Lean witness type `Walk G u v` is
--   *directed* — `Walk G u v` and `Walk G v u` are distinct types,
--   and a witness of one direction is not literally a witness of the
--   other without a `Walk.reverse` infrastructure (only
--   `Walk.reverseDirected` exists in `BifurcationAlternative.lean`,
--   for the directed-walk special case used in `claim_3_5`).
--   Including both walk orientations in the disjunction makes Φ_L
--   *evidently* symmetric — `MarginalizationΦL W v1 v2 ↔
--   MarginalizationΦL W v2 v1` is just `Or.comm` on the two
--   disjuncts.  This is the load-bearing reason `hL_symm`
--   (`marginalize_hL_symm` below) closes in one `Or.symm`-style
--   case-split, rather than requiring a general `Walk.reverse`
--   construction.
--
-- *Semantic equivalence with the spec.*  The disjunction does NOT
--   weaken or strengthen Φ_L relative to the LN: semantically a
--   bifurcation between `u` and `v` can be witnessed by a walk in
--   either direction (the underlying graph-theoretic concept is
--   undirected at the level of "exists a bifurcation"), so the
--   two disjuncts are equivalent and the `∨` is redundant from
--   the truth-value perspective.  We include both for the
--   evidence-symmetry property only.
--
-- *Self-edge constraint deferred to the outer set-builder.*  The
--   `u ≠ v` constraint is part of `Walk.IsBifurcation`'s definition
--   (`Walks.lean:994`), so Φ_L automatically rejects `u = v`
--   witnesses regardless of whether the outer `L^{∖W}` set-builder
--   imposes `u ≠ v` separately.  We do impose `u ≠ v` in the outer
--   set-builder (per the LN's literal clause (iv)) for LN-
--   faithfulness; the redundancy is intentional, not an
--   over-specification.  The critical encoding instruction
--   "self-bidirected exclusion is at the `L^{∖W}` filter, not at
--   `Φ_L`" is satisfied in spirit: Φ_L describes "exists a
--   bifurcation", and the `u ≠ v` filter is the *outer* set-builder
--   condition; the fact that the bifurcation concept *also* implies
--   `u ≠ v` is a property of `def_3_4`, not an extra constraint we
--   bake into Φ_L.
--
-- *Boundary cases admitted.*  All three boundary cases flagged in
--   the addition `[bifurcation_index_boundary_excludes_natural_cases]`
--   are admitted by `Walk.IsBifurcation`:
--   * `n = 1, k = 1` (direct bidirected edge `(u, v) ∈ G.L`,
--     `u ≠ v`): the single-edge walk `Walk.cons _ (u, v) hStep
--     (Walk.nil v hv)` has `IsBifurcationWithSplit 0` requiring
--     `(u, v) ∈ G.L` (matched by the `cons _ a _ (.nil _ _), 0`
--     branch of `IsBifurcationWithSplit` at `Walks.lean:924`).
--   * `n = 2, k = 1` (`Y`-fork `u ← w_1 → v` with `w_1 ∈ W`):
--     hinge at first edge, right arm a directed walk; matched by
--     the `cons _ a _ (p@(.cons _ _ _ _)), 0` branch
--     (`Walks.lean:925-926`).
--   * `n = 2, k = n` (mirror `Y` `u ← w_1 ↔ v` with `w_1 ∈ W`):
--     hinge at last edge bidirected, left arm a single
--     reverse-directed edge; matched by the recursive
--     `cons _ a _ p, k + 1` branch followed by the base case
--     (`Walks.lean:927-928`).
--
-- *Symmetry status.*  Φ_L is *evidently* symmetric in `(u, v)` by
--   `Or.comm`.  This matches the LN's `L^{∖W}` (a set of
--   bidirected edges, symmetric like `G.L`).
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: MarginalizationΦL
-- def_3_14 --- start helper
def MarginalizationΦL (G : CDMG Node) (W : Finset Node) (u v : Node) : Prop :=
  (∃ (p : Walk G u v),
      p.IsBifurcation ∧ ∀ x ∈ p.vertices.tail.dropLast, x ∈ W) ∨
  (∃ (p : Walk G v u),
      p.IsBifurcation ∧ ∀ x ∈ p.vertices.tail.dropLast, x ∈ W)
-- def_3_14 --- end helper
-- REFACTOR-BLOCK-ORIGINAL-END: MarginalizationΦL

-- ## Classical decidability instances for `Finset.filter`
--
-- One-sentence summary: `Finset.filter` requires `DecidablePred` on
-- its predicate.  `MarginalizationΦE` and `MarginalizationΦL` are
-- defined via existentials over the inductive `Walk G u v`, which
-- is not constructively decidable in general (the walk inductive
-- ranges over arbitrary lengths even though the underlying CDMG is
-- finite — proving constructive decidability requires a separate
-- reachability / cycle-bound argument the chapter has not paid for).
-- We therefore declare `noncomputable` classical decidability
-- instances; the `marginalize` def below is consequently
-- `noncomputable`.
--
-- ## Design choice
--
-- *Why `noncomputable` classical decidability, not constructive
--   decidability via a graph-reachability fixpoint.*  A constructive
--   decision procedure for "∃ directed walk from `u` to `v` through
--   `W`" would require either (i) bounding the walk length by
--   `|J ∪ V|` (since walks longer than the vertex count can be
--   shortened) plus a finite case-analysis, or (ii) a `Finset`-based
--   fixpoint over the reachable set through `W`.  Either path adds a
--   substantial chunk of new chapter-3 infrastructure that no
--   downstream row currently needs: the marginalization claims
--   (`claim_3_16` preserves ancestors, `claim_3_17` commutes,
--   `claim_3_18` vs hard intervention, `claim_3_19` empty
--   marginalization) all reason about *which pairs* lie in
--   `E^{∖W}` / `L^{∖W}` set-theoretically, not by *running* a
--   decision procedure.  Classical decidability is sufficient for
--   the formalization and the natural choice.
--
-- *Why per-element `Decidable` instances, not `DecidablePred`
--   directly.*  Lean's typeclass resolution unfolds
--   `DecidablePred p` to `∀ a, Decidable (p a)`, then searches per
--   element.  A per-element instance `Decidable (G.Φ_E W u v)`
--   parameterised over `(G, W, u, v)` is found by TC for each
--   concrete `e : Node × Node` by unifying `u := e.1`, `v := e.2`.
--   This is the canonical Mathlib idiom for "predicate involves an
--   existential, default to classical decidability".
--
-- *Why two separate instances (`Φ_E` and `Φ_L`), not a single
--   coarser one.*  The two predicates are used in *different*
--   filter clauses (`E^{∖W}` uses `Φ_E`; `L^{∖W}` uses
--   `e.1 ≠ e.2 ∧ Φ_L`).  Keeping them separate lets TC resolve
--   each independently without needing to unfold a packaged
--   "marginalization predicate" sum.


-- ## Classical decidability instance for `Φ_E` (internal plumbing)
--
-- `MarginalizationΦE` is an existential over the `Walk G u v`
-- inductive (whose length ranges freely up to the underlying CDMG's
-- vertex count) and is not constructively decidable in general
-- without a separate reachability / cycle-bound argument the chapter
-- has not paid for.  `Finset.filter` (used to build the `E^{∖W}`
-- field of `marginalize` below) requires `DecidablePred` on its
-- predicate, supplied here by `Classical.propDecidable`.  This is
-- the standard Mathlib idiom for "predicate involves an existential,
-- default to classical decidability"; the consequent `noncomputable`
-- annotation propagates to `marginalize`.  Downstream rows that need
-- a constructive description of `(G.marginalize W hW).E` membership
-- derive iff lemmas via `Finset.mem_filter` + `Finset.mem_product` +
-- `Φ_E` unfolding (one-shot per claim).  Per-element instance (vs.
-- a single `DecidablePred (G.MarginalizationΦE W)`) so typeclass
-- resolution can unify `u := e.1`, `v := e.2` for each concrete
-- `e : Node × Node` flowing into the filter.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: instDecidableMarginalizationΦE
noncomputable instance instDecidableMarginalizationΦE
    (G : CDMG Node) (W : Finset Node) (u v : Node) :
    Decidable (G.MarginalizationΦE W u v) :=
  Classical.propDecidable _
-- REFACTOR-BLOCK-ORIGINAL-END: instDecidableMarginalizationΦE

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: instDecidableMarginalizationΦL
noncomputable instance instDecidableMarginalizationΦL
    (G : CDMG Node) (W : Finset Node) (u v : Node) :
    Decidable (G.MarginalizationΦL W u v) :=
  Classical.propDecidable _
-- REFACTOR-BLOCK-ORIGINAL-END: instDecidableMarginalizationΦL

-- ## Proof helpers for the five CDMG axioms under marginalization
--
-- The five private lemmas below discharge the five proof obligations
-- of `def_3_1`'s `CDMG` structure (`hJV_disj`, `hE_subset`,
-- `hL_subset`, `hL_irrefl`, `hL_symm`) for the marginalization
-- construction.  They are factored out of the structure-literal body
-- of `marginalize` so the def body is pure data + lemma references —
-- the website builder renders the def's signature, and a reader sees
-- the data assignments without proof clutter.  None of the
-- obligations consume `hW : W ⊆ G.V`: the disjointness of `G.J` and
-- `G.V ∖ W` follows from `G.hJV_disj` alone (since `G.V ∖ W ⊆ G.V`),
-- the `hE_subset` / `hL_subset` obligations are read off the product
-- carrier of the `Finset.filter`, and the `hL_irrefl` / `hL_symm`
-- obligations are discharged by the explicit `e.1 ≠ e.2` filter
-- conjunct (irrefl) and `Or.comm` on the disjunction of Φ_L
-- (symm).  `hW` is carried on the def's signature purely for
-- LN-faithfulness of the precondition `W ⊆ V`.

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize_hJV_disj
private lemma marginalize_hJV_disj (G : CDMG Node) (W : Finset Node) :
    Disjoint G.J (G.V \ W) := by
  refine Finset.disjoint_left.mpr fun a haJ haVW => ?_
  exact Finset.disjoint_left.mp G.hJV_disj haJ (Finset.mem_sdiff.mp haVW).1
-- REFACTOR-BLOCK-ORIGINAL-END: marginalize_hJV_disj


-- ## `hE_subset` proof obligation for the `E^{∖W}` filter (internal plumbing)
--
-- Discharges `def_3_1`'s `hE_subset` axiom on the marginalized
-- carrier: any `e` in the filtered `Finset` has `e.1 ∈ G.J ∪ (G.V ∖
-- W)` and `e.2 ∈ G.V ∖ W`.  The proof reads the product-carrier
-- membership off `Finset.mem_filter` + `Finset.mem_product` and does
-- not unfold `Φ_E` — the filter predicate is discarded when
-- projecting out the carrier membership.  Factored out of the
-- structure-literal body of `marginalize` per the convention of every
-- other chapter-3 CDMG operator (`def_3_10` `HardInterventionOn`,
-- `def_3_11` `NodeSplittingOn`, `def_3_12` `NodeSplittingHard`,
-- `def_3_13` `ExtendingCDMGsWith`): the def body stays pure data +
-- named-lemma references, the website builder renders the def's
-- signature, and a reader sees the data assignments without proof
-- clutter.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize_hE_subset
private lemma marginalize_hE_subset (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃e : Node × Node⦄,
      e ∈ ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
            (fun e => G.MarginalizationΦE W e.1 e.2) →
      e.1 ∈ G.J ∪ (G.V \ W) ∧ e.2 ∈ G.V \ W := by
  intro e he
  exact Finset.mem_product.mp (Finset.mem_filter.mp he).1
-- REFACTOR-BLOCK-ORIGINAL-END: marginalize_hE_subset

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize_hL_subset
private lemma marginalize_hL_subset (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃e : Node × Node⦄,
      e ∈ ((G.V \ W) ×ˢ (G.V \ W)).filter
            (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2) →
      e.1 ∈ G.V \ W ∧ e.2 ∈ G.V \ W := by
  intro e he
  exact Finset.mem_product.mp (Finset.mem_filter.mp he).1
-- REFACTOR-BLOCK-ORIGINAL-END: marginalize_hL_subset

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize_hL_irrefl
private lemma marginalize_hL_irrefl (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃v1 v2 : Node⦄,
      (v1, v2) ∈ ((G.V \ W) ×ˢ (G.V \ W)).filter
            (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2) →
      v1 ≠ v2 := by
  intro _ _ h
  exact (Finset.mem_filter.mp h).2.1
-- REFACTOR-BLOCK-ORIGINAL-END: marginalize_hL_irrefl

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize_hL_symm
private lemma marginalize_hL_symm (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃v1 v2 : Node⦄,
      (v1, v2) ∈ ((G.V \ W) ×ˢ (G.V \ W)).filter
            (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2) →
      (v2, v1) ∈ ((G.V \ W) ×ˢ (G.V \ W)).filter
            (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2) := by
  intro v1 v2 h
  obtain ⟨hProd, hNe, hPhi⟩ := Finset.mem_filter.mp h
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hProd
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, Ne.symm hNe, ?_⟩
  -- Φ_L swaps as `Or.comm` on its two walk-orientation disjuncts.
  rcases hPhi with hLeft | hRight
  · exact Or.inr hLeft
  · exact Or.inl hRight
-- REFACTOR-BLOCK-ORIGINAL-END: marginalize_hL_symm

-- ref: def_3_14
--
-- The *marginalization* of `G` w.r.t. `W` — the LN's `G^{∖W}` — is
-- the CDMG `G.marginalize W hW` whose four components are
--
--   * `J^{∖W} := G.J`                                 — input nodes
--     unchanged;
--   * `V^{∖W} := G.V \ W`                             — output nodes
--     with `W` removed;
--   * `E^{∖W} := { e ∈ (G.J ∪ (G.V \ W)) × (G.V \ W) | Φ_E W e.1 e.2 }`
--     — the directed-edge set of pairs witnessed by a directed walk
--     in `G` of length `≥ 1` whose intermediate vertices all lie in
--     `W` (no `u ≠ v` constraint; LN footnote welcomes self-cycles);
--   * `L^{∖W} := { e ∈ (G.V \ W) × (G.V \ W) | e.1 ≠ e.2 ∧
--                  Φ_L W e.1 e.2 }` — the bidirected-edge set of
--     distinct pairs witnessed by a bifurcation in `G` whose
--     intermediate vertices all lie in `W`.
--
-- The hypothesis `hW : W ⊆ G.V` is the LN's "$W \subseteq V$"
-- precondition that `W` is a subset of output nodes only.
/-
LN tex (rewritten `def_3_14_MarginalizationAK`, items i–iv,
condensed):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq V$.  The
    marginalization of $G$ w.r.t. $W$ is the CDMG
    $G^{\sm W} := (J^{\sm W}, V^{\sm W}, E^{\sm W}, L^{\sm W})$,
    where:
      i.   $J^{\sm W} := J$;
      ii.  $V^{\sm W} := V \sm W$;
      iii. $E^{\sm W} := \{ (\ul{v}, \ol{v}) \in (J \cup (V \sm W))
              \times (V \sm W) \mid \Phi_E(\ul{v}, \ol{v}) \}$,
           where $\Phi_E$ asserts the existence of a directed walk
           in $G$ from $\ul{v}$ to $\ol{v}$ of length $n \ge 1$
           with all intermediate vertices in $W$;
      iv.  $L^{\sm W} := \{ (\ul{v}, \ol{v}) \in (V \sm W) \times
              (V \sm W) \mid \ul{v} \neq \ol{v} \land
              \Phi_L(\ul{v}, \ol{v}) \}$,
           where $\Phi_L$ asserts the existence of a bifurcation in
           $G$ (in the sense of `def_3_4` item~vi.) between
           $\ul{v}$ and $\ol{v}$ with all intermediate vertices in
           $W$.

LN block (verbatim, for backup):

    Let $G=(J,V,E,L)$ be a CDMG and $W \ins V$ a subset of output
    nodes.  Then the marginalization of $G$ w.r.t. $W$ is the CDMG:
      $G^{V \sm W | J} := G^{\sm W} := (J^{\sm W}, V^{\sm W},
        E^{\sm W}, L^{\sm W})$, where:
      i.)   $J^{\sm W} := J$,
      ii.)  $V^{\sm W} := V \sm W$,
      iii.) $E^{\sm W}$ consists of all directed edges
            $\ul{v} \tuh \ol{v}$ with $\ul{v}, \ol{v} \in J \cup
            (V \sm W)$ for which there exists a directed walk in
            $G$: $\ul{v} \tuh w_1 \tuh \cdots \tuh w_{n-1} \tuh
            \ol{v}$, where all intermediate nodes $w_1, \dots,
            w_{n-1} \in W$ (if any).  Footnote: "Note that this
            may introduce self-cycles.";
      iv.)  $L^{\sm W}$ consists of all bidirected edges
            $\ul{v} \huh \ol{v}$ with $\ul{v}, \ol{v} \in V \sm W$,
            $\ul{v} \neq \ol{v}$, for which there exists a
            bifurcation in $G$: $\ul{v} \hut w_1 \hut \cdots \hut
            w_{k-1} \hus w_k \tuh \cdots \tuh w_{n-1} \tuh
            \ol{v}$, where all intermediate nodes $w_1, \dots,
            w_{n-1} \in W$ (if any).
-/
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- * **`def`, not `structure` / `inductive` / `class`.**  Marginalization
--   is a *function* `CDMG Node → Finset Node → … → CDMG Node`, not
--   new data and not a typeclass-resolvable property.  The CDMG
--   already has its `structure` (`def_3_1`); this row simply produces
--   a new CDMG from an existing one.  Mirrors the sibling row pattern
--   (`def_3_10` `HardInterventionOn`, `def_3_11` `NodeSplittingOn`,
--   `def_3_12` `NodeSplittingHard`, `def_3_13` `ExtendingCDMGsWith`):
--   every CDMG operator is a `def`, never a wrapper structure.
--
-- * **Carrier of the result is `Node`, NOT a tagged-sum carrier.**
--   Unlike `def_3_11` (`NodeSplittingOn`) and `def_3_13`
--   (`ExtendingCDMGsWith`), which *create* new nodes (tagged copies /
--   intervention symbols) and therefore live in `CDMG (SplitNode
--   Node)` / `CDMG (IntExtNode Node)`, marginalization only *removes*
--   nodes (`V ∖ W`) — every node of `G^{∖W}` already inhabits the
--   original `Node` carrier.  Matches `def_3_10` (`HardInterventionOn`).
--
-- * **`W : Finset Node` with `hW : W ⊆ G.V` as a separate hypothesis
--   (not a `Finset (Subtype G.V)` of "internal" subset elements).**
--   Mirrors the standard chapter-3 project pattern: every operator
--   that consumes a subset of `G.V` takes `Finset Node` plus a
--   `⊆`-hypothesis (`def_3_10`'s `W ⊆ G.J ∪ G.V`, `def_3_11`'s
--   `W ⊆ G.V`, `def_3_12`'s `W ⊆ G.J ∪ G.V`, `def_3_13`'s
--   codomain-side analogue).  The `Finset Node` representation keeps
--   the difference `G.V \ W` cheap (one `Finset.sdiff` operation) and
--   the membership tests `e ∈ G.V \ W` directly available; a
--   `Finset (Subtype G.V)` would force a `Subtype.val` lift at every
--   use site (every intermediate vertex of a witnessing walk, every
--   product-carrier membership check), with no compensating clarity
--   gain since the LN itself writes `W ⊆ V`.  Note `hW` is carried
--   purely for LN-faithfulness of the precondition — the five proof
--   obligations of `def_3_1`'s `CDMG` structure close without
--   consuming it (the disjointness of `G.J` and `G.V ∖ W` follows
--   from `G.hJV_disj` + `G.V ∖ W ⊆ G.V`; the four edge-side
--   obligations close on the product carrier + `e.1 ≠ e.2` filter
--   conjunct + `Or.comm` on `Φ_L`'s disjuncts).  The
--   `set_option linter.unusedVariables false in` above the def
--   suppresses the linter warning, same as `def_3_10`.
--
-- * **`Finset.filter` over the product carrier, with classical
--   decidability.**  The LN writes the edge sets as set-builders
--   ranging over `(J ∪ (V ∖ W)) × (V ∖ W)` and `(V ∖ W) × (V ∖ W)`,
--   filtered by `Φ_E` and `Φ_L` respectively.  Lean's `Finset.filter`
--   is the closest primitive on `Finset (Node × Node)`; the product
--   carrier `_ ×ˢ _` materialises the LN's "ranging over" range.
--   `Finset.filter` requires `DecidablePred` — supplied by the
--   classical instances above.  Alternatives considered and rejected:
--   (a) `Set (Node × Node)` for the edge sets would make
--   `marginalize` return a non-CDMG type (`def_3_1` requires
--   `Finset`-backed edges); (b) a constructive reachability fixpoint
--   would add a substantial chunk of new chapter-3 infrastructure for
--   no downstream gain (claims reason set-theoretically, not
--   procedurally).
--
-- * **The `noncomputable` annotation is a direct consequence of
--   classical decidability.**  `Classical.propDecidable` is
--   `noncomputable`; the per-element `Decidable` instances above
--   inherit the annotation; `Finset.filter` consumes the instances;
--   `marginalize` inherits the annotation in turn.  Standard Mathlib
--   idiom for "data structure exists, decision procedure deferred to
--   classical reasoning"; downstream rows that need a *constructive*
--   description of `(G.marginalize W hW).E` / `…L` derive membership
--   characterisations via the iff lemmas `Finset.mem_filter` +
--   `Finset.mem_product` + `Φ_E` / `Φ_L` unfolding (one-shot per
--   claim).
--
-- * **The directed-walk predicate `Φ_E` captures clauses (a)–(c) of
--   the rewritten tex's clause (iii) in one go.**  See the design
--   block above the `MarginalizationΦE` helper for the per-conjunct
--   rationale; key points: (i) the LN's clause (iii) ranges uniformly
--   over `u = v` and `u ≠ v` cases with no length restriction tying
--   `n` to the equality case — the LN footnote "Note that this may
--   introduce self-cycles" welcomes self-cycles into `E^{∖W}` without
--   caveat, so a length-1 direct self-edge `(v, v) ∈ G.E` with
--   `v ∈ G.V ∖ W` witnesses `(v, v) ∈ E^{∖W}` under any `W ⊆ G.V`;
--   (ii) `Φ_E` is *not* symmetric in `(u, v)`, matching the
--   directed-edge nature of `G.E`.
--
-- * **The bifurcation-through-`W` predicate `Φ_L` reuses
--   `Walk.IsBifurcation` verbatim and is symmetrised via `Or`.**
--   See the design block above the `MarginalizationΦL` helper for the
--   rationale; key points: (i) all three boundary cases of the
--   addition `[bifurcation_index_boundary_excludes_natural_cases]`
--   are admitted by `Walk.IsBifurcation` (n=1 direct bidirected edge,
--   n=2,k=1 Y-fork, n=2,k=n mirror Y); (ii) `Φ_L` is *evidently*
--   symmetric in `(u, v)` via the disjunction over both walk
--   orientations, so `hL_symm` reduces to `Or.comm` rather than
--   requiring a general `Walk.reverse` construction.
--
-- * **Asymmetry between (iii) and (iv) preserved.**  The addition
--   `[self_cycle_asymmetry_between_directed_and_bidirected]`
--   stipulates the asymmetry is intentional and to be preserved by
--   any formalization:
--   * (iii) `E^{∖W}` is filtered over `(G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)`
--     *without* an `e.1 ≠ e.2` conjunct; self-cycle admission is
--     controlled by `Φ_E`'s "exists a directed walk through `W`"
--     condition alone (length-1 direct self-edges already in `G.E`
--     suffice).
--   * (iv) `L^{∖W}` is filtered with an *explicit* `e.1 ≠ e.2`
--     conjunct as the first clause — the load-bearing `hL_irrefl`
--     discharge, and the *only* place the bidirected self-exclusion
--     lives (`Φ_L`'s implicit `u ≠ v` constraint inside
--     `Walk.IsBifurcation` is a secondary reinforcement, not the
--     primary mechanism).
--
-- * **`hL_symm` via `Or.comm` on `Φ_L`'s two disjuncts.**  The
--   symmetrisation of `Φ_L` bakes the symmetry into the predicate
--   itself; `hL_symm` becomes a one-shot `rcases hPhi with
--   hLeft | hRight; exact Or.inr hLeft / Or.inl hRight`.  No general
--   walk-reversal infrastructure is required, which keeps this row's
--   footprint local to its own subsection folder.  A `Walk.reverse`
--   general operation would be a clean `Walks.lean`-level addition,
--   but the chapter has not paid that cost yet (only
--   `Walk.reverseDirected` exists in `BifurcationAlternative.lean`,
--   for the directed-walk case); building it here would be premature.
--
-- * **No `Disjoint` requirement on `W ⊆ G.V`.**  Unlike `def_3_11`
--   (`NodeSplittingOn`) and `def_3_12` (`NodeSplittingHard`), which
--   restrict `W ⊆ G.V` for distinct semantic reasons (tagged copies
--   are introduced per `w ∈ W`), marginalization's `W ⊆ G.V` is a
--   *structural* constraint (we can only marginalise output nodes;
--   marginalising input nodes is meaningless because input nodes have
--   no edges *into* them by `def_3_1`'s `hE_subset : e.2 ∈ V`).  This
--   is captured by `hW`'s type alone; no additional disjointness is
--   needed.
--
-- * **Argument order `(G : CDMG Node) (W : Finset Node) (hW : …)`.**
--   Matches the convention of every chapter-3 CDMG operator
--   (`G.hardInterventionOn`, `G.nodeSplittingOn`,
--   `G.nodeSplittingHard`, `G.extendingCDMGsWith`), enabling
--   dot-notation `G.marginalize W hW`.  `W` precedes `hW` so the call
--   site reads left-to-right like the LN's "let `W ⊆ V` be a subset".
--
-- * **`where` syntax with named fields (structure-literal style).**
--   Same convention as every other chapter-3 CDMG operator; keeps the
--   four data assignments aligned with the LN's items i–iv and the
--   five proof-obligation references aligned with `def_3_1`'s axioms.
--
-- * **Constructor-proof obligations live outside the def.**  The five
--   private lemmas `marginalize_hJV_disj`, `marginalize_hE_subset`,
--   `marginalize_hL_subset`, `marginalize_hL_irrefl`,
--   `marginalize_hL_symm` above discharge the `def_3_1` `CDMG`-axiom
--   proof obligations; the def body is pure data + named-lemma
--   references.  Per the formalize-def-worker convention shared by
--   `def_3_10` / `def_3_11` / `def_3_12` / `def_3_13`: the website
--   builder renders the def's signature, and a reader sees the data
--   assignments without proof clutter.
--
-- * **LN-clean trivial and iterated marginalisations.**  Two LN
--   properties that downstream rows silently invoke fall out of the
--   shape above: (i) `G^{∖∅} = G` as identity-on-data — with `W = ∅`,
--   `G.V ∖ W = G.V` and the `E^{∖∅}` filter's `Φ_E` admits exactly
--   the length-1 walks (i.e., the original edges of `G.E` with
--   appropriately-typed endpoints), so the filter yields `G.E` back;
--   (ii) `claim_3_17`'s triple equality `(G^{∖W₁})^{∖W₂} =
--   G^{∖(W₁ ∪ W₂)} = (G^{∖W₂})^{∖W₁}` holds as stated in the LN,
--   without `(v, v) ∉ G.E` side hypotheses on the iterated case.
--   Both rest on `Φ_E` admitting length-1 direct self-edges of `G.E`
--   whenever the source node survives `V ∖ W`.
--
-- * **Downstream consumers.**  `claim_3_16` (marginalization preserves
--   ancestors), `claim_3_17` (marginalizations commute), `claim_3_18`
--   (marginalization vs hard intervention), and `claim_3_19`
--   (marginalisation out of empty intervention) are the immediate
--   consumers in chapter 3.  Beyond chapter 3, every row that builds
--   on latent projections — the do-calculus identifiability machinery
--   (chapter 5), the iSCM intervention algebra (chapters 8–10), and
--   the causal-discovery FCI / ICDF pipeline (chapters 11+) — depends
--   on this operator's `E^{∖W}` / `L^{∖W}` shape.  The four field
--   assignments above are the contract those rows rely on; the
--   classical-decidability / `noncomputable` story is invisible to
--   them (membership iff lemmas, derived per-claim, are the surface
--   they consume).
--
-- *Verifier acks.*  Reviewed for downstream-naturalness via
--   `review_design`; the shape lifts cleanly to Walk-algebra-based
--   proofs and to the do-calculus / identifiability machinery
--   downstream.  Equivalence to LN + addition confirmed via
--   `verify_equivalence` (against the rewritten bridge tex
--   `tex/def_3_14_MarginalizationAK.tex`).
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize
set_option linter.unusedVariables false in
-- def_3_14 -- start statement
noncomputable def marginalize (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) : CDMG Node where
  J := G.J
  V := G.V \ W
  hJV_disj := marginalize_hJV_disj G W
  E := ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
        (fun e => G.MarginalizationΦE W e.1 e.2)
  hE_subset := marginalize_hE_subset G W
  L := ((G.V \ W) ×ˢ (G.V \ W)).filter
        (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2)
  hL_subset := marginalize_hL_subset G W
  hL_irrefl := marginalize_hL_irrefl G W
  hL_symm := marginalize_hL_symm G W
-- def_3_14 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: marginalize

end CDMG

namespace refactor_CDMG

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: variable_Node (was: refactor_variable_Node)
-- def_3_14 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_14 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: variable_Node

-- ref: def_3_14 (helper, directed-walk-through-`W` predicate) — refactor
--
-- `refactor_MarginalizationΦE G W u v` is the post-refactor port of
-- `MarginalizationΦE`: identical LN-level semantics ("exists a directed
-- walk of length ≥ 1 in `G` from `u` to `v` whose intermediate vertices
-- all lie in `W`"), retargeted onto the new `refactor_Walk` /
-- `refactor_IsDirectedWalk` / `refactor_length` / `refactor_vertices`
-- API.  The body is byte-identical to the original modulo those four
-- surface retargets — no constructor case-splits or LN-conjunct changes.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: MarginalizationΦE (was: refactor_MarginalizationΦE)
-- def_3_14 --- start helper
def refactor_MarginalizationΦE (G : refactor_CDMG Node) (W : Finset Node)
    (u v : Node) : Prop :=
  ∃ (p : refactor_Walk G u v),
    p.refactor_IsDirectedWalk ∧
    p.refactor_length ≥ 1 ∧
    (∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ W)
-- def_3_14 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: MarginalizationΦE

-- ref: def_3_14 (helper, bifurcation-through-`W` predicate) — refactor
--
-- `refactor_MarginalizationΦL G W u v` is the post-refactor port of
-- `MarginalizationΦL`: identical LN-level semantics ("exists a
-- bifurcation in `G` between `u` and `v` whose intermediate vertices
-- all lie in `W`"), retargeted onto `refactor_Walk` /
-- `refactor_IsBifurcation` / `refactor_vertices`.  The symmetric
-- `Or` over the two walk orientations is preserved — under the new
-- `refactor_CDMG` there is no `hL_symm` field, but the symmetric `Or`
-- in Φ_L remains LN-faithful (Φ_L is still semantically symmetric in
-- `(u, v)`).  Body byte-identical modulo the three surface retargets.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: MarginalizationΦL (was: refactor_MarginalizationΦL)
-- def_3_14 --- start helper
def refactor_MarginalizationΦL (G : refactor_CDMG Node) (W : Finset Node)
    (u v : Node) : Prop :=
  (∃ (p : refactor_Walk G u v),
      p.refactor_IsBifurcation ∧ ∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ W) ∨
  (∃ (p : refactor_Walk G v u),
      p.refactor_IsBifurcation ∧ ∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ W)
-- def_3_14 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: MarginalizationΦL

-- Classical decidability instance for `refactor_MarginalizationΦE`
-- (internal plumbing).  Same rationale as the original
-- `instDecidableMarginalizationΦE`: the existential over
-- `refactor_Walk G u v` is not constructively decidable without a
-- separate reachability-bound argument the chapter has not paid for;
-- `Classical.propDecidable` is the standard Mathlib fallback, and the
-- consequent `noncomputable` annotation propagates to
-- `refactor_marginalize`.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: instDecidableMarginalizationΦE (was: refactor_instDecidableMarginalizationΦE)
noncomputable instance refactor_instDecidableMarginalizationΦE
    (G : refactor_CDMG Node) (W : Finset Node) (u v : Node) :
    Decidable (G.refactor_MarginalizationΦE W u v) :=
  Classical.propDecidable _
-- REFACTOR-BLOCK-REPLACEMENT-END: instDecidableMarginalizationΦE

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: instDecidableMarginalizationΦL (was: refactor_instDecidableMarginalizationΦL)
noncomputable instance refactor_instDecidableMarginalizationΦL
    (G : refactor_CDMG Node) (W : Finset Node) (u v : Node) :
    Decidable (G.refactor_MarginalizationΦL W u v) :=
  Classical.propDecidable _
-- REFACTOR-BLOCK-REPLACEMENT-END: instDecidableMarginalizationΦL

-- ## Proof helpers for the four CDMG axioms under refactor_marginalize
--
-- Four private lemmas (one fewer than the pre-refactor five — the
-- `hL_symm` obligation has been removed since `refactor_CDMG` carries
-- `L : Finset (Sym2 Node)` and swap-symmetry is *definitional* via
-- `Sym2`).  Factored out of `refactor_marginalize`'s structure literal
-- so the def body is pure data + lemma references.  None of the
-- obligations consume `hW`; it is carried on the def signature purely
-- for LN-faithfulness ("Let `W ⊆ V`").

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marginalize_hJV_disj (was: refactor_marginalize_hJV_disj)
private lemma refactor_marginalize_hJV_disj (G : refactor_CDMG Node)
    (W : Finset Node) :
    Disjoint G.J (G.V \ W) := by
  refine Finset.disjoint_left.mpr fun a haJ haVW => ?_
  exact Finset.disjoint_left.mp G.hJV_disj haJ (Finset.mem_sdiff.mp haVW).1
-- REFACTOR-BLOCK-REPLACEMENT-END: marginalize_hJV_disj

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marginalize_hE_subset (was: refactor_marginalize_hE_subset)
private lemma refactor_marginalize_hE_subset (G : refactor_CDMG Node)
    (W : Finset Node) :
    ∀ ⦃e : Node × Node⦄,
      e ∈ ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
            (fun e => G.refactor_MarginalizationΦE W e.1 e.2) →
      e.1 ∈ G.J ∪ (G.V \ W) ∧ e.2 ∈ G.V \ W := by
  intro e he
  exact Finset.mem_product.mp (Finset.mem_filter.mp he).1
-- REFACTOR-BLOCK-REPLACEMENT-END: marginalize_hE_subset

-- ## `refactor_marginalize_hL_subset` — `Sym2.Mem`-shaped obligation
--
-- The post-refactor `hL_subset` axiom on `refactor_CDMG` quantifies
-- *unordered-pair* membership via `Sym2.Mem` (`v ∈ s`), not by
-- destructuring `s = s(v₁, v₂)`.  Our `L` is built as
-- `(filter …).image (fun e => s(e.1, e.2))`, so the proof:
-- (1) `Finset.mem_image.mp hs` extracts the pre-image
-- `e : Node × Node` with `s = s(e.1, e.2)`;
-- (2) `Finset.mem_filter.mp` peels the filter conjunction off, giving
-- `(e ∈ product) ∧ (e.1 ≠ e.2 ∧ Φ_L …)`;
-- (3) `Finset.mem_product` gives `e.1 ∈ G.V \ W ∧ e.2 ∈ G.V \ W`;
-- (4) `Sym2.mem_iff.mp hv` reduces `v ∈ s(e.1, e.2)` to
-- `v = e.1 ∨ v = e.2`, and a case-split closes via `rfl`.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marginalize_hL_subset (was: refactor_marginalize_hL_subset)
private lemma refactor_marginalize_hL_subset (G : refactor_CDMG Node)
    (W : Finset Node) :
    ∀ ⦃s : Sym2 Node⦄,
      s ∈ (((G.V \ W) ×ˢ (G.V \ W)).filter
              (fun e => e.1 ≠ e.2 ∧ G.refactor_MarginalizationΦL W e.1 e.2)).image
            (fun e => s(e.1, e.2)) →
      ∀ ⦃v : Node⦄, v ∈ s → v ∈ G.V \ W := by
  intro s hs v hv
  obtain ⟨e, hFilter, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hProd, _⟩ := Finset.mem_filter.mp hFilter
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hProd
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact h1
  · exact h2
-- REFACTOR-BLOCK-REPLACEMENT-END: marginalize_hL_subset

-- ## `refactor_marginalize_hL_irrefl` — `Sym2.IsDiag`-shaped obligation
--
-- The post-refactor `hL_irrefl` axiom on `refactor_CDMG` is phrased as
-- `¬ s.IsDiag` (Mathlib's canonical "no self-pair" predicate on `Sym2`),
-- not as the pre-refactor `v₁ ≠ v₂` on ordered pairs.  The proof reads
-- the `e.1 ≠ e.2` conjunct off the filter, and `Sym2.mk_isDiag_iff`
-- pulls `s(e.1, e.2).IsDiag` back to `e.1 = e.2`, contradicting.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marginalize_hL_irrefl (was: refactor_marginalize_hL_irrefl)
private lemma refactor_marginalize_hL_irrefl (G : refactor_CDMG Node)
    (W : Finset Node) :
    ∀ ⦃s : Sym2 Node⦄,
      s ∈ (((G.V \ W) ×ˢ (G.V \ W)).filter
              (fun e => e.1 ≠ e.2 ∧ G.refactor_MarginalizationΦL W e.1 e.2)).image
            (fun e => s(e.1, e.2)) →
      ¬ s.IsDiag := by
  intro s hs hDiag
  obtain ⟨e, hFilter, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨_, hNe, _⟩ := Finset.mem_filter.mp hFilter
  exact hNe (Sym2.mk_isDiag_iff.mp hDiag)
-- REFACTOR-BLOCK-REPLACEMENT-END: marginalize_hL_irrefl

-- ref: def_3_14
--
-- The *marginalization* of `G` w.r.t. `W` — the LN's `G^{∖W}` — as the
-- `refactor_CDMG` `G.refactor_marginalize W hW`.  Post-refactor port of
-- `marginalize` against the `cdmg_typed_edges` design (`def_3_1`'s
-- post-refactor shape: `L : Finset (Sym2 Node)`, no `hL_symm` axiom).
-- The four data fields are:
--   * `J^{∖W} := G.J`;
--   * `V^{∖W} := G.V \ W`;
--   * `E^{∖W} := { e ∈ (G.J ∪ (G.V \ W)) × (G.V \ W) | Φ_E W e.1 e.2 }`
--     — unchanged shape from the original, retargeted onto
--     `refactor_MarginalizationΦE`;
--   * `L^{∖W} := { s(e.1, e.2) | e ∈ (G.V \ W) × (G.V \ W),
--                  e.1 ≠ e.2, Φ_L W e.1 e.2 }` — the same set of
--     unordered pairs as the original's ordered-pair `L^{∖W}`, lifted
--     through the `Sym2.mk` quotient via `Finset.image`.  Build pattern:
--     `(filter …).image (fun e => s(e.1, e.2))` — filter on the
--     ordered-pair carrier first (so the `e.1 ≠ e.2` conjunct stays
--     writable), then `image` lifts to `Finset (Sym2 Node)`.
--
-- ## Design choice — post-refactor deltas
--
-- * **`L` is built via `(filter …).image (fun e => s(e.1, e.2))`, not
--   directly as a `Finset.filter` over a `Sym2`-carrier.**  Filtering
--   directly over `Finset (Sym2 Node)` would require either (i) a
--   pre-existing `Sym2`-carrier `Finset` to filter from (which we don't
--   have — the LN's `L^{∖W}` is set-builder-defined, not derived from
--   `G.L`), or (ii) hand-building such a carrier from `(G.V \ W) ×ˢ
--   (G.V \ W)` via a more elaborate `Sym2`-equivalence-class step.
--   The filter-then-image pattern is the cleanest LN-faithful encoding:
--   the ordered-pair filter mirrors the LN's set-builder
--   `{ (ū, ō) ∈ (V \ W) × (V \ W) | ū ≠ ō ∧ Φ_L(ū, ō) }` literally,
--   and `Finset.image (fun e => s(e.1, e.2))` is the standard Mathlib
--   idiom for quotienting an ordered-pair `Finset` to its `Sym2`
--   image.  Both pairs `(u, v)` and `(v, u)` in the source filter
--   collapse to the same `s(u, v)` in the image, mirroring the
--   unordered-pair semantics.
--
-- * **No `refactor_marginalize_hL_symm` field.**  The post-refactor
--   `refactor_CDMG` structure carries only four proof obligations
--   (`hJV_disj`, `hE_subset`, `hL_subset`, `hL_irrefl`); the
--   pre-refactor `hL_symm` field is gone because swap-symmetry is
--   *definitional* on `Sym2` (`s(v, w) = s(w, v)` by quotient
--   construction).  The pre-refactor `marginalize_hL_symm` proof
--   (which closed via `Or.comm` on Φ_L's two walk-orientation
--   disjuncts) has no analogue here — the symmetry it asserted is
--   structurally vacuous post-refactor.
--
-- * **`refactor_MarginalizationΦL` keeps the symmetric `Or` over the
--   two walk orientations**, even though no `hL_symm` field consumes
--   it.  The symmetric encoding is *semantically* faithful to the LN's
--   "bifurcation between `ū` and `ō`" phrasing (an undirected concept
--   at the LN level), and downstream consumers (`claim_3_16`–`3_19`)
--   may want a symmetric Φ_L for their own purposes.  Dropping the
--   `Or` here would be a gratuitous deviation from the original; the
--   refactor's principle is "port mechanically, preserve LN-level
--   semantics", not "trim every redundancy".
--
-- * **`hW` remains carried, `noncomputable` remains.**  Both
--   unchanged from the original — `hW` is signature-level LN-fidelity
--   only, and `noncomputable` is inherited from the classical
--   decidability instances above.  Same `set_option
--   linter.unusedVariables false in` to suppress the linter warning
--   on the unused `hW`.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marginalize (was: refactor_marginalize)
set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
-- def_3_14 -- start statement
noncomputable def refactor_marginalize (G : refactor_CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) : refactor_CDMG Node where
  J := G.J
  V := G.V \ W
  hJV_disj := refactor_marginalize_hJV_disj G W
  E := ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
        (fun e => G.refactor_MarginalizationΦE W e.1 e.2)
  hE_subset := refactor_marginalize_hE_subset G W
  L := (((G.V \ W) ×ˢ (G.V \ W)).filter
        (fun e => e.1 ≠ e.2 ∧ G.refactor_MarginalizationΦL W e.1 e.2)).image
        (fun e => s(e.1, e.2))
  hL_subset := refactor_marginalize_hL_subset G W
  hL_irrefl := refactor_marginalize_hL_irrefl G W
-- def_3_14 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: marginalize

end refactor_CDMG

end Causality
