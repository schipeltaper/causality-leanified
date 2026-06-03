import Chapter3_GraphTheory.Section3_1.EdgeRelations

namespace Causality

/-!
# CDMG restrictions: J-nodes have no incoming arrowheads, only point to V,
  and are pairwise non-adjacent

This file formalises `claim_3_1` — the LN `Remark` that reads three
substantive restrictions off the structural fields of `def_3_1`.  Verbatim LN tex:

```
With the notations \ref{not-cdmg} the restrictions in definition
\ref{def-cdmg} mean that the nodes $j \in J$ will not have any
arrowheads pointing towards them: $ j \hus v \notin G$. Nodes
$j \in J$ can only point towards nodes $v \in V$: edges $j \tuh v$
are allowed. Furthermore, no two nodes in $J$ are adjacent.
```

Operator addition `[implicit_universal_quantifier_in_hus_clause]` —
treated as part of the LN — clarifies that the two displayed formal
expressions carry an implicit universal quantification over `v`.  The
"edges $j \tuh v$ are allowed" half is *permissive* ("its presence is
not asserted, only that no restriction forbids it"), so we encode only
the *restrictive* content of sentence 2, namely `G.tuh j v → v ∈ G.V`,
not a positive existence claim.

The three theorems mirror the LN's three sentences in order:

* `CDMG.no_hus_into_J`           — sentence 1.
* `CDMG.tuh_from_J_target_in_V`  — sentence 2 (restrictive half only).
* `CDMG.no_J_J_adjacent`         — sentence 3.

Bodies are short case analyses on `hus` / `sus`, closed by
`hE_subset` / `hL_subset` projections and
`Finset.disjoint_left.mp G.hJV_disj` from `CDMG.lean`.

The LN-critic working-phase report flagged three notational subtleties
on the source text — all *resolved* by the existing CDMG type design:

* `undirected_edge_between_j_and_v_unaddressed` — there is no `\tut` /
  undirected edge type in CDMGs (see the design block on `sus` in
  `CDMGNotation.lean`), so the literal-reading "$j - v$ slips through"
  corner case is vacuous.
* `only_points_to_V_assumes_J_V_disjoint` — `hJV_disj` is precisely the
  required disjointness hypothesis and lives as a structure field on
  `CDMG`.
* `hus_notation_may_not_cover_bidirected_arrowhead_at_j` — `\hus`
  decodes via `def_3_2` item 6 as `\hut ∨ \huh`, which DOES include the
  bidirected case; so "$j \hus v \notin G$" really does mean "neither
  directed-into-`j` nor bidirected-into-`j`", consistent with the LN
  prose.

None of these flags changes the shape below.
-/

namespace CDMG

variable {Node : Type*} [DecidableEq Node]

-- ref: claim_3_1 (part 1/3)
--
-- *No arrowheads pointing into J.*  For every `j ∈ G.J` and every
-- `v : Node`, `G.hus j v` fails — i.e. neither a directed edge
-- `v → j` (the `G.hut j v` disjunct, which unfolds to
-- `(v, j) ∈ G.E`) nor a bidirected edge `j ↔ v` (the `G.huh j v`
-- disjunct, which unfolds to `(j, v) ∈ G.L`) exists.  Proof
-- sketch: each disjunct of `hus` forces
-- `j ∈ G.V` (via `hE_subset.2` or `hL_subset.1`), contradicting
-- `hj : j ∈ G.J` via `hJV_disj`.
--
-- Encoding choices.  `v : Node` is universally quantified (not
-- restricted to `v ∈ G`) because `G.hus j v` already forces
-- `v ∈ G` via `hE_subset` / `hL_subset`, so the membership
-- hypothesis would add nothing and only burden downstream
-- callers.  `j` sits on the LEFT of `G.hus j v` (focal vertex
-- first, matching `CDMGNotation`'s `hus v1 v2` convention), so
-- the Lean spelling reads exactly like the LN's
-- `$j \hus v \notin G$`.  The bare `(v : Node)` binder in the
-- signature is the direct encoding of operator addition
-- `[implicit_universal_quantifier_in_hus_clause]` (top-of-file
-- block): the LN's `$j \hus v \notin G$` carries an implicit
-- universal quantifier over `v` that we lift to a top-level
-- binder rather than leaving it informal.
--
-- Mathlib re-use.  None — this is a projection on bespoke
-- `CDMG` fields (`hE_subset`, `hL_subset`, `hJV_disj`), not a
-- consequence of any mathlib graph lemma.  The CDMG type is
-- not a `SimpleGraph` / `Quiver` / `Digraph` (no first-class
-- mixed-graph type in mathlib carries a J/V partition plus a
-- bidirected layer; see the design block in `CDMG.lean`), so
-- a future reader should not hunt for a phantom "no incoming
-- edges into subset A" mathlib lemma — by design the proof
-- lives in CDMG-land.
--
-- Downstream consequences.  This is the structural witness
-- that "J-nodes are roots":
--   * Chapter 4 CBNs treat `J` as the exogenous interventional
--     input layer with no parents; the CBN factorisation
--     `p(V | J) = ∏_v p(v | Pa(v))` rests on
--     `Pa(j) = ∅` for `j ∈ J`, and the Lean-side discharge of
--     that emptiness chains through exactly this lemma (a
--     parent of `j` would be the source of an edge with
--     arrowhead at `j`, ruled out here).
--   * Chapters 11–16 (causal discovery, FCI, ICDF) treat
--     "no arrowhead pointing into a context / intervention
--     node" as a hard structural invariant the discovery
--     algorithm may assume from the outset; the theorem is
--     the Lean-side witness those routines `apply` (or
--     pattern-match against) when pruning candidate edges
--     into `J`.
-- claim_3_1 -- start statement
theorem no_hus_into_J (G : CDMG Node) {j : Node} (hj : j ∈ G.J) (v : Node) :
    ¬ G.hus j v
-- claim_3_1 -- end statement
  := by
    intro h
    rcases h with h_hut | h_huh
    · exact Finset.disjoint_left.mp G.hJV_disj hj (G.hE_subset h_hut).2
    · exact Finset.disjoint_left.mp G.hJV_disj hj (G.hL_subset h_huh).1

-- ref: claim_3_1 (part 2/3)
--
-- *J-nodes only point to V.*  For every `j ∈ G.J` and every
-- `v : Node`, if `G.tuh j v` (a directed edge `j → v`, i.e.
-- `(j, v) ∈ G.E`) holds then the target `v` lies in `G.V`.
-- Proof sketch: immediate from `hE_subset.2` applied to
-- `(j, v) ∈ G.E`.
--
-- Restrictive direction only.  The LN's "edges $j \tuh v$ are
-- allowed" looks like a positive permission, but the operator
-- addition is explicit: "its presence is not asserted, only that
-- no restriction forbids it."  So we do NOT add an
-- `∃ v, G.tuh j v` clause.  The actual restrictive content of
-- sentence 2 — "Nodes $j \in J$ can only point towards nodes
-- $v \in V$" — is precisely `G.tuh j v → v ∈ G.V`.
--
-- Constraint / known limitation.  The permissive half of
-- sentence 2 is entirely *unencoded* — by design, not by
-- oversight.  An `∃ v, G.tuh j v` (or any positive
-- "permission-is-non-vacuous" witness) would be redundant and
-- noisy: the permission is already folded into the type by
-- `hE_subset`'s `e.1 ∈ J ∪ V` (which licences any `j ∈ J` as
-- an edge source) plus the absence of any further restriction
-- on `E` beyond that subset constraint.  A downstream consumer
-- that genuinely needs witness existence (e.g. a CBN factor
-- requiring `Ch(j) ≠ ∅`) adds that hypothesis at its use site
-- rather than reading it off this lemma.
--
-- `hj : j ∈ G.J` is kept in the signature even though
-- `hE_subset.2` alone suffices: the LN sentence is explicitly
-- scoped to `j ∈ J`, and downstream "source-only J" arguments
-- (chapters 4–16) chain through this lemma with `hj` already in
-- hand rather than via a separate retrieval beat.  The implicit
-- `{v : Node}` binder on the target is the direct encoding of
-- operator addition `[implicit_universal_quantifier_in_hus_clause]`
-- (which covers the parallel `\tuh` half of the same sentence):
-- the LN's "edges $j \tuh v$" carries the implicit "for every
-- node `v` in the graph" quantifier, picked up here as the
-- implicit Lean binder discharged at the use site by
-- `h : G.tuh j v`.
--
-- Mathlib re-use.  None — `hE_subset.2` is a one-step projection
-- on the bespoke `CDMG` structure (see `CDMG.lean`).  Mathlib's
-- `SimpleGraph` / `Quiver` carry no analogous "edge source lives
-- in `J ∪ V`, target lives in `V`" field, so there is nothing
-- to import.  Future readers should not look for a `Digraph`-
-- side analogue.
--
-- Downstream consequences.  This is the workhorse "children of
-- an intervention live in V" lemma:
--   * Chapter 5 do-calculus repeatedly pivots on "if we
--     intervene at `j ∈ J`, the affected vertices are children
--     of `j` lying in `V`"; do-calculus soundness proofs
--     `apply` this lemma to discharge the target-side
--     membership goal and chain through to the next rewrite.
--   * Chapters 8–10 iSCMs treat `J` as the index set of
--     interventions whose mechanisms write into `V`-vertices
--     only; the iSCM Markov property and counterfactual
--     identification arguments both reach for this lemma at
--     the point they need "no intervention writes back into
--     the intervention layer".
-- claim_3_1 -- start statement
theorem tuh_from_J_target_in_V (G : CDMG Node) {j : Node} (_hj : j ∈ G.J)
    {v : Node} (h : G.tuh j v) : v ∈ G.V
-- claim_3_1 -- end statement
  := (G.hE_subset h).2

-- ref: claim_3_1 (part 3/3)
--
-- *No two J-nodes are adjacent.*  For any distinct
-- `j1, j2 ∈ G.J` (witnessed by `hne : j1 ≠ j2`),
-- `G.adjacent j1 j2` fails.  Proof sketch: `adjacent` unfolds
-- to `sus = tuh ∨ hut ∨ huh`; each disjunct forces one of
-- `j1`, `j2` into `G.V` (via `hE_subset` or `hL_subset`),
-- contradicting J-membership via `hJV_disj`.  The distinctness
-- witness `hne` is recorded in the signature to match the LN's
-- distinctness scope but is not consumed by the case-split
-- (each disjunct discharges on the J/V disjointness alone);
-- see Encoding choices below for why we still keep the binder.
--
-- Encoding choices.  The binder `(hne : j1 ≠ j2)` is the
-- explicit encoding of the LN's "no *two* nodes in $J$"
-- wording — in mathematical English "two" carries implicit
-- distinctness, so the LN's sentence-3 claim space is
-- `{(j1, j2) ∈ J × J : j1 ≠ j2}`, not all of `J × J`.
-- Dropping the binder would silently widen the Lean claim by
-- the diagonal `j1 = j2` case, and that diagonal is a separate
-- structural fact (a consequence of sentence 1 plus the
-- `E` / `L` subset restrictions and `J ∩ V = ∅`), not what
-- sentence 3 itself asserts; bundling the two would conflate
-- two distinct LN sentences into a single claim.  Using
-- `G.adjacent` (from `def_3_3`) rather than spelling out
-- `G.sus` keeps the LN's vocabulary ("two nodes adjacent")
-- visible at the Lean level — a call that `review_design`
-- independently judged "more natural" than inlining the
-- three-disjunct `sus` expansion.
--
-- We deliberately do NOT strengthen to the unrestricted form
-- (no distinctness hypothesis), even though `¬ G.adjacent j j`
-- for `j ∈ G.J` is in fact provable: `G.adjacent j j` unfolds
-- to `G.sus j j = G.tuh j j ∨ G.hut j j ∨ G.huh j j`, and each
-- disjunct contradicts `J ∩ V = ∅` via `hE_subset` /
-- `hL_subset` (mirroring theorem 1 on the self-edge case).
-- That self-case is a corollary of sentence 1 (plus the
-- structural disjointness), not of sentence 3; folding it into
-- this theorem would mis-attribute it.  If a downstream
-- consumer genuinely needs `¬ G.adjacent j j` for `j ∈ G.J`,
-- the right move is to add a separately-named companion lemma
-- at that consumer's introduction time — we do not pre-add one
-- here, in line with claude.md's "don't design for hypothetical
-- future requirements" rule.
--
-- Mathlib re-use.  None — same story as parts 1 and 2.  The
-- bespoke `CDMG` type has no mathlib analogue for the J/V
-- partition + bidirected layer (`SimpleGraph` is undirected
-- without a J/V split; `Quiver` is parallel-ordered without a
-- bidirected channel), so the proof is a short case analysis
-- on the three `sus` disjuncts, each closed by a
-- structure-field projection.  No `SimpleGraph.notAdj`-flavoured
-- mathlib lemma applies.
--
-- Downstream consequences.  This is the structural witness
-- that "distinct intervention nodes are mutually unconfounded":
--   * Chapters 8–10 iSCMs use J–J non-adjacency to derive
--     mutual independence of intervention indicators: two
--     distinct non-adjacent exogenous nodes induce independent
--     random variables in the associated Markov kernel, and
--     that independence is what makes the iSCM factorisation
--     kernel-product-shaped on the `J` side.
--   * Chapters 11–16 (FCI, ICDF, discovery): "no edge between
--     distinct intervention nodes" is a structural invariant
--     the discovery routines exploit when pruning the J × J
--     skeleton.  Consumers reach for this lemma while
--     iterating over distinct pairs `(j1, j2)` in the skeleton,
--     so the `hne : j1 ≠ j2` hypothesis is already in hand at
--     the call site.
-- claim_3_1 -- start statement
theorem no_J_J_adjacent (G : CDMG Node) {j1 j2 : Node}
    (hj1 : j1 ∈ G.J) (hj2 : j2 ∈ G.J) (_hne : j1 ≠ j2) :
    ¬ G.adjacent j1 j2
-- claim_3_1 -- end statement
  := by
    intro h
    rcases h with h_tuh | h_hut | h_huh
    · exact Finset.disjoint_left.mp G.hJV_disj hj2 (G.hE_subset h_tuh).2
    · exact Finset.disjoint_left.mp G.hJV_disj hj1 (G.hE_subset h_hut).2
    · exact Finset.disjoint_left.mp G.hJV_disj hj1 (G.hL_subset h_huh).1

end CDMG

end Causality
