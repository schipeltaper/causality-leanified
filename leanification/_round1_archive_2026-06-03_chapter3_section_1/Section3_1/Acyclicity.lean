import Chapter3_GraphTheory.Section3_1.Walks

namespace Causality

/-!
# Acyclicity of a CDMG: `def_3_6`

This file formalises the foundational acyclicity predicate for a CDMG.
Acyclicity is the load-bearing hypothesis under which essentially every
downstream object becomes tractable: `def_3_7` carves CDMGs into the
ADMG / CADMG / DAG taxonomy by acyclicity; `claim_3_2` proves the
fundamental "acyclic ⟺ admits a topological order" equivalence; the
intervention operations (`do`, `split`, `swig`, marginalisation) all
have a separate "preserves acyclicity" lemma each; chapter 5+'s `id`-
and `σ`-separation theory collapses to the simpler `d`-separation in
the acyclic regime; iSCMs (chapter 8) are *defined* as acyclic when
their underlying graph is, and the existence-and-uniqueness of a
solution function in `Prp:acyclic_scms_are_simple` runs by induction on
a topological order obtained from acyclicity; the FCI algorithm
(chapter 11) is originally designed for acyclic DMGs and its
completeness is proved in that case.

## LN block (verbatim)

```
A CDMG $G=(J,V,E,L)$ is called *acyclic* if there does not exist any
non-trivial directed walk from $v$ to itself in $G$ for any node
$v \in G$.
```

## Operator addition (treated as part of the LN — authoritative)

```
[nontrivial_directed_walk_not_defined_in_block] A non-trivial directed
walk is a directed walk $v_0 \tuh \cdots \tuh v_n$ with $n \ge 1$
(i.e. one that traverses at least one edge); the trivial walk
consisting of a single node $v_0$ is excluded. In particular, a
self-loop $v \tuh v$ constitutes a non-trivial directed walk from $v$
to itself, so an acyclic CDMG contains no self-loops on any $v \in V$.
```

This addition pins down two things the literal LN leaves implicit and
that our Lean encoding must honour:

1. "Non-trivial" = the walk has at least one edge, i.e.
   `0 < p.length` in our encoding (because `Walk.length` counts edges /
   `cons` constructors, see `Walks.lean`).  The trivial walk
   `Walk.nil hv : Walk G v v` has `length = 0` and is therefore
   excluded by the `0 < p.length` clause — exactly the carve-out the
   addition mandates.

2. Self-loops `(v, v) ∈ G.E` for `v ∈ G.V` constitute a non-trivial
   directed walk from `v` to itself, via `Walk.cons (.forward h)
   (Walk.nil hv) : Walk G v v` (which has `length = 1` and satisfies
   `IsDirectedWalk`).  Any CDMG with a directed self-loop is therefore
   automatically non-acyclic under our encoding — no extra clause
   needed, the addition is honoured *automatically* by the way the
   walk type was built in `Walks.lean`.  Working-phase wording-check
   subtlety `directed_self_loops_not_excluded` flagged this corner
   case; the addition is the operator's resolution of it.

The substantive design discussion lives in the comment block
immediately above the `start statement` marker; read that before
modifying this row.
-/

namespace CDMG

variable {Node : Type*} [DecidableEq Node]

-- ref: def_3_6
--
-- A CDMG `G` is *acyclic* if no vertex `v ∈ G` admits a non-trivial
-- directed walk back to itself.  Encoded literally as the negation of
-- a directed-walk existential, with `0 < p.length` carving out the
-- trivial walk per the operator addition
-- `[nontrivial_directed_walk_not_defined_in_block]`.
/-
LN tex (verbatim, `\label{def-acylic}`):

  A CDMG $G=(J,V,E,L)$ is called \emph{acyclic} if there does not
  exist any non-trivial directed walk from $v$ to itself in $G$ for
  any node $v \in G$.

LN addition `[nontrivial_directed_walk_not_defined_in_block]` (treated
as part of the LN):

  A non-trivial directed walk is a directed walk
  $v_0 \tuh \cdots \tuh v_n$ with $n \ge 1$ (i.e. one that traverses
  at least one edge); the trivial walk consisting of a single node
  $v_0$ is excluded.  In particular, a self-loop $v \tuh v$
  constitutes a non-trivial directed walk from $v$ to itself, so an
  acyclic CDMG contains no self-loops on any $v \in V$.
-/
-- ## Design choice
--
-- *Why the `CDMG` namespace.*  `IsAcyclic` is a *property of the
--   graph* — it inspects only `G`'s edges and vertices, never the
--   walk endpoints from "outside" — so it lives field-style on `CDMG`
--   itself.  Reading `G.IsAcyclic` (dot-notation) mirrors how
--   `CDMG.tuh / hut / huh / suh / hus / sus` (the seven items of
--   `def_3_2` in `CDMGNotation.lean`) and the structure-level fields
--   `CDMG.hE_subset` etc. (in `CDMG.lean`) are addressed.  Contrast
--   the walk-level predicates `Walk.IsDirectedWalk` etc. which live
--   directly under `Causality` because they characterise *walks*, not
--   graphs.  Same reason `def_3_5`'s `Anc / Desc / Pa / Ch` are
--   *under* `Causality` (not `CDMG`): those are families parametric
--   in a vertex `v` — they aren't field-style predicates on `G`.
--
-- *Why `∀ v ∈ G, …` rather than `∀ v : Node, v ∈ G → …` or
--   `∀ v ∈ G.V`.*  Three choices were on the table.
--   1. `∀ v ∈ G, …` (chosen).  This reads literally as the LN's "for
--      any node $v \in G$".  Lean's bounded-forall syntax `∀ v ∈ G, P
--      v` desugars to `∀ v, v ∈ G → P v`, with `∈` resolved via the
--      `Membership Node (CDMG Node)` instance (`def_3_2` item 1,
--      `CDMGNotation.lean`), which unfolds `v ∈ G` to `v ∈ G.J ∪
--      G.V`.  Exactly the LN's literal reading.
--   2. `∀ v : Node, …`.  Rejected: this quantifies over the entire
--      ambient `Node` type, not just the vertices of `G`.  Most
--      `Node` values are *not* in `G` and there is no walk from such
--      `v` to `v` at all (`Walk G v v` has only `nil` as a
--      constructor for non-`G` vertices, which requires `v ∈ G` —
--      so vacuous for non-`G` vertices anyway), but expanding the
--      quantifier to all of `Node` makes the LN-faithfulness less
--      transparent.
--   3. `∀ v ∈ G.V`.  Rejected: the LN literally writes "$v \in G$",
--      which by the `def_3_2` item-1 membership convention is
--      `v ∈ G.J ∪ G.V`, *not* just `v ∈ G.V`.  Restricting to `G.V`
--      would deviate from the LN.  The deviation is harmless on its
--      face — per def_3_1's `hE_subset` (`E ⊆ (J ∪ V) × V`), the
--      target of any directed edge is in `V`, so no directed walk
--      can end at a J-node, and the acyclicity clause is vacuous for
--      `v ∈ G.J`.  Working-phase wording-check subtlety
--      `node_membership_v_in_g_informal` flagged this asymmetry as
--      potentially intentional (quantify only over output nodes
--      because J-nodes are automatically fine) or potentially
--      incidental (quantify over all `J ∪ V` with vacuous J
--      coverage).  We take the literal LN reading; the J-quantifier
--      half is automatically vacuous so no expressive power is lost.
--
-- *Why `¬ ∃ p, P p` rather than `∀ p, ¬ P p`.*  Logically equivalent
--   (and Mathlib's `not_exists` rewrites between them).  We pick `¬
--   ∃` because it mirrors the LN's surface phrasing ("there does not
--   exist any non-trivial directed walk").  Mathlib's
--   `SimpleGraph.IsAcyclic` is `∀ ⦃v⦄ (c : G.Walk v v), ¬c.IsCycle`
--   (the `∀ … ¬` shape), but Mathlib's `SimpleGraph` does not have a
--   J/V split nor a bidirected channel and quantifies over walks
--   ranging over a single ambient `V` — the `⦃v⦄` instance-implicit
--   plus the lack of an `v ∈ G`-style membership makes the
--   comparison only structural, not literal.  Downstream consumers
--   that want the `∀ p, ¬` form get there by `rw [not_exists] at h`
--   in a single rewrite.
--
-- *Why `0 < p.length` is the encoding of "non-trivial".*  Per
--   working-phase subtlety
--   `trivial_walk_satisfies_all_specialized_walk_types` (registered
--   globally in `leanification/working_subtlety_register.json` and
--   discussed at length in the design block above
--   `Walk.IsDirectedWalk` in `Walks.lean`), the trivial walk
--   `Walk.nil hv : Walk G v v` satisfies
--   `Walk.IsDirectedWalk = True` *vacuously*.  Without the length
--   clause, every CDMG with a vertex would be non-acyclic — the
--   trivial walk would witness `∃ p, p.IsDirectedWalk` for every
--   vertex in `G`.  The LN dodges this by adding the "non-trivial"
--   qualifier, which the operator addition pins down as "$n \ge 1$",
--   i.e. "at least one edge".  Since `Walk.length` counts edges /
--   `cons` constructors (`length nil = 0`, `length (cons _ p) =
--   length p + 1`, see `Walks.lean`), `0 < p.length` is the literal
--   encoding of "$n \ge 1$".
--
--   The `Walks.lean` design block above `Walk.length` already
--   anticipates this row by name: "`def_3_6` acyclicity says
--   `non-trivial directed walk', i.e. `0 < p.length`, without
--   wanting to peer inside" — i.e. the choice not to `@[simp]`-tag
--   `length` was deliberately made to let `def_3_6` quote the length
--   primitively.  Other equivalent encodings —
--   `p ≠ .nil _` (data-equality, requires `Subsingleton`-style
--   reasoning) or `p.support.length ≠ 1` (vertex-count rather than
--   edge-count) — were rejected: `0 < p.length` is the most
--   compositional with downstream `Walk`-induction proofs (chapter
--   5+ `m`-connection arguments often peel a `cons` off and reduce
--   to a strictly shorter walk; `0 < p.length` is preserved by such
--   reductions exactly when at least one `cons` remains).
--
-- *How the LN addition is honoured automatically — self-loops.*  The
--   addition's second sentence ("a self-loop $v \tuh v$ constitutes
--   a non-trivial directed walk from $v$ to itself, so an acyclic
--   CDMG contains no self-loops on any $v \in V$") is *not* an
--   additional clause we need to encode — it falls out of the
--   encoding automatically.  Concrete witness: given `h : G.tuh v v`
--   for some `v ∈ G.V` (hence `v ∈ G` via `Finset.mem_union.mpr ∘
--   Or.inr`) and the trivial tail `Walk.nil hv : Walk G v v`, the
--   walk `Walk.cons (.forward h) (Walk.nil hv) : Walk G v v` has
--   `length = 1 > 0` and `IsDirectedWalk = True` (by the
--   `.cons (.forward _)`-recurse clause of `Walk.IsDirectedWalk` and
--   `(Walk.nil _).IsDirectedWalk = True`).  So `∃ p, p.IsDirectedWalk
--   ∧ 0 < p.length` is witnessed, and `G.IsAcyclic` is `¬` of that
--   for `v ∈ G`, hence forces `¬ G.tuh v v` for every `v ∈ G.V`.
--   Working-phase wording-check subtlety
--   `directed_self_loops_not_excluded` (resolved by this addition)
--   is therefore *honoured by the encoding without extra work*.
--
-- *Why a `def`, not an `abbrev` / `class` / `Decidable` instance.*  A
--   plain `def` returning `Prop` is the right shape for a "predicate
--   on a graph that downstream chapters use as a hypothesis".
--   * An `abbrev` would inline at every use site, defeating the
--     purpose of giving acyclicity a stable name and forcing
--     downstream `unfold IsAcyclic` everywhere.
--   * A `class` would dispatch via typeclass inference, which is
--     wrong here: acyclicity is a *contingent* property of a
--     specific `G`, not a structural property of the type
--     `CDMG Node`.  Different `G : CDMG Node` instances will or will
--     not be acyclic; typeclass inference cannot pick the right one.
--   * No `Decidable (G.IsAcyclic)` instance is provided.
--     Decidability follows in principle from the fact that
--     non-trivial directed walks in a finite graph can be enumerated
--     up to length `(G.J ∪ G.V).card` (via the `claim_3_2`
--     topological-order equivalence — a cycle exists iff a cycle of
--     length at most `|J ∪ V|` exists, which can be checked by
--     bounded BFS).  But no chapter-3 proof needs the decidability,
--     and threading it through `noncomputable` boundaries via
--     `Classical.dec` is the cheaper alternative.  Add the instance
--     on demand (a downstream chapter-5+ proof that uses
--     `if G.IsAcyclic then …` would be the trigger).
--
-- *Mathlib re-use.*  No direct fit.  Mathlib has `SimpleGraph.
--   IsAcyclic` and `DiGraph.IsAcyclic`, but `SimpleGraph` is
--   undirected and has no J/V split and no bidirected channel, and
--   `DiGraph` (if used) likewise has no mixed-edge structure.  We
--   re-use `Walk` and `Walk.IsDirectedWalk` (the chapter-3 walk
--   infrastructure built in `Walks.lean`) and construct the
--   predicate from those, rather than coercing to a Mathlib graph
--   type and losing the J/V/L structure.
--
-- *Why compose `Walk` + `Walk.IsDirectedWalk`, not roll a fresh
--   `inductive DirectedCycle G v` (or `Walk.IsDirectedCycle p`)
--   predicate.*  The chosen shape decomposes acyclicity into three
--   independently-defined chapter-3 primitives — `Walk` (def_3_4
--   item 1), `IsDirectedWalk` (def_3_4 item 2), `length` (def_3_4
--   item 1 helper) — held together by the length-positivity guard
--   `0 < p.length`.  The alternative ("define a bespoke
--   `inductive DirectedCycle` on `CDMG`, prove a `IsAcyclic ↔
--   no cycle` equivalence once, expose only the cycle type to
--   downstream chapters") was rejected because it breaks
--   composition on three axes.
--   1. **Lemma re-use.**  Every lemma already on `Walk` (`support`,
--      `length`, `IsPath`, the four into/out classifications) and
--      every future walk-level lemma (concat, reverse, sub-walk,
--      support-`Nodup` interactions) is immediately usable for
--      acyclicity arguments without coercion.  A fresh
--      `DirectedCycle` type would force re-derivation of all of
--      this on the new type — `claim_3_2`'s forward direction
--      ("extract a topological order") needs to walk down a longest
--      directed walk and case-split on its tail; that argument
--      runs natively on `Walk` recursion, but would require a
--      bespoke recursor on a cycle type.
--   2. **Triple duty for `IsDirectedWalk`.**  The same predicate
--      `p.IsDirectedWalk` already underpins ancestor reachability
--      (`def_3_5`'s `Anc / Desc / Pa / Ch`) and the bifurcation
--      arms (`def_3_4` item 6 — both arms are directed walks).
--      Acyclicity here adds a third call site for free.  A separate
--      cycle inductive would not benefit any of those consumers and
--      would force per-consumer translation lemmas
--      "`DirectedCycle ↔ directed walk with v = w`".
--   3. **Per-operation preservation lemmas reduce to walk
--      correspondence.**  Every graph operation in `def_3_10`
--      (hard intervention `do`), `def_3_11` (node splitting `split` /
--      `swig`), `def_3_14` (marginalisation), and `def_3_15`
--      (acyclification) carries an "if `G.IsAcyclic` then
--      `G_op.IsAcyclic`" obligation.  Under our shape, each such
--      lemma reduces to "directed walks in `G_op` correspond to
--      directed walks in `G` (or a sub-class thereof) preserving
--      `0 < length`" — a per-operation walk-correspondence stated
--      once.  A cycle-inductive shape would need a separate
--      `DirectedCycle G ↔ DirectedCycle G_op` correspondence per
--      operation, threading the new type instead of leaning on
--      already-needed walk lemmas.
--   The cost — `IsAcyclic` quotes three pieces (`Walk`,
--   `IsDirectedWalk`, `length`) rather than one — is trivial; the
--   compositional payoff lasts through chapter 11+ FCI, where
--   walk-level reachability lemmas drive structure-learning
--   completeness proofs that would otherwise need a parallel
--   cycle-side infrastructure.
--
-- *Downstream consumers (load-bearing for ten chapters).*
--   * `def_3_7` (CDMG taxonomy) defines CADMG, ADMG, DAG, … as
--     CDMGs that are acyclic (plus further J/L vanishing conditions);
--     each item directly references `G.IsAcyclic`.
--   * `claim_3_2` (acyclic ⟺ topological order) is the fundamental
--     equivalence built on top: its forward direction extracts a
--     topological order from `G.IsAcyclic`, its backward direction
--     contradicts `G.IsAcyclic` from a directed cycle in the order's
--     image.
--   * `def_3_15` (acyclification) and the intervention preservation
--     lemmas (`do`, `split`, `swig`, marginalisation) each have a
--     stated form "if `G.IsAcyclic` then `G_{op}.IsAcyclic`",
--     phrased as a separate lemma per operation.
--   * Chapter 5+'s `id` vs `σ` separation collapse: in the acyclic
--     case the two separations agree, simplifying the do-calculus
--     soundness proofs.
--   * Chapter 8's iSCMs: `def:scm_acyclic` defines acyclic iSCMs as
--     iSCMs whose causal graph is acyclic — `G.IsAcyclic` is the
--     literal hypothesis.  `Prp:acyclic_scms_are_simple` (= every
--     acyclic iSCM has an essentially unique solution function)
--     runs by induction on a topological order obtained from
--     acyclicity.
--   * Chapter 11+ FCI: completeness in the acyclic ADMG setting
--     hinges on `G.IsAcyclic`.
--   The encoding choice here therefore composes: downstream proofs
--   pattern-match on `G.IsAcyclic` as a hypothesis, derive a
--   topological order via `claim_3_2`, and proceed by topological
--   induction — exactly the LN's paradigm.
--
-- *Constraints / known limitations.*
--   1. **The J-node case is vacuous (subtlety
--      `node_membership_v_in_g_informal`).**  For `v ∈ G.J`, no
--      directed walk can *end* at `v` because `hE_subset` forces
--      `(v_{k}, v_{k+1}) ∈ G.E → v_{k+1} ∈ G.V`, so the only
--      `Walk G v v` for a J-node is `Walk.nil hv` (length 0).  The
--      `0 < p.length` clause then excludes that single witness, so
--      the J-node clause of `∀ v ∈ G` is auto-satisfied.  No expressive
--      power lost relative to a `∀ v ∈ G.V`-only quantifier.
--   2. **Acyclicity excludes directed self-loops (subtlety
--      `directed_self_loops_not_excluded`, resolved by the LN
--      addition).**  As detailed in the design block above, any
--      `(v, v) ∈ G.E` for `v ∈ G.V` triggers a length-1 directed walk
--      witness, making `G.IsAcyclic = False`.  This is consistent
--      with standard graph theory (cycles of length 1 are cycles)
--      but is a behavioural difference from `def_3_1` (which admits
--      `E` self-loops freely).  Downstream rows that wish to
--      *construct* an acyclic CDMG must ensure their `E` field has
--      no self-loops.
--   3. **Bidirected self-loops are already excluded at the `def_3_1`
--      level.**  `CDMG.hL_irrefl` forces `(v, v) ∉ G.L`, so there is
--      no analogous concern on the bidirected side.  But our
--      acyclicity predicate inspects only *directed* walks, so it is
--      blind to bidirected structure regardless — `G.IsAcyclic`
--      depends only on `G.E`, not on `G.L`.
--   4. **No `Decidable` instance** (see design block).
--   5. **The literal LN quantification is over `J ∪ V`, not a more
--      restrictive subset.**  Should a future row need a "restricted
--      acyclicity" notion (e.g. "no cycle confined to `V \ W`"),
--      that would be a separate definition, not a refinement of
--      `IsAcyclic`.
-- def_3_6 -- start statement
def IsAcyclic (G : CDMG Node) : Prop :=
  ∀ v ∈ G, ¬ ∃ p : Walk G v v, p.IsDirectedWalk ∧ 0 < p.length
-- def_3_6 -- end statement

end CDMG

end Causality
