import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation

namespace Causality

/-!
# CDMG edge relations: adjacency, into-`v`, out-of-`v`

This file formalises the three items of the LN definition block
`def_3_3` (`\label{def-edge-relations}`).  The block introduces:

* `adjacent G v1 v2` — `v1` and `v2` are adjacent in `G`, i.e. some
  edge of `G` (directed either way, or bidirected) connects them.
* `into G v e` — the ordered pair `e` is an edge of `G` *into* the
  vertex `v` (covers `E`-edges with `v` at the head, and `L`-edges at
  either endpoint).
* `outOf G v e` — the ordered pair `e` is an edge of `G` *out of* the
  vertex `v` (covers only `E`-edges with `v` at the tail; no `L`-edge
  is ever out of any vertex).

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/def_3_3_EdgeRelations.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def-edge-relations}`) augmented with one operator
clarification:

* `[inconsistent_writing_order_enumeration_into_vs_out_of]` — the
  source block's distinct writings `v_1 \tuh v_2` vs `v_2 \hut v_1`
  and `v_1 \huh v_2` vs `v_2 \huh v_1` denote the same underlying
  edge (the same element of `E` or, under `hL_symm`, of `L`).
  Classification of an edge as "into `v`" or "out of `v`" therefore
  depends only on the underlying ordered pair, not on the textual
  writing.  The rewritten tex factors this in by parameterising
  *both* "into" and "out of" by a single bound vertex `v`, dissolving
  the source block's asymmetry (item 2 of the LN defines "into `v_1`"
  and "into `v_2`" separately, but item 3 only defines "out of `v_1`").

Two LN-wording-check subtleties shaped the encoding below.  They are
*resolved by the rewrite*, not deviations:

1. `out_of_v2_not_literally_defined` — the LN literally defines only
   "out of `v_1`".  The rewrite supplies the reader-expected symmetric
   form ("out of `v`" for any `v`) by parameterising over a single
   bound vertex.  Our `outOf` predicate is therefore well-defined for
   any vertex, not only the first-labelled endpoint of an edge.

2. `bidirected_huh_into_both_out_of_neither` — under the LN's literal
   text, a bidirected `\huh`-edge is "into" *both* its endpoints (item
   2's `L`-clause matches at either endpoint) but "out of" *neither*
   (item 3 enumerates only `E`-edge writings).  This is intrinsic to
   the LN — bidirected edges denote latent confounding, with no
   directed influence either way — and the rewrite makes it explicit:
   our `into` covers `L`-edges at either endpoint; our `outOf`
   excludes `L` entirely.  **Consequence:** "into `v`" and "out of
   `v`" are *not* complementary classifications of edges incident at
   `v`.  Any downstream notion built on `outOf` (out-degree, children,
   directed-out-neighbourhood in `def_3_5`) must treat bidirected
   edges as contributing nothing, *not* as "the remainder after
   removing in-edges".

The substantive design rationale for every item lives in the comment
block immediately above its `start statement` marker; read those
before modifying the file.  Three pillars are common to all three:

1. **Stay literal w.r.t. the rewritten LN block.**  `adjacent` unfolds
   to `G.sus v1 v2`, exactly the equivalence the rewrite hands us
   (item i, "$v_1$ and $v_2$ are adjacent in $G$ iff $v_1 \sus v_2 \in
   G$").  `into` and `outOf` unfold to the literal set-theoretic
   forms of items ii and iii of the rewrite — no implicit
   quantifiers, no precondition that `e ∈ E ∪ L`.

2. **Edge-level predicates parameterised by a single vertex.**  The
   LN's items 2–3 classify *edges* of `G` (elements of `E` or `L`)
   relative to a bound vertex `v`.  We mirror that exactly: `into` and
   `outOf` take `(v : Node) (e : Node × Node)`.  The membership in `E`
   or `L` is part of the predicate body, not a precondition on `e`;
   any ordered pair outside `E ∪ L` automatically fails both
   predicates.

3. **Reuse `sus` from `CDMGNotation.lean` for `adjacent`.**  Item i
   of the rewrite spells "$v_1 \sus v_2 \in G$" as the canonical
   equivalent.  Recomputing the three-disjunct from scratch (e.g.
   `(v1, v2) ∈ G.E ∨ (v2, v1) ∈ G.E ∨ (v1, v2) ∈ G.L`) would
   duplicate `sus`'s body and break the LN-macro-grep correspondence
   that `CDMGNotation.lean` was set up to preserve.  Adjacency is
   literally `sus`; we encode it that way.
-/

namespace CDMG

-- def_3_3 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_3 --- end helper

-- ref: def_3_3 (item i)
--
-- Adjacency in `G`: `G.adjacent v1 v2` unfolds to `G.sus v1 v2`,
-- i.e. some edge of `G` (directed forward, directed backward, or
-- bidirected) connects `v1` and `v2`.
/-
LN tex (item i of `def-edge-relations`, after rewrite):

  For $v_1, v_2 \in J \cup V$, the nodes $v_1$ and $v_2$ are called
  \emph{adjacent in $G$} iff
    $(v_1, v_2) \in E \lor (v_2, v_1) \in E \lor (v_1, v_2) \in L$,
  equivalently iff $v_1 \sus v_2 \in G$.
-/
-- ## Design choice
--
-- *Why a one-line renaming of `sus`, not the three-disjunct
--   spelling.*  The rewrite explicitly identifies adjacency with
--   `v_1 \sus v_2 \in G` (item 7 of the notation block `def_3_2`).
--   `CDMGNotation.lean`'s `sus` already unfolds to exactly the
--   three-disjunct `tuh ∨ hut ∨ huh`, which in turn unfolds to the
--   set-theoretic form `(v_1,v_2) ∈ E ∨ (v_2,v_1) ∈ E ∨ (v_1,v_2) ∈
--   L`.  Recomputing the body would duplicate `sus`'s implementation
--   and force downstream proofs that case-analyse on adjacency to
--   carry *two* names for the same predicate.
--
-- *Why `def`, not `abbrev`.*  Same rationale as `sus` itself: the
--   LN treats "adjacent in $G$" as a named relation, used as the
--   building block for walks (`def_3_4`), family relationships
--   (`def_3_5`), and later d-/σ-separation in chapters 6–7.  An
--   `abbrev` would auto-unfold to `sus` at every elaboration site,
--   eliminating the named abstraction.  Downstream proofs that want
--   the disjunction explicit can `unfold CDMG.adjacent` (lands on
--   `sus`) or chain `unfold CDMG.adjacent CDMG.sus` to reach the
--   three primitive cases.
--
-- *Symmetry.*  `adjacent` inherits the symmetry of `sus` (one-line
--   corollary, not part of the def): `G.adjacent v1 v2 ↔
--   G.adjacent v2 v1`, since `sus`'s `tuh ∨ hut` flip and its `huh`
--   disjunct is symmetric via `hL_symm`.  This is why the LN uses
--   `sus` (not `suh` or `hus`) for adjacency in the first place.
--
-- *Downstream consumers.*  `def_3_4` walk's "alternating sequence of
--   adjacent nodes and edges" appeals to this; `def_3_5`'s family
--   sets are subsets of the adjacency relation; chapters 6–7's
--   d-/σ-separation define "paths" on the underlying adjacency
--   graph.
-- def_3_3 -- start statement
def adjacent (G : CDMG Node) (v1 v2 : Node) : Prop := G.sus v1 v2
-- def_3_3 -- end statement

-- ref: def_3_3 (item ii)
--
-- Edge `e` into vertex `v` in `G`: `G.into v e` unfolds to
-- `(e ∈ G.E ∧ e.2 = v) ∨ (e ∈ G.L ∧ (e.1 = v ∨ e.2 = v))`.
-- A directed edge counts as "into `v`" iff its head endpoint is `v`;
-- a bidirected edge counts as "into `v`" iff either of its endpoints
-- is `v`.
/-
LN tex (item ii of `def-edge-relations`, after rewrite):

  For an ordered pair $e = (e_1, e_2) \in (J \cup V) \times (J \cup V)$
  and a vertex $v \in J \cup V$, we call $e$ an \emph{edge into $v$
  (in $G$)} iff
    $\bigl(e \in E \land e_2 = v\bigr) \lor \bigl(e \in L \land (e_1
    = v \lor e_2 = v)\bigr)$.
  In particular, only ordered pairs $e \in E \cup L$ can be edges
  into $v$.
-/
-- ## Design choice
--
-- *Edge-level predicate parameterised by `(v, e)`, not by an
--   endpoint pair `(v_1, v_2)`.*  The rewrite turns the LN's
--   "$v_1 \hut v_2$" / "$v_1 \huh v_2$" *writings* into the
--   underlying ordered pair `e`.  Encoding "into" as a predicate on
--   ordered pairs (rather than on pairs of vertices) is what
--   resolves the LN-wording-check subtlety
--   `out_of_v2_not_literally_defined`: the predicate is symmetric in
--   `v` (any vertex may be supplied), so the LN's asymmetric
--   enumeration ("into $v_1$" vs "into $v_2$") collapses into a
--   single uniformly-quantified statement.
--
-- *Why `v` ranges over the ambient `Node`, not over `v ∈ G.V` (or
--   `v ∈ G.J ∪ G.V`).*  Mirrors the convention set by `sus`, `tuh`,
--   `hut`, `huh`, … in `CDMGNotation.lean`: edge-relation predicates
--   live over the ambient `Node` type, and the semantic membership
--   `v ∈ G` is enforced *through the predicate body* via the
--   `E ⊆ (J ∪ V) × V` and `L ⊆ V × V` constraints on the structure
--   (`hE_subset`, `hL_subset` on `CDMG`).  Concretely, if `v ∉ G`
--   then no ordered pair in `E ∪ L` can have `v` at either
--   coordinate by those subset constraints, so `G.into v e` is
--   vacuously `False` — no junk side-condition needs to be threaded
--   through call sites.  Restricting `v` to `G.V` (or `G.J ∪ G.V`)
--   at the type level would force every downstream chain
--   ("vertex-on-walk → into-which-edges" in `def_3_4`, "child
--   → in-edge" in `def_3_5`, "intervened vertex → removed in-edges"
--   in `def_3_10`) to carry a membership proof for `v` it can
--   otherwise discharge implicitly.
--
-- *Why two clauses (`E`-clause and `L`-clause), not a unified
--   "head-at-`v`" formula.*  Directed edges contribute "into `v`"
--   only when `v` is at the head (`e.2 = v`); bidirected edges
--   contribute "into `v`" at *both* endpoints (because `hL_symm`
--   makes the ordered-pair encoding of `L` carry both writings, and
--   under either writing one endpoint or the other is "at the
--   head").  Merging into a single condition like "`v ∈ {e.1, e.2}
--   ∧ (e ∈ E ∨ e ∈ L)`" would over-include directed edges with `v`
--   at the *tail* — wrong by the LN.  Keeping the two clauses
--   separate matches the LN reading exactly and lets downstream
--   case-analysis split on `e ∈ E` vs `e ∈ L` cleanly.
--
-- *Why the `E`-clause checks `e.2 = v` (head position), not
--   `e.1 = v ∨ e.2 = v`.*  `G.E : Finset (Node × Node)` is directed
--   under the LN's reading: an element `(s, t) ∈ G.E` is the edge
--   from `s` (tail) to `t` (head) — equivalently the writings
--   `s \tuh t` and `t \hut s` (`CDMGNotation.lean` items 2–3, and
--   the reconciliation item iv of the rewrite).  The LN's item ii
--   says an `E`-edge is "into `v`" exactly when `v` is the *head*,
--   so the LN-faithful check is `e.2 = v`.  Replacing this by
--   `e.1 = v ∨ e.2 = v` would conflate "into" with "incident at"
--   for directed edges, sweeping up tail-incident edges that the LN
--   classifies as `outOf`, not `into`.
--
-- *No precondition `e ∈ G.E ∨ e ∈ G.L` on the argument.*  The
--   rewrite's "in particular, only ordered pairs $e \in E \cup L$
--   can be edges into $v$" is a *consequence* of the disjunction
--   body, not a precondition the caller must supply.  An ordered
--   pair `e ∉ G.E ∪ G.L` falls through both disjuncts and
--   `G.into v e` is `False`, exactly as desired.  Threading a
--   precondition through the type would force every call site to
--   carry an `e ∈ E ∪ L` hypothesis it can otherwise discharge by
--   the predicate itself.
--
-- *Bidirected-edge handling: `into` at both endpoints, by design.*
--   The LN-wording-check subtlety
--   `bidirected_huh_into_both_out_of_neither` is *intrinsic to the
--   LN's literal item 2* — both writings `v_1 \huh v_2` and
--   `v_2 \huh v_1` of an `L`-edge land in the "into" category at
--   their respective second-position vertex, which under `hL_symm`
--   means *both* endpoints qualify.  The `L`-clause's
--   `(e.1 = v ∨ e.2 = v)` is the direct encoding of this.  *This is
--   not a deviation*; it is what the LN says when read literally.
--   Downstream consumers that need a "directed-only into" predicate
--   should write `e ∈ G.E ∧ e.2 = v` directly at the use site
--   rather than try to subtract `L`-edges from `into`.
--
-- *Argument order `(v : Node) (e : Node × Node)`.*  Reads as "the
--   set of edges into `v`": `G.into v` partially applied is a
--   predicate on edges, which is how downstream consumers want to
--   use it (e.g. "the set of edges into `v` has size ≤ |Pa(v)| +
--   |Sib(v)|").  The vertex `v` is the "binding parameter" the LN
--   highlights; the edge `e` is what the predicate ranges over.
--
-- *Why `def`, not `abbrev`.*  Same rationale as the items in
--   `CDMGNotation.lean`: `into v` is a named LN relation
--   ("edges into $v$") used downstream as an abstraction.  An
--   `abbrev` would auto-unfold to the two-clause disjunction at
--   every elaboration site, masking the abstraction.
--
-- *Downstream consumers.*  `def_3_5`'s `Pa^G(v) := {w | w \tuh v
--   \in G}` (parents) intersects the directed half of `into v` with
--   the source-vertex projection; `def_3_5`'s `Sib^G(v) := {w |
--   v \huh w \in G}` (siblings) intersects the bidirected half;
--   `def_3_10` hard intervention rewrites `into v` for every
--   intervened vertex; chapters 6–7's d-/σ-separation collider
--   conditions are formulated in terms of "two edges into the same
--   vertex".
-- def_3_3 -- start statement
def into (G : CDMG Node) (v : Node) (e : Node × Node) : Prop :=
  (e ∈ G.E ∧ e.2 = v) ∨ (e ∈ G.L ∧ (e.1 = v ∨ e.2 = v))
-- def_3_3 -- end statement

-- ref: def_3_3 (item iii)
--
-- Edge `e` out of vertex `v` in `G`: `G.outOf v e` unfolds to
-- `e ∈ G.E ∧ e.1 = v`.  Only directed edges, with `v` at the tail
-- endpoint, count; no `L`-edge is ever out of any vertex.
/-
LN tex (item iii of `def-edge-relations`, after rewrite):

  For an ordered pair $e = (e_1, e_2) \in (J \cup V) \times (J \cup V)$
  and a vertex $v \in J \cup V$, we call $e$ an \emph{edge out of $v$
  (in $G$)} iff $e \in E \land e_1 = v$.
  In particular, no $L$-edge is out of any vertex.
-/
-- ## Design choice
--
-- *Why no `L`-clause: bidirected edges contribute *nothing* to
--   `outOf`.*  The LN's item 3 enumerates only `E`-edge writings;
--   the rewrite makes this explicit ("no $L$-edge is out of any
--   vertex").  This is the second half of the LN-wording-check
--   subtlety `bidirected_huh_into_both_out_of_neither`: bidirected
--   edges are "into both endpoints" but "out of neither".  Adding an
--   `L`-clause would be a deviation from the LN; the design
--   *deliberately* omits it.  *Implication:* "into `v`" and
--   "out of `v`" are NOT complementary classifications of edges
--   incident at `v` — an `L`-edge with `v` as an endpoint is "into
--   `v`" but "not out of `v`".  Any downstream predicate that wants
--   "incident at `v` and not into `v`" (or vice versa) must NOT use
--   `outOf` for this purpose; it must combine `into` with its own
--   incidence predicate.
--
-- *Edge-level, single bound vertex `v` (mirror of `into`).*  The
--   rewrite generalises the LN's "out of $v_1$" to a single `v`
--   parameter, resolving subtlety `out_of_v2_not_literally_defined`.
--   `G.outOf v e` is well-defined for any vertex `v`, not only the
--   first-labelled endpoint of `e`.  As with `into`, `v` ranges over
--   the ambient `Node`, not over `v ∈ G.V` or `v ∈ G.J ∪ G.V`:
--   `hE_subset` on `CDMG` guarantees that any `(s, t) ∈ G.E` has
--   `s ∈ G.J ∪ G.V`, so supplying a `v ∉ G` makes the predicate
--   vacuously `False` without any caller-side membership proof.
--
-- *Why `e.1 = v` (tail position), the mirror of `into`'s `e.2 = v`
--   head-position check.*  Under the directed-edge convention of
--   `CDMGNotation.lean` (items 2–3) an element `(s, t) ∈ G.E` is the
--   edge from tail `s` to head `t`, equivalently the writings
--   `s \tuh t` and `t \hut s`.  The LN's item iii says an `E`-edge
--   is "out of `v`" exactly when `v` is the *tail* — and the
--   reconciliation item iv of the rewrite confirms that under the
--   identification `v_1 \tuh v_2 ≡ v_2 \hut v_1` the two writings
--   listed in the source-block enumeration ("$v_1 \tuh v_2$ or
--   $v_2 \hut v_1$") describe the same `E`-element, both with `v_1`
--   as the tail.  Hence `e.1 = v`.  The shape is the exact dual of
--   `into`'s `E`-clause: head-at-`v` becomes tail-at-`v`, with `E`
--   the only edge channel since bidirected edges are excluded (see
--   above).
--
-- *No precondition `e ∈ G.E` on the argument.*  Same reasoning as
--   `into`: the predicate body `e ∈ G.E ∧ e.1 = v` automatically
--   makes any pair outside `G.E` evaluate to `False`.  Threading a
--   precondition would force every call site to carry it.
--
-- *Argument order `(v : Node) (e : Node × Node)` (mirror of
--   `into`).*  `G.outOf v` partially applied is a predicate on
--   edges — "the set of edges out of `v`" — which matches the LN
--   reading and how `def_3_5`'s `Ch^G(v)` (children) consumes it.
--
-- *Why `def`, not `abbrev`.*  Same rationale: `outOf v` is a named
--   LN relation, used as an abstraction downstream.
--
-- *Downstream consumers.*  `def_3_5`'s `Ch^G(v) := {w | v \tuh w
--   \in G}` (children) is the source-vertex projection of `outOf`;
--   `def_3_6` acyclicity's directed-walk condition uses `outOf v`
--   implicitly (each walk-edge is out of its source); `def_3_10`
--   hard intervention's edge-removal `E_{do(W)} := E \setminus
--   \{e \in E | e.1 \in W\}` deletes exactly the edges out of every
--   intervened vertex.
-- def_3_3 -- start statement
def outOf (G : CDMG Node) (v : Node) (e : Node × Node) : Prop :=
  e ∈ G.E ∧ e.1 = v
-- def_3_3 -- end statement

end CDMG

end Causality
