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
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: adjacent
-- def_3_3 -- start statement
def adjacent (G : CDMG Node) (v1 v2 : Node) : Prop := G.sus v1 v2
-- def_3_3 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: adjacent

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
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: into
-- def_3_3 -- start statement
def into (G : CDMG Node) (v : Node) (e : Node × Node) : Prop :=
  (e ∈ G.E ∧ e.2 = v) ∨ (e ∈ G.L ∧ (e.1 = v ∨ e.2 = v))
-- def_3_3 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: into

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
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: outOf
-- def_3_3 -- start statement
def outOf (G : CDMG Node) (v : Node) (e : Node × Node) : Prop :=
  e ∈ G.E ∧ e.1 = v
-- def_3_3 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: outOf

end CDMG

namespace refactor_CDMG

-- def_3_3 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_3 --- end helper

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: adjacent (was: refactor_adjacent)
-- ref: def_3_3 (item i) — refactor
--
-- Adjacency in `G`: `G.refactor_adjacent v1 v2` unfolds to
-- `G.refactor_sus v1 v2`.  Body identical to the original modulo the
-- `CDMG → refactor_CDMG` type retarget; the `sus` predicate already
-- absorbs the `Sym2`-based re-typing of `L` inside its `huh`-disjunct,
-- so no ordered-pair-on-`L` syntax surfaces at this site.
/-
LN tex (item i of `def-edge-relations`):

  For $v_1, v_2 \in J \cup V$, $v_1$ and $v_2$ are called \emph{adjacent
  in $G$} iff
    $(v_1, v_2) \in E \lor (v_2, v_1) \in E \lor (v_1, v_2) \in L$,
  equivalently iff $v_1 \sus v_2 \in G$.
-/
-- ## Design choice
--
-- *Delegation to `refactor_sus`, not inlining the three-way
--   disjunction.*  Item i of the LN block lists two equivalent
--   spellings of adjacency — a three-disjunct set-theoretic form
--   `(v_1, v_2) \in E \lor (v_2, v_1) \in E \lor (v_1, v_2) \in L` and
--   the compact macro form `v_1 \sus v_2 \in G` (def_3_2 item 7).
--   `refactor_sus` already encodes exactly that three-disjunct as
--   `refactor_tuh ∨ refactor_hut ∨ refactor_huh`, which in turn unfolds
--   to the set-theoretic form (with the `huh`-disjunct now phrased as
--   `s(v_1, v_2) ∈ G.L` under the `Sym2` retyping of `L`).  Delegating
--   keeps adjacency *definitionally tied* to the notation primitive
--   rather than duplicating the disjunction in a second place — if a
--   downstream notation tweak ever changes the channel-set "exists an
--   edge between" (e.g. a hypothetical fourth edge type added in a
--   later refactor), adjacency follows automatically, with no
--   shadow copy of the disjunction to keep in sync.  Recomputing the
--   body would also force every downstream proof that case-analyses on
--   adjacency to carry two names (`refactor_adjacent` and
--   `refactor_sus`) for the same predicate.
--
-- *Body unchanged modulo the `G`-type retarget; the `Sym2` retyping
--   of `L` is fully absorbed inside `refactor_sus`.*  The original
--   `adjacent` was `G.sus v1 v2`; the refactored version is
--   `G.refactor_sus v1 v2`.  No ordered-pair-on-`L` syntax surfaces at
--   this site, because the `huh`-disjunct inside `refactor_sus`
--   internally rewrites `(v_1, v_2) ∈ L` to `s(v_1, v_2) ∈ G.L` (see
--   `CDMGNotation.lean`'s `refactor_huh` design block).  This is the
--   minimal-touch port the refactor demands: adjacency itself has no
--   `L`-clause to retype.
--
-- *Symmetry of `refactor_adjacent G v1 v2` and
--   `refactor_adjacent G v2 v1` is inherited from `refactor_sus`.*
--   Under the `Sym2` typing of `L`, `refactor_sus` is *structurally*
--   symmetric: the `tuh ∨ hut` pair flips into itself when arguments
--   are swapped, and the `huh`-disjunct's symmetry is now a
--   *definitional* equality `s(v_1, v_2) = s(v_2, v_1)` via Mathlib's
--   `Sym2` swap quotient (no `hL_symm` invocation needed, contrast
--   with the pre-refactor encoding).  Hence
--   `refactor_adjacent G v1 v2 ↔ refactor_adjacent G v2 v1` is a
--   one-line consequence — no separate `hadjacent_symm` field or
--   lemma is needed in this row; downstream consumers can lean on
--   `refactor_sus`'s symmetry directly.  This is why the LN uses
--   `\sus` (not `\suh` or `\hus`) for adjacency in the first place.
--
-- *Why `def`, not `abbrev`.*  Same rationale as in the original
--   `adjacent` and as `refactor_sus` itself: the LN treats "adjacent
--   in `G`" as a named relation, the building block for walks
--   (`def_3_4`), family relationships (`def_3_5`), and later
--   d-/σ-separation (chapters 6–7).  An `abbrev` would auto-unfold to
--   `refactor_sus` at every elaboration site, eliminating the named
--   abstraction.  Downstream proofs that want the disjunction explicit
--   can chain `unfold refactor_CDMG.refactor_adjacent
--   refactor_CDMG.refactor_sus` to reach the three primitive cases.
--
-- *Downstream consumers are insensitive to the refactor at this
--   site.*  `def_3_4`'s "alternating sequence of adjacent nodes and
--   edges" appeals to adjacency; `def_3_5`'s family sets are subsets
--   of the adjacency relation; chapters 6–7's d-/σ-separation define
--   "paths" on the underlying adjacency graph.  Each such consumer
--   sees the same one-line def `G.adjacent v1 v2 := G.sus v1 v2`
--   after Phase 7 cleanup; only the *body of `sus`* changed shape
--   (its `huh`-disjunct), not the adjacency-level API.  So the
--   refactor's cascade through adjacency is structurally invisible to
--   every adjacency-consuming proof.
-- def_3_3 -- start statement
def refactor_adjacent (G : refactor_CDMG Node) (v1 v2 : Node) : Prop :=
  G.refactor_sus v1 v2
-- def_3_3 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: adjacent

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: intoE (was: refactor_intoE)
-- ref: def_3_3 (item ii, E-channel half) — refactor
--
-- Directed (E-channel) edge `e` into vertex `v` in `G`:
-- `G.refactor_intoE v e` unfolds to `e ∈ G.E ∧ e.2 = v` — an ordered
-- pair counts as "into v" on the directed channel iff its head is `v`.
-- Net-new declaration: the original unified `into` is split by channel
-- because under the refactor `G.L : Finset (Sym2 Node)` no longer
-- admits ordered-pair membership, so the L-clause needs its own
-- predicate (next decl `refactor_intoL`).  Body identical to the
-- E-disjunct of the original `into`.
/-
LN tex (item ii of `def-edge-relations`, E-channel half):

  For an ordered pair $e = (e_1, e_2) \in (J \cup V) \times (J \cup V)$
  and $v \in J \cup V$, $e$ is an \emph{edge into $v$} on the directed
  channel iff $e \in E \land e_2 = v$.
-/
-- ## Design choice
--
-- *Net-new declaration (E-channel half of a forced split).*  The
--   original unified `def into` had a single body
--   `(e ∈ G.E ∧ e.2 = v) ∨ (e ∈ G.L ∧ (e.1 = v ∨ e.2 = v))` — a
--   disjunction over `E ∪ L`-membership, with the single argument
--   `e : Node × Node` serving both disjuncts because both `G.E` and
--   `G.L` had the *same* ordered-pair carrier.  Under the refactor
--   `G.L : Finset (Sym2 Node)`, so the `e ∈ G.L` disjunct can no
--   longer typecheck: a single `e` cannot simultaneously be an ordered
--   pair (for the E-clause) and an unordered pair (for the L-clause).
--   The natural resolution — *one predicate per carrier* — is to
--   split `into` into an E-half and an L-half; this declaration is the
--   E-half.  Its body is *identical* to the E-disjunct of the original
--   `into` (`e ∈ G.E ∧ e.2 = v`); no semantic content is lost in the
--   split, only the disjunction is dissolved at the type level.
--
-- *Split rather than a sum-type unification.*  A "preserve the unified
--   API" alternative — `def into (v) (e : Node × Node ⊕ Sym2 Node)`
--   with a `match` over the two summands — was considered and
--   rejected.  Every downstream consumer would have to wrap edges in
--   `Sum.inl` / `Sum.inr` at the call site and case-split through the
--   sum to dispatch on channel; the unified predicate would gain
--   nothing because the case-split is *already* present at the call
--   site (the consumer reaches `into` from a context where the channel
--   is known).  Existential wrapping was rejected for the same reason.
--   The split mirrors how `def_3_5` already splits family operators:
--   `Pa` and `Ch` consume `G.E`, `Sib` consumes `G.L`, each typed by
--   its carrier; the typed-edges design ethos of `cdmg_typed_edges`
--   makes this the consistent shape across the chapter (see workspace
--   `def_3_3` for the full split-vs-sum rationale).
--
-- *Argument typing `(e : Node × Node)`, same as the original `into`'s
--   E-clause.*  No subtype wrapping into `((J ∪ V) × V)` — consistent
--   with `refactor_CDMG.E : Finset (Node × Node)` keeping its carrier
--   ordered-pair-typed plus a separate `hE_subset` field, rather than
--   pushing the subset constraint into the type.  The "in particular,
--   only edges in `G.E` can be into `v` on the E-channel" property is
--   a *consequence* of the `e ∈ G.E` conjunct in the body, not a
--   precondition the caller must supply.  An ordered pair `e ∉ G.E`
--   falls through the `e ∈ G.E` check and `G.refactor_intoE v e` is
--   `False`, exactly as desired.
--
-- *Body `e ∈ G.E ∧ e.2 = v`, not `e ∈ G.E ∧ (e.1 = v ∨ e.2 = v)`.*
--   The LN's "into `v`" specifically means "`v` is the head"; the head
--   coordinate is `.2` under the LN's `(tail, head)` directed-edge
--   convention used throughout chapter 3 (cf. `CDMGNotation.lean`'s
--   `refactor_tuh` body `(v1, v2) ∈ G.E` for the writing
--   `v_1 \tuh v_2`).  Replacing `e.2 = v` with the symmetric form
--   `e.1 = v ∨ e.2 = v` would conflate "into" with "incident at" for
--   directed edges — sweeping up the tail-incident edges that the LN
--   classifies as `outOf`, not `into`.  This was a load-bearing design
--   constraint of the original `into` and is preserved verbatim here.
--
-- *Why no unified `refactor_into` that abstracts over both carriers.*
--   Built on top of the split below (`refactor_intoL`), a unified
--   predicate `refactor_into v` would have to take its edge argument
--   as either a sum type (`Node × Node ⊕ Sym2 Node`) or behind an
--   existential.  Either way, downstream consumers gain nothing: every
--   use site already knows which channel it's working on (walk-step
--   constructors `.forwardE` / `.backwardE` vs `.bidir` in
--   `def_3_4`'s typed `WalkStep`; family operators `Pa`/`Ch` vs `Sib`
--   in `def_3_5`; collider-classification in `def_3_15`–`def_3_18`).
--   Threading a sum at every call site would force a `.elim` /
--   `match` on the channel tag where the channel is already
--   syntactically known — pure overhead.  Splitting at the def site
--   pushes the case-analysis to its natural place (the call site,
--   where the channel is bound) instead of into the consumer.
--
-- *Edge-level predicate parameterised by `(v, e)`, mirroring the
--   original `into` shape.*  The LN's item ii classifies *edges* of
--   `G` relative to a bound vertex `v`; the order `(v : Node) (e :
--   Node × Node)` matches that reading ("`G.refactor_intoE v`
--   partially applied is the predicate `edge is into v on the E
--   channel`").  Resolves the LN-wording-check subtlety
--   `out_of_v2_not_literally_defined` the same way the original
--   `into` did: the predicate is well-defined for *any* vertex `v`,
--   not only the first-labelled endpoint of a particular writing.
--
-- *Why `v` ranges over the ambient `Node`, not over `v ∈ G.V`
--   (or `v ∈ G.J ∪ G.V`).*  Mirror of the original `into`'s argument
--   convention, in turn matching `refactor_sus`, `refactor_tuh`, etc.
--   in `CDMGNotation.lean`.  If `v ∉ G`, no pair in `G.E` can have
--   `v` at the `.2` coordinate (by `refactor_CDMG.hE_subset`'s
--   `e.2 ∈ V`), so `G.refactor_intoE v e` is vacuously `False` — no
--   junk side-condition is threaded through call sites.  Restricting
--   `v` to `G.V ∪ G.J` at the type level would force every downstream
--   chain ("vertex-on-walk → into-which-edges" in `def_3_4`,
--   "child → in-edge" in `def_3_5`, "intervened vertex → removed
--   in-edges" in `def_3_10`) to carry a membership proof for `v` it
--   can otherwise discharge implicitly.
--
-- *Why `def`, not `abbrev`.*  Same rationale as the original `into`
--   and the items in `CDMGNotation.lean`: `refactor_intoE v` is a
--   named LN relation ("edges into `v` on the directed channel")
--   used downstream as an abstraction.  An `abbrev` would auto-unfold
--   to `e ∈ G.E ∧ e.2 = v` at every elaboration site, masking the
--   abstraction.  Downstream proofs unfold on demand via
--   `unfold refactor_CDMG.refactor_intoE`.
--
-- *Downstream consumers (E-channel half of `into`'s original
--   consumers).*  `def_3_5`'s `Pa^G(v) := {w | w \tuh v \in G}`
--   (parents) is the source-vertex projection of `refactor_intoE`;
--   `def_3_10` hard intervention rewrites `refactor_intoE` for every
--   intervened vertex (the removed-edges set is
--   `{e ∈ G.E | e.2 ∈ W}`, exactly the union of `refactor_intoE` over
--   `W`); chapters 6–7's d-/σ-separation collider conditions, on the
--   directed-edge half, are formulated as "two `refactor_intoE`-edges
--   at the same vertex".
-- def_3_3 -- start statement
def refactor_intoE (G : refactor_CDMG Node) (v : Node) (e : Node × Node) : Prop :=
  e ∈ G.E ∧ e.2 = v
-- def_3_3 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: intoE

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: intoL (was: refactor_intoL)
-- ref: def_3_3 (item ii, L-channel half) — refactor
--
-- Bidirected (L-channel) edge `s` into vertex `v` in `G`:
-- `G.refactor_intoL v s` unfolds to `s ∈ G.L ∧ v ∈ s` — an unordered
-- pair `s : Sym2 Node` counts as "into v" on the bidirected channel iff
-- `s ∈ G.L` and `v` is one of the two endpoints `s` mentions (Mathlib's
-- `Sym2.Mem` / `Membership Node (Sym2 Node)`).  Net-new declaration
-- paired with `refactor_intoE`; the representative-free `v ∈ s`
-- collapses the original `into`'s `e.1 = v ∨ e.2 = v` disjunction by
-- construction, and recovers the LN's "into both endpoints" reading of
-- a bidirected edge exactly.
/-
LN tex (item ii of `def-edge-relations`, L-channel half):

  For an unordered pair $s \in \mathrm{Sym}^2(V)$ (the underlying
  element of $L$) and $v \in J \cup V$, $s$ is an \emph{edge into $v$}
  on the bidirected channel iff $s \in L$ and $v \in s$.
-/
-- ## Design choice
--
-- *Net-new declaration (L-channel half of a forced split).*  Strictly
--   net-new in the sense that the original unified `into` body was a
--   single disjunction `(e ∈ G.E ∧ e.2 = v) ∨ (e ∈ G.L ∧ (e.1 = v ∨
--   e.2 = v))` rather than two pre-split halves.  The forcing reason
--   is the same as for `refactor_intoE`: under
--   `G.L : Finset (Sym2 Node)`, the unified disjunction can no longer
--   typecheck because a single `e` cannot simultaneously be an ordered
--   pair and an unordered pair.  Splitting the L-half off into its
--   own predicate with a `Sym2 Node`-typed argument is the natural
--   resolution; see `refactor_intoE`'s "split rather than a sum-type
--   unification" item for the cross-cutting rationale shared between
--   the two halves.
--
-- *Argument typing `(s : Sym2 Node)`, the carrier of `G.L`.*  Mirrors
--   `refactor_CDMG.L : Finset (Sym2 Node)` exactly; no subtype wrap.
--   The change from the original's `e : Node × Node` to `s : Sym2 Node`
--   is purely a *carrier-typing* shift: the L-channel "edge" the LN
--   refers to is now an unordered pair (the LN's
--   `(V × V) / ((v_1, v_2) \sim (v_2, v_1))` element), and the
--   predicate types accordingly.  Universally quantifies via the
--   Mathlib membership relation `v ∈ s` (`Sym2.Mem` /
--   `Membership Node (Sym2 Node)`), the canonical idiom for "every
--   node `s` mentions" — handling both endpoints simultaneously
--   without picking a representative.  This mirrors
--   `refactor_CDMG.hL_subset`'s use of `Sym2.Mem` to express "every
--   node of every L-edge lies in `V`".
--
-- *Body `s ∈ G.L ∧ v ∈ s`, not destructuring `s` to `s(v_1, v_2)` and
--   checking `v = v_1 ∨ v = v_2`.*  Under the swap quotient
--   `s(v_1, v_2) = s(v_2, v_1)`, picking a representative `(v_1, v_2)`
--   has no canonical value — Mathlib's `Sym2.lift` exists precisely to
--   express functions on `Sym2` without picking one.  The membership
--   form `v ∈ s` handles both endpoints simultaneously and is
--   *literally* the LN's "`v` is one of the two endpoints `s`
--   mentions".  Destructuring via `Sym2.mk` was rejected for the same
--   reasons as in `refactor_CDMG.hL_subset` (see `CDMG.lean`'s design
--   block, item on `hL_subset`): forces a choice that the quotient
--   has no canonical answer for, *and* would require every
--   `refactor_intoL`-consuming proof to destructure through `Sym2.lift`
--   /`Sym2.ind` at the use site rather than the centralised
--   `Sym2.Mem` lookup.
--
-- *Connection to the LN's "into both endpoints" reading of bidirected
--   edges* (wording-check subtlety
--   `bidirected_huh_into_both_out_of_neither`).  The LN's literal item
--   2 says a `v_1 \huh v_2` edge is "into `v_1` AND into `v_2`".
--   Under our split this is captured by *both*
--   `G.refactor_intoL v_1 s(v_1, v_2)` AND
--   `G.refactor_intoL v_2 s(v_1, v_2)` holding, which the
--   `Sym2`-membership condition `v ∈ s` delivers automatically:
--   `v_1 ∈ s(v_1, v_2)` and `v_2 ∈ s(v_1, v_2)` are both true by
--   construction (Mathlib's `Sym2.mem_iff_exists` /
--   `Sym2.mk_left_mem` / `Sym2.mk_right_mem`).  No `(e.1 = v ∨ e.2 =
--   v)` disjunction needed — the swap quotient does the disjunction
--   for free.  This is faithful to the LN; *downstream consumers that
--   build out-degree, children, or any "incident-at-v-but-not-into-v"
--   notion must NOT treat `refactor_intoL` as complementary to
--   `refactor_outOf`*: an `L`-edge incident at `v` is `refactor_intoL`
--   but never `refactor_outOf`, exactly mirroring the LN.
--
-- *No precondition `s ∈ G.L` on the argument.*  Same reasoning as the
--   original `into` and `refactor_intoE`: the predicate body's
--   `s ∈ G.L` conjunct makes any `s` outside `G.L` automatically
--   `False`.  No call site needs to thread an `s ∈ G.L` hypothesis.
--
-- *Why `v` ranges over the ambient `Node`, not over `v ∈ G.V` (or
--   `G.J ∪ G.V`).*  Mirror of `refactor_intoE` and the original
--   `into`: `refactor_CDMG.hL_subset` guarantees `v ∈ s ∈ G.L → v ∈
--   G.V`, so a `v ∉ G` makes `G.refactor_intoL v s` vacuously `False`
--   without any caller-side membership proof.  Note: even though the
--   LN's text restricts `v` to `J ∪ V`, our `v ∈ G.V` (via
--   `hL_subset`) is the tighter property the L-channel actually
--   delivers — L-edges live over `V`, not over `J ∪ V`.
--
-- *Why two predicates, not a unified `refactor_into`.*  See the
--   matching item in `refactor_intoE`'s design block.  The split lets
--   each downstream consumer dispatch on its known channel without
--   case-analysing a sum type; under the typed-walks design of
--   `def_3_4`'s refactored `WalkStep`, the `.bidir` constructor's
--   "edge into endpoint" lookup naturally picks `refactor_intoL`,
--   while `.forwardE` / `.backwardE` pick `refactor_intoE`.  Each
--   walk-step type knows which to call without an intermediate sum.
--
-- *Why `def`, not `abbrev`.*  Same as `refactor_intoE`: `intoL v` is
--   a named LN-derived relation used downstream; `abbrev` would
--   auto-unfold and mask the abstraction.
--
-- *Downstream consumers (L-channel half of `into`'s original
--   consumers).*  `def_3_5`'s `Sib^G(v) := {w | v \huh w \in G}`
--   (siblings) is the partner-vertex projection of `refactor_intoL`
--   (via `Sym2.lift` over the unordered pair); `def_3_10` hard
--   intervention's L-side removal (`L_{do(W)} := L \ {s ∈ L | ∃ v ∈
--   W, v ∈ s}`) is `Finset.filter` against the existential closure
--   of `refactor_intoL`; chapters 6–7's collider conditions, on the
--   bidirected-edge half, are "two `refactor_intoL`-edges at the
--   same vertex" — and crucially can use the structural symmetry of
--   `Sym2` membership for the σ-separation symmetry of `claim_3_22`
--   (the *driving* downstream consumer of the encoding choice).
-- def_3_3 -- start statement
def refactor_intoL (G : refactor_CDMG Node) (v : Node) (s : Sym2 Node) : Prop :=
  s ∈ G.L ∧ v ∈ s
-- def_3_3 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: intoL

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: outOf (was: refactor_outOf)
-- ref: def_3_3 (item iii) — refactor
--
-- Edge `e` out of vertex `v` in `G`: `G.refactor_outOf v e` unfolds to
-- `e ∈ G.E ∧ e.1 = v`.  Only directed edges, with `v` at the tail
-- endpoint, count; no `L`-edge is ever out of any vertex.  Body
-- identical to the original `outOf` modulo the `CDMG → refactor_CDMG`
-- type retarget: the LN excludes L-edges from `outOf` by construction
-- (no L-clause in item iii), so the refactor's L-side retyping is
-- structurally invisible here.  The LN-wording-check subtlety
-- `bidirected_huh_into_both_out_of_neither` continues to apply:
-- bidirected edges contribute zero to `outOf`, even though
-- `refactor_intoL` matches at both their endpoints.
/-
LN tex (item iii of `def-edge-relations`):

  For an ordered pair $e = (e_1, e_2) \in (J \cup V) \times (J \cup V)$
  and $v \in J \cup V$, $e$ is an \emph{edge out of $v$ (in $G$)} iff
  $e \in E \land e_1 = v$.  In particular, no $L$-edge is out of any
  vertex.
-/
-- ## Design choice
--
-- *Body unchanged from the original `outOf`; only `G`'s type is
--   retargeted from `CDMG` to `refactor_CDMG`.*  The LN's item iii
--   enumerates only the E-channel orderings `v_1 \tuh v_2` and
--   `v_2 \hut v_1` — both writings of the *same* ordered `E`-edge.
--   There is no L-channel disjunct in the literal LN text, so there is
--   no retyping pressure on this declaration: `L`'s carrier shift
--   `Finset (Node × Node) → Finset (Sym2 Node)` doesn't surface at any
--   site in the body.  The pre-refactor proof script — "destructure on
--   `e ∈ G.E` and read `e.1`" — ports mechanically: the only diff is
--   the `G : refactor_CDMG Node` parameter shape.  This is the
--   archetypal mechanical-port case the refactor-row briefing
--   describes.
--
-- *Why no L-channel disjunct (i.e. `outOf` is *not* defined
--   symmetrically with `into`).*  Wording-check subtlety
--   `bidirected_huh_into_both_out_of_neither` flagged this asymmetry:
--   the LN treats a bidirected edge as "into both endpoints, out of
--   neither".  Under the LN's CDMG semantics this is *intentional* —
--   a bidirected edge denotes latent confounding, with no directed
--   influence either way — so `refactor_outOf` correctly excludes the
--   `L` channel, just as the original `outOf` did.  *Critical
--   consequence: "into" and "out of" are NOT complementary at any
--   vertex with incident `\huh`-edges.*  A future downstream consumer
--   that defines "out-degree" or "children" via `Finset.filter` over
--   `G.E` will need *this exact predicate* (E-channel only); the
--   literal LN behaviour is the right anchor.  Any consumer that
--   wants "incident at `v` but not into `v`" must combine
--   `refactor_intoE` / `refactor_intoL` with its own incidence
--   predicate — *not* read it off `¬ refactor_outOf`.
--
-- *Symmetry with `refactor_intoE`: same E-only argument typing
--   `(e : Node × Node)`.*  Keeps the E-channel half of "into vs out
--   of" syntactically uniform — the same `Finset (Node × Node)`
--   carrier, the same vertex-ranges-over-`Node` convention, the same
--   `.1` / `.2` head-vs-tail dispatch.  Asymmetry lives only in
--   *which* coordinate is checked: `refactor_intoE` checks `e.2 = v`
--   (head-at-`v`); `refactor_outOf` checks `e.1 = v` (tail-at-`v`).
--   This dual shape is what makes downstream destructurings of a
--   single edge produce both classifications cheaply: case-analyse on
--   `e = (s, t)`, then `refactor_intoE` fires for `t = v` and
--   `refactor_outOf` fires for `s = v`, with no further pattern
--   matching.
--
-- *`e.1 = v` (tail position), the dual of `refactor_intoE`'s
--   `e.2 = v` (head position).*  Under the directed-edge convention of
--   `CDMGNotation.lean` (items 2–3) an element `(s, t) ∈ G.E` is the
--   edge from tail `s` to head `t`, equivalently the writings
--   `s \tuh t` and `t \hut s`.  The LN's item iii says an `E`-edge is
--   "out of `v`" exactly when `v` is the *tail* — the reconciliation
--   item iv of the rewrite confirms that under the identification
--   `v_1 \tuh v_2 \equiv v_2 \hut v_1` the two writings listed in the
--   source-block enumeration ("`v_1 \tuh v_2` or `v_2 \hut v_1`")
--   describe the same `E`-element, both with `v_1` as the tail.
--   Hence `e.1 = v`.
--
-- *Subtlety `out_of_v2_not_literally_defined` — handled by the
--   addition `[inconsistent_writing_order_enumeration_into_vs_out_of]`,
--   no Lean-level intervention needed.*  The LN's text literally only
--   defines "out of `v_1`" for an edge written as `v_1 \star v_2`.
--   The addition resolves this by clarifying that edge-set membership
--   in the "out of `v`" category depends only on the underlying
--   `E`-element, not on the textual writing.  *This is exactly what
--   `refactor_outOf` encodes*: `e ∈ G.E ∧ e.1 = v` ranges over edges
--   whose tail is `v` regardless of writing order, with `v` a freely
--   bound vertex parameter — no implicit-writing-order ambiguity
--   carries over into the Lean.  The original `outOf` already resolved
--   this in the same way; the refactor preserves the resolution
--   verbatim.
--
-- *No precondition `e ∈ G.E` on the argument.*  Same reasoning as the
--   original `outOf` and `refactor_intoE`: the predicate body
--   `e ∈ G.E ∧ e.1 = v` makes any pair outside `G.E` automatically
--   evaluate to `False`.  Threading a precondition would force every
--   call site to carry it.
--
-- *Why `v` ranges over the ambient `Node`.*  Same rationale as
--   `refactor_intoE`: `refactor_CDMG.hE_subset` guarantees any
--   `(s, t) ∈ G.E` has `s ∈ G.J ∪ G.V`, so supplying a `v ∉ G`
--   makes the predicate vacuously `False` without any caller-side
--   membership proof.
--
-- *Why `def`, not `abbrev`.*  Same rationale: `refactor_outOf v` is a
--   named LN relation, used as an abstraction downstream.
--
-- *Downstream consumers (unchanged shape from the original `outOf`).*
--   `def_3_5`'s `Ch^G(v) := {w | v \tuh w \in G}` (children) is the
--   target-vertex projection of `refactor_outOf`; `def_3_6`
--   acyclicity's directed-walk condition uses `refactor_outOf v`
--   implicitly (each directed walk-edge is out of its source);
--   `def_3_10` hard intervention's edge-removal
--   `E_{do(W)} := E \setminus \{e ∈ E | e.1 ∈ W\}` deletes exactly
--   the edges out of every intervened vertex — i.e. the union of
--   `refactor_outOf v` over `v ∈ W`.  None of these consumers need to
--   adapt to the refactor: the `outOf` API surface is identical
--   pre/post (modulo the `G` type), because the `L`-channel retyping
--   does not surface here.
-- def_3_3 -- start statement
def refactor_outOf (G : refactor_CDMG Node) (v : Node) (e : Node × Node) : Prop :=
  e ∈ G.E ∧ e.1 = v
-- def_3_3 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: outOf

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: into
-- The pre-refactor `into` predicate combined the E- and L-channels in a
-- single Prop.  Under `cdmg_typed_edges` it is split into two channel-
-- specific predicates, `intoE` and `intoL`, each carried by its own
-- REPLACEMENT block above.  No combined `into` declaration survives in
-- the post-refactor design; this empty REPLACEMENT block exists only so
-- the finalize-time marker validator can pair the ORIGINAL `into` block
-- with a same-named REPLACEMENT.
-- REFACTOR-BLOCK-REPLACEMENT-END: into

end refactor_CDMG

end Causality
