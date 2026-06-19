import Chapter3_GraphTheory.Section3_1.Walks

namespace Causality

/-!
# Family relationships on a CDMG: items 1–14 of `def_3_5`

This file formalises every named family-relation set introduced in
`def_3_5` (`\label{def:family_rel}`).  Every separation argument and
do-calculus rewrite in chapters 5+ ultimately rests on these sets:
`Pa / Ch / Anc / Desc` underpin local Markov properties and the
backdoor / front-door / general adjustment criteria, `Dist` parametrises
the c-component decomposition used by the ID algorithm, `Sc` flags the
non-acyclic regime in which `σ`-separation supplants `d`-separation,
and `NonDesc` carves the "untouched-by-do(A)" frontier for hard
intervention.  Getting the carrier and self-membership behaviour right
here is therefore load-bearing for ten chapters.

## LN block (verbatim)

```
Let $G=(J,V,E,L)$ be a CDMG, $v,w \in V$ and $A \ins J \cup V$ a subset of nodes.
We then define:
  1. The set of *parents* of $v$ in $G$: $\Pa^G(v):=\{w \in G | w \tuh v \in G\}$.
  2. The set of *parents* of $A$ in $G$: $\Pa^G(A):= \bigcup_{v \in A} \Pa^G(v)$.
  3. The set of *children* of $v$ in $G$: $\Ch^G(v):=\{w \in G | v \tuh w \in G\}$.
  4. The set of *children* of $A$ in $G$: $\Ch^G(A):= \bigcup_{v \in A} \Ch^G(v)$.
  5. The set of *siblings* of $v$ in $G$: $\Sib^G(v):=\{w \in G | v \huh w \in G\}$.
  6. The set of *ancestors* of $v$ in $G$:
        $\Anc^G(v):=\{w \in G | \exists \text{ directed walk: } w \tuh \cdots \tuh v \in G\}$.
        Note: $v \in \Anc^G(v)$.
  7. The set of *ancestors* of $A$ in $G$: $\Anc^G(A):= \bigcup_{v \in A} \Anc^G(v)$.
        Note: $A \ins \Anc^G(A)$.
  8. The set of *descendants* of $v$ in $G$:
        $\Desc^G(v):=\{w \in G | \exists \text{ directed walk: } v \tuh \cdots \tuh w \in G\}$.
        Note: $v \in \Desc^G(v)$.
  9. The set of *descendants* of $A$ in $G$: $\Desc^G(A):= \bigcup_{v \in A} \Desc^G(v)$.
        Note: $A \ins \Desc^G(A)$.
 10. The set of *non-descendants* of $A$ in $G$:
        $\NonDesc^G(A) := (J \cup V) \sm \Desc^G(A)$.
 11. The *strongly connected component* of $v$ in $G$:
        $\Sc^G(v) := \Anc^G(v) \cap \Desc^G(v)$.
        Note: $v \in \Sc^G(v)$.
 12. The (union of) *strongly connected components* of $A$ in $G$:
        $\Sc^G(A) := \bigcup_{v \in A} \Sc^G(v)$.
        Note: $A \ins \Sc^G(A)$.
 13. The *district* of $v$ in $G$:
        $\Dist^G(v) := \{w \in G | \exists \text{ bidirected walk: }
            v \huh v_1 \huh \cdots \huh v_{n-1} \huh w \in G\}$.
        Note: $v \in \Dist^G(v)$.
 14. The *district* of $A$ in $G$: $\Dist^G(A) := \bigcup_{v \in A} \Dist^G(v)$.
        Note: $A \ins \Dist^G(A)$.
```

(The LN source contains a commented-out `MBl^G_d` / `MBl^G_\sigma`
"Markov blanket" block; those items are NOT formalised here per the
LN's own comment-out, deferred until the acyclification machinery of
`def_3_15` is in place.)

## Operator additions that fire here (treated as part of the LN spec)

* `[self_membership_notes_require_length_zero_walks]` — the LN's
  "$v \in \Anc^G(v)$ / $\Desc^G(v)$ / $\Sc^G(v)$ / $\Dist^G(v)$" notes
  hold UNCONDITIONALLY (no self-loop required) because the trivial
  walk of length $0$ (single vertex, no edges) is admitted as both
  a directed and a bidirected walk.  This is *already* enforced one
  layer down by `Walks.lean`: `Walk.nil hv : Walk G v v` is the
  trivial walk, and both `Walk.IsDirectedWalk (Walk.nil _) = True`
  and `Walk.IsBidirectedWalk (Walk.nil _) = True` reduce vacuously.
  Concretely, `(Walk.nil hv) : Walk G v v` is a witness of
  `∃ p : Walk G v v, p.IsDirectedWalk`, hence `v ∈ Anc G v` whenever
  `v ∈ G`; analogously for `Desc / Sc / Dist`.

* `[type_mismatch_individual_vs_set_versions]` — the LN preamble says
  "$v, w \in V$" but the single-vertex defs (Pa / Ch / Sib / Anc /
  Desc / Sc / Dist) are read for any `v ∈ J ∪ V` so that the
  set-versions `Pa^G(A) := ⋃_{v ∈ A} Pa^G(v)` over `A ⊆ J ∪ V` are
  well-typed.  Concretely, our single-vertex defs take `v : Node`
  unconditionally — no subtype, no `v ∈ G` hypothesis.  Membership in
  the resulting Finset is filtered by the underlying edge/walk
  predicate, so e.g. `Pa G j` for `j ∈ J` returns the empty Finset
  (because `G.hE_subset` forces every directed edge `(w, j) ∈ G.E` to
  satisfy `j ∈ G.V`, contradicting disjointness of `J` and `V` from
  `G.hJV_disj`), as the LN's natural reading demands.

* `[district_walk_indexing_ambiguous_for_small_n]` — the LN's
  "$v \huh v_1 \huh \cdots \huh v_{n-1} \huh w$" is syntactic sugar
  for "any-length bidirected walk including the length-0 walk at
  $v$".  We encode this literally as
  `∃ p : Walk G v w, p.IsBidirectedWalk`, with NO nonzero-length
  side condition and no bidirected-self-loop requirement (CDMGs
  forbid those anyway, per `CDMG.hL_irrefl`).

## Core encoding choices (load-bearing across the whole file)

* **Carrier: `Finset Node` uniformly.**  Every family-relation set is
  a `Finset Node`, never a `Set Node`.  Three reasons.
  (1) The LN reads "$\{w \in G | \ldots\}$" — the ambient universe is
      `G.J ∪ G.V`, itself a `Finset Node` — so the natural Lean shape
      is a filter on `G.J ∪ G.V`.
  (2) Downstream rows compose family sets with set-algebra:
      `NonDesc G A := (G.J ∪ G.V) \ DescSet G A` uses `Finset.sdiff`;
      `Sc G v := Anc G v ∩ Desc G v` uses `Finset.inter`; the
      set-versions use `Finset.biUnion`.  All of these stay inside
      `Finset Node` with zero coercion; switching `Anc` to `Set Node`
      would force `Finset.toSet` lifts at every set-version
      definition.
  (3) `Finset Node` carries decidable membership and a `Fintype`
      instance, which downstream chapters 4+ rely on for sums over
      family sets (e.g. CBN factorisations `∑_{w ∈ Pa(v)} …`).

* **`noncomputable` for the walk-existential items.**  Walk
  reachability (`Anc / Desc / Dist`, and transitively `Sc / NonDesc /
  AncSet / DescSet / ScSet / DistSet`) is not primitively decidable
  because `Walk G u w` is an inductive of arbitrary length.  We use
  `open Classical in` to import `Classical.propDecidable`, allowing
  `Finset.filter` to resolve its `DecidablePred` obligation
  classically; the resulting defs are `noncomputable`.  This is a
  pragmatic choice for chapter 3 — decidability could be recovered
  constructively by bounding walk length at `(G.J ∪ G.V).card` (every
  reachable vertex is reachable by a *path*, whose length is at most
  the carrier's cardinality) and searching, but the construction adds
  significant overhead and is not needed for any chapter 3 proof.
  Plain `Pa / Ch / Sib`, whose predicates reduce to `Finset`
  membership, stay computable.

* **Single-vertex defs take `v : Node` unconditionally.**  Per
  operator addition `[type_mismatch_individual_vs_set_versions]`.  No
  `v ∈ G` hypothesis, no subtype.  This makes the set-versions
  `A.biUnion (G.Pa)` over `A : Finset Node` well-typed without
  coercions, even when `A` happens to contain a `j ∈ G.J` (whose
  family sets degenerate to the empty Finset, as the LN demands).

* **Set versions named with the `Set` suffix.**  The LN overloads
  `Pa^G(v)` (single vertex) and `Pa^G(A)` (set of vertices) under one
  symbol; Lean cannot.  We split into `Pa` (single) and `PaSet` (set,
  built via `Finset.biUnion`).  Analogously `Ch / ChSet`, `Anc /
  AncSet`, `Desc / DescSet`, `Sc / ScSet`, `Dist / DistSet`.
  `Sib` has no set-version per the LN (the `\item[]` for siblings is
  commented out in the source).  `NonDesc` is only ever a set-version
  per the LN.

* **Directed-self-loops corner case for `Pa / Ch`.**  Per `def_3_1`,
  directed self-loops `(v, v) ∈ G.E` are admitted by the CDMG type
  (only bidirected self-loops are forbidden, via `hL_irrefl`).  Under
  the literal LN reading "$\Pa^G(v) := \{w | w \tuh v\}$", this means
  `v ∈ G.Pa v` and `v ∈ G.Ch v` whenever `v → v ∈ G.E`.  The LN
  source contains a *commented-out* alternative for the set-version
  ("maybe better for sets: $\Pa^G(A) := (\bigcup \Pa^G(v)) \sm A$.
  but then if $v \tuh v \in E$ then $v \notin \Pa^G(\{v\}) \neq
  \Pa^G(v) \ni v$") — the author considered and rejected the
  exclusive form, so the inclusive form $\Pa^G(\{v\}) = \Pa^G(v)$ is
  intentional.  We follow the literal LN; downstream proofs that
  silently assume "parents distinct from `v`" must add the
  `v ∉ G.Pa v` hypothesis at the use site.

* **All defs live under `namespace CDMG`.**  Mirrors
  `CDMGNotation.lean` / `EdgeRelations.lean`: every relation taking a
  `G : CDMG Node` as its first argument is callable via dot-notation
  `G.Pa v` / `G.Anc v` / `G.PaSet A`, matching the LN's `\Pa^G(v)`
  reading left-to-right.

## Subtleties registered by the working-phase wording check

The four ids reported by `check_ln_wording` for this row are:
* `single_vertex_defs_typed_V_but_set_versions_iterate_over_A_in_JV`
  — resolved by operator addition
  `[type_mismatch_individual_vs_set_versions]`, encoded via the
  `v : Node` (unrestricted) signature.
* `directed_self_loop_makes_v_own_parent_child` — flagged above; we
  follow literal LN (inclusive).
* `anc_desc_dist_self_inclusion_relies_on_trivial_walk_convention` —
  resolved by operator addition
  `[self_membership_notes_require_length_zero_walks]`, with the
  trivial-walk reading enforced one layer down in `Walks.lean`.
* `district_walk_notation_does_not_quantify_n` — resolved by operator
  addition `[district_walk_indexing_ambiguous_for_small_n]`, encoded
  as the literal `∃ p : Walk G v w, p.IsBidirectedWalk` without
  length-side-condition.
-/

namespace CDMG

variable {Node : Type*} [DecidableEq Node]

/-! ## Items 1–2 — parents -/

-- ref: def_3_5 (item 1 — Pa^G(v))
--
-- Parents of a vertex `v` in `G`: the set of nodes `w ∈ J ∪ V` that
-- have a directed edge to `v`.  Literal LN: `{w ∈ G | w → v ∈ G}`.
/-
LN tex (item 1):

  The set of *parents* of $v$ in $G$:
    $\Pa^G(v):=\{w \in G\,|\, w \tuh v \in G\}$.
-/
-- ## Design choice
--
-- *Carrier `Finset Node` via `Finset.filter` on `G.J ∪ G.V`.*  See
--   the top docstring's "Core encoding choices".  This is the natural
--   shape for "$\{w \in G | \ldots\}$" and the load-bearing choice for
--   chapter 4+: CBN factorisations `∏_v p(v | Pa(v))` index ordered
--   products over `Pa`, which requires a `Finset` (with `DecidableEq`
--   for product expansion), not a `Set`.  `(w, v) ∈ G.E` is
--   `Finset`-membership decidable, so this def stays computable.
--
-- *Why `(w, v) ∈ G.E`, not `G.tuh w v` / `G.edgeOutOf w v`.*  Both
--   unfold to the same thing; the bare `(w, v) ∈ G.E` is one less
--   layer of indirection and matches the LN's "$w \tuh v \in G$"
--   reading via `def_3_2`'s `tuh w v := (w, v) ∈ G.E`.  A `simp only
--   [CDMG.tuh]` from a consumer reaches the same shape.
--
-- *Signature `v : Node` (unrestricted), not `v ∈ G.V`.*  Per operator
--   addition `[type_mismatch_individual_vs_set_versions]`, the
--   single-vertex def is read for any `v ∈ J ∪ V`, so the set-version
--   `PaSet` over `A ⊆ J ∪ V` type-checks without a coercion.
--   *Boundary consequence:* for any `j ∈ G.J`, `G.Pa j = ∅` —
--   `G.hE_subset` forces every directed edge `(w, j) ∈ G.E` to have
--   target `j ∈ G.V`, contradicting `G.hJV_disj`.  Inputs have no
--   parents; this is the LN's intended reading made literal.
--
-- *Directed self-loops admit `v ∈ G.Pa v`.*  Per `def_3_1`, `(v, v)
--   ∈ G.E` is type-admissible (only bidirected self-loops are
--   forbidden, via `hL_irrefl`).  The LN considered and rejected the
--   `\sm A` exclusion at the set-version level — see `PaSet` below —
--   so the inclusive reading is intentional.  Downstream proofs that
--   need "parents distinct from `v`" add the `v ∉ G.Pa v` hypothesis
--   at the use site rather than baking it into this def.
-- def_3_5 -- start statement
def Pa (G : CDMG Node) (v : Node) : Finset Node :=
  (G.J ∪ G.V).filter (fun w => (w, v) ∈ G.E)
-- def_3_5 -- end statement

-- ref: def_3_5 (item 2 — Pa^G(A))
--
-- Parents of a *set* of vertices `A` in `G`: the union of `Pa^G(v)`
-- over `v ∈ A`.  Encoded as `Finset.biUnion`.
/-
LN tex (item 2):

  The set of *parents* of $A$ in $G$:
    $\Pa^G(A):= \bigcup_{v \in A} \Pa^G(v)$.
-/
-- ## Design choice
--
-- *`Finset.biUnion`, not `⋃` over `Set`.*  Keeps the carrier in
--   `Finset Node`; reuses `DecidableEq Node` from `def_3_1` for the
--   union's deduplication.  Stays computable.
--
-- *`A : Finset Node`, not `A ⊆ G.J ∪ G.V`.*  Per addition
--   `[type_mismatch_individual_vs_set_versions]`; even if `A` strays
--   outside `G.J ∪ G.V`, the per-vertex `G.Pa v` for an out-of-graph
--   `v` just contributes the empty finset (since the filter universe
--   is `G.J ∪ G.V`).  Avoiding a subset hypothesis keeps consumers
--   free of `Finset.subset_*` plumbing.
--
-- *Pure `biUnion`, no `\ A` subtraction.*  The LN source (visible
--   above) contains a commented-out alternative `\Pa^G(A) :=
--   (\bigcup_{v ∈ A} \Pa^G(v)) \sm A`, with the author's own caveat
--   "but then if $v \tuh v \in E$ then $v \notin \Pa^G(\{v\}) \neq
--   \Pa^G(v) \ni v$".  The author *deliberately rejected* the
--   exclusive form to preserve `\Pa^G(\{v\}) = \Pa^G(v)` under
--   directed self-loops.  We follow the LN literally — no `\ A` —
--   which gives `G.PaSet {v} = G.Pa v` definitionally and lets the
--   set / single-vertex versions interoperate without case-splitting
--   on self-loops.  Downstream rows needing the exclusive form must
--   spell `G.PaSet A \ A` at the use site.
-- def_3_5 -- start statement
def PaSet (G : CDMG Node) (A : Finset Node) : Finset Node :=
  A.biUnion G.Pa
-- def_3_5 -- end statement

/-! ## Items 3–4 — children -/

-- ref: def_3_5 (item 3 — Ch^G(v))
--
-- Children of a vertex `v` in `G`: the set of nodes `w ∈ J ∪ V` such
-- that `v` has a directed edge to `w`.  Literal LN: `{w ∈ G | v → w}`.
/-
LN tex (item 3):

  The set of *children* of $v$ in $G$:
    $\Ch^G(v):=\{w \in G\,|\, v \tuh w \in G\}$.
-/
-- ## Design choice
--
-- *Mirror of `Pa` with arguments swapped on the edge predicate.*  The
--   filter is `(v, w) ∈ G.E` (note the *vertex* `v` is fixed, `w`
--   ranges).  By `G.hE_subset`, any `w` actually in `G.Ch v` lies in
--   `G.V` (the edge target must be an output node), so `G.Ch v` is
--   automatically disjoint from `G.J` — even though we filter over the
--   broader carrier `G.J ∪ G.V` for symmetry with `Pa`.  Same
--   computable status (Finset-membership predicate) as `Pa`.
--
-- *Asymmetry with `Pa` at the input-node boundary.*  Unlike `G.Pa j =
--   ∅` for `j ∈ G.J` (forced by `hE_subset`), `G.Ch j` for `j ∈ G.J`
--   can be non-empty: an input node may have outgoing directed edges
--   into `G.V`.  Operator addition `[type_mismatch_individual_vs_set
--   _versions]` explicitly highlights this case ("input nodes ($v
--   \in J$) may have children, descendants, etc.").  Future rows
--   that quantify "for every node with no children" should remember
--   to include input nodes in the quantification, not exclude them.
--
-- *Directed self-loops admit `v ∈ G.Ch v`.*  Symmetric to the
--   `Pa` corner case; same LN-author-aware design.
-- def_3_5 -- start statement
def Ch (G : CDMG Node) (v : Node) : Finset Node :=
  (G.J ∪ G.V).filter (fun w => (v, w) ∈ G.E)
-- def_3_5 -- end statement

-- ref: def_3_5 (item 4 — Ch^G(A))
--
-- Children of a *set* of vertices `A` in `G`: union of `Ch^G(v)` over
-- `v ∈ A`.
/-
LN tex (item 4):

  The set of *children* of $A$ in $G$:
    $\Ch^G(A):= \bigcup_{v \in A} \Ch^G(v)$.
-/
-- ## Design choice
--
-- *Mirror of `PaSet`.*  Same `Finset.biUnion` shape, computable,
--   same justification for the unrestricted `A : Finset Node` typing.
--   As with `PaSet`, no `\ A` subtraction — `G.ChSet {v} = G.Ch v`
--   definitionally (matters under directed self-loops).  Downstream
--   `def_3_10` hard intervention pattern-matches on `ChSet A` to
--   identify the edges to cut.
-- def_3_5 -- start statement
def ChSet (G : CDMG Node) (A : Finset Node) : Finset Node :=
  A.biUnion G.Ch
-- def_3_5 -- end statement

/-! ## Item 5 — siblings (no set-version per LN) -/

-- ref: def_3_5 (item 5 — Sib^G(v))
--
-- Siblings of a vertex `v` in `G`: the set of nodes `w ∈ J ∪ V`
-- connected to `v` by a *bidirected* edge.  Literal LN:
-- `{w ∈ G | v ↔ w ∈ G}`.  Symmetric in `v` / `w` as a graph relation
-- (via `CDMG.hL_symm`), even though the filter spelling fixes one
-- argument order.
/-
LN tex (item 5):

  The set of *siblings* of $v$ in $G$:
    $\Sib^G(v):=\{w \in G\,|\, v \huh w \in G\}$.

  (No set-version: the `\item[]` for siblings of a set $A$ is commented
  out in the LN source.)
-/
-- ## Design choice
--
-- *Filter on `(v, w) ∈ G.L`.*  Same Finset-filter shape as `Pa / Ch`.
--   By `G.hL_subset`, any actual sibling `w` lies in `G.V`; the broader
--   `G.J ∪ G.V` carrier is for uniformity with the other family sets.
--   Stays computable.
--
-- *Boundary: `G.Sib j = ∅` for `j ∈ G.J`.*  By `G.hL_subset`,
--   bidirected edges live in `V × V`, so for any `j ∈ G.J` the filter
--   predicate `(j, w) ∈ G.L` is unsatisfiable (would force `j ∈ G.V`,
--   contradicting `G.hJV_disj`).  Inputs have no siblings — like
--   `Pa`, unlike `Ch`.  This is the LN's natural reading under
--   addition `[type_mismatch_individual_vs_set_versions]`.
--
-- *Bidirected self-loops are forbidden by `G.hL_irrefl`* (see
--   `CDMG.lean`'s design block), so `v ∉ G.Sib v` always.  This
--   stands in deliberate contrast to `Pa / Ch`, where directed
--   self-loops admit `v` as its own parent / child.
--
-- *Symmetry available via `G.hL_symm` but not baked in.*  The filter
--   spells `(v, w) ∈ G.L`; by symmetry of `L`, the equivalent
--   `(w, v) ∈ G.L` filter yields the same finset.  We pick the
--   `(v, w)` order to match the LN's "$v \huh w \in G$" notation
--   reading left-to-right.
--
-- *No `SibSet` per LN.*  The LN source has a commented-out line
--   ("%\item[] The set of *children* of $A$ in $G$: …" — the comment
--   accidentally repeats the children template) where a sibling
--   set-version would have gone.  We follow the LN literally: no
--   `SibSet` def is introduced.  Downstream consumers needing
--   "siblings of a set" can spell `A.biUnion (G.Sib)` inline.
-- def_3_5 -- start statement
def Sib (G : CDMG Node) (v : Node) : Finset Node :=
  (G.J ∪ G.V).filter (fun w => (v, w) ∈ G.L)
-- def_3_5 -- end statement

/-! ## Items 6–7 — ancestors -/

-- ref: def_3_5 (item 6 — Anc^G(v))
--
-- Ancestors of a vertex `v` in `G`: the set of nodes `w ∈ J ∪ V` from
-- which there exists a *directed walk* `w → … → v`.  Literal LN:
-- `{w ∈ G | ∃ directed walk w → … → v}`.  Note: `v ∈ Anc^G(v)`
-- unconditionally, via the trivial (length-0) walk `Walk.nil hv`.
/-
LN tex (item 6):

  The set of *ancestors* of $v$ in $G$:
    $\Anc^G(v):=\{w \in G\,|\,
      \exists \text{ directed walk: } w \tuh \cdots \tuh v \in G\}$.
  Note: $v \in \Anc^G(v)$.
-/
-- ## Design choice
--
-- *`noncomputable` + `open Classical in`.*  The predicate
--   `fun w => ∃ p : Walk G w v, p.IsDirectedWalk` is not primitively
--   decidable (`Walk G u w` is an inductive of arbitrary length;
--   typeclass inference cannot synthesise a `DecidablePred` for the
--   existential).  We import classical decidability locally for the
--   `Finset.filter`.  A constructively decidable variant is recoverable
--   later — every reachable vertex is reachable by a *path* whose
--   length is at most `(G.J ∪ G.V).card`, so a bounded BFS works — but
--   the construction is not needed by any chapter 3 proof, so we pay
--   the `noncomputable` cost upfront.  See top docstring's "Core
--   encoding choices" for the cross-cutting rationale.
--
-- *Self-membership `v ∈ G.Anc v` via the trivial walk.*  When
--   `v ∈ G`, the witness `Walk.nil (h : v ∈ G) : Walk G v v` satisfies
--   `IsDirectedWalk = True` (vacuous, see `Walks.lean`'s design block
--   for item 2).  So the LN note "$v \in \Anc^G(v)$" follows
--   immediately from the filter predicate, no extra clause needed.
--   This encodes operator addition
--   `[self_membership_notes_require_length_zero_walks]` literally —
--   no `∪ {v}` patch, no self-loop hypothesis.
--
-- *Downstream load.*  `Anc` is the substrate for `Sc := Anc ∩ Desc`
--   (item 11), and chapter 5+'s ancestor-closure adjustment criteria,
--   σ-separation, and the ID algorithm's c-component identification
--   all destructure `Anc(A)`.  Keeping the carrier as `Finset Node`
--   (not `Set`) lets those downstream rows use `Finset.subset` /
--   `Finset.union` lemmas directly.
-- def_3_5 -- start statement
open Classical in
noncomputable def Anc (G : CDMG Node) (v : Node) : Finset Node :=
  (G.J ∪ G.V).filter (fun w => ∃ p : Walk G w v, p.IsDirectedWalk)
-- def_3_5 -- end statement

-- ref: def_3_5 (item 7 — Anc^G(A))
--
-- Ancestors of a *set* of vertices `A` in `G`: union of `Anc^G(v)`
-- over `v ∈ A`.  Note: `A ⊆ Anc^G(A)` (for any `v ∈ A ∩ (J ∪ V)`,
-- by the single-vertex note `v ∈ Anc^G(v)`).
/-
LN tex (item 7):

  The set of *ancestors* of $A$ in $G$:
    $\Anc^G(A):= \bigcup_{v \in A} \Anc^G(v)$.
  Note: $A \ins \Anc^G(A)$.
-/
-- ## Design choice
--
-- *`noncomputable` because `Anc` is.*  `biUnion` propagates the
--   noncomputable status from `G.Anc`.  Same `Finset.biUnion` shape
--   as `PaSet / ChSet`, no `\ A` subtraction (LN literal).
--
-- *Self-inclusion `A ⊆ G.AncSet A` (LN note).*  For any `v ∈ A` with
--   `v ∈ G.J ∪ G.V`, we have `v ∈ G.Anc v` (via the trivial walk), so
--   `v ∈ G.AncSet A` via `Finset.mem_biUnion`.  No extra clause.
--
-- *Used by `def_3_15` (acyclification) and chapter-5 ancestral-set
--   adjustment.*  The d-/σ-separation completeness theorems quantify
--   over ancestor-closed sets `A = AncSet A`; chapter 5+ rewrites
--   pattern-match on this fixed-point shape.
-- def_3_5 -- start statement
noncomputable def AncSet (G : CDMG Node) (A : Finset Node) : Finset Node :=
  A.biUnion G.Anc
-- def_3_5 -- end statement

/-! ## Items 8–9 — descendants -/

-- ref: def_3_5 (item 8 — Desc^G(v))
--
-- Descendants of a vertex `v` in `G`: the set of nodes `w ∈ J ∪ V`
-- reachable from `v` by a directed walk `v → … → w`.  Note:
-- `v ∈ Desc^G(v)` unconditionally, via the trivial walk.
/-
LN tex (item 8):

  The set of *descendants* of $v$ in $G$:
    $\Desc^G(v):=\{w \in G\,|\,
      \exists \text{ directed walk: } v \tuh \cdots \tuh w \in G\}$.
  Note: $v \in \Desc^G(v)$.
-/
-- ## Design choice
--
-- *Mirror of `Anc` with walk direction flipped.*  Filter predicate
--   `∃ p : Walk G v w, p.IsDirectedWalk` (note `Walk G v w` vs
--   `Walk G w v` for `Anc`).  Same `noncomputable` + `open Classical
--   in` pattern.  Self-inclusion via `Walk.nil` works identically.
--
-- *Why a separate def, not `Desc := fun v => Anc G^op v`.*  We do not
--   carry an opposite-graph operation `G^op` on CDMGs (it would
--   permute directed edges but leave bidirected ones, which is rarely
--   useful elsewhere in chapter 3).  Spelling `Desc` directly avoids
--   wrapping every consumer in an op-graph translation.
--
-- *Downstream load — load-bearing for chapter 5+ interventions.*
--   Hard intervention `do(A=a)` (chapter 5) cuts incoming edges to
--   `A`; the post-intervention graph leaves `Desc^G(A)` invariant
--   in distribution.  `NonDesc` (item 10) is the `Desc`-complement
--   that gives the "untouched-by-do(A)" frontier.  σ-separation
--   (chapter 5+) also pattern-matches on `Desc`-membership for
--   colliders.
-- def_3_5 -- start statement
open Classical in
noncomputable def Desc (G : CDMG Node) (v : Node) : Finset Node :=
  (G.J ∪ G.V).filter (fun w => ∃ p : Walk G v w, p.IsDirectedWalk)
-- def_3_5 -- end statement

-- ref: def_3_5 (item 9 — Desc^G(A))
--
-- Descendants of a *set* of vertices `A` in `G`: union over `v ∈ A`.
/-
LN tex (item 9):

  The set of *descendants* of $A$ in $G$:
    $\Desc^G(A):= \bigcup_{v \in A} \Desc^G(v)$.
  Note: $A \ins \Desc^G(A)$.
-/
-- ## Design choice
--
-- *Mirror of `AncSet`.*  `Finset.biUnion`, `noncomputable` (because
--   `Desc` is), no `\ A` subtraction, `A ⊆ G.DescSet A` follows from
--   per-vertex self-inclusion via `Walk.nil`.
--
-- *Used directly by `NonDesc` (item 10).*  The complement-on-
--   `(J ∪ V)` builds on `DescSet`, so the choice of `Finset` carrier
--   here propagates to `Finset.sdiff` for `NonDesc`.
-- def_3_5 -- start statement
noncomputable def DescSet (G : CDMG Node) (A : Finset Node) : Finset Node :=
  A.biUnion G.Desc
-- def_3_5 -- end statement

/-! ## Item 10 — non-descendants (set-version only) -/

-- ref: def_3_5 (item 10 — NonDesc^G(A))
--
-- Non-descendants of a *set* `A` in `G`: the complement of
-- `Desc^G(A)` inside the ambient vertex set `J ∪ V`.  Per LN, this is
-- only a set-version operation (no single-vertex `NonDesc^G(v)`
-- defined — though it would coincide with `NonDesc^G({v})`).
/-
LN tex (item 10):

  The set of *non-descendants* of $A$ in $G$:
    $\NonDesc^G(A) := (J \cup V) \sm \Desc^G(A)$.
-/
-- ## Design choice
--
-- *`Finset.sdiff` on the ambient `G.J ∪ G.V`.*  Direct transcription
--   of the LN's `(J ∪ V) \ Desc^G(A)`.  `Finset.sdiff` is the
--   standard set-difference on Finsets, decidable via `DecidableEq
--   Node` from `def_3_1`.  Keeping the universe as `G.J ∪ G.V` (not
--   the ambient `Node` type) is *load-bearing*: `NonDesc` is meant
--   to enumerate "graph nodes that are not descendants of `A`", and
--   the LN's `(J ∪ V) \ Desc^G(A)` literal reading restricts to the
--   graph's vertex set.
--
-- *`noncomputable` because `DescSet` is.*  Propagates from the
--   walk-existential predicate in `Desc`.
--
-- *Why no single-vertex `NonDesc^G(v)`.*  The LN simply does not
--   define one — only the set-version appears (item 10 has no `\item`
--   for a vertex case).  Consumers can spell `G.NonDesc {v}` if they
--   need the singleton version.
--
-- *Downstream — hard-intervention frontier (chapter 5+).*  Under
--   `do(A=a)`, the conditional distribution `p(NonDesc(A) | do(A))`
--   coincides with the observational `p(NonDesc(A))` (the
--   "untouched-by-do(A)" component), and adjustment formulae quantify
--   over `NonDesc(A)`-valued sums.  This makes `NonDesc` central to
--   identification proofs in chapters 5–7.
-- def_3_5 -- start statement
noncomputable def NonDesc (G : CDMG Node) (A : Finset Node) : Finset Node :=
  (G.J ∪ G.V) \ G.DescSet A
-- def_3_5 -- end statement

/-! ## Items 11–12 — strongly connected components -/

-- ref: def_3_5 (item 11 — Sc^G(v))
--
-- Strongly connected component of a vertex `v` in `G`: intersection
-- of `v`'s ancestors and `v`'s descendants — exactly the nodes
-- mutually directed-walk-reachable with `v`.  Note: `v ∈ Sc^G(v)`
-- unconditionally (since `v ∈ Anc^G(v) ∩ Desc^G(v)`).
/-
LN tex (item 11):

  The *strongly connected component* of $v$ in $G$:
    $\Sc^G(v) := \Anc^G(v) \cap \Desc^G(v)$.
  Note: $v \in \Sc^G(v)$.
-/
-- ## Design choice
--
-- *`Finset.inter` of `Anc` and `Desc`.*  Direct transcription of the
--   LN's `Anc^G(v) ∩ Desc^G(v)` — no recomputation of walks, just
--   reuse of the two existing family sets.  `Finset.inter` is
--   decidable via `DecidableEq Node`; the inherited `noncomputable`
--   comes from `Anc / Desc`, not the intersection.
--
-- *Self-membership `v ∈ G.Sc v`.*  Follows from `v ∈ G.Anc v` and
--   `v ∈ G.Desc v` (when `v ∈ G`), via `Finset.mem_inter`.  Encodes
--   the LN note + addition `[self_membership_notes_require_length_
--   zero_walks]`.
--
-- *Why the name `Sc` (capital S, lowercase c).*  Matches the LN
--   macro `\Sc^G` literally.  Alternative spellings considered:
--   `SCC` (acronym-style) was rejected as deviating from the LN
--   text; `stronglyConnected` (camelCase) was rejected as longer
--   without information gain.
--
-- *Downstream — σ-separation regime (chapter 5+).*  In cyclic CDMGs
--   `d`-separation is incomplete; the LN's `def_3_15`
--   (acyclification) collapses each `Sc^G(v)` to a single node, and
--   σ-separation pattern-matches on `Sc`-class membership.  Keeping
--   `Sc` as a `Finset` (not the equivalence-class quotient itself)
--   defers the quotient construction to `def_3_15` and keeps the
--   surface API uniform with the other family sets.
-- def_3_5 -- start statement
noncomputable def Sc (G : CDMG Node) (v : Node) : Finset Node :=
  G.Anc v ∩ G.Desc v
-- def_3_5 -- end statement

-- ref: def_3_5 (item 12 — Sc^G(A))
--
-- Union of strongly connected components over `v ∈ A`.
/-
LN tex (item 12):

  The (union of) *strongly connected components* of $A$ in $G$:
    $\Sc^G(A) := \bigcup_{v \in A} \Sc^G(v)$.
  Note: $A \ins \Sc^G(A)$.
-/
-- ## Design choice
--
-- *Mirror of `AncSet / DescSet`.*  `Finset.biUnion`, no `\ A`
--   subtraction (LN literal), `A ⊆ G.ScSet A` via per-vertex
--   self-inclusion.  `noncomputable` propagates from `Sc`.
--
-- *Not the union of equivalence classes per se.*  `ScSet A` returns
--   the union of `v`'s mutual-reachability set as `v` ranges over
--   `A` — which equals the union of the SCCs containing each `v ∈
--   A ∩ (J ∪ V)`.  The actual SCC equivalence partition is built
--   later in `def_3_15` (acyclification); here we just expose the
--   union.
-- def_3_5 -- start statement
noncomputable def ScSet (G : CDMG Node) (A : Finset Node) : Finset Node :=
  A.biUnion G.Sc
-- def_3_5 -- end statement

/-! ## Items 13–14 — districts -/

-- ref: def_3_5 (item 13 — Dist^G(v))
--
-- District of a vertex `v` in `G`: the set of nodes `w ∈ J ∪ V`
-- reachable from `v` by a *bidirected* walk
-- `v ↔ v_1 ↔ … ↔ v_{n-1} ↔ w`.  Note: `v ∈ Dist^G(v)`
-- unconditionally, via the trivial (length-0) bidirected walk — see
-- operator addition `[district_walk_indexing_ambiguous_for_small_n]`.
/-
LN tex (item 13):

  The *district* of $v$ in $G$:
    $\Dist^G(v) := \{w \in G\,|\,
      \exists \text{ bidirected walk: }
      v \huh v_1 \huh \cdots \huh v_{n-1} \huh w \in G\}$.
  Note: $v \in \Dist^G(v)$.
-/
-- ## Design choice
--
-- *Predicate `∃ p : Walk G v w, p.IsBidirectedWalk`.*  Direct
--   bidirected-walk analogue of `Desc`.  Per operator addition
--   `[district_walk_indexing_ambiguous_for_small_n]`, the LN's
--   indexed `v_1 \huh \cdots \huh v_{n-1}` notation is read as
--   "any-length bidirected walk including the length-0 walk at `v`";
--   the indexing imposes NO lower bound on walk length.  We encode
--   exactly this — no `0 < p.length` side condition, no
--   bidirected-self-loop requirement.
--
-- *Self-membership `v ∈ G.Dist v` via the trivial walk
--   (load-bearing).*  Since CDMGs forbid bidirected self-loops
--   (`hL_irrefl`), the *only* way to witness `v ∈ G.Dist v` is the
--   trivial walk `Walk.nil hv : Walk G v v`, which satisfies
--   `IsBidirectedWalk = True` vacuously.  Without this trivial-walk
--   reading the LN's note "$v \in \Dist^G(v)$" would fail in graphs
--   with no bidirected edges incident to `v` — see subtlety
--   `anc_desc_dist_self_inclusion_relies_on_trivial_walk_convention`.
--   This is the most fragile of the four self-membership notes (the
--   `Anc / Desc / Sc` cases can be witnessed by a length-≥1 walk in
--   common graphs; `Dist` cannot when no bidirected edge touches `v`).
--
-- *`noncomputable` + `open Classical in`.*  Same rationale as
--   `Anc / Desc`: bidirected-walk-existence is not primitively
--   decidable for arbitrary `Node` types.
--
-- *Downstream — c-component decomposition (chapter 5+).*  The ID
--   algorithm partitions the output set `V` into c-components — the
--   equivalence classes of `Dist`-mutual-reachability — and recursively
--   identifies queries `c`-component by `c`-component.  Pearl/Tian's
--   c-factorisation `p_*(V) = ∏_c p(c | Pa(c))` indexes over Dist
--   classes; keeping `Dist` as a `Finset Node` makes the product
--   well-typed.
-- def_3_5 -- start statement
open Classical in
noncomputable def Dist (G : CDMG Node) (v : Node) : Finset Node :=
  (G.J ∪ G.V).filter (fun w => ∃ p : Walk G v w, p.IsBidirectedWalk)
-- def_3_5 -- end statement

-- ref: def_3_5 (item 14 — Dist^G(A))
--
-- District of a *set* of vertices `A` in `G`: union over `v ∈ A`.
/-
LN tex (item 14):

  The *district* of $A$ in $G$:
    $\Dist^G(A) := \bigcup_{v \in A} \Dist^G(v)$.
  Note: $A \ins \Dist^G(A)$.
-/
-- ## Design choice
--
-- *Mirror of `AncSet / DescSet / ScSet`.*  `Finset.biUnion`, no `\ A`
--   subtraction (LN literal), `A ⊆ G.DistSet A` via per-vertex
--   self-inclusion through the trivial bidirected walk.
--   `noncomputable` propagates from `Dist`.
--
-- *Union of c-components (chapter 5+).*  When `A` is the union of
--   one or more complete c-components, `DistSet A = A`; this
--   idempotent fixed-point shape is the standard hypothesis in c-
--   component identification (ID algorithm).
-- def_3_5 -- start statement
noncomputable def DistSet (G : CDMG Node) (A : Finset Node) : Finset Node :=
  A.biUnion G.Dist
-- def_3_5 -- end statement

end CDMG

end Causality
