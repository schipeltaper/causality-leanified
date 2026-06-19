import Chapter3_GraphTheory.Section3_1.Bifurcation

/-!
# Marginalization a.k.a. latent projection on CDMGs (def 3.14)

This file formalises *definition 3.14* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex` lines
934 -- 959, label `def:G_marginalization`): given a CDMG
`G = (J, V, E, L)` and a subset `W ⊆ V` of output nodes, the
*marginalization of `G` w.r.t. `W`* -- also called the
*latent projection of `G` onto `J ∪ V \ W`* -- is the new CDMG
`G^{V\W | J} = G^{\sm W} = (J^{\sm W}, V^{\sm W}, E^{\sm W}, L^{\sm W})`
obtained by deleting the nodes of `W` and replacing every walk
through `W` by a single edge:

  * the input nodes are unchanged (`J^{\sm W} := J`);
  * the output nodes lose `W` (`V^{\sm W} := V \ W`);
  * the directed edges of `G^{\sm W}` are *all* pairs
    `(u, v)` with `u ∈ J ∪ V \ W`, `v ∈ V \ W` for which a
    directed walk `u → w_1 → ⋯ → w_{n-1} → v` exists in `G`
    with every intermediate node `w_i ∈ W`;
  * the bidirected edges of `G^{\sm W}` are *all* pairs
    `{u, v}` with `u, v ∈ V \ W`, `u ≠ v` for which a
    bifurcation `u ⟵ ⋯ ⟵ w_{k-1} \hus w_k → ⋯ → v` exists in
    `G` with every intermediate node `w_i ∈ W`.

This is *the* foundational graph transformation of Section 3.2;
the next four claims of the section (claims 3.16 -- 3.19) and the
$i\sigma$-separation-under-marginalization lemma of Section 3.3
(`graphs.tex` line 1416, `lem:stability_separation_marginalization`)
all compose with it, and chapters 4 -- 16 reuse it via
`L`-projection arguments for identification and discovery.

## Where this gets used downstream

* **claim_3_16** (`graphs.tex` Rem 964, "Marginalization preserves
  ancestral relations, bifurcations and acyclicity") -- the
  `@[simp]` membership lemmas `mem_marginalize_E` /
  `mem_marginalize_L` are the gateway: an ancestor / bifurcation /
  topological-order argument in `G^{\sm W}` reduces (via these
  lemmas) to a walk-existential statement in `G`.
* **claim_3_17** (`graphs.tex` Lem 997, "Marginalizations
  commute") -- iterating `G.marginalize` requires the
  no-precondition design (see the design note below) and uses
  walk concatenation through the `E` membership lemma to assemble
  / disassemble iterated walks.
* **claim_3_18** (`graphs.tex` Lem 1122, "Marginalization and
  intervention commute") -- composes `G.marginalize` with
  `G.hardInterventionOn` (`Section3_2/HardInterventionOn.lean`);
  the `J`-unchanged design of `marginalize` and the `V`-unchanged
  design of `hardInterventionOn` make the equality on input /
  output nodes a one-liner.
* **claim_3_19** (`graphs.tex` Lem 1167) -- equates
  `G.hardInterventionOn W` with the SWIG of `G` on `W`
  marginalised over the output halves of the split vertices.
* **`lem:stability_separation_marginalization`**
  (`graphs.tex` line 1416, Section 3.3) -- $i\sigma$-separation
  is invariant under marginalization; the proof reuses the
  walk-shrinkage / walk-expansion idiom of claim_3_16.
* **Chapters 4 -- 16** -- causal Bayesian networks (CBNs),
  do-calculus, iSCMs, identification, and the FCI / ICDF
  algorithms repeatedly use latent projection to control the
  hidden-variable substrate. The `@[simp]` lemmas below are the
  membership-level interface to every such use.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

-- def_3_14 (helper)
-- title: Walks -- "every intermediate vertex lies in `W`"
--
-- A small `Prop`-valued predicate on `Walk G v w` saying that
-- every *intermediate* vertex of the walk lies in `W`. The
-- "intermediate" vertices of a walk are `support.tail.dropLast`:
-- `support` is `v_0, v_1, …, v_n`, dropping the head removes
-- `v_0` and dropping the last removes `v_n`, leaving
-- `v_1, …, v_{n-1}` -- the LN's "$w_1, \dots, w_{n-1}$".
--
-- For length-0 walks (`nil v`, `support = [v]`,
-- `support.tail = []`, `support.tail.dropLast = []`) and
-- length-1 walks (`cons s (nil w)`,
-- `support = [v, w]`, `support.tail = [w]`,
-- `support.tail.dropLast = []`) the interior is empty and the
-- predicate holds vacuously. This matches the LN's "$w_1, \dots,
-- w_{n-1} \in W$ (if any)" -- the "(if any)" parenthetical
-- explicitly admits the case of no intermediate nodes.
--
-- ## Design choice
--
-- * **`support.tail.dropLast` extracts exactly the LN's
--   $w_1, \dots, w_{n-1}$ list, including the empty case.** The
--   LN's "$w_1, \dots, w_{n-1} \in W$ (if any)" clause names a
--   *list* of intermediate vertices and parenthetically admits
--   the *empty* list. A walk's `support` is the vertex sequence
--   `[v_0, v_1, \dots, v_n]`; `support.tail.dropLast` drops the
--   head `v_0` and the last `v_n`, returning exactly
--   `[v_1, \dots, v_{n-1}]` -- and automatically `[]` whenever
--   `n ≤ 1` (a length-0 `Walk.nil v` or a length-1 single-edge
--   walk). The "(if any)" parenthetical *demands* this
--   vacuously-true behaviour on a single-edge walk: the LN's
--   item-iii formula `u → w_1 → ⋯ → w_{n-1} → v` has a minimal
--   `n = 1` reading (single arrow `u → v`, empty intermediate
--   list), so any encoding that forced a non-empty interior
--   would mis-state the definition for single-edge walks.
--
--   Two alternatives were considered and rejected:
--     * A bespoke inductive type `WalkInteriorIn G v w W` with
--       `nil` / `cons` constructors paralleling `Walk`. Doable,
--       but adds a parallel inductive (and a parallel induction
--       principle) where a `Prop` over the already-existing
--       `Walk.support` list suffices.
--     * `∀ x ∈ π.support, x ∈ W ∪ {v, w}` (quantify over the
--       *whole* support, granting the endpoints as exceptions).
--       Equivalent on the empty interior but forces every use
--       site to discharge the `∪ {endpoints}` case-split
--       explicitly; the `support.tail.dropLast` form hides this
--       in the list-construction itself.
--
--   This `tail.dropLast` slicing is the idiomatic
--   "internal-nodes-of-a-walk" pattern: `Walk.support` is a
--   `List`, so `simp` lemmas and `List.forall_mem_*` rewrites
--   chip the predicate apart along the same shape that
--   `support` produces. Downstream walk-concatenation reasoning
--   (claims 3.16 -- 3.18) leans on this: the `support` of a
--   concatenated walk is the concatenation of the supports
--   (modulo the duplicated hinge vertex), and
--   `support.tail.dropLast` splits cleanly along that
--   decomposition.
--
-- * **`∀ x ∈ list, x ∈ W` vs. `↑list ⊆ W`.** Both are
--   equivalent. The `∀`-form is more idiomatic in Lean and
--   composes better with `simp` lemmas about `support` /
--   `support.tail` / `support.dropLast` (which return concrete
--   list expressions; `∀ ∈` then triggers `List.forall_mem_cons`
--   etc.). The `⊆` form would require routing through
--   `List.subset_iff` and a coercion lemma. Mathlib's recurring
--   pattern at this layer is the `∀`-form (`List.Nodup`,
--   `List.Pairwise`, …), so we follow suit.
--
-- * **Helper predicate, not inlined twice.** Used in both `E`
--   and `L` membership conditions of `CDMG.marginalize` below.
--   Downstream proofs (claims 3.16 -- 3.19) will pattern-match
--   `π.InteriorIn W` directly. Defining it once here lets every
--   call site read `π.InteriorIn W` rather than re-spelling out
--   `∀ x ∈ π.support.tail.dropLast, x ∈ W`.
--
-- * **Argument order: walk first, set second.** Matches the
--   dot-notation idiom `π.InteriorIn W` (Lean inserts `π` into
--   the first explicit argument). Mirrors `Walk.IsDirected`,
--   `Walk.IsBifurcation`, etc.
/-- Predicate "every intermediate vertex of the walk `π` lies
in `W`". For `π : Walk G v w`, this says
`∀ x ∈ π.support.tail.dropLast, x ∈ W`, i.e. the vertex sequence
`v_1, …, v_{n-1}` (with the start and end vertices excluded) is
contained in `W`. Length-0 and length-1 walks have empty
interiors, so the predicate holds vacuously. Mirrors the LN's
"$w_1, \dots, w_{n-1} \in W$ (if any)" clause in
`graphs.tex` def_3_14 items iii and iv. -/
def InteriorIn {v w : α} (π : Walk G v w) (W : Set α) : Prop :=
  ∀ x ∈ π.support.tail.dropLast, x ∈ W

/-- Unfolding lemma for `Walk.InteriorIn`: it is by-definition
`∀ x ∈ π.support.tail.dropLast, x ∈ W`. Useful when invoking
`List`-level reasoning about the support directly. Not tagged
`@[simp]` -- downstream proofs typically pattern-match
`InteriorIn` as a predicate rather than unfold it, so eagerly
unfolding it would clutter the goal state. -/
theorem interiorIn_def {v w : α} (π : Walk G v w) (W : Set α) :
    π.InteriorIn W ↔ ∀ x ∈ π.support.tail.dropLast, x ∈ W :=
  Iff.rfl

end Walk

namespace CDMG

-- def_3_14
-- title: MarginalizationAK
--
-- The *marginalization* of a CDMG `G = (J, V, E, L)` with
-- respect to a subset `W ⊆ V` of output nodes (a.k.a. the
-- *latent projection of `G` onto `J ∪ V \ W`*). The new CDMG
-- `G^{\sm W} = (J^{\sm W}, V^{\sm W}, E^{\sm W}, L^{\sm W})` is
-- obtained by:
--
--   * keeping the inputs (`J^{\sm W} := J`);
--   * removing `W` from the outputs (`V^{\sm W} := V \ W`);
--   * lifting every directed walk in `G` through `W` to a
--     single directed edge in `E^{\sm W}` (LN's `\tuh` triple
--     formula in def_3_14 item iii);
--   * lifting every bifurcation in `G` through `W` to a single
--     bidirected edge in `L^{\sm W}` (LN's bifurcation formula
--     in def_3_14 item iv).
--
-- The LN's footnote on item iii ("Note that this may introduce
-- self-cycles.") is faithfully reproduced: when a directed walk
-- from `u` to `u` exists in `G` with every intermediate vertex
-- in `W` (e.g. `u → w → u` for `w ∈ W`), the pair `(u, u)`
-- enters `E^{\sm W}` as a self-loop.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(def_3_14, lines 934 -- 959):

\begin{defmark}
\begin{Def}[Marginalization a.k.a.\ latent projection on CDMGs]\label{def:G_marginalization}
  Let $G=(J,V,E,L)$ be a CDMG and $W \ins V$ a subset of output nodes.
  Then the \emph{marginalization of $G$ w.r.t.\ $W$} or the
  \emph{latent projection of $G$ onto $J\cup V \sm W$} is the CDMG:
  \[  G^{V\sm W | J} := G^{\sm W} := (J^{\sm W},V^{\sm W},E^{\sm W},L^{\sm W}), \]
  where:
  \begin{enumerate}[label=\roman*.)]
      \item $J^{\sm W}:= J$,
      \item $V^{\sm W}:= V \sm W$,
      \item $E^{\sm W}$ consists of all directed edges $\ul{v} \tuh \ol{v}$ with
          $\ul{v},\ol{v} \in J \cup V \sm W$
          for which there exists a directed walk in $G$:
          \[\ul{v} \tuh w_1 \tuh \cdots \tuh w_{n-1} \tuh \ol{v}, \]
          where all intermediate nodes $w_1,\dots,w_{n-1} \in W$ (if any).%
          \footnote{Note that this may introduce self-cycles.}
      \item $L^{\sm W}$ consists of all bidirected edges $\ul{v} \huh \ol{v}$ with
          $\ul{v},\ol{v} \in V \sm W$, $\ul{v} \neq \ol{v}$,
          for which there exists a bifurcation in $G$:
          \[\ul{v} \hut w_1 \hut \cdots \hut w_{k-1} \hus w_k
             \tuh \cdots \tuh w_{n-1} \tuh \ol{v}, \]
          where all intermediate nodes $w_1,\dots,w_{n-1} \in W$ (if any).
  \end{enumerate}
\end{Def}
\end{defmark}
-/
--
-- ## Design choice
--
-- * **Overall shape: `CDMG → Set α → CDMG`, all fields
--   discharged in place.** Mirrors `hardInterventionOn`
--   (def_3_10, `Section3_2/HardInterventionOn.lean`), the other
--   graph-transformation row of Section 3.2 -- same shape, same
--   idiom. Both transformations take a CDMG plus a set of nodes
--   and return a new CDMG; both build the result via
--   `where`-syntax with the four data fields (`J`, `V`, `E`,
--   `L`) and the six structural-constraint fields
--   (`disjoint_JV`, `E_subset`, `L_subset`, `L_irrefl`,
--   `L_symm`, `disjoint_EL`) discharged colocated with the
--   construction. We do not factor the construction through an
--   intermediate `structure` or pre-built constructor: the
--   colocated style matches the Mathlib house pattern for
--   one-shot CDMG / graph builders and makes claim_3_18
--   ("intervention and marginalization commute") read as a
--   field-by-field comparison through the `@[simp]` membership
--   lemmas of both transformations.
--
-- * **No `W ⊆ G.V` precondition.** The LN literally writes
--   "let `W ⊆ V`", but the four-component formula is
--   well-defined for any `W : Set α`: vertices in
--   `W \ G.V` simply don't appear on any `Walk G _ _` (because
--   walks of length ≥ 1 force their internal vertices into
--   `G.J ∪ G.V` via `G.E_subset` / `G.L_subset`), so
--   `π.InteriorIn W` is unaffected by the spurious part of `W`.
--   `G.V \ W` collapses to `G.V \ (W ∩ G.V)`, matching the LN's
--   restricted `W`. The same design choice was made for
--   `hardInterventionOn` (`Section3_2/HardInterventionOn.lean`,
--   "no precondition" design note) and for the same two reasons:
--
--     1. **Iteration works unconditionally** (claim_3_17). The
--        outer call in `(G.marginalize W₁).marginalize W₂`
--        would otherwise need a hypothesis
--        `W₂ ⊆ (G.marginalize W₁).V = G.V \ W₁`. The LN's
--        statement of claim_3_17 quietly assumes the two
--        subsets are subsets of the original `G.V`, with no
--        re-derivation for the outer call.
--     2. **Composition with `hardInterventionOn` is cleaner**
--        (claim_3_18). The two transformations have different
--        natural preconditions in the LN
--        (`W ⊆ J ∪ V` for `hardInterventionOn`,
--        `W ⊆ V` for `marginalize`), and dropping both at the
--        Lean level lets the equality
--        `(G_{do(W₁)})^{\sm W₂} = (G^{\sm W₂})_{do(W₁)}` be
--        stated as a single equation of `CDMG α` values
--        without conditional side-hypotheses on the two
--        constituent transformations.
--
-- * **`E^{\sm W}` membership: walk-existential `∃ π : Walk G u v`
--   with `π.IsDirected ∧ π.InteriorIn W`.** This is the most
--   direct transliteration of the LN's item iii formula. The
--   trio of conditions matches the LN's three syntactic
--   constraints: endpoint membership (`p.1 ∈ G.J ∪ (G.V \ W)`
--   and `p.2 ∈ G.V \ W`), directed-walk shape (`π.IsDirected`),
--   and intermediate-in-`W` (`π.InteriorIn W`). The
--   `Walk` type is the data-level walk inductive from
--   `Section3_1/Walks.lean` (def_3_4 item 1).
--
--   **`p.2 ∈ G.V \ W` strengthens the LN's
--   "$\ol{v} \in J \cup V \sm W$".** The LN writes *both*
--   endpoints as members of `J ∪ V \ W`, but the CDMG's
--   structural constraint `E_subset : E ⊆ (J ∪ V) ×ˢ V`
--   (def_3_1) forces every directed-edge target into `V`, and
--   `J ∩ V = ∅` by `disjoint_JV`. Together these mean that on
--   any actual length-≥-1 directed walk in `G`, the endpoint
--   `p.2` already lives in `V`, so an LN-style target in
--   `J ∪ (V \ W)` is automatically in `V \ W` -- our
--   strengthening is an equivalent rewriting under CDMG
--   semantics, not a tightening of the definition. We keep
--   `p.2 ∈ G.V \ W` explicitly (rather than the literal LN
--   union) to mirror the structural-field type (sources in
--   `J ∪ V`, targets in `V`); this makes the `E_subset`
--   obligation on `G.marginalize W` discharge by a one-line
--   destructure of the membership tuple, with no need to
--   re-derive `p.2 ∈ V` from the walk witness.
--
--   We additionally require `1 ≤ π.length` -- the LN's formula
--   `u \tuh w_1 \tuh \cdots \tuh w_{n-1} \tuh v` has a minimal
--   `n = 1` reading (a single arrow `u \tuh v` with no
--   intermediate nodes; the LN's "(if any)" parenthetical
--   refers to the intermediate `w_i`, not to the existence of
--   *any* edge). Without `1 ≤ π.length`, the trivial walk
--   `Walk.nil u : Walk G u u` -- which is vacuously
--   `IsDirected` and vacuously `InteriorIn W` (its
--   `support.tail.dropLast = []`) -- would force a self-loop
--   `(u, u) ∈ E^{\sm W}` for *every* `u ∈ G.J ∪ (G.V \ W)`,
--   regardless of whether `G` actually contains any cycle
--   through `u`. That spurious universal self-loop falsifies
--   the LN's claim_3_16 item 3 ("if `G` is acyclic then so is
--   `G^{\sm W}`"): under `Acyclicity.lean`'s definition
--   `IsAcyclic := ∀ v ∈ G, ¬ ∃ π : Walk G v v, π.IsDirected ∧
--   1 ≤ π.length`, an `IsAcyclic G` would no longer lift to
--   `IsAcyclic (G.marginalize W)`. The LN's footnote on
--   item iii ("Note that this may introduce self-cycles") is
--   about *genuine* cycles backed by a length-≥-1 walk through
--   `W` (e.g. `u → w → u` with `w ∈ W` collapsing to a
--   self-loop `u → u`), not about a universal trivial self-loop
--   on every vertex.
--
--   For `p.1 ≠ p.2` the new conjunct is free: any walk between
--   distinct endpoints has length ≥ 1 structurally. The only
--   behavioural change is for `p.1 = p.2`, where we now
--   correctly demand a genuine non-trivial cycle witness --
--   exactly what claim_3_16 item 3 and the
--   acyclicity-composition arguments of claims 3.17 / 3.18
--   want when they reason about self-edges of the marginalized
--   graph.
--
-- * **`L^{\sm W}` membership: TWO walk-existentials joined by
--   `∨`.** The LN's item iv reads "there exists a bifurcation
--   $\ul{v} \hut \cdots \tuh \ol{v}$" -- but the LN's notion of
--   "between" is symmetric (the LN's `L` is symmetric, encoded
--   in def_3_1 as the `L_symm` field). In Lean, a bifurcation
--   is a property of a specific `Walk G u v` (a directional
--   data object), and `IsBifurcation` is *not* symmetric: a
--   single backward step `u ⟵[G] v` (from `(v, u) ∈ G.E`) is a
--   bifurcation of type `Walk G u v`, but its reverse is a
--   single forward step `u ⟶[G] v` of type `Walk G v u`, which
--   is *not* a bifurcation (forward steps do not satisfy the
--   `\hus` arrowhead-at-source constraint on the hinge). The
--   LN's symmetric `L` then forces us to read the bifurcation
--   existential in *both* walk directions:
--
--     `(∃ π : Walk G p.1 p.2, π.IsBifurcation ∧ π.InteriorIn W) ∨
--      (∃ π : Walk G p.2 p.1, π.IsBifurcation ∧ π.InteriorIn W)`
--
--   This is the cleanest encoding of "LN's symmetric `between`"
--   in our directional walk type, and it trivialises the
--   `L_symm` proof (the `∨` is symmetric in `p.1, p.2`). The
--   alternative -- prove that any `IsBifurcation` walk reverses
--   to an `IsBifurcation` walk -- fails on exactly the
--   single-step backward case described above.
--
-- * **`L^{\sm W}` excludes pairs already in `E^{\sm W}` (in
--   either direction).** This is the most subtle deviation from
--   the LN's literal definition, forced by the `disjoint_EL`
--   field of `def_3_1.CDMG`. The LN treats *directed* and
--   *bidirected* edges as different *kinds* of objects (def_3_1
--   writes `E ⊆ (J ∪ V) × V` and `L ⊆ V × V / ((v_1, v_2) ∼
--   (v_2, v_1))` -- different ambient types), so the LN's
--   "two (disjoint) sets of edges" is automatically satisfied
--   even if some pair `(u, v)` is both a directed edge from `u`
--   to `v` *and* a bidirected edge between `u` and `v`: those
--   are different mathematical objects in the LN's view.
--
--   Our Lean encoding (`def_3_1.CDMG`, the design choice block
--   on `disjoint_EL`) collapses both into `Set (α × α)` for
--   ergonomics, and enforces literal set-disjointness via the
--   `disjoint_EL` field. The LN's marginalization *can* produce
--   collisions of this kind: e.g. with `V = {u, v, w₁, w₂}`,
--   `W = {w₁, w₂}`, `G.E = {(u, w₁), (w₁, v), (w₂, u)}`,
--   `G.L = {(w₁, w₂), (w₂, w₁)}`, both `(u, v) ∈ E^{\sm W}_LN`
--   (via the directed walk `u → w₁ → v`) and `(u, v) ∈ L^{\sm
--   W}_LN` (via the bifurcation `u ⟵ w₂ ⟷ w₁ → v`). To satisfy
--   our `disjoint_EL`, we exclude such collisions from `L^{\sm
--   W}` via two `¬ ∃ directed walk` clauses (in either walk
--   direction, for `L_symm`-preservation reasons described
--   below).
--
--   The mathematical content is preserved at the level of
--   *bifurcation existence*: if a directed walk `u → ⋯ → v`
--   through `W` exists in `G`, then its reversal `v ⟵ ⋯ ⟵ u`
--   is a length-≥-1 walk in `G` whose every step is
--   `.backward` -- and an all-`.backward` walk is a
--   bifurcation (with empty right arm; the LN's $k = n$ case).
--   So under the symmetric reading of "between", the LN's
--   "bifurcation between u and v in G" existential is True
--   whenever the LN's "directed walk between u and v through
--   W" existential is True (via the reversal). And under our
--   marginalization, `(v, u)` being a single-step `.backward`
--   bifurcation in `G^{\sm W}` (using the directed edge
--   `(u, v) ∈ E^{\sm W}` read as a `.backward` step from `v` to
--   `u`) provides the bifurcation in `G^{\sm W}`. Hence
--   claim_3_16's "marginalization preserves bifurcations" still
--   holds under our encoding, *provided* downstream callers
--   read "bifurcation between v_1 and v_2" symmetrically -- which
--   matches the LN's own usage of "between".
--
--   The deviation is purely syntactic at the `L^{\sm W}`
--   membership level: a pair `(u, v)` that is both a directed
--   edge and a bidirected edge in the LN's `G^{\sm W}` is
--   recorded *only* in `E^{\sm W}` in our encoding, with the
--   "bidirected" component subsumed into the existing directed
--   edge (semantically, our `(u, v) ∈ E^{\sm W}` is the union
--   of the LN's directed-edge and bidirected-edge contributions
--   collapsed onto the same ordered pair).
--
-- * **The two exclusion clauses are symmetric in `p.1, p.2`.**
--   We exclude `(u, v) ∈ L^{\sm W}` whenever *either*
--   `(u, v) ∈ E^{\sm W}` or `(v, u) ∈ E^{\sm W}`. Excluding
--   only `(u, v)` and not `(v, u)` would break `L_symm`: if
--   `(u, v) ∈ G.E^{\sm W}` and `(v, u) ∉ G.E^{\sm W}`, then
--   `(u, v) ∉ L^{\sm W}` (one-side exclusion) but `(v, u)` may
--   still be in `L^{\sm W}` (its `(v, u)` direction's
--   `E^{\sm W}` membership doesn't trigger). Excluding both
--   directions keeps the exclusion clause itself symmetric and
--   `L_symm` holds trivially.
--
-- * **No `notation` introduced at this row.** The LN's
--   `G^{\sm W}` / `G^{V\sm W | J}` macros are concise but would
--   create a notational dependency before any downstream proof
--   exists to motivate the precise token / precedence choice
--   (left-superscript notation is fiddly in Lean's parser).
--   Callers in claims 3.16 -- 3.19 write `G.marginalize W`
--   explicitly; a later notation row can add `^{\sm}` syntax if
--   the volume of use cases makes the prose form clunky.
--   Mirrors the same design choice in
--   `Section3_2/HardInterventionOn.lean` ("no new notation at
--   this row").
--
-- * **Name `marginalize`, dot-projection `G.marginalize W`.**
--   The row title is `MarginalizationAK` (a.k.a. latent
--   projection); a single Lean identifier has to be searchable
--   and pronounceable. `marginalize` reads as the prose name
--   and matches Mathlib's CamelCase convention for definitions
--   taking arguments (`Set.image`, `Finset.filter`, ...). The
--   dot-projection `G.marginalize W` lines up exactly with the
--   LN's `G^{\sm W}` ("the marginalization of `G` with respect
--   to `W`") phrasing.
--
-- * **Structural fields discharged in-place.** Each of the
--   seven `CDMG` obligations
--   (`disjoint_JV`, `E_subset`, `L_subset`, `L_irrefl`,
--   `L_symm`, `disjoint_EL`) is a one- to three-line
--   consequence of the set-membership unfolding plus a
--   destructure / projection. We do not factor any of these
--   into named lemmas because they are colocated with the
--   construction (matching the Mathlib house style for one-shot
--   structure builders) and no downstream row needs them as
--   standalone lemmas.
--
--   * `disjoint_JV` -- `G.J ∩ (G.V \ W) ⊆ G.J ∩ G.V`, vacuous
--     by `G.disjoint_JV`.
--   * `E_subset` -- our `E` set already carries the relevant
--     `p.1 ∈ G.J ∪ (G.V \ W)` and `p.2 ∈ G.V \ W` membership
--     proofs in its membership clauses; rebundling them gives
--     `p ∈ (G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)` directly.
--   * `L_subset` -- analogous, with both endpoints in
--     `G.V \ W`.
--   * `L_irrefl` -- direct from the `p.1 ≠ p.2` clause of the
--     `L` set definition.
--   * `L_symm` -- every clause of the `L` set definition is
--     symmetric in `p.1, p.2` (membership conditions swap,
--     `≠` is symmetric via `Ne.symm`, the two exclusion clauses
--     swap into each other, and the bifurcation `∨` is
--     symmetric via `Or.symm`).
--   * `disjoint_EL` -- our `L` set has the
--     `¬ ∃ π : Walk G p.1 p.2, π.IsDirected ∧ π.InteriorIn W`
--     clause built in, and an `E` membership produces a walk
--     witness `⟨π, hπ_dir, hπ_int, _⟩` (where the final `_`
--     drops the unused `1 ≤ π.length` conjunct of `E`) that
--     directly contradicts it.

/-- The *marginalization* of the CDMG `G` with respect to a set
of output nodes `W ⊆ α`: the new CDMG `G^{\sm W}` obtained by
deleting the nodes of `W` (`V^{\sm W} := G.V \ W`, inputs
unchanged) and replacing every walk through `W` by a single
edge -- a directed edge in `E^{\sm W}` if the walk is directed,
a bidirected edge in `L^{\sm W}` if the walk is a bifurcation.
See `lecture-notes/lecture_notes/graphs.tex` definition
`def:G_marginalization` (def_3_14 of the LN).

This is intentionally well-defined for *every* `W : Set α`,
with no `W ⊆ G.V` precondition -- see the design note above for
why (iteration / composition cleanliness, mirroring
`hardInterventionOn`). The four `@[simp]` lemmas
`marginalize_J`, `marginalize_V`, `mem_marginalize_E`,
`mem_marginalize_L` below characterise the four components of
the result.

The `L^{\sm W}` membership condition takes the bifurcation
existential in *both* walk directions (the LN's symmetric
"between" reading) and excludes pairs already in `E^{\sm W}` in
either direction (Lean-encoding-specific, see the design note
on `disjoint_EL`). Downstream claims that quantify over
bifurcation *existence* (e.g. claim_3_16) should also use the
symmetric reading. -/
def marginalize (G : CDMG α) (W : Set α) : CDMG α where
  J := G.J
  V := G.V \ W
  disjoint_JV := by
    rw [Set.disjoint_left]
    rintro x hJ ⟨hV, _⟩
    exact Set.disjoint_left.mp G.disjoint_JV hJ hV
  E := { p : α × α |
    p.1 ∈ G.J ∪ (G.V \ W) ∧ p.2 ∈ G.V \ W ∧
    ∃ π : Walk G p.1 p.2, π.IsDirected ∧ π.InteriorIn W ∧ 1 ≤ π.length }
  E_subset := by
    rintro ⟨u, v⟩ ⟨hu, hv, _⟩
    exact ⟨hu, hv⟩
  L := { p : α × α |
    p.1 ∈ G.V \ W ∧ p.2 ∈ G.V \ W ∧ p.1 ≠ p.2 ∧
    (¬ ∃ π : Walk G p.1 p.2, π.IsDirected ∧ π.InteriorIn W) ∧
    (¬ ∃ π : Walk G p.2 p.1, π.IsDirected ∧ π.InteriorIn W) ∧
    ((∃ π : Walk G p.1 p.2, π.IsBifurcation ∧ π.InteriorIn W) ∨
     (∃ π : Walk G p.2 p.1, π.IsBifurcation ∧ π.InteriorIn W)) }
  L_subset := by
    rintro ⟨u, v⟩ ⟨hu, hv, _, _, _, _⟩
    exact ⟨hu, hv⟩
  L_irrefl := by
    intro v₁ v₂ h
    exact h.2.2.1
  L_symm := by
    intro v₁ v₂ h
    obtain ⟨hu, hv, hne, hnE_uv, hnE_vu, h_or⟩ := h
    exact ⟨hv, hu, hne.symm, hnE_vu, hnE_uv, h_or.symm⟩
  disjoint_EL := by
    rw [Set.disjoint_left]
    intro p hE hL
    obtain ⟨_, _, π, hπ_dir, hπ_int, _⟩ := hE
    obtain ⟨_, _, _, hnE_uv, _, _⟩ := hL
    exact hnE_uv ⟨π, hπ_dir, hπ_int⟩

/-- The *input* nodes of the marginalization `G.marginalize W`
are exactly `G.J` -- marginalization does not touch inputs. By
definition. -/
@[simp] theorem marginalize_J (G : CDMG α) (W : Set α) :
    (G.marginalize W).J = G.J := rfl

/-- The *output* nodes of the marginalization `G.marginalize W`
are exactly `G.V \ W` -- removal of `W` from the output set. By
definition. -/
@[simp] theorem marginalize_V (G : CDMG α) (W : Set α) :
    (G.marginalize W).V = G.V \ W := rfl

/-- *Directed-edge* membership in the marginalization: a pair
`p = (u, v)` is a directed edge of `G.marginalize W` iff
`u ∈ G.J ∪ (G.V \ W)`, `v ∈ G.V \ W`, and there is a directed
walk from `u` to `v` in `G` of length ≥ 1 whose every
intermediate vertex lies in `W`. The `1 ≤ π.length` conjunct
forbids the trivial `Walk.nil u` (which would otherwise force a
universal self-loop on every output vertex and break
`IsAcyclic` preservation -- see the file's design notes); the
LN's self-cycle footnote refers to length-≥-1 closed walks
through `W`, not to trivial self-loops. Holds by `Iff.rfl`. -/
@[simp] theorem mem_marginalize_E
    (G : CDMG α) (W : Set α) {p : α × α} :
    p ∈ (G.marginalize W).E ↔
      p.1 ∈ G.J ∪ (G.V \ W) ∧ p.2 ∈ G.V \ W ∧
      ∃ π : Walk G p.1 p.2,
        π.IsDirected ∧ π.InteriorIn W ∧ 1 ≤ π.length :=
  Iff.rfl

/-- *Bidirected-edge* membership in the marginalization: a pair
`p = (u, v)` is a bidirected edge of `G.marginalize W` iff
`u, v ∈ G.V \ W`, `u ≠ v`, *no* directed walk from `u` to `v`
(or from `v` to `u`) in `G` has interior in `W`, and *some*
bifurcation between `u` and `v` (in either walk direction) in
`G` has interior in `W`.

The two `¬ ∃ directed walk` clauses are the Lean-encoding
deviation from the LN's literal definition (forced by
`def_3_1.CDMG`'s `disjoint_EL` field); see the file's design
notes for the full discussion. Bifurcation existence between
`u` and `v` is read *symmetrically* (in either walk direction)
to match the LN's symmetric `between`-of-pairs convention and
to make `L_symm` hold trivially. Holds by `Iff.rfl`. -/
@[simp] theorem mem_marginalize_L
    (G : CDMG α) (W : Set α) {p : α × α} :
    p ∈ (G.marginalize W).L ↔
      p.1 ∈ G.V \ W ∧ p.2 ∈ G.V \ W ∧ p.1 ≠ p.2 ∧
      (¬ ∃ π : Walk G p.1 p.2, π.IsDirected ∧ π.InteriorIn W) ∧
      (¬ ∃ π : Walk G p.2 p.1, π.IsDirected ∧ π.InteriorIn W) ∧
      ((∃ π : Walk G p.1 p.2, π.IsBifurcation ∧ π.InteriorIn W) ∨
       (∃ π : Walk G p.2 p.1, π.IsBifurcation ∧ π.InteriorIn W)) :=
  Iff.rfl

end CDMG

end Causality
