import Chapter3_GraphTheory.Section3_1.CDMG

namespace Causality

/-!
# Hard intervention on CDMGs (`def_3_10`)

This file formalises the LN definition `def_3_10`
(`\label{def:G_hard_intervention}`) — the *hard intervention*
operation `G ↦ G_{\doit(W)}` on a CDMG.  Given a CDMG
`G = (J, V, E, L)` and a subset of nodes `W ⊆ J ∪ V`, the intervened
CDMG has

* `J_{\doit(W)} := J ∪ W` (every node of `W` becomes an input node),
* `V_{\doit(W)} := V ∖ W`,
* `E_{\doit(W)} := E ∖ { (v₁, v₂) ∈ E | v₂ ∈ W }` (every directed
  edge whose head lies in `W` is removed),
* `L_{\doit(W)} := L ∖ { (v₁, v₂) ∈ L | v₂ ∈ W }`, *symmetrised*
  under the `hL_symm` axiom of `def_3_1` so that `L_{\doit(W)}` is a
  symmetric subset of `(V ∖ W) × (V ∖ W)`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/def_3_10_HardInterventionOn.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:G_hard_intervention}`).  The symmetrisation of item iv is
documented in the tex's *"Remark on item iv.\ and the symmetry of
`L`"*: under `def_3_1`'s ordered-pair encoding the literal one-sided
removal at item iv does NOT preserve `hL_symm`, so the constructor
*must* produce a symmetric `L_{\doit(W)}` in order to satisfy the
CDMG axioms.  The two-sided filter `fun e => e.1 ∉ W ∧ e.2 ∉ W` is
the unique reading consistent with both (a) the LN's natural-language
gloss "remove all edges into nodes from `W`" (a bidirected edge is
into *both* of its endpoints, `def_3_3` item ii) and (b) the LN's own
assertion that `G_{\doit(W)}` is itself a CDMG.

The substantive design rationale — why this Lean shape, why
`Finset.filter`, why the asymmetric `e.2 ∉ W` for `E` and the
symmetric `e.1 ∉ W ∧ e.2 ∉ W` for `L`, how `W ∩ J ≠ ∅` behaves —
lives in the `--` comment block immediately above the `def`
declaration.  Read that block before changing a field; it is the
load-bearing contract for the do-calculus chapters (ch. 5+) and the
iSCM intervention algebra (ch. 8+).
-/

namespace CDMG

-- def_3_10 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_10 --- end helper

-- ref: def_3_10
--
-- The *hard intervention on `G` with respect to `W`* is the CDMG
-- `G.hardInterventionOn W hW` whose four components are
--
--   * `J' := G.J ∪ W`                                 — every node of
--     `W` is converted to an input node;
--   * `V' := G.V \ W`                                 — every node of
--     `W` is removed from `V`;
--   * `E' := { e ∈ G.E | e.2 ∉ W }`                   — every directed
--     edge whose head is in `W` is removed; every other directed edge
--     is retained;
--   * `L' := { e ∈ G.L | e.1 ∉ W ∧ e.2 ∉ W }`         — every
--     bidirected edge incident at any node of `W` (either endpoint) is
--     removed.
--
-- The hypothesis `hW : W ⊆ G.J ∪ G.V` is the LN's
-- "$W \subseteq J \cup V$" precondition.
/-
LN tex (rewritten `def_3_10_HardInterventionOn`, items i–iv):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq J \cup V$.
    The intervened CDMG of $G$ w.r.t. $W$ is
    $G_{\doit(W)} := (J_{\doit(W)}, V_{\doit(W)}, E_{\doit(W)},
                      L_{\doit(W)})$,
    where
      i.   $J_{\doit(W)} := J \cup W$;
      ii.  $V_{\doit(W)} := V \sm W$;
      iii. $E_{\doit(W)} := E \sm \{ (v_1, v_2) \in E \mid v_2 \in W \}$;
      iv.  $L_{\doit(W)} := L \sm \{ (v_1, v_2) \in L \mid v_2 \in W \}$,
           symmetrised in the Lean encoding to preserve `hL_symm`
           (see "Remark on item iv.\ and the symmetry of $L$" in the
           tex spec).

LN block (verbatim, for backup):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq J \cup V$ a
    subset of nodes.  The *intervened CDMG* w.r.t. $W$ of $G$ is the
    CDMG $G_{\doit(W)} := (J_{\doit(W)}, V_{\doit(W)}, E_{\doit(W)},
    L_{\doit(W)})$, where i.) $J_{\doit(W)} := J \cup W$, ii.)
    $V_{\doit(W)} := V \sm W$, iii.) $E_{\doit(W)} := E \sm
    \{ v \tuh w \mid v \in G, w \in W \}$, iv.) $L_{\doit(W)} :=
    L \sm \{ v \huh w \mid v \in G, w \in W \}$, where we turn all
    nodes from $W$ into input nodes and remove all edges into nodes
    from $W$.
-/
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- * **`def`, not `structure` / `inductive` / `class`.** A hard
--   intervention is a *function* `CDMG Node → Finset Node → … →
--   CDMG Node`, not new data and not a typeclass-resolvable property.
--   The CDMG already has its `structure` (`def_3_1`); this row simply
--   produces a new CDMG from an existing one.  Wrapping the result
--   in a fresh structure (e.g. a `HardInterventionOn` record carrying
--   the intervened graph as a field) was rejected because every
--   downstream consumer in ch. 5 / ch. 8+ destructures the intervened
--   graph the same way any other CDMG is destructured — via
--   `(G.hardInterventionOn W hW).J`, `…V`, `…E`, `…L` — and an extra
--   wrapping layer would force a re-destructuring step at every such
--   call site.  An `inductive` was rejected for the same reason: it
--   would force pattern-matching on the constructor where the LN
--   simply names the four fields.
--
-- * **`hW : W ⊆ G.J ∪ G.V` is an explicit argument, not a sub-condition
--   threaded through the body.**  The LN's "Let $W \subseteq J \cup V$"
--   is part of the *signature* of the hard intervention operation;
--   without it the resulting tuple would still satisfy the five CDMG
--   axioms (the typing constraints on `G.E` and `G.L` alone are
--   strong enough — see the "$W \cap J \neq \emptyset$" bullet below
--   for why `hW` is not consumed in the proofs), but the LN-faithful
--   *statement* requires `hW` at the signature level.  Making it an
--   explicit argument keeps the precondition visible at every call
--   site and is the natural place for downstream lemmas about
--   `G.hardInterventionOn W` to plug it in.  Pushing `hW` into an
--   instance was rejected: subset facts are not typeclass-resolvable
--   in any general way and would force every caller to manually
--   discharge the membership.
--
-- * **`Finset.filter` for the edge-set removals, not `Finset.image` /
--   recursion / a quotient.**  The LN writes the removal sets in
--   set-builder form `E \setminus \{ … \mid … \}`.  Lean's
--   `Finset.filter` is the closest primitive (`Finset.mem_filter`
--   gives exactly `e ∈ s.filter p ↔ e ∈ s ∧ p e`), shares the
--   `Finset (Node × Node)` carrier with every other consumer in
--   chapter 3 (`def_3_5`'s family-set filters, `def_3_8`'s
--   topological-order projections), and decidability of the
--   filter-predicate follows from `[DecidableEq Node]`.
--   `Finset.image` was rejected because the LN takes a *difference*
--   with the original edge set, not a re-mapping; recursion is
--   overkill for a single set-comprehension.  A quotient encoding
--   was rejected at the `def_3_1` design stage (see `CDMG.lean`); we
--   inherit the ordered-pair-plus-symmetry choice here.
--
-- * **Directed-edge removal is one-sided (`e.2 ∉ W`); bidirected-edge
--   removal is two-sided (`e.1 ∉ W ∧ e.2 ∉ W`).**  Item iii of the
--   rewritten tex says "remove every directed edge whose head lies
--   in `W`": the head of `(v₁, v₂) ∈ G.E` is `v₂`, so the
--   kept-condition is `e.2 ∉ W` — no symmetrisation needed on the
--   directed channel because `G.E` itself is not symmetric.
--   Item iv literally writes the analogous one-sided condition
--   `v₂ ∈ W` for `L`, but, crucially, under `def_3_1`'s ordered-pair
--   encoding of `L` (with `hL_symm` enforcing
--   `(v₁, v₂) ∈ L ↔ (v₂, v₁) ∈ L`), the one-sided filter does *not*
--   preserve symmetry: for `w ∈ W ∩ V` and `v ∈ V \ W`, both pairs
--   `(v, w)` and `(w, v)` lie in `G.L` and together represent the
--   same bidirected edge; the one-sided rule deletes `(v, w)` (its
--   second slot is `w`) but retains `(w, v)` (its second slot is
--   `v`), so `L'` would fail `hL_symm` and the four-tuple would
--   *not* be a CDMG.  The tex's "Remark on item iv.\ and the
--   symmetry of `L`" explicitly defers the reconciliation to this
--   Lean encoding: the constructor *must* produce a symmetric
--   `L_{\doit(W)}`.  Two independent arguments pin down the
--   two-sided reading as the unique LN-faithful one:
--
--     (a) The LN's own natural-language gloss "remove all edges into
--         nodes from `W`".  A bidirected edge `v₁ \huh v₂` is into
--         *both* endpoints by `def_3_3` item ii (the `L`-clause of
--         `into`), so the LN's gloss reads "delete every bidirected
--         edge with an endpoint in `W`".  This is exactly the
--         two-sided filter.
--
--     (b) The LN's assertion that `G_{\doit(W)}` is itself a CDMG.
--         Symmetry of `L_{\doit(W)}` is required by the `def_3_1`
--         axiom `hL_symm`; the one-sided rule does not deliver it;
--         the two-sided rule does.
--
--   Any future row asserting "`G_{\doit(W)}` has no bidirected edge
--   incident at `W`" (e.g. the iSCM intervention-edge lemmas of
--   ch. 8+, or the disjoint-intervention commutativity rows
--   `claim_3_8` / `claim_3_11`) builds on this contract.
--
--   This is a *registered content deviation* from the LN's literal
--   item iv; the register entry is
--   `hard_intervention_l_symmetrized_removal` in
--   `leanification/deviations.json` (grep that id for the full
--   rationale, the manager-accepted status, and the recorded two-node
--   counter-example: `G2` over `Fin 2`, `G.L = {(0,1),(1,0)}`,
--   `W = {1}` — the LN-literal one-sided filter yields `{(1,0)}`
--   whereas the Lean two-sided filter yields `∅`).  The deviation is
--   *structural* (forced by `def_3_1`'s ordered-pair encoding of `L`
--   with `hL_symm` as a separate axiom), not stylistic: any literal
--   reading would not type-check as a CDMG.
--
--   The `hL_irrefl` and `hL_symm` proof obligations of `G_{\doit(W)}`
--   transport from `G`'s axioms.  Since `L'` is a `Finset.filter` of
--   `G.L`, every pair in `L'` is also in `G.L`, so `G.hL_irrefl`
--   applies pointwise.  For `hL_symm`: if `(v₁, v₂) ∈ L'` then
--   `(v₁, v₂) ∈ G.L` and `v₁ ∉ W ∧ v₂ ∉ W`; `G.hL_symm` gives
--   `(v₂, v₁) ∈ G.L`, and the predicate `e.1 ∉ W ∧ e.2 ∉ W` is
--   *symmetric* under the swap (the two conjuncts commute), so
--   `(v₂, v₁) ∈ L'`.  The one-sided filter would not deliver this
--   second step — that is the load-bearing reason the symmetric form
--   is the only one that fits the structure constructor.
--
--   WARNING — membership reasoning on `(G.hardInterventionOn W hW).L`.
--   A reader cribbing the LN's one-sided item iv is liable to write
--     `(v, w) ∈ (G.hardInterventionOn W hW).L
--        ↔ (v, w) ∈ G.L ∧ w ∉ W`            -- WRONG
--   That biconditional is *false* in this Lean encoding: take
--   `v ∈ W ∩ V` and `w ∉ W`.  The pair `(v, w)` lies in `G.L` and
--   satisfies `w ∉ W`, so the wrong rule would put it in `L'`; but
--   the actual two-sided filter rejects it because `v ∈ W`.  The
--   correct membership rule is
--     `(v, w) ∈ (G.hardInterventionOn W hW).L
--        ↔ (v, w) ∈ G.L ∧ v ∉ W ∧ w ∉ W`.
--   The expected downstream lemma is `mem_hardInterventionOn_L_iff`
--   (two-sided, paralleling `Finset.mem_filter`); do *not* introduce
--   a one-sided convenience variant — it will silently mis-handle the
--   mirror pair and quietly contradict `hL_symm`.
--
-- * **Items i, ii are verbatim LN translations; item iii's `v ∈ G`
--   clause is folded into `def_3_1`'s `hE_subset` typing.**  Items i
--   (`J' := G.J ∪ W`) and ii (`V' := G.V \ W`) are direct, literal
--   translations of the LN set-builder formulae — no design choice
--   beyond the `Finset` carrier was made, and no deviation exists
--   there.  In item iii the LN's set-builder reads
--   `{ v \tuh w | v ∈ G, w ∈ W }`; per the tex's "Disambiguation of
--   the LN's `v ∈ G` quantifier" paragraph, the informal `v ∈ G`
--   abbreviates `v ∈ J ∪ V`.  Under `def_3_1`'s
--   `hE_subset : (v₁, v₂) ∈ E → v₁ ∈ J ∪ V ∧ v₂ ∈ V`, the clause
--   `v₁ ∈ J ∪ V` is *automatic* on every element of `G.E`, so the
--   `Finset.filter` predicate reduces to the single conjunct
--   `e.2 ∉ W`.  This is a *presentation simplification*, not a
--   content deviation: a reader comparing the Lean filter to the LN
--   set-builder line-by-line should treat the missing `v₁ ∈ J ∪ V`
--   clause as redundant (already discharged by `hE_subset`), not
--   missing.
--
-- * **`hJV_disj` for `G_{\doit(W)}` is one line of set algebra.**
--   `(G.J ∪ W) ∩ (G.V \ W) = ∅` decomposes as the union of (i)
--   `G.J ∩ (G.V \ W) = ∅`, which follows from `G.hJV_disj`
--   (`G.J ∩ G.V = ∅`) and `(G.V \ W) ⊆ G.V`, and (ii)
--   `W ∩ (G.V \ W) = ∅`, which is immediate from `Finset.sdiff`.
--   The proof does not consume `hW`; the disjointness is structural,
--   independent of the `W ⊆ J ∪ V` precondition.
--
-- * **`W ∩ J ≠ ∅` is admitted; behaviour matches the tex
--   case-analysis.**  The LN hypothesis is `W ⊆ J ∪ V`; we do *not*
--   additionally require `W ∩ J = ∅`.  The tex's "On the case
--   $W \cap J \neq \emptyset$" paragraph spells out the behaviour:
--   items i and ii are *idempotent* on `W ∩ J` (`G.J ∪ W` is unchanged
--   at those nodes; `G.V \ W` is unaffected because `G.J` is disjoint
--   from `G.V` by `hJV_disj`); items iii and iv still mechanically
--   fire on edges with head in `W ∩ J`, but `def_3_1`'s typing
--   constraints `E ⊆ (J ∪ V) × V` and `L ⊆ V × V` forbid any edge
--   from having its head in `J` in the first place, so the filters
--   are *de facto* no-ops on `W ∩ J`.  We do not bake the idempotency
--   into the type; any downstream row that wants "intervening on a
--   subset of `J` is the identity" derives it as a lemma.  This is
--   also the reason `hW` is not consumed in the five proof
--   obligations below: the typing constraints from `G` already
--   exclude every problematic case, and `hW` is carried purely for
--   LN-faithfulness of the *signature*.
--
-- * **Argument order `(G : CDMG Node) (W : Finset Node) (hW : …)`.**
--   `G` first matches the convention of every chapter-3 predicate
--   (`G.tuh`, `G.huh`, `G.adjacent`, `G.into`, `G.outOf`), enabling
--   dot-notation `G.hardInterventionOn W hW`.  `W` precedes `hW`
--   so the call site reads left-to-right like the LN's "let
--   `W ⊆ J ∪ V` be a subset".
--
-- * **`where` syntax with named fields, not anonymous-constructor
--   `⟨ … ⟩`.**  The CDMG `structure` has nine fields (`J`, `V`,
--   `hJV_disj`, `E`, `hE_subset`, `L`, `hL_subset`, `hL_irrefl`,
--   `hL_symm`).  An anonymous-constructor form would interleave data
--   and proof obligations in a positional list, making the
--   correspondence with `def_3_1`'s `structure` opaque at a glance.
--   `where … J := … V := …` keeps every field labelled and lets
--   the proof obligations sit next to the data they refer to.
--
-- * **Downstream consumers.**  Every do-calculus row of ch. 5 (the
--   interventional CBN factorisation `do(W)`, the three rules of
--   do-calculus, identifiability via the ID algorithm), the iSCM
--   intervention algebra of ch. 8–10 (composition of hard
--   interventions, disjoint-intervention commutativity), and the
--   marginalisation-intervention interaction of `claim_3_18`, as
--   well as the topological-order preservation of `claim_3_3` /
--   `claim_3_13`, all rest on the four field assignments above.
--   The symmetric-removal choice in `L_{\doit(W)}` is the *contract*
--   those rows rely on; any deviation would break the
--   "`G_{\doit(W)}` is itself a CDMG" assumption every one of them
--   silently uses.
-- def_3_10 -- start statement
def hardInterventionOn (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V) : CDMG Node where
  J := G.J ∪ W
  V := G.V \ W
  hJV_disj := by
    -- `hW` is part of the signature for LN-faithfulness ("Let
    -- `W ⊆ J ∪ V`"), but is not consumed in the five proof obligations:
    -- `def_3_1`'s typing constraints on `G.E` / `G.L` already exclude
    -- every problematic case (see the `W ∩ J ≠ ∅` design-choice bullet
    -- above).  The `let _` mirrors the convention used in
    -- `CDMGRestrictions.lean` for unused LN-faithful hypotheses.
    let _ := hW
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
    · exact Finset.disjoint_left.mpr fun a haJ haVW =>
        Finset.disjoint_left.mp G.hJV_disj haJ (Finset.mem_sdiff.mp haVW).1
    · exact Finset.disjoint_left.mpr fun a haW haVW =>
        (Finset.mem_sdiff.mp haVW).2 haW
  E := G.E.filter (fun e => e.2 ∉ W)
  hE_subset := by
    intro e he
    obtain ⟨heE, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨he1, he2V⟩ := G.hE_subset heE
    refine ⟨?_, Finset.mem_sdiff.mpr ⟨he2V, he2⟩⟩
    rcases Finset.mem_union.mp he1 with hJ | hV
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
    · by_cases hW1 : e.1 ∈ W
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hW1)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, hW1⟩)
  L := G.L.filter (fun e => e.1 ∉ W ∧ e.2 ∉ W)
  hL_subset := by
    intro e he
    obtain ⟨heL, he1, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨he1V, he2V⟩ := G.hL_subset heL
    exact ⟨Finset.mem_sdiff.mpr ⟨he1V, he1⟩, Finset.mem_sdiff.mpr ⟨he2V, he2⟩⟩
  hL_irrefl := by
    intro v1 v2 h
    exact G.hL_irrefl (Finset.mem_filter.mp h).1
  hL_symm := by
    intro v1 v2 h
    obtain ⟨hL, h1, h2⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨G.hL_symm hL, h2, h1⟩
-- def_3_10 -- end statement

end CDMG

end Causality
