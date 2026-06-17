import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGTypes
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn

namespace Causality

/-!
# Node-splitting hard intervention / SWIG on CDMGs (`def_3_12`)

This file formalises the LN definition `def_3_12`
(`\label{def:G_node-splitting_intervention}` in `graphs.tex`) — the
*single-world intervention graph* (SWIG) operation `G ↦ G_{swig(W)}` on
a CDMG.  Given a CDMG `G = (J, V, E, L)` and a subset `W ⊆ V` of output
nodes, the SWIG has

* `J_{swig(W)} := J ⊍ W^i` (the input-side copies `W^i` of `W` are
  reclassified as input nodes),
* `V_{swig(W)} := (V ∖ W) ⊍ W^o` (each `w ∈ W` is replaced by its
  output-side copy `w^o`),
* `E_{swig(W)} := { (v_1^i, v_2^o) | (v_1, v_2) ∈ E }` (every directed
  edge of `G` is reattached as a directed edge from the input-side tag
  of its source to the output-side tag of its target),
* `L_{swig(W)} := { (v_1^o, v_2^o) | (v_1, v_2) ∈ L }` (every
  bidirected edge of `G` is lifted with **both** endpoints carrying the
  `^o` superscript — no element of `W^i` appears as an endpoint of any
  bidirected edge in the SWIG).

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/def_3_12_NodeSplittingHard.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:G_node-splitting_intervention}`).  The rewrite folds the
two working-phase wording-check items in line:

* `implicit_disjointness_of_copies_from_original_nodes` — the LN's
  fresh-copy disjointness `W^o ∩ V = W^i ∩ V = W^o ∩ J = W^i ∩ J = W^o ∩
  W^i = ∅` is realised **at the type level** by reusing `def_3_11`'s
  `SplitNode Node` `inductive` (three distinct constructors `unsplit`,
  `copy0`, `copy1`), with the SWIG-side reading `copy0 ↔ ^o`,
  `copy1 ↔ ^i` (see the design block on the main def for the rationale
  of reusing `SplitNode` rather than introducing a parallel
  `SwigNode`).
* `closing_remark_uses_removal_language_for_a_constructive_definition`
  — the LN's closing gloss "removing all edges into `W^i` / out of
  `W^o`" is a *descriptive* remark on items i.–iv., not a separate
  edge-deletion step; in the Lean encoding the "removal" is purely
  structural (no edge ending in `W^i` or starting in `W^o` is ever
  included in `E_{swig(W)}` to begin with, because the set-builder
  `(toCopy1 W e.1, toCopy0 W e.2)` only ever produces a `^i`-tagged
  source and a `^o`-tagged target).

The substantive design rationale — the choice of reusing `SplitNode`
(rather than introducing a parallel `SwigNode`), the direct (rather
than composed) construction, how the closing-remark phrasing is
realised structurally, and how each CDMG axiom of `def_3_1` is
discharged on the tagged-sum carrier — lives in the `--` comment block
immediately above the `def` declaration.  Read that block before
changing a field; it is the load-bearing contract for `claim_3_9`
(SWIG acyclicity) and every downstream SWIG-consumer in the
do-calculus / counterfactual chapters that pattern-match on SWIG
membership.
-/

namespace CDMG

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: nodeSplittingHard
-- def_3_12 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_12 --- end helper

-- Private helper: `toCopy0 W` is injective on `Node`.  Used by
-- `nodeSplittingHard`'s `hL_irrefl` to lift `G.hL_irrefl`'s
-- `v_1 ≠ v_2` on `Node` up to `toCopy0 W v_1 ≠ toCopy0 W v_2` on
-- `SplitNode Node`.  An identical lemma lives in `NodeSplittingOn.lean`
-- as `toCopy0_inj` but is `private`-scoped to that file, so we
-- re-derive it locally here.  Proof by case-analysis on `a ∈ W`,
-- `b ∈ W`: distinct constructors `.copy0` vs `.unsplit` on the
-- cross-cases, constructor injectivity within each matched case.
-- Extracted as a top-level lemma so the `injection` / `cases` tactics
-- inside its body operate on the *free* variables `a`, `b`, sidestepping
-- the "dependent elimination failed" error that arises when `cases` is
-- applied to an equality whose two sides are projections of a single
-- term.
private lemma swig_toCopy0_inj {W : Finset Node} {a b : Node}
    (h : toCopy0 W a = toCopy0 W b) : a = b := by
  unfold toCopy0 at h
  by_cases hWa : a ∈ W
  · by_cases hWb : b ∈ W
    · rw [if_pos hWa, if_pos hWb] at h
      injection h
    · rw [if_pos hWa, if_neg hWb] at h
      cases h
  · by_cases hWb : b ∈ W
    · rw [if_neg hWa, if_pos hWb] at h
      cases h
    · rw [if_neg hWa, if_neg hWb] at h
      injection h

-- ## Proof helpers for the five CDMG axioms under SWIG
--
-- The five private lemmas below discharge the five proof obligations
-- of `def_3_1`'s `CDMG` structure (`hJV_disj`, `hE_subset`,
-- `hL_subset`, `hL_irrefl`, `hL_symm`) for the SWIG construction.
-- They are factored out of the structure-literal body of
-- `nodeSplittingHard` so the def body is pure data + lemma references
-- — the website builder renders the def's signature, and a reader
-- sees the data assignments without proof clutter.  None of the
-- obligations consume `hW`; `hW` is carried on the def's signature
-- purely for LN-faithfulness ("Let `W ⊆ V`").

private lemma nodeSplittingHard_hJV_disj (G : CDMG Node) (W : Finset Node) :
    Disjoint (G.J.image SplitNode.unsplit ∪ W.image SplitNode.copy1)
        ((G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0) := by
  rw [Finset.disjoint_left]
  rintro x hxJ hxV
  rcases Finset.mem_union.mp hxJ with hJ | hC1
  · -- `x ∈ G.J.image .unsplit`: pick the preimage `j ∈ G.J`, rewriting
    -- `x = .unsplit j`.
    obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hJ
    rcases Finset.mem_union.mp hxV with hVu | hC0
    · -- `x = .unsplit j` is in `(G.V \ W).image .unsplit`: the preimage
      -- `v` agrees with `j` by constructor injectivity, so
      -- `j ∈ G.V \ W ⊆ G.V`, contradicting `j ∈ G.J` via `G.hJV_disj`.
      obtain ⟨v, hvVW, hveq⟩ := Finset.mem_image.mp hVu
      cases hveq
      exact Finset.disjoint_left.mp G.hJV_disj hjJ
        (Finset.mem_sdiff.mp hvVW).1
    · -- `x = .unsplit j` is in `W.image .copy0`: constructor mismatch.
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hC0
      cases hweq
  · -- `x ∈ W.image .copy1`: pick the preimage `w ∈ W`, rewriting
    -- `x = .copy1 w`.
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hC1
    rcases Finset.mem_union.mp hxV with hVu | hC0
    · -- `x = .copy1 w` is in `(G.V \ W).image .unsplit`: constructor
      -- mismatch.
      obtain ⟨_, _, hveq⟩ := Finset.mem_image.mp hVu
      cases hveq
    · -- `x = .copy1 w` is in `W.image .copy0`: constructor mismatch.
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hC0
      cases hweq

private lemma nodeSplittingHard_hE_subset (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃e : SplitNode Node × SplitNode Node⦄,
      e ∈ G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2)) →
      e.1 ∈ (G.J.image SplitNode.unsplit ∪ W.image SplitNode.copy1) ∪
              ((G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0) ∧
        e.2 ∈ (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0 := by
  intro e he
  obtain ⟨e', he'E, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨he'1, he'2⟩ := G.hE_subset he'E
  refine ⟨?_, ?_⟩
  · -- Source slot `toCopy1 W e'.1`.
    by_cases hW1 : e'.1 ∈ W
    · -- `e'.1 ∈ W`: `toCopy1 W e'.1 = .copy1 e'.1`, lands in
      -- `J_{swig} = G.J.image .unsplit ∪ W.image .copy1` via the right
      -- summand `W.image .copy1`.
      simp only [toCopy1, hW1, if_true]
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨e'.1, hW1, rfl⟩
    · -- `e'.1 ∉ W`: `toCopy1 W e'.1 = .unsplit e'.1`.
      simp only [toCopy1, hW1, if_false]
      rcases Finset.mem_union.mp he'1 with hJ | hV
      · -- `e'.1 ∈ G.J`: lands in `J_{swig}` via `G.J.image .unsplit`.
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨e'.1, hJ, rfl⟩
      · -- `e'.1 ∈ G.V`: combined with `e'.1 ∉ W`, `e'.1 ∈ G.V \ W`, so
        -- `.unsplit e'.1` lands in `V_{swig}` via `(G.V \ W).image .unsplit`.
        refine Finset.mem_union_right _ ?_
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr
          ⟨e'.1, Finset.mem_sdiff.mpr ⟨hV, hW1⟩, rfl⟩
  · -- Target slot `toCopy0 W e'.2`.  `e'.2 ∈ G.V` already by `G.hE_subset`.
    by_cases hW2 : e'.2 ∈ W
    · -- `e'.2 ∈ W`: `toCopy0 W e'.2 = .copy0 e'.2`, lands in `V_{swig}`
      -- via the right summand `W.image .copy0`.
      simp only [toCopy0, hW2, if_true]
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨e'.2, hW2, rfl⟩
    · -- `e'.2 ∉ W`: combined with `e'.2 ∈ G.V`, `e'.2 ∈ G.V \ W`, so
      -- `.unsplit e'.2` lands in `V_{swig}` via `(G.V \ W).image .unsplit`.
      simp only [toCopy0, hW2, if_false]
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr
        ⟨e'.2, Finset.mem_sdiff.mpr ⟨he'2, hW2⟩, rfl⟩

private lemma nodeSplittingHard_hL_subset (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃e : SplitNode Node × SplitNode Node⦄,
      e ∈ G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2)) →
      e.1 ∈ (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0 ∧
        e.2 ∈ (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0 := by
  intro e he
  obtain ⟨e', he'L, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨he'1, he'2⟩ := G.hL_subset he'L
  refine ⟨?_, ?_⟩
  · by_cases hW1 : e'.1 ∈ W
    · simp only [toCopy0, hW1, if_true]
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨e'.1, hW1, rfl⟩
    · simp only [toCopy0, hW1, if_false]
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr
        ⟨e'.1, Finset.mem_sdiff.mpr ⟨he'1, hW1⟩, rfl⟩
  · by_cases hW2 : e'.2 ∈ W
    · simp only [toCopy0, hW2, if_true]
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨e'.2, hW2, rfl⟩
    · simp only [toCopy0, hW2, if_false]
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr
        ⟨e'.2, Finset.mem_sdiff.mpr ⟨he'2, hW2⟩, rfl⟩

private lemma nodeSplittingHard_hL_irrefl (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃v1 v2 : SplitNode Node⦄,
      (v1, v2) ∈ G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2)) →
      v1 ≠ v2 := by
  intro v1 v2 h
  obtain ⟨e', he'L, heq⟩ := Finset.mem_image.mp h
  have hne : e'.1 ≠ e'.2 := G.hL_irrefl he'L
  intro hv12
  apply hne
  have h1 : toCopy0 W e'.1 = v1 := by
    have := congrArg Prod.fst heq; simpa using this
  have h2 : toCopy0 W e'.2 = v2 := by
    have := congrArg Prod.snd heq; simpa using this
  have hSplitEq : toCopy0 W e'.1 = toCopy0 W e'.2 := by
    rw [h1, h2, hv12]
  exact swig_toCopy0_inj hSplitEq

private lemma nodeSplittingHard_hL_symm (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃v1 v2 : SplitNode Node⦄,
      (v1, v2) ∈ G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2)) →
      (v2, v1) ∈ G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2)) := by
  intro v1 v2 h
  obtain ⟨e', he'L, heq⟩ := Finset.mem_image.mp h
  have h1 : toCopy0 W e'.1 = v1 := by
    have := congrArg Prod.fst heq; simpa using this
  have h2 : toCopy0 W e'.2 = v2 := by
    have := congrArg Prod.snd heq; simpa using this
  have hsym : (e'.2, e'.1) ∈ G.L := G.hL_symm he'L
  refine Finset.mem_image.mpr ⟨(e'.2, e'.1), hsym, ?_⟩
  simp [h1, h2]

-- ref: def_3_12
--
-- The *single-world intervention graph (SWIG)* of `G` with respect to
-- `W`, also called the *node-splitting hard intervention* on `G`, is
-- the CDMG `G.nodeSplittingHard hG W hW` over the carrier
-- `SplitNode Node` whose four components are
--
--   * `J' := G.J.image .unsplit ∪ W.image .copy1`     — input nodes
--     are the original `G.J` (lifted via `unsplit`) together with the
--     LN's `W^i` copies (the `.copy1`-tagged elements of `W`), which
--     are *reclassified as input nodes* by the SWIG construction;
--   * `V' := (G.V \ W).image .unsplit ∪ W.image .copy0` — output
--     nodes are the unsplit residual `G.V \ W` (lifted via `unsplit`)
--     together with the LN's `W^o` copies (the `.copy0`-tagged
--     elements of `W`);
--   * `E' := G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))` —
--     every directed edge `v_1 → v_2 ∈ G.E` of `G` is reattached as
--     `(v_1^i, v_2^o) ∈ E'` — the source slot picks up the `^i` tag
--     (or stays `unsplit` outside `W`) via `toCopy1`, and the target
--     slot picks up the `^o` tag (or stays `unsplit` outside `W`) via
--     `toCopy0`.  **No transfer edges** are added (contrast with
--     `def_3_11`'s node-splitting, which adds `(w^0, w^1)` for every
--     `w ∈ W`);
--   * `L' := G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2))`     —
--     every bidirected edge `v_1 ↔ v_2 ∈ G.L` is lifted with **both**
--     endpoints carrying the `^o` superscript.  Identical to
--     `def_3_11`'s `L_{spl(W)}` clause: no element of `W^i` (i.e.\
--     `.copy1 w`) ever appears as an endpoint of any bidirected edge
--     in `L_{swig(W)}`.
--
-- The hypotheses `hG : G.IsCADMG` and `hW : W ⊆ G.V` are the LN's
-- "Let $G$ be a CADMG" and "$W \subseteq V$" preconditions
-- respectively; see design-choice bullet (d) below for the input-side
-- role of `hG` (acyclicity is consumed downstream by `claim_3_9`, not
-- here).
/-
LN tex (rewritten `def_3_12_NodeSplittingHard`, items i–iv):

    Let $G = (J, V, E, L)$ be a CADMG (in particular a CDMG) and
    $W \subseteq V$ a subset of output nodes.  The SWIG w.r.t.\ $W$
    of $G$ is the CDMG $G_{swig(W)} := (J_{swig(W)}, V_{swig(W)},
                                          E_{swig(W)}, L_{swig(W)})$,
    where (using tagged copies $W^o := \{w^o \mid w \in W\}$,
    $W^i := \{w^i \mid w \in W\}$ realised at the type level, and the
    convention $v^o := v^i := v$ for $v \in J \cup (V \setminus W)$ as
    notational shorthand inside the set-builders below):
      i.   $J_{swig(W)} := J \dcup W^i$;
      ii.  $V_{swig(W)} := (V \setminus W) \dcup W^o$;
      iii. $E_{swig(W)} := \{ (v_1^i, v_2^o) \mid (v_1, v_2) \in E \}$;
      iv.  $L_{swig(W)} := \{ (v_1^o, v_2^o) \mid (v_1, v_2) \in L \}$.

LN block (verbatim, for backup):

    Let $G=(J,V,E,L)$ be a CADMG and $W \subseteq V$ a subset of the
    output nodes.  The SWIG w.r.t.\ $W$ of $G$ is the CADMG
    $G_{swig(W)} := (J_{swig(W)}, V_{swig(W)}, E_{swig(W)},
    L_{swig(W)})$, constructed as follows.  We first make two disjoint
    copies of the nodes in $W$: $W^o := \{w^o \mid w \in W\}$,
    $W^i := \{w^i \mid w \in W\}$.  Note that we consider $w^o \neq w^i$
    for $w \in W$.  However, for brevity, for $v \in J \cup V \sm W$ we
    put $v^o := v^i := v$.  We then define:
      i.   $J_{swig(W)} := J \dcup W^i$,
      ii.  $V_{swig(W)} := (V \sm W) \dcup W^o$,
      iii. $E_{swig(W)} := \{ v_1^i \to v_2^o \mid v_1 \to v_2 \in E \}$,
      iv.  $L_{swig(W)} := \{ v_1^o \leftrightarrow v_2^o
                              \mid v_1 \leftrightarrow v_2 \in L \}$,
    where we turn all nodes of $W^i$ into input nodes, removing all
    edges into $W^i$, and we turn all nodes of $W^o$ into output nodes,
    removing all edges out of $W^o$.
-/
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- * **(a) Tagged node universe encoded by *reusing* `def_3_11`'s
--   `SplitNode Node` `inductive`, with the convention
--   `.copy0 ↔ ^o` (output side) and `.copy1 ↔ ^i` (input side).**
--   The rewritten tex's "Tagged copies of `W`" paragraph fixes the
--   semantics: `W^o` and `W^i` are realised as type-level tagged
--   copies so the five disjointness assertions
--   `W^o ∩ V = W^i ∩ V = W^o ∩ J = W^i ∩ J = W^o ∩ W^i = ∅` hold
--   *by typing* rather than as side conditions.  `def_3_11`'s
--   `SplitNode Node` (three named constructors `unsplit`, `copy0`,
--   `copy1`, with `deriving DecidableEq`) is *exactly* such a
--   tagged-sum carrier and was designed for precisely this paradigm.
--   Reusing it has three concrete payoffs:
--     (i) The SWIG and the node-split graph then live on the *same*
--         carrier type, so claims relating them (notably the LN's own
--         "node-split, then hard-intervene at `W^i`" composite
--         reading, and any future downstream lemma about SWIG-vs-spl
--         congruence) state literal carrier-level equations rather
--         than threading a coercion `SwigNode → SplitNode` through
--         every claim.
--    (ii) The notational-shorthand helpers `toCopy0 W` and
--         `toCopy1 W` (LN's `v^0 := v^1 := v` shorthand for
--         `v ∈ J ∪ (V \ W)`) are *already* defined in
--         `NodeSplittingOn.lean`; they serve identically here (with
--         the SWIG-side reading `toCopy0 ↔ ^o`, `toCopy1 ↔ ^i`), so
--         we get the LN's set-builders item iii / iv for free.
--   (iii) The semantic motivation cross-checks: per
--         `NodeSplittingOn.lean`'s design block, `.copy0` already
--         represents the "natural / observational side" (the
--         pre-intervention identity, on which latent confounding and
--         ancestry are inherited from `G`) while `.copy1` represents
--         the "intervened / do-side" (causally isolated from its
--         observational counterpart).  This is exactly the SWIG-side
--         reading: `^o` is the natural / observational side, `^i` is
--         the intervened side.  The naming `.copy0` / `.copy1`
--         predates the SWIG-paradigm naming `^o` / `^i` but the
--         semantics line up on the nose.
--   An alternative — introducing a fresh `inductive SwigNode (Node :
--   Type*)` with constructors `unsplit`, `copyO`, `copyI` — was
--   rejected because it would (a) duplicate every structural lemma
--   that already exists for `SplitNode`, (b) force a coercion
--   `SwigNode ↔ SplitNode` at every place a downstream row composes
--   SWIG with node-splitting, and (c) hide the LN's own commented-out
--   "node-split, then hard-intervene at `W^i`" reading behind a
--   carrier mismatch.  The LN-critic working-phase subtlety
--   `implicit_disjointness_of_copies_from_original_nodes` is resolved
--   identically to `def_3_11`: by typing.
--
-- * **(b) Direct construction, NOT a composition of
--   `nodeSplittingOn` and `hardInterventionOn`.**  The rewritten tex
--   spec explicitly says (Conceptual motivation paragraph): "Items
--   i.–iv.\ below realise this composite construction *directly* as
--   four set-builders, without first constructing the intermediate
--   node-split graph: nothing is `included and then removed'."  The
--   LN-paradigm reading "node-split, then hard-intervene at `W^i`" is
--   present as *motivation* but the LN itself writes out the four
--   set-builders directly, and so do we.  A composed implementation
--     `(G.nodeSplittingOn W hW).hardInterventionOn (W.image .copy1) hW'`
--   would be type-correct (the inner `nodeSplittingOn` lifts to
--   `CDMG (SplitNode Node)`; the outer `hardInterventionOn` operates
--   on that lifted carrier, removing the `.copy1 w` nodes from `V`
--   and the transfer edges `(.copy0 w, .copy1 w)`) but was rejected
--   on three grounds:
--     (i) It does NOT match the LN's literal item-by-item statement.
--         The four set-builders i.–iv.\ are stated directly; mirroring
--         them directly in Lean preserves the LN paradigm at the
--         statement-marker-wrapped level — a downstream reader of the
--         website-rendered statement sees the four LN clauses
--         line-by-line, not a composite of two unrelated operators.
--    (ii) Definitional unfolding for downstream proofs is *cleaner*
--         with the direct form: `Finset.mem_image` fires once on each
--         of the four field expressions, vs.\ a two-stage
--         `Finset.mem_filter`-of-`Finset.mem_image`-of-`Finset.mem_union`
--         chain under the composed form.  Downstream `claim_3_9`
--         (SWIG acyclicity) and the do-calculus / counterfactual
--         consumers will inspect SWIG membership pointwise; the
--         direct form keeps that inspection one `Finset.mem_image`
--         away.
--   (iii) The composed form's `nodeSplittingOn` clause introduces
--         *transfer edges* `(.copy0 w, .copy1 w)` that the
--         outer `hardInterventionOn` immediately removes; nothing
--         downstream sees them, but they appear as intermediate
--         clutter in unfolding traces.  The direct form just doesn't
--         add them in the first place — matching the LN's "nothing
--         is included and then removed" framing literally.
--   The composed form may surface later as a *lemma* (e.g.\
--     "`G.nodeSplittingHard hG W hW = (G.nodeSplittingOn W hW).hardInterventionOn
--       (W.image .copy1) _`")
--   that proves the equivalence; we do not bake it into the def
--   itself.  This mirrors the LN paradigm: state the SWIG directly,
--   prove the composition equation as a downstream theorem when a
--   consumer needs it.
--
-- * **(c) The closing-remark phrasing "removing all edges into
--   `W^i` / out of `W^o`" is realised *structurally*, not as a
--   separate edge-deletion step.**  The rewritten tex's
--   "Disambiguation of the LN's closing remark" paragraph is
--   explicit: the LN closing sentence is a *descriptive gloss* on
--   items i.–iv., not a separate procedural step.  In the Lean
--   encoding this is literal:
--     – "Removing all edges into `W^i`" means *no* edge in
--       `E_{swig(W)}` or `L_{swig(W)}` has a target tagged `.copy1`.
--       For `E_{swig(W)}`, our set-builder produces
--       `(toCopy1 W e.1, toCopy0 W e.2)`; the target slot is
--       `toCopy0 W e.2`, which is either `.unsplit e.2` (if
--       `e.2 ∉ W`) or `.copy0 e.2` (if `e.2 ∈ W`) — *never* `.copy1`.
--       For `L_{swig(W)}`, both endpoints go through `toCopy0`, so
--       neither slot can produce `.copy1`.  No "removal" step is
--       executed because no edge with `.copy1` target is *ever
--       included*.
--     – "Removing all edges out of `W^o`" reads, in the rewritten tex
--       disambiguation, as *directed only*: no *directed* edge in
--       `E_{swig(W)}` has a source tagged `.copy0`.  Our set-builder's
--       source slot is `toCopy1 W e.1`, which is either `.unsplit e.1`
--       (if `e.1 ∉ W`) or `.copy1 e.1` (if `e.1 ∈ W`) — *never*
--       `.copy0`.  (Bidirected edges may legitimately have endpoints
--       in `W^o` via item iv., per the disambiguation; this is not a
--       contradiction.)
--   So both halves of the LN's closing sentence are realised by the
--   *shape* of our set-builders.  No filter, no difference, no
--   explicit deletion step appears in the Lean encoding — the LN's
--   procedural-sounding wording is translated to its structural
--   referent in the direct construction.  This resolves the
--   LN-critic working-phase subtlety
--   `closing_remark_uses_removal_language_for_a_constructive_definition`.
--
-- * **(d) Acyclicity is faithful to the LN on *both* sides of the
--   def — `(hG : G.IsCADMG)` on the input signature, and
--   acyclicity-preservation on the output deferred to `claim_3_9`
--   (the def returns `CDMG (SplitNode Node)`, not a CADMG).**  Two
--   halves; they sit on opposite sides of the def.
--
--   *(Input side — `hG : G.IsCADMG` on the signature.)*  The LN's
--   opening "Let $G$ be a CADMG" is the *input domain restriction*
--   for the SWIG operation; faithfully formalising the LN's input
--   quantifier means tagging `G` with the acyclicity proposition.
--   Chapter 3 has *no `CADMG` structure type* — `def_3_7`
--   (`Section3_1/CDMGTypes.lean:176`) defines CADMG-ness as a
--   propositional predicate `IsCADMG := IsAcyclic` on top of `CDMG`,
--   so the natural Lean rendering of "Let `G` be a CADMG" is
--   `(G : CDMG Node) (hG : G.IsCADMG)` — `G` carries the data, `hG`
--   carries the acyclicity side condition.  The body genuinely does
--   not consume `hG`: the four field assignments and the five
--   CDMG-typing proof obligations (`hJV_disj`, `hE_subset`,
--   `hL_subset`, `hL_irrefl`, `hL_symm`) are all acyclicity-free,
--   exactly as the rewritten tex's "paradigm-observation" paragraph
--   asserts — and that is precisely why SWIG-acyclicity is a
--   *separately stated and separately proved* preservation lemma in
--   `claim_3_9` rather than a bundled output field.  But the binder
--   still belongs on the signature, because dropping it would
--   silently loosen the LN's input quantifier domain to admit
--   non-acyclic CDMG inputs — a CONTENT deviation, not a presentation
--   simplification.  This was the precise issue flagged by
--   `verify_equivalence_strict` (adversarial) against an earlier
--   `(G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V)`-only signature;
--   the fix is to add `(hG : G.IsCADMG)` between `G` and `W`.  The
--   existing `set_option linter.unusedVariables false in` already
--   absorbs the (deliberately) unused `hG` binder without further
--   plumbing.
--
--   *(Output side — return type `CDMG (SplitNode Node)`, not
--   `CADMG`.)*  Acyclicity *preservation* — the LN's incidental
--   assertion that "$G_{swig(W)}$ is itself a CADMG" — is *deferred*
--   to `claim_3_9` (`SwigAcyclic`).  The def itself returns
--   `CDMG (SplitNode Node)`, mirroring the established chapter
--   pattern: `def_3_10` (`hardInterventionOn`) returns `CDMG` and
--   lifts acyclicity in `claim_3_3` (`AcyclicPreservedUnderDo`);
--   `def_3_11` (`nodeSplittingOn`) returns `CDMG` and lifts the
--   topological-order property in `claim_3_6`
--   (`SplitTopologicalOrder`).  `verify_equivalence_strict`
--   *explicitly* approved this output-side `CADMG → CDMG` split as a
--   PRESENTATION choice (not a CONTENT deviation) on the strength of
--   the chapter pattern: the structural bundling stays at the
--   foundational `CDMG` layer, and the named
--   acyclicity / order-preservation predicates lift on the CDMG via
--   separately stated theorems.  Downstream SWIG-consumers in
--   chapters 5+ (do-calculus, counterfactual identification) will
--   quantify `(hG : G.IsCADMG)` at the theorem level, instantiate
--   `G.nodeSplittingHard hG W hW`, and supply `claim_3_9` as the
--   acyclicity witness for the SWIG — no carrier change, no
--   CADMG-structure unfolding, just the standard split-construction
--   pattern.
--
-- * **`Finset.image` for every set-builder, not `Finset.filter` /
--   recursion / a quotient.**  Identical rationale to
--   `def_3_11`-`NodeSplittingOn.lean`: the LN writes the four
--   components as set-builders ranging over `G.E` / `G.L` / `W`;
--   Lean's `Finset.image` is the closest primitive, shares the
--   `Finset (SplitNode Node × SplitNode Node)` carrier between the
--   three image clauses, and decidability of `Finset.image`
--   construction follows from the `DecidableEq` instances on `Node`
--   and `SplitNode Node`.
--
-- * **Items i, ii literal three-piece-union into two-piece-union: a
--   key departure from `def_3_11` at the J/V level.**  In
--   `def_3_11`, the carrier is split into *three* pieces
--   `(V \ W).image .unsplit ∪ W.image .copy0 ∪ W.image .copy1` (both
--   tagged copies live in `V`).  In SWIG, the same carrier is split
--   into *two pieces per side* — `W.image .copy1` joins `J` (item
--   i: `G.J.image .unsplit ∪ W.image .copy1`) and `W.image .copy0`
--   joins `V \ W` (item ii: `(G.V \ W).image .unsplit ∪ W.image
--   .copy0`).  This is the literal SWIG specification: the `^i`
--   copies are reclassified as input nodes, while the `^o` copies
--   remain output nodes.  At the `Disjoint` proof obligation level
--   (`hJV_disj`) this manifests as a four-way constructor-disjointness
--   case split: `J vs (V\W)` (both unsplit, discharged by
--   `G.hJV_disj`), `J vs W^o` (unsplit vs copy0, constructor
--   mismatch), `W^i vs (V\W)` (copy1 vs unsplit, constructor
--   mismatch), `W^i vs W^o` (copy1 vs copy0, constructor mismatch).
--
-- * **Item iii: single-clause `Finset.image`, no transfer edges.**
--   Contrast with `def_3_11`'s item iii, which is a *two-clause
--   union* (lifted edges plus transfer edges `(.copy0 w, .copy1 w)`).
--   In SWIG, item iii is the lifted-edges clause alone:
--   `G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))`.  No
--   `W.image (fun w => (.copy0 w, .copy1 w))` summand.  This is
--   forced by the SWIG construction's "hard-intervene at `W^i`"
--   semantics: the transfer edge `(w^o, w^i)` would have its target
--   in `W^i` — exactly the edges the LN's closing remark "removes",
--   realised here by simply not including them.  Source slot uses
--   `toCopy1` (the LN's `^i`), target slot uses `toCopy0` (the LN's
--   `^o`), matching the LN's item iii verbatim.
--
-- * **Item iv: identical to `def_3_11`'s item iv.**
--   `G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2))`.  Both
--   endpoints carry the `^o` superscript.  This matches `def_3_11`'s
--   one-sided `W^0`-only bidirected convention (per
--   `NodeSplittingOn.lean`'s design block), and is the reason
--   bidirected edges incident to `W^o` *survive* in `L_{swig(W)}`
--   (cf.\ the disambiguation remark on the LN's closing sentence:
--   "out of `W^o`" reads as *directed only*).
--
-- * **Self-loops on `W` produce no cycles in `G_{swig(W)}`.**  Per the
--   rewritten tex's "Self-loops on `W` produce no cycles in
--   `G_{swig(W)}`" paragraph: a directed self-loop `(w, w) ∈ G.E`
--   for `w ∈ W` lifts (via item iii) to `(.copy1 w, .copy0 w)` —
--   *not* a self-loop, since `.copy1 w ≠ .copy0 w` by the tagged-copy
--   construction.  Moreover it does not form a length-2 cycle with
--   any other edge: every edge in `E_{swig(W)}` has its source tagged
--   `.copy1` (or `.unsplit`) and its target tagged `.copy0` (or
--   `.unsplit`), so no edge has `.copy0 w` as a source.  This
--   contrasts with `def_3_11`, where the same self-loop yields a
--   2-cycle via the transfer edge — a key reason SWIG-acyclicity is
--   *cleanly* preservable from `G.IsAcyclic` even when `G` has
--   self-loops, whereas the node-split's acyclicity preservation
--   requires a self-loop-free precondition.  Downstream `claim_3_9`
--   will lean on this.
--
-- * **Argument order
--   `(G : CDMG Node) (hG : G.IsCADMG) (W : Finset Node) (hW : W ⊆ G.V)`.**
--   The `(G) (W) (hW)` backbone matches the convention of every other
--   chapter-3 operator (`def_3_10` `hardInterventionOn`, `def_3_11`
--   `nodeSplittingOn`), enabling dot-notation
--   `G.nodeSplittingHard hG W hW`.  `hG` is inserted *between* `G`
--   and `W` (rather than appended after `hW`) because it is a side
--   condition on `G` itself — the LN's "Let `G` be a CADMG" is the
--   input domain restriction (see bullet (d) above) — and Lean
--   conventions keep the side-condition binder adjacent to the data
--   it constrains.  `W` then precedes `hW` so the remainder of the
--   call site reads left-to-right like the LN's "Let `W ⊆ V` be a
--   subset".  This is the only place the chapter-3 operator argument
--   pattern departs from the bare `(G) (W) (hW)` form, and the
--   departure is forced by the LN's "CADMG" (rather than "CDMG") input
--   quantifier — every chapter-3 operator that takes a CADMG input
--   will carry the same `hG` insertion in the same slot.
--
-- * **`where` syntax with named fields, not anonymous-constructor
--   `⟨ … ⟩`.**  Same rationale as `def_3_10` / `def_3_11`: keeps every
--   field labelled and lets the proof obligations (passed as named
--   private lemmas) sit next to the data they refer to.
--
-- * **Downstream consumers.**  `claim_3_9` (SWIG acyclicity — the
--   immediate next row) is the first consumer; it proves that the
--   SWIG of an acyclic `G` is itself acyclic, upgrading the
--   `CDMG (SplitNode Node)` return type to a CADMG.  Beyond that,
--   the do-calculus and counterfactual chapters (chs.\ 5 / 9 / 10)
--   build joint distributions over `G.nodeSplittingHard hG W hW` for
--   SWIG-based counterfactual identification, and the d-separation
--   chapters (chs.\ 6 / 7) consume SWIG-membership pointwise when
--   reading off identification graph structures.  Each of these
--   rests on the four field assignments above; the tagged-sum carrier
--   `SplitNode Node` (reused from `def_3_11`) is the contract those
--   rows rely on.
-- Both `hG : G.IsCADMG` and `hW : W ⊆ G.V` are bound on the signature
-- for LN-faithfulness ("Let `G` be a CADMG, `W ⊆ V`") but neither is
-- consumed by any of the five CDMG obligations — the type-level
-- distinction of `SplitNode`'s three constructors and `G`'s own
-- CDMG-typing axioms discharge them; `hG`'s acyclicity is only
-- consumed downstream by `claim_3_9` (cf.\ bullet (d) above for the
-- input-side / output-side acyclicity story).  The `set_option` keeps
-- the linter quiet for *both* unused binders without dropping either
-- from the signature (both are part of the LN-faithful encoding and
-- the call-site contract `G.nodeSplittingHard hG W hW`).
set_option linter.unusedVariables false in
-- def_3_12 -- start statement
def nodeSplittingHard (G : CDMG Node) (hG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V) :
    CDMG (SplitNode Node) where
  J := G.J.image SplitNode.unsplit ∪ W.image SplitNode.copy1
  V := (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
  hJV_disj := by exact nodeSplittingHard_hJV_disj G W
  E := G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))
  hE_subset := by exact nodeSplittingHard_hE_subset G W
  L := G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2))
  hL_subset := by exact nodeSplittingHard_hL_subset G W
  hL_irrefl := by exact nodeSplittingHard_hL_irrefl G W
  hL_symm := by exact nodeSplittingHard_hL_symm G W
-- def_3_12 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: nodeSplittingHard

end CDMG

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: nodeSplittingHard (was: refactor_nodeSplittingHard)
namespace refactor_CDMG

-- def_3_12 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_12 --- end helper

-- Private helper: `refactor_toCopy0 W` is injective on `Node`.  Used
-- by `refactor_nodeSplittingHard_hL_irrefl` to lift `G.hL_irrefl` on
-- the `Sym2` carrier through `Sym2.isDiag_map`.  An identical lemma
-- lives in `NodeSplittingOn.lean` as `refactor_toCopy0_inj` but is
-- `private`-scoped to that file, so we re-derive it locally here
-- (mirroring the original `swig_toCopy0_inj` / `toCopy0_inj`
-- pre-refactor split).  Proof by case-analysis on `a ∈ W`, `b ∈ W`:
-- distinct constructors `.copy0` vs `.unsplit` on the cross-cases,
-- constructor injectivity within each matched case.
private lemma refactor_swig_toCopy0_inj {W : Finset Node} {a b : Node}
    (h : refactor_toCopy0 W a = refactor_toCopy0 W b) : a = b := by
  unfold refactor_toCopy0 at h
  by_cases hWa : a ∈ W
  · by_cases hWb : b ∈ W
    · rw [if_pos hWa, if_pos hWb] at h
      injection h
    · rw [if_pos hWa, if_neg hWb] at h
      cases h
  · by_cases hWb : b ∈ W
    · rw [if_neg hWa, if_pos hWb] at h
      cases h
    · rw [if_neg hWa, if_neg hWb] at h
      injection h

-- ## Proof helpers for the four CDMG axioms under SWIG (post-refactor)
--
-- The four private lemmas below discharge the four proof obligations
-- of `def_3_1`'s post-refactor `refactor_CDMG` structure
-- (`hJV_disj`, `hE_subset`, `hL_subset`, `hL_irrefl`) for the SWIG
-- construction.  **One fewer than the pre-refactor five** — the
-- pre-refactor `nodeSplittingHard_hL_symm` obligation is gone because
-- `refactor_CDMG.L : Finset (Sym2 Node)` makes swap-symmetry
-- *definitional* via the `Sym2` quotient: `s(v_1, v_2) = s(v_2, v_1)`
-- by construction, so the LN's compound
-- "`(v_1, v_2) \in L ⟹ (v_2, v_1) \in L`" axiom disappears from
-- `refactor_CDMG` entirely.  This is the central refactor delta
-- visible at the obligation-count level; the structural rationale
-- (Mathlib's `Sym2 α` is literally `(α × α) / ((a,b) ∼ (b,a))`, which
-- is exactly the encoding the LN's compound L-axiom would otherwise
-- have to mimic) lives in the `refactor_CDMG` design block
-- (`Section3_1/CDMG.lean`) and the refactor plan
-- (`leanification/refactors/refactor_cdmg_typed_edges.md`).
--
-- *Why factor four `private lemma`s rather than inline anonymous
-- proofs into the structure literal?*  Three reasons, identical to
-- the pre-refactor pattern:
--   (i) The `def` body becomes pure data + lemma references — the
--       website builder renders the def's signature and a reader sees
--       the four field assignments at a glance, without proof clutter
--       interrupting the LN-paradigm i.–iv. correspondence.
--  (ii) Each LN-clause obligation is isolated: a single broken
--       obligation produces a focused error message at the named
--       helper rather than a cascade at the structure-literal site.
--       Useful both during the initial port and when downstream
--       changes (Mathlib version bumps, etc.) trigger re-elaboration.
-- (iii) Should a downstream lemma ever need to cite the
--       per-obligation invariant (e.g. an `nodeSplittingHard.L`
--       membership characterisation closing on `hL_subset`'s shape),
--       a named top-level lemma is available for that citation,
--       avoiding a re-derivation inside the consumer.
-- None of the four obligations consume `hW` or `hG`; both are carried
-- on the def's signature purely for LN-faithfulness ("Let `G` be a
-- CADMG, `W ⊆ V`").
--
-- *The four helpers fall into two natural groups* — useful framing
-- for a reader scanning the diff to see where the refactor's
-- substance lands:
--   - **Group A: J/V/E ports (`hJV_disj`, `hE_subset`).**
--     L-independent; mechanical ports of the pre-refactor
--     `nodeSplittingHard_h{JV_disj,E_subset}`.  The refactor leaves
--     `def_3_1.J`, `.V`, `.E`, `.hJV_disj`, `.hE_subset` untouched, so
--     only names and types change (`refactor_` prefix; `refactor_CDMG`
--     / `refactor_SplitNode` in place of `CDMG` / `SplitNode`).  The
--     proof scripts are line-for-line identical to the pre-refactor
--     versions.
--   - **Group B: L-side ports (`hL_subset`, `hL_irrefl`).**
--     Substantive shape change.  The L-field carrier moves from
--     `Finset (Node × Node)` (pre-refactor) to `Finset (Sym2 Node)`
--     (post-refactor), so the two obligations get *new shapes*:
--       * `hL_subset` is now universally quantified via `Sym2.Mem`
--         (`∀ ⦃s⦄, s ∈ L → ∀ ⦃v⦄, v ∈ s → v ∈ V`), not the
--         pre-refactor `e.1 ∈ V ∧ e.2 ∈ V` on ordered pairs;
--       * `hL_irrefl` discharges via `¬ s.IsDiag` (Mathlib's
--         canonical self-pair predicate on `Sym2 _`), not the
--         pre-refactor `v_1 ≠ v_2` on ordered pairs.
--     Both proofs reduce to one-line lifts via Mathlib's
--     `Sym2.mem_map` / `Sym2.isDiag_map` over the underlying
--     `G.hL_subset` / `G.hL_irrefl` of the source CDMG — a much
--     terser argument than the pre-refactor `congrArg Prod.fst/snd`
--     + manual destructure route.  See each helper's preamble below
--     for the per-helper specifics.
private lemma refactor_nodeSplittingHard_hJV_disj
    (G : refactor_CDMG Node) (W : Finset Node) :
    Disjoint (G.J.image refactor_SplitNode.unsplit
                ∪ W.image refactor_SplitNode.copy1)
        ((G.V \ W).image refactor_SplitNode.unsplit
                ∪ W.image refactor_SplitNode.copy0) := by
  rw [Finset.disjoint_left]
  rintro x hxJ hxV
  rcases Finset.mem_union.mp hxJ with hJ | hC1
  · obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hJ
    rcases Finset.mem_union.mp hxV with hVu | hC0
    · obtain ⟨v, hvVW, hveq⟩ := Finset.mem_image.mp hVu
      cases hveq
      exact Finset.disjoint_left.mp G.hJV_disj hjJ
        (Finset.mem_sdiff.mp hvVW).1
    · obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hC0
      cases hweq
  · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hC1
    rcases Finset.mem_union.mp hxV with hVu | hC0
    · obtain ⟨_, _, hveq⟩ := Finset.mem_image.mp hVu
      cases hveq
    · obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hC0
      cases hweq

private lemma refactor_nodeSplittingHard_hE_subset
    (G : refactor_CDMG Node) (W : Finset Node) :
    ∀ ⦃e : refactor_SplitNode Node × refactor_SplitNode Node⦄,
      e ∈ G.E.image (fun e =>
            (refactor_toCopy1 W e.1, refactor_toCopy0 W e.2)) →
      e.1 ∈ (G.J.image refactor_SplitNode.unsplit
              ∪ W.image refactor_SplitNode.copy1) ∪
              ((G.V \ W).image refactor_SplitNode.unsplit
                ∪ W.image refactor_SplitNode.copy0) ∧
        e.2 ∈ (G.V \ W).image refactor_SplitNode.unsplit
                ∪ W.image refactor_SplitNode.copy0 := by
  intro e he
  obtain ⟨e', he'E, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨he'1, he'2⟩ := G.hE_subset he'E
  refine ⟨?_, ?_⟩
  · by_cases hW1 : e'.1 ∈ W
    · simp only [refactor_toCopy1, hW1, if_true]
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨e'.1, hW1, rfl⟩
    · simp only [refactor_toCopy1, hW1, if_false]
      rcases Finset.mem_union.mp he'1 with hJ | hV
      · refine Finset.mem_union_left _ ?_
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨e'.1, hJ, rfl⟩
      · refine Finset.mem_union_right _ ?_
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr
          ⟨e'.1, Finset.mem_sdiff.mpr ⟨hV, hW1⟩, rfl⟩
  · by_cases hW2 : e'.2 ∈ W
    · simp only [refactor_toCopy0, hW2, if_true]
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨e'.2, hW2, rfl⟩
    · simp only [refactor_toCopy0, hW2, if_false]
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr
        ⟨e'.2, Finset.mem_sdiff.mpr ⟨he'2, hW2⟩, rfl⟩

-- `hL_subset` is the load-bearing post-refactor signature change at
-- this row: it is now universally quantified via `Sym2.Mem`
-- (`∀ ⦃s⦄, s ∈ L → ∀ ⦃v⦄, v ∈ s → v ∈ V`) on the
-- `Sym2 (refactor_SplitNode Node)` carrier, NOT the pre-refactor
-- `e.1 ∈ V ∧ e.2 ∈ V` on ordered pairs.  Strategy mirrors
-- `refactor_nodeSplittingOn_hL_subset` verbatim (same `Sym2`-typed
-- `L` image): `Finset.mem_image` extracts the underlying
-- `s₀ : Sym2 Node` with `s₀ ∈ G.L` and
-- `Sym2.map (refactor_toCopy0 W) s₀ = s`; `Sym2.mem_map` extracts the
-- preimage endpoint `w ∈ s₀` with `refactor_toCopy0 W w = v`;
-- `G.hL_subset hs₀L hwS` gives `w ∈ G.V`; then case-split on
-- `w ∈ W` to land in `W.image .copy0` or `(G.V \ W).image .unsplit`.
-- The SWIG-side `V'` is a two-piece union (no `.copy1` summand,
-- contrast with `def_3_11`'s three-piece) so each branch needs only a
-- single level of `mem_union_left` / `mem_union_right`.
private lemma refactor_nodeSplittingHard_hL_subset
    (G : refactor_CDMG Node) (W : Finset Node) :
    ∀ ⦃s : Sym2 (refactor_SplitNode Node)⦄,
      s ∈ G.L.image (Sym2.map (refactor_toCopy0 W)) →
      ∀ ⦃v : refactor_SplitNode Node⦄, v ∈ s →
        v ∈ (G.V \ W).image refactor_SplitNode.unsplit
              ∪ W.image refactor_SplitNode.copy0 := by
  intro s hs v hv
  obtain ⟨s₀, hs₀L, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨w, hwS, rfl⟩ := Sym2.mem_map.mp hv
  have hwV : w ∈ G.V := G.hL_subset hs₀L hwS
  by_cases hwW : w ∈ W
  · simp only [refactor_toCopy0, hwW, if_true]
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_image.mpr ⟨w, hwW, rfl⟩
  · simp only [refactor_toCopy0, hwW, if_false]
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr
      ⟨w, Finset.mem_sdiff.mpr ⟨hwV, hwW⟩, rfl⟩

-- `hL_irrefl` likewise undergoes a load-bearing post-refactor shape
-- change: it is now `¬ s.IsDiag` (Mathlib's canonical `Sym2 _`
-- self-pair predicate, `s.IsDiag ↔ ∃ v, s = s(v,v)`), NOT the
-- pre-refactor `v₁ ≠ v₂` on ordered pairs.  The shape is *forced* by
-- the upstream refactor: `refactor_CDMG.hL_irrefl` is itself phrased
-- as `∀ ⦃s : Sym2 Node⦄, s ∈ L → ¬ s.IsDiag` (see the upstream design
-- block in `Section3_1/CDMG.lean`, bullet "`hL_irrefl` is phrased as
-- `¬ s.IsDiag`…"), so this helper *must* return `¬ s.IsDiag` to be
-- assignable to the SWIG's `hL_irrefl` field — there is no choice
-- here, only an alignment with the upstream contract.
--
-- The discharge mechanism is the central post-refactor simplification:
-- `Sym2.isDiag_map : Function.Injective f → (Sym2.map f s).IsDiag ↔
-- s.IsDiag` reduces the obligation in one rewrite.  The injectivity
-- premise is supplied by `refactor_swig_toCopy0_inj` (the local
-- helper above); the source-side `s₀.IsDiag` then contradicts
-- `G.hL_irrefl`'s `¬ s₀.IsDiag` for `s₀ ∈ G.L`.
--
-- Pre-refactor (ordered-pair `L`) this helper had to (i) extract `v₁`,
-- `v₂` from the image via two `congrArg Prod.fst/snd` rewrites,
-- (ii) lift the assumed `v₁ = v₂` back to `toCopy0 W e'.1 = toCopy0 W
-- e'.2`, (iii) invoke a manual `toCopy0`-injectivity destructure, and
-- (iv) close on `G.hL_irrefl`'s `≠`-conclusion.  Post-refactor the
-- entire pipeline collapses to one `Sym2.isDiag_map` invocation —
-- exactly the `refactor_nodeSplittingOn_hL_irrefl` idiom (sibling
-- REPLACEMENT block, `NodeSplittingOn.lean`).
private lemma refactor_nodeSplittingHard_hL_irrefl
    (G : refactor_CDMG Node) (W : Finset Node) :
    ∀ ⦃s : Sym2 (refactor_SplitNode Node)⦄,
      s ∈ G.L.image (Sym2.map (refactor_toCopy0 W)) →
      ¬ s.IsDiag := by
  intro s hs hDiag
  obtain ⟨s₀, hs₀L, rfl⟩ := Finset.mem_image.mp hs
  have hs₀Diag : s₀.IsDiag :=
    (Sym2.isDiag_map (fun _ _ => refactor_swig_toCopy0_inj)).mp hDiag
  exact G.hL_irrefl hs₀L hs₀Diag

-- ref: def_3_12 (post-refactor port for `cdmg_typed_edges`)
--
-- The *single-world intervention graph (SWIG)* of `G` with respect to
-- `W`, also called the *node-splitting hard intervention* on `G`,
-- ported against the refactored `def_3_1`-`refactor_CDMG` with
-- `L : Finset (Sym2 Node)`.  The four components are
--
--   * `J' := G.J.image .unsplit ∪ W.image .copy1`    — input nodes
--     are the original `G.J` (lifted via `unsplit`) together with the
--     LN's `W^i` copies (the `.copy1`-tagged elements of `W`),
--     which are *reclassified as input nodes* by the SWIG
--     construction;
--   * `V' := (G.V \ W).image .unsplit ∪ W.image .copy0` — output
--     nodes are the unsplit residual `G.V \ W` (lifted via
--     `unsplit`) together with the LN's `W^o` copies (the
--     `.copy0`-tagged elements of `W`);
--   * `E' := G.E.image (fun e => (refactor_toCopy1 W e.1,
--             refactor_toCopy0 W e.2))` — every directed edge
--     `v_1 → v_2 ∈ G.E` of `G` is reattached as
--     `(v_1^i, v_2^o) ∈ E'`.  No transfer edges (contrast with
--     `def_3_11`'s node-splitting);
--   * `L' := G.L.image (Sym2.map (refactor_toCopy0 W))` — every
--     bidirected (unordered) edge `s(v_1, v_2) ∈ G.L` is lifted
--     pointwise on both endpoints via `refactor_toCopy0 W`, so both
--     endpoints carry the `^o` superscript.  No element of `W^i`
--     ever appears in `L'`.
--
-- The hypotheses `hG : G.refactor_IsCADMG` and `hW : W ⊆ G.V` are the
-- LN's "Let $G$ be a CADMG" and "$W \subseteq V$" preconditions
-- respectively.
/-
LN tex (rewritten `def_3_12_NodeSplittingHard`, items i–iv):

    Let $G = (J, V, E, L)$ be a CADMG (in particular a CDMG) and
    $W \subseteq V$ a subset of output nodes.  The SWIG w.r.t.\ $W$
    of $G$ is the CDMG $G_{swig(W)} := (J_{swig(W)}, V_{swig(W)},
                                          E_{swig(W)}, L_{swig(W)})$,
    where (using tagged copies $W^o := \{w^o \mid w \in W\}$,
    $W^i := \{w^i \mid w \in W\}$ realised at the type level, and the
    convention $v^o := v^i := v$ for $v \in J \cup (V \setminus W)$ as
    notational shorthand inside the set-builders below):
      i.   $J_{swig(W)} := J \dcup W^i$;
      ii.  $V_{swig(W)} := (V \setminus W) \dcup W^o$;
      iii. $E_{swig(W)} := \{ (v_1^i, v_2^o) \mid (v_1, v_2) \in E \}$;
      iv.  $L_{swig(W)} := \{ s(v_1^o, v_2^o) \mid s(v_1, v_2) \in L \}$.
-/
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- * **Shape: `def` returning `refactor_CDMG (refactor_SplitNode Node)`,
--   not `class`, not a fresh `inductive`, not a `structure` wrapping
--   the result.**  The SWIG is *data computed from `(G, hG, W, hW)`*
--   — a concrete CDMG over an enlarged carrier — so the natural Lean
--   rendering is a `def` that constructs the four `refactor_CDMG`
--   fields directly.  Three alternatives were considered and rejected:
--     - **`class`:** wrong because we never want Lean to "infer the
--       SWIG of `G` at `W`".  SWIG is a parameterised operation, not a
--       property to be resolved by typeclass search; using `class`
--       would also force a singleton instance per `(G, W)` pair, which
--       is type-theoretically awkward (instances should not depend on
--       value-level data of a finer type than the indexed type).
--     - **fresh `inductive SwigGraph`:** would commit to a new
--       structural type encoding only the four SWIG fields, requiring
--       a coercion `SwigGraph → refactor_CDMG (refactor_SplitNode
--       Node)` at every consumer.  Downstream chs.\ 4 / 5 / 6 / 7 / 9
--       / 10 destructure SWIGs via the four `refactor_CDMG` fields
--       (`.J`, `.V`, `.E`, `.L`); making the consumer go through a
--       coercion at every destructure is gratuitous indirection.  The
--       direct `refactor_CDMG`-valued `def` makes those destructures
--       free.
--     - **`structure NodeSplittingHard … where output : refactor_CDMG
--       …`** (i.e. wrap the resulting CDMG inside a record):  same
--       coercion-tax problem as above, plus it obfuscates that the
--       SWIG *is* a CDMG of the same kind as `G` (over an enlarged
--       carrier) — losing the LN-paradigm `G ↦ G_{swig(W)}` reading
--       where both source and target inhabit the same conceptual
--       category "(refactor_)CDMGs".
--   The chosen `def` shape is uniform with every other chapter-3
--   operator (`refactor_hardInterventionOn`, `refactor_nodeSplittingOn`,
--   `refactor_marginalizeOut`), all of which return a `refactor_CDMG`
--   directly.  This keeps the chapter's API homogeneous: every CDMG
--   operator is a `refactor_CDMG → ⋯ → refactor_CDMG` mapping at the
--   type level.
--
-- * **Carrier of the result is `refactor_SplitNode Node`, not `Node`
--   itself with an injected tag nor `Sum Node Node`.**  The LN's
--   `v^o ≠ v^i` for `v ∈ W` combined with `v^o = v^i = v` for
--   `v ∉ W` (the "Tagged copies of $W$" + "Notational shorthand for
--   non-$W$ nodes" paragraphs of the rewritten tex) is *precisely*
--   the universal property of `refactor_SplitNode` (the tagged-sum
--   carrier introduced by `def_3_11`'s REPLACEMENT block in
--   `NodeSplittingOn.lean`).  Three alternatives rejected:
--     - **Inlining into `Node` itself with a string tag, e.g.
--       `Node ⊕ (Node × Bool)`:** would force consumers to track the
--       tag by hand at every destructure, and would not yield the
--       LN's `v^o = v^i = v` shorthand for `v ∉ W` (the shorthand
--       would have to be defined ad-hoc).
--     - **`Sum Node Node` (just two copies):** doesn't admit the
--       three-way distinction `unsplit` / `copy0` / `copy1`; would
--       force `v ∉ W` to be encoded as a "left-copy-of-self"
--       convention that loses the LN's `v^o = v^i = v` literal
--       reading.
--     - **A fresh `inductive SwigNode (W : Finset Node)` parameterised
--       by `W`:** rejected for the same reasons enumerated in (a)
--       below — it would force a coercion `SwigNode → SplitNode` at
--       every place the LN's "node-split, then hard-intervene at
--       `W^i`" reading composes the two operators.  Reusing
--       `refactor_SplitNode` makes that composition state a literal
--       carrier-level equation.
--
-- * **Post-refactor port — `L : Finset (Sym2 (refactor_SplitNode
--   Node))`.**  The only field whose Lean *shape* changes versus the
--   pre-refactor encoding is `L_{swig(W)}`.  Pre-refactor:
--     `L := G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2))`
--   over `Finset (Node × Node)`, requiring a separate `hL_symm` proof
--   obligation that explicitly swapped the underlying pair and
--   re-routed it through `G.hL_symm`.  Post-refactor:
--     `L := G.L.image (Sym2.map (refactor_toCopy0 W))`
--   over `Finset (Sym2 (refactor_SplitNode Node))`.  Under the `Sym2`
--   typing the obligation reduces by *three* structural
--   simplifications, identical to `refactor_nodeSplittingOn`:
--
--   - **No two-endpoints destructure.**  `Sym2.map` lifts the
--     unordered-pair structure pointwise.  Membership reasoning at
--     L-manipulation sites uses `Sym2.mem_map`
--     (`v ∈ Sym2.map f s ↔ ∃ w ∈ s, f w = v`).
--
--   - **No `hL_symm` obligation.**  Under `Sym2`,
--     `s(v_1, v_2) = s(v_2, v_1)` is definitional, so the entire
--     pre-refactor `nodeSplittingHard_hL_symm` proof obligation
--     disappears — no L-side fifth field on `refactor_CDMG`.  The
--     refactor's central design commitment lands at this row exactly
--     as it does at `def_3_11` (sibling REPLACEMENT block in
--     `NodeSplittingOn.lean`).
--
--   - **`hL_irrefl` discharges via `¬ s.IsDiag`, not `v_1 ≠ v_2`.**
--     The upstream `refactor_CDMG.hL_irrefl` is itself phrased as
--     `∀ ⦃s : Sym2 Node⦄, s ∈ L → ¬ s.IsDiag` (see the upstream
--     design block in `Section3_1/CDMG.lean`, bullet "`hL_irrefl`
--     is phrased as `¬ s.IsDiag`…"), so the SWIG's `hL_irrefl` field
--     *must* match that shape — there is no choice here, only an
--     alignment with the upstream contract.  The discharge in the
--     `refactor_nodeSplittingHard_hL_irrefl` private helper is
--     one-line via Mathlib's
--     `Sym2.isDiag_map : Function.Injective f →
--     (Sym2.map f s).IsDiag ↔ s.IsDiag` lifted through
--     `refactor_swig_toCopy0_inj` and combined with `G.hL_irrefl`'s
--     `¬ s₀.IsDiag` for the source edge `s₀ ∈ G.L`.  Pre-refactor,
--     this same obligation needed four pipeline steps (`congrArg
--     Prod.fst`, `congrArg Prod.snd`, `toCopy0`-injectivity
--     destructure, close on `G.hL_irrefl`'s `≠`-conclusion) — a
--     substantive simplification, not just a name change.
--
--   - **The `^o`-only-on-`L` convention is preserved structurally.**
--     `Sym2.map (refactor_toCopy0 W)` of an edge `s(w_1, w_2) ∈ G.L`
--     with `w_1, w_2 ∈ W` lands on `s(.copy0 w_1, .copy0 w_2)` —
--     never on `.copy1 w_1` or `.copy1 w_2`.  Identical to
--     `refactor_nodeSplittingOn`'s item iv lift, same idiom on a
--     different upstream operator (one without the transfer-edge
--     clause).
--
-- * **(a) Reuse of `refactor_SplitNode` / `refactor_toCopy0` /
--   `refactor_toCopy1` from `NodeSplittingOn.lean`.**  The
--   post-refactor sibling row (`refactor_nodeSplittingOn`) introduces
--   the tagged-sum carrier `refactor_SplitNode Node` (three named
--   constructors `unsplit`, `copy0`, `copy1`) and the two
--   notational-shorthand functions `refactor_toCopy0 W` and
--   `refactor_toCopy1 W`, all namespace-`refactor_CDMG`-public.  We
--   reuse them verbatim, with the SWIG-side reading
--   `refactor_toCopy0 ↔ ^o` and `refactor_toCopy1 ↔ ^i`.  Identical
--   rationale to the pre-refactor encoding (cf. the ORIGINAL block
--   above): SWIG and node-split graphs live on the *same* carrier
--   type, so claims relating them state literal carrier-level
--   equations rather than threading a coercion through.  The
--   pre-refactor wording-check subtlety
--   `implicit_disjointness_of_copies_from_original_nodes` is
--   resolved identically — by typing.
--
-- * **(b) Direct construction, NOT a composition of
--   `refactor_nodeSplittingOn` and `refactor_hardInterventionOn`.**
--   Same rationale as pre-refactor: the LN's literal item-by-item
--   statement places the four set-builders directly; mirroring them
--   directly in Lean preserves the LN paradigm at the
--   statement-marker-wrapped level.  Definitional unfolding for
--   downstream proofs is cleaner with the direct form (one
--   `Finset.mem_image` per field, not a two-stage chain), and no
--   intermediate transfer-edges-immediately-removed appear in
--   unfolding traces.  The composed form may surface later as a
--   lemma proving the equivalence; we do not bake it into the def.
--
-- * **(c) The closing-remark phrasing "removing all edges into
--   `W^i` / out of `W^o`" is realised *structurally*.**  Same
--   rationale as pre-refactor; under the `Sym2`-typed `L`, the
--   "no edges into `W^i`" gloss extends naturally to bidirected
--   edges too (since `Sym2.map (refactor_toCopy0 W)` only ever
--   produces `Sym2` elements with both endpoints `^o`-tagged or
--   unsplit — never `.copy1`).  Resolves wording-check subtlety
--   `closing_remark_uses_removal_language_for_a_constructive_definition`
--   identically.
--
-- * **(d) Acyclicity is faithful to the LN on *both* sides of the
--   def — `(hG : G.refactor_IsCADMG)` on the input signature, and
--   acyclicity-preservation on the output deferred to a separate
--   downstream lemma (the def returns `refactor_CDMG`, not a CADMG).**
--   The LN's "Let $G$ be a CADMG" is the input domain restriction;
--   chapter 3 has *no `CADMG` structure type* — `refactor_IsCADMG`
--   is the post-refactor predicate
--   `refactor_IsCADMG (G : refactor_CDMG Node) : Prop :=
--   G.refactor_IsAcyclic` defined in
--   `Section3_1/CDMGTypes.lean`'s REPLACEMENT block (line 475).
--   The body genuinely does not consume `hG`: the four field
--   assignments and the four CDMG-typing proof obligations
--   (`hJV_disj`, `hE_subset`, `hL_subset`, `hL_irrefl`) are all
--   acyclicity-free.  The `set_option linter.unusedVariables false in`
--   absorbs the deliberately-unused `hG` binder.  Acyclicity
--   *preservation* — that `G_{swig(W)}` is itself a CADMG — is
--   deferred to a separately stated downstream lemma (the
--   post-refactor analogue of `claim_3_9`, ported alongside this
--   row); the def itself returns `refactor_CDMG (refactor_SplitNode
--   Node)`, mirroring the established chapter pattern (cf.
--   `refactor_hardInterventionOn` and `refactor_nodeSplittingOn`).
--
-- * **`Finset.image` for every set-builder.**  Identical rationale to
--   `refactor_nodeSplittingOn`: the LN writes the four components as
--   set-builders ranging over `G.E` / `G.L` / `W`; Lean's
--   `Finset.image` is the closest primitive.  Decidability follows
--   from the `DecidableEq` instances on `Node` and
--   `refactor_SplitNode Node` (and Mathlib's derived
--   `DecidableEq (Sym2 _)` for the `L`-side).
--
-- * **Items i, ii literal three-piece-union into two-piece-union per
--   side: a key departure from `def_3_11` at the J/V level.**  In
--   `refactor_nodeSplittingOn`, the carrier is split into *three*
--   pieces `(V \ W).image .unsplit ∪ W.image .copy0 ∪ W.image .copy1`
--   on the V-side (both tagged copies live in `V`).  In SWIG, the
--   same carrier is split into *two pieces per side* —
--   `W.image .copy1` joins `J` (item i) and `W.image .copy0` joins
--   `V \ W` (item ii).  This is the literal SWIG specification: the
--   `^i` copies are reclassified as input nodes.  At the `hJV_disj`
--   level this manifests as a four-way constructor-disjointness
--   case split: `J vs (V\W)` (both unsplit, discharged by
--   `G.hJV_disj`), `J vs W^o` (constructor mismatch), `W^i vs (V\W)`
--   (constructor mismatch), `W^i vs W^o` (constructor mismatch).
--
-- * **Item iii: single-clause `Finset.image`, no transfer edges.**
--   Contrast with `def_3_11`'s item iii, which is a *two-clause
--   union* (lifted edges plus transfer edges `(.copy0 w, .copy1 w)`).
--   In SWIG, item iii is the lifted-edges clause alone:
--   `G.E.image (fun e => (refactor_toCopy1 W e.1,
--                          refactor_toCopy0 W e.2))`.  No transfer
--   summand.  This is forced by the SWIG construction's
--   "hard-intervene at `W^i`" semantics: the transfer edge
--   `(w^o, w^i)` would have its target in `W^i` — exactly the edges
--   the LN's closing remark "removes", realised here by simply not
--   including them.
--
-- * **Item iv: identical lift idiom to `def_3_11`'s item iv post-
--   refactor.**  `G.L.image (Sym2.map (refactor_toCopy0 W))`.  Both
--   endpoints carry the `^o` superscript via the single
--   `Sym2.map (refactor_toCopy0 W)` lift; no pointwise
--   pair-destructure.  Bidirected edges incident to `W^o` survive in
--   `L_{swig(W)}` (cf. the disambiguation remark on the LN's closing
--   sentence: "out of `W^o`" reads as *directed only*).  Same lift
--   idiom as the sibling `refactor_nodeSplittingOn` (line 1594 of
--   `NodeSplittingOn.lean`) — same operator, same Sym2.map shape.
--
--   *Why `refactor_toCopy0`, not `refactor_toCopy1`, on the L-field
--   lift?*  LN item iv reads `v_1^o ↔ v_2^o` — both endpoints get the
--   *output* tag (`.copy0`), never the input tag (`.copy1`).  The
--   asymmetry mirrors the SWIG's role: the input-side copies `W^i`
--   are *terminal* nodes from the directed-edge perspective (no edge
--   exits `W^i`, since by item iii every directed edge has source
--   tagged `.copy1` / `.unsplit` and target tagged `.copy0` /
--   `.unsplit`, but `W^i` consists of `.copy1`-tagged elements which
--   no `.copy1`-tagged target edge can reach), and a fortiori carry
--   no bidirected edges either.  Inverting the lift to
--   `Sym2.map (refactor_toCopy1 W)` would silently relocate every
--   bidirected edge between `W`-vertices into `W^i`, breaking the
--   SWIG's intended semantics: bidirected confounding between
--   intervened nodes would be re-attributed to the input-side
--   (post-intervention) copies rather than the output-side
--   (observational) copies.  Downstream `claim_3_22` (σ-separation
--   symmetry, post-refactor analogue) and the do-calculus / SWIG
--   factorisation lemmas (ch. 5) depend on the LN's literal item iv
--   reading; the `refactor_toCopy0` choice here is not a free
--   parameter.
--
--   *Why a single `Sym2.map`, not `Sym2.lift`-of-`Sym2.mk` plus a
--   case split?*  `Sym2.map : (α → β) → Sym2 α → Sym2 β` is exactly
--   the pointwise lift that preserves the swap quotient
--   (`Sym2.map f s(a,b) = s(f a, f b)`), so item iv's set-builder
--   "`s(v_1^o, v_2^o) | s(v_1, v_2) ∈ L`" is *literally*
--   `Finset.image (Sym2.map (refactor_toCopy0 W)) G.L`.  Using
--   `Sym2.lift` would force picking a representative pair and then
--   re-quotienting — extra boilerplate with no expressive gain,
--   since `Sym2.map` already encapsulates the well-defined-by-symm
--   pattern.
--
-- * **Self-loops on `W` produce no cycles in `G_{swig(W)}`.**  Per the
--   rewritten tex: a directed self-loop `(w, w) ∈ G.E` for `w ∈ W`
--   lifts (via item iii) to `(.copy1 w, .copy0 w)` — *not* a
--   self-loop, since `.copy1 w ≠ .copy0 w` by the tagged-copy
--   construction.  Moreover it does not form a length-2 cycle:
--   every edge in `E_{swig(W)}` has source tagged `.copy1` /
--   `.unsplit` and target tagged `.copy0` / `.unsplit`, so no edge
--   has `.copy0 w` as a source.  This contrasts with
--   `refactor_nodeSplittingOn`, where the same self-loop yields a
--   2-cycle via the transfer edge.  Downstream (post-refactor
--   `claim_3_9` analogue) will lean on this.
--
-- * **Argument order `(G : refactor_CDMG Node) (hG : G.refactor_IsCADMG)
--   (W : Finset Node) (hW : W ⊆ G.V)`.**  Same backbone as the
--   pre-refactor encoding.  `hG` sits between `G` and `W` because it
--   is a side condition on `G` itself.  Mirrors
--   `refactor_nodeSplittingOn`'s `(G, W, hW)` argument order with the
--   addition of the LN-CADMG hypothesis.
--
-- * **`where` syntax with named fields, not anonymous-constructor
--   `⟨ … ⟩`.**  The `refactor_CDMG` `structure` has eight fields —
--   one fewer than the pre-refactor nine, because `hL_symm` is gone
--   (swap-symmetry definitional on `Sym2`).  `where … J := … V := …`
--   keeps every field labelled and lets the proof obligations sit
--   next to the data they refer to.  Mirrors
--   `refactor_nodeSplittingOn`'s choice verbatim.
--
-- * **Downstream consumers.**  The post-refactor `claim_3_9`
--   analogue (SWIG acyclicity) is the immediate next consumer.  Then
--   the do-calculus / counterfactual chapters (chs. 5 / 9 / 10) and
--   the σ/d-separation chapters (chs. 6 / 7) inspect SWIG membership
--   pointwise.  Post-refactor, the L-side consumers see the
--   `Sym2`-native image — no manual `(toCopy0, toCopy0)` ordered-pair
--   construction is needed; the membership rule on
--   `(G.refactor_nodeSplittingHard hG W hW).L` reduces to a single
--   `Finset.mem_image.mp` + `Sym2.mem_map.mp` chain.
-- Both `hG : G.refactor_IsCADMG` and `hW : W ⊆ G.V` are bound on the
-- signature for LN-faithfulness ("Let `G` be a CADMG, `W ⊆ V`") but
-- neither is consumed by any of the four CDMG obligations — the
-- type-level distinction of `refactor_SplitNode`'s three constructors
-- and `G`'s own axioms discharge them.  The `set_option` keeps the
-- linter quiet for both unused binders without dropping either from
-- the signature.
set_option linter.unusedVariables false in
-- def_3_12 -- start statement
def refactor_nodeSplittingHard (G : refactor_CDMG Node)
    (hG : G.refactor_IsCADMG) (W : Finset Node) (hW : W ⊆ G.V) :
    refactor_CDMG (refactor_SplitNode Node)
-- def_3_12 -- end statement
    where
  J := G.J.image refactor_SplitNode.unsplit ∪ W.image refactor_SplitNode.copy1
  V := (G.V \ W).image refactor_SplitNode.unsplit ∪ W.image refactor_SplitNode.copy0
  hJV_disj := by exact refactor_nodeSplittingHard_hJV_disj G W
  E := G.E.image (fun e => (refactor_toCopy1 W e.1, refactor_toCopy0 W e.2))
  hE_subset := by exact refactor_nodeSplittingHard_hE_subset G W
  L := G.L.image (Sym2.map (refactor_toCopy0 W))
  hL_subset := by exact refactor_nodeSplittingHard_hL_subset G W
  hL_irrefl := by exact refactor_nodeSplittingHard_hL_irrefl G W

end refactor_CDMG
-- REFACTOR-BLOCK-REPLACEMENT-END: nodeSplittingHard

end Causality
