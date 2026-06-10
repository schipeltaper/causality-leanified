import Chapter3_GraphTheory.Section3_1.CDMG

namespace Causality

/-!
# Node-splitting on CDMGs (`def_3_11`)

This file formalises the LN definition `def_3_11`
(`\label{def:G_node-splitting}` in `graphs.tex`) — the *node-splitting*
operation `G ↦ G_{\spl(W)}` on a CDMG.  Given a CDMG
`G = (J, V, E, L)` and a subset `W ⊆ V` of output nodes, the
node-split graph has

* `J_{\spl(W)} := J` (input nodes unchanged);
* `V_{\spl(W)} := (V ∖ W) ⊍ W^0 ⊍ W^1` (each `w ∈ W` replaced by
  two tagged copies `w^0`, `w^1`);
* `E_{\spl(W)} := { (v_1^1, v_2^0) | (v_1, v_2) ∈ E } ∪
                   { (w^0, w^1) | w ∈ W }`
  (every directed edge of `G` is lifted to point from the `^1`-copy
  of its source to the `^0`-copy of its target, plus a *transfer
  edge* `w^0 → w^1` for every `w ∈ W`);
* `L_{\spl(W)} := { (v_1^0, v_2^0) | (v_1, v_2) ∈ L }` (every
  bidirected edge of `G` is lifted with **both** endpoints carrying
  the `^0` superscript — no element of `W^1` appears as the endpoint
  of any bidirected edge).

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/def_3_11_NodeSplittingOn.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:G_node-splitting}`) augmented with the operator
clarification
`[disjointness_of_new_copies_only_partially_stipulated]`:
the disjointness assertions
`W^0 ∩ V = W^1 ∩ V = W^0 ∩ J = W^1 ∩ J = W^0 ∩ W^1 = ∅`
are realised **at the type level** — `W^0` and `W^1` are constructed
as *tagged copies* (here via an `inductive` `SplitNode Node` with
distinct constructors), so disjointness is a *typing* fact rather
than a side condition.

The substantive design rationale — the choice of an `inductive`
`SplitNode` over a `Sum`-based encoding, the encoding of the
`v^0 := v^1 := v` notational shorthand as helper functions
`toCopy0` / `toCopy1`, the literal `Finset.image`-based set-builders
for `E_{\spl(W)}` and `L_{\spl(W)}`, and how each CDMG axiom of
`def_3_1` is discharged on the tagged-sum carrier — lives in the
`--` comment block immediately above the `def` declaration.  Read
that block before changing a field; it is the load-bearing contract
for downstream chapter-3 rows that compose node-splitting with hard
intervention (`def_3_12` SWIG) or that reason about topological
orders on the split graph (`claim_3_6` SplitTopologicalOrder).
-/

namespace CDMG

-- def_3_11 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_11 --- end helper

-- ## Helper: the tagged-sum node universe of the split graph
--
-- *`inductive` with three named constructors, not `Sum Node (Node ×
--   Bool)`.*  The LN's "two tagged copies `W^0`, `W^1` plus the
--   unsplit nodes" reads as three distinguishable kinds of element;
--   the named constructors `unsplit`, `copy0`, `copy1` mirror the LN
--   symbols `v`, `w^0`, `w^1` one-for-one and let downstream pattern
--   matches read `| .unsplit v => …` / `| .copy0 w => …` /
--   `| .copy1 w => …` instead of nested `Sum.inl` / `Sum.inr`
--   destructuring.  A `Sum Node (Node × Bool)` encoding
--   (`Sum.inl v` for unsplit, `Sum.inr (w, false)` for `w^0`,
--   `Sum.inr (w, true)` for `w^1`) was the workspace's expected
--   fallback; we picked the named-constructor form because it is
--   identical in expressive power, shorter at every use site, and
--   matches the LN notation without a translation table.
--
-- *`deriving DecidableEq`.*  `def_3_1`'s `CDMG` carrier requires
--   `[DecidableEq Node]`; the split graph lives over `SplitNode Node`,
--   so we need `[DecidableEq (SplitNode Node)]` to satisfy
--   `CDMG (SplitNode Node)`.  The `deriving` handler generates the
--   instance `[DecidableEq Node] → DecidableEq (SplitNode Node)` for
--   free; the alternative (a hand-written `DecidableEq` instance) is
--   pure boilerplate.
--
-- *No membership predicates on `W` or proofs `hv : v ∉ W` /
--   `hw : w ∈ W` baked into the constructors.*  A richer
--   `inductive SplitNode (Node : Type*) (W : Set Node)` carrying
--   per-constructor membership proofs would force every consumer to
--   manipulate those proofs through every pattern match (and would
--   make `DecidableEq` non-trivial because the proof argument has
--   `Prop` type with `Eq` undecidable in general).  Disjointness of
--   the three constructors is structural; whether a `copy0 w` is
--   "valid" (i.e.\ `w ∈ W`) is then enforced by the *`Finset`* level
--   of `J_{\spl(W)}` / `V_{\spl(W)}` membership rather than by the
--   *type* itself.  This matches the LN reading: `W^0` is a `Finset`
--   inside the carrier `SplitNode Node`, not a separate type.
-- def_3_11 --- start helper
inductive SplitNode (Node : Type*) where
  | unsplit (v : Node) : SplitNode Node
  | copy0 (w : Node) : SplitNode Node
  | copy1 (w : Node) : SplitNode Node
  deriving DecidableEq
-- def_3_11 --- end helper

-- ## Helper: the `v^0` notational shorthand
--
-- *Function `Node → SplitNode Node`, parameterised by `W : Finset
--   Node`.*  The LN convention is `v^0 := v` if `v ∈ J ∪ (V ∖ W)`
--   and `v^0 := (the tagged copy of v in W^0)` if `v ∈ W`.  In Lean
--   this is a single function: branch on `v ∈ W` (decidable from
--   `[DecidableEq Node]` on `Finset Node`), return the tagged
--   constructor on the `W`-branch and the unsplit injection on the
--   complement.  Encoding this as a *function* (rather than as two
--   separate cases inside every set-builder) directly mirrors the
--   LN's "notational shorthand" framing and keeps the
--   `E_{\spl(W)}` / `L_{\spl(W)}` definitions terse and uniform.
--
-- *Total on all of `Node`, not partial.*  The function is defined on
--   *every* `v : Node`, including `v ∈ G.J` and `v ∈ G.V ∖ W`.  At
--   those `v`-values the function returns `.unsplit v`, exactly the
--   LN's "`v^0 := v`" convention — extended literally to the entire
--   ambient `Node` type so the function has a single uniform
--   signature.  Restricting to a subtype (`{v : Node // v ∈ G ∨
--   v ∈ W}`) was rejected as gratuitous typing noise: every
--   set-builder in `E_{\spl(W)}` / `L_{\spl(W)}` ranges over pairs
--   coming from `G.E` / `G.L`, whose endpoints already satisfy the
--   subtype condition by `def_3_1`'s typing axioms.
-- def_3_11 --- start helper
def toCopy0 (W : Finset Node) (v : Node) : SplitNode Node :=
  if v ∈ W then SplitNode.copy0 v else SplitNode.unsplit v
-- def_3_11 --- end helper

-- ## Helper: the `v^1` notational shorthand
--
-- Same shape as `toCopy0` above, returning `SplitNode.copy1 v` on
-- the `W`-branch instead of `SplitNode.copy0 v`.  See the design
-- block above `toCopy0` for the rationale; the two helpers differ
-- only in which tagged copy they pick on the `W`-branch.
-- def_3_11 --- start helper
def toCopy1 (W : Finset Node) (v : Node) : SplitNode Node :=
  if v ∈ W then SplitNode.copy1 v else SplitNode.unsplit v
-- def_3_11 --- end helper

-- Private helper: `toCopy0 W` is injective on `Node`.  Used by
-- `nodeSplittingOn`'s `hL_irrefl` to lift `G.hL_irrefl`'s
-- `v_1 ≠ v_2` on `Node` up to `toCopy0 W v_1 ≠ toCopy0 W v_2` on
-- `SplitNode Node`.  Proof by case-analysis on `a ∈ W`, `b ∈ W`:
-- distinct constructors `.copy0` vs `.unsplit` on the cross-cases,
-- constructor injectivity within each matched case.  Extracted as a
-- top-level lemma so the `injection` / `cases` tactics inside its
-- body operate on the *free* variables `a`, `b`, sidestepping the
-- "dependent elimination failed" error that arises when `cases` is
-- applied to an equality whose two sides are projections of a single
-- term (`e'.1`, `e'.2`).
private lemma toCopy0_inj {W : Finset Node} {a b : Node}
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

-- ## Proof helpers for the five CDMG axioms under node splitting
--
-- The five private lemmas below discharge the five proof obligations
-- of `def_3_1`'s `CDMG` structure (`hJV_disj`, `hE_subset`,
-- `hL_subset`, `hL_irrefl`, `hL_symm`) for the node-splitting
-- construction.  They are factored out of the structure-literal body
-- of `nodeSplittingOn` so the def body is pure data + lemma
-- references — the website builder renders the def's signature, and
-- a reader sees the data assignments without proof clutter.  None of
-- the obligations consume `hW`; `hW` is carried on the def's
-- signature purely for LN-faithfulness (the LN's "Let `W ⊆ V`").

private lemma nodeSplittingOn_hJV_disj (G : CDMG Node) (W : Finset Node) :
    Disjoint (G.J.image SplitNode.unsplit)
        ((G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
          ∪ W.image SplitNode.copy1) := by
  rw [Finset.disjoint_left]
  rintro x hxJ hxV
  obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hxJ
  rcases Finset.mem_union.mp hxV with hxV12 | hxC1
  · rcases Finset.mem_union.mp hxV12 with hxVuns | hxC0
    · -- `x = .unsplit j` is in `(G.V \ W).image .unsplit`: the
      -- preimage `v` agrees with `j` by constructor injectivity, so
      -- `j ∈ G.V \ W ⊆ G.V`, contradicting `j ∈ G.J`.
      obtain ⟨v, hvVW, hveq⟩ := Finset.mem_image.mp hxVuns
      cases hveq
      exact Finset.disjoint_left.mp G.hJV_disj hjJ
        (Finset.mem_sdiff.mp hvVW).1
    · -- `x = .unsplit j` is in `W.image .copy0`: constructor mismatch.
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hxC0
      cases hweq
  · -- `x = .unsplit j` is in `W.image .copy1`: same constructor mismatch.
    obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hxC1
    cases hweq

private lemma nodeSplittingOn_hE_subset (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃e : SplitNode Node × SplitNode Node⦄,
      e ∈ G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))
          ∪ W.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w)) →
      e.1 ∈ G.J.image SplitNode.unsplit ∪
              ((G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
                ∪ W.image SplitNode.copy1) ∧
        e.2 ∈ (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
                ∪ W.image SplitNode.copy1 := by
  intro e he
  rcases Finset.mem_union.mp he with hImg | hTrans
  · -- Lifted edge.
    obtain ⟨e', he'E, rfl⟩ := Finset.mem_image.mp hImg
    obtain ⟨he'1, he'2⟩ := G.hE_subset he'E
    refine ⟨?_, ?_⟩
    · by_cases hW1 : e'.1 ∈ W
      · simp only [toCopy1, hW1, if_true]
        refine Finset.mem_union_right _ ?_
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨e'.1, hW1, rfl⟩
      · simp only [toCopy1, hW1, if_false]
        rcases Finset.mem_union.mp he'1 with hJ | hV
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e'.1, hJ, rfl⟩)
        · refine Finset.mem_union_right _ ?_
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_union_left _ ?_
          exact Finset.mem_image.mpr
            ⟨e'.1, Finset.mem_sdiff.mpr ⟨hV, hW1⟩, rfl⟩
    · by_cases hW2 : e'.2 ∈ W
      · simp only [toCopy0, hW2, if_true]
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨e'.2, hW2, rfl⟩
      · simp only [toCopy0, hW2, if_false]
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr
          ⟨e'.2, Finset.mem_sdiff.mpr ⟨he'2, hW2⟩, rfl⟩
  · -- Transfer edge.
    obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hTrans
    refine ⟨?_, ?_⟩
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨w, hwW, rfl⟩
    · refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨w, hwW, rfl⟩

private lemma nodeSplittingOn_hL_subset (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃e : SplitNode Node × SplitNode Node⦄,
      e ∈ G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2)) →
      e.1 ∈ (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
              ∪ W.image SplitNode.copy1 ∧
        e.2 ∈ (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
                ∪ W.image SplitNode.copy1 := by
  intro e he
  obtain ⟨e', he'L, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨he'1, he'2⟩ := G.hL_subset he'L
  refine ⟨?_, ?_⟩
  · by_cases hW1 : e'.1 ∈ W
    · simp only [toCopy0, hW1, if_true]
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨e'.1, hW1, rfl⟩
    · simp only [toCopy0, hW1, if_false]
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr
        ⟨e'.1, Finset.mem_sdiff.mpr ⟨he'1, hW1⟩, rfl⟩
  · by_cases hW2 : e'.2 ∈ W
    · simp only [toCopy0, hW2, if_true]
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨e'.2, hW2, rfl⟩
    · simp only [toCopy0, hW2, if_false]
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr
        ⟨e'.2, Finset.mem_sdiff.mpr ⟨he'2, hW2⟩, rfl⟩

private lemma nodeSplittingOn_hL_irrefl (G : CDMG Node) (W : Finset Node) :
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
  exact toCopy0_inj hSplitEq

private lemma nodeSplittingOn_hL_symm (G : CDMG Node) (W : Finset Node) :
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

-- ref: def_3_11
--
-- The *node-splitting on `G` with respect to `W`* is the CDMG
-- `G.nodeSplittingOn W hW` over the carrier `SplitNode Node` whose
-- four components are
--
--   * `J' := G.J.image .unsplit`                       — input nodes
--     unchanged, lifted into `SplitNode Node` via the `unsplit`
--     constructor;
--   * `V' := (G.V \ W).image .unsplit ∪
--             W.image .copy0 ∪ W.image .copy1`         — output
--     nodes partition into the unsplit part `V \ W` (still injected
--     via `unsplit`) and the two tagged copies `W^0`, `W^1`;
--   * `E' := G.E.image (fun e => (toCopy1 W e.1,
--             toCopy0 W e.2)) ∪
--             W.image (fun w => (.copy0 w, .copy1 w))` — every
--     directed edge `v_1 → v_2 ∈ G.E` is lifted with `v_1^1` on the
--     source and `v_2^0` on the target; the transfer edges
--     `w^0 → w^1` for `w ∈ W` are added in a separate clause;
--   * `L' := G.L.image (fun e => (toCopy0 W e.1,
--             toCopy0 W e.2))`                          — every
--     bidirected edge `v_1 ↔ v_2 ∈ G.L` is lifted with *both*
--     endpoints carrying the `^0` superscript.  No element of `W^1`
--     ever appears in `L'`.
--
-- The hypothesis `hW : W ⊆ G.V` is the LN's "$W \subseteq V$"
-- precondition.
/-
LN tex (rewritten `def_3_11_NodeSplittingOn`, items i–iv):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq V$ a subset of
    output nodes.  The node-split graph w.r.t. $W$ is the CDMG
    $G_{\spl(W)} := (J_{\spl(W)}, V_{\spl(W)}, E_{\spl(W)},
                      L_{\spl(W)})$,
    where (using the tagged copies $W^0 := \{w^0 \mid w \in W\}$,
    $W^1 := \{w^1 \mid w \in W\}$ realised at the type level, and the
    convention $v^0 := v^1 := v$ for $v \in J \cup (V \setminus W)$
    as notational shorthand inside the set-builders below):
      i.   $J_{\spl(W)} := J$;
      ii.  $V_{\spl(W)} := (V \setminus W) \dcup W^0 \dcup W^1$;
      iii. $E_{\spl(W)} := \{ (v_1^1, v_2^0) \mid (v_1, v_2) \in E \}
                         \cup \{ (w^0, w^1) \mid w \in W \}$;
      iv.  $L_{\spl(W)} := \{ (v_1^0, v_2^0) \mid (v_1, v_2) \in L \}$.

LN block (verbatim, for backup):

    Let $G=(J,V,E,L)$ be a CDMG and $W \subseteq V$ a subset of the
    output nodes.  The node-split graph w.r.t. $W$ of $G$ is the
    CDMG $G_{\spl(W)} := (J_{\spl(W)}, V_{\spl(W)}, E_{\spl(W)},
    L_{\spl(W)})$, constructed as follows.  We first make two
    disjoint copies of the nodes in $W$: $W^0 := \{w^0 \mid w \in W\}$,
    $W^1 := \{w^1 \mid w \in W\}$.  Note that we consider
    $w^0 \neq w^1$ for $w \in W$.  Additionally (for convenience), for
    $v \in J \cup V \setminus W$ we put $v^0 := v^1 := v$.  We then
    define:
      i.   $J_{\spl(W)} := J$,
      ii.  $V_{\spl(W)} := (V \setminus W) \dcup W^0 \dcup W^1$,
      iii. $E_{\spl(W)} := \{ v_1^1 \to v_2^0 \mid v_1 \to v_2 \in E \}
                         \cup \{ w^0 \to w^1 \mid w \in W \}$,
      iv.  $L_{\spl(W)} := \{ v_1^0 \leftrightarrow v_2^0
                              \mid v_1 \leftrightarrow v_2 \in L \}$.
-/
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- * **`def`, not `structure` / `inductive` / `class`.**  Node
--   splitting is a *function* `CDMG Node → Finset Node → … →
--   CDMG (SplitNode Node)`, not new data and not a typeclass-
--   resolvable property.  The CDMG already has its `structure`
--   (`def_3_1`); this row produces a new CDMG over the tagged-sum
--   carrier `SplitNode Node` from an existing one.  Wrapping the
--   result in a fresh structure (e.g. a `NodeSplittingOn` record
--   carrying the split graph as a field) was rejected because every
--   downstream consumer (SWIG `def_3_12`, `claim_3_6`
--   SplitTopologicalOrder, `claim_3_12` HardInterventionNodeSplit)
--   destructures the split graph the same way any other CDMG is
--   destructured — via `(G.nodeSplittingOn W hW).J`, `…V`, `…E`,
--   `…L` — and an extra wrapping layer would force a re-destructuring
--   step at every such call site.  Mirrors the sibling `def_3_10`
--   (`HardInterventionOn`).
--
-- * **Carrier of the result is `SplitNode Node`, NOT `Node`.**  This
--   is the load-bearing departure from `def_3_10`: hard intervention
--   keeps the same node universe (`Finset Node` operations on
--   `J ∪ W` / `V \ W`), whereas node splitting *creates new nodes*
--   (`w^0`, `w^1`) that must be type-level distinct from the
--   original `Node` and from each other.  The
--   `addition_to_the_LN`
--   `[disjointness_of_new_copies_only_partially_stipulated]` fixes
--   the semantics: disjointness is at the *type level*, encoded via
--   an `inductive` `SplitNode` with three named constructors so the
--   LN's `W^0 ∩ V = W^1 ∩ V = W^0 ∩ J = W^1 ∩ J = W^0 ∩ W^1 = ∅`
--   becomes a typing fact, not a `Disjoint` proof obligation.
--   Downstream consumers see the carrier change in the return type
--   `CDMG (SplitNode Node)` and pattern-match on `.unsplit` /
--   `.copy0` / `.copy1` as needed (or, when the unsplit-only branch
--   suffices, project through the `unsplit` constructor).
--
-- * **`hW : W ⊆ G.V` is an explicit argument, not a sub-condition
--   threaded through the body.**  The LN's "Let $W \subseteq V$" is
--   part of the *signature* of node splitting.  In contrast with
--   `def_3_10`'s `W ⊆ G.J ∪ G.V` (which permits `W ∩ G.J ≠ ∅`),
--   node splitting requires `W ⊆ G.V` strictly: the construction
--   *removes* members of `W` from `V` and creates tagged copies, so
--   it only makes sense on output nodes.  `hW` is part of the
--   signature but is not consumed in every proof obligation (the
--   type-level disjointness of the three `SplitNode` constructors
--   already discharges most of the work); the few obligations that
--   do consume it are the `hJV_disj` and `hE_subset` / `hL_subset`
--   set-membership cases that route the unsplit `G.V \ W` branch
--   through the `unsplit` constructor.
--
-- * **`Finset.image` for every set-builder, not `Finset.filter` /
--   recursion / a quotient.**  The LN writes the four components as
--   set-builders ranging over `G.E` / `G.L` / `W`.  Lean's
--   `Finset.image` is the closest primitive (`Finset.mem_image` gives
--   exactly `b ∈ s.image f ↔ ∃ a ∈ s, f a = b`), shares the
--   `Finset (SplitNode Node × SplitNode Node)` carrier between the
--   three image clauses, and decidability of `Finset.image`
--   construction follows from the `DecidableEq` instances on `Node`
--   and `SplitNode Node`.  `Finset.filter` was rejected because the
--   construction *creates* new elements via `toCopy0` / `toCopy1`,
--   not selects a subset of existing ones; recursion is overkill
--   for a single set-comprehension; a quotient encoding was rejected
--   at the `def_3_1` design stage and we inherit the ordered-pair
--   choice here.
--
-- * **Notational shorthand `v^0 := v^1 := v` as helper *functions*
--   `toCopy0` / `toCopy1`, not as a coercion.**  The LN's
--   "$v^0 := v^1 := v$ for $v \in J \cup (V \setminus W)$" is
--   *meta-notation* used inside the set-builders for items iii and
--   iv; it is NOT a coercion that re-assigns the meaning of `v` in
--   the ambient carrier (per the operator clarification, "untagged
--   nodes $v \in J \cup (V \sm W)$ remain of their original kind in
--   the ambient carrier").  The Lean rendering as a function
--   `toCopy0 W : Node → SplitNode Node` (branching on `v ∈ W` to
--   pick either `SplitNode.copy0 v` or `SplitNode.unsplit v`)
--   captures exactly this reading: the *original* `v : Node`
--   continues to inhabit `Node`, and the function is just the
--   per-set-builder lift into `SplitNode Node`.  A `Coe Node
--   (SplitNode Node)` instance was rejected because (i) `Node` is
--   polymorphic and a global coercion would fire across the
--   chapter, and (ii) there are *two* such lifts (`toCopy0` and
--   `toCopy1`) differing only on `W` — neither is canonical.
--
-- * **Items i, ii: literal `Finset.image` translations.**  Item i
--   (`J' := G.J.image .unsplit`) injects every input node through
--   the `unsplit` constructor; item ii's three-piece union
--   `(G.V \ W).image .unsplit ∪ W.image .copy0 ∪ W.image .copy1`
--   spells out the LN's `(V \ W) \dcup W^0 \dcup W^1` literally,
--   with the LN's three pieces in left-to-right order.
--
-- * **Item iii: two-clause union, lifted edges plus transfer edges.**
--   The first clause `G.E.image (fun e => (toCopy1 W e.1,
--   toCopy0 W e.2))` lifts every directed edge `v_1 → v_2 ∈ G.E` to
--   the LN's `(v_1^1, v_2^0)`.  The second clause
--   `W.image (fun w => (.copy0 w, .copy1 w))` adds the *transfer
--   edges* `w^0 → w^1` for every `w ∈ W`.  These two clauses are
--   semantically disjoint (the transfer edges have `.copy0` on the
--   source side, which the first clause's `toCopy1` cannot produce
--   on `v_1 ∈ G.J ∪ G.V`); the union is taken literally for
--   LN-faithfulness, not because the disjointness is content-bearing.
--
-- * **Item iv: single-clause `Finset.image`, both endpoints via
--   `toCopy0`.**  The LN's *asymmetric* choice of `^0` on both
--   endpoints of every lifted bidirected edge (per the wording-check
--   subtlety `spl_L_attached_to_W0_only_silently`) is the load-
--   bearing convention.  No bidirected edge in `L_{\spl(W)}` has
--   `.copy1 w` as an endpoint.  Downstream rows that reason about
--   the bidirected/latent structure (c-components, m-separation,
--   confounding ancestry) build on this one-sided convention, and
--   swapping `^0` for `^1` would change the chapter's semantics.
--   The semantic motivation is the SWIG-style reading composed
--   downstream in `def_3_12` (NodeSplittingHard): each `w^0`-copy
--   represents the *natural* / observational side of `w` (its
--   pre-intervention identity, on which latent confounding and
--   ancestry are inherited from `G`), while each `w^1`-copy
--   represents the *intervened* / `do`-side, which is causally
--   isolated from its observational counterpart.  Bidirected edges
--   encode latent confounding, which by SWIG semantics lives
--   entirely on the natural (`W^0`) side; the intervened
--   `W^1`-copies have no latent structure by design.  This is what
--   makes the one-sided lift the unique LN-faithful reading and not
--   a typo — `review_design` PASS surfaced exactly this point.
--
-- * **Self-loops `(v, v) ∈ E` for `v ∈ W` produce 2-cycles
--   `v^0 → v^1 → v^0` in `E_{\spl(W)}`; the result is still a CDMG.**
--   Per the wording-check subtlety
--   `spl_self_loop_creates_two_cycle_in_split` and the rewritten
--   tex's "Self-loops on $W$ produce $2$-cycles" paragraph: the
--   first clause of item iii produces the lifted edge `(v^1, v^0)`
--   and the second clause adds the transfer edge `(v^0, v^1)`,
--   yielding a directed 2-cycle.  This does NOT invalidate the
--   CDMG axioms (`def_3_1` does not require acyclicity); it only
--   means downstream claims about node-splitting preserving
--   acyclicity (cf. `claim_3_6` SplitTopologicalOrder) must add a
--   self-loop-free precondition on `G`.
--
-- * **Type-level disjointness collapses the `hJV_disj` /
--   `hE_subset` / `hL_subset` proof obligations.**  Because
--   `SplitNode.unsplit`, `SplitNode.copy0`, `SplitNode.copy1` are
--   distinct constructors of an `inductive` type, any
--   `Disjoint`-style obligation between two of the three `Finset`
--   images reduces to a per-element `Finset.mem_image` check and a
--   constructor-mismatch `cases` or `SplitNode.noConfusion`.  The
--   only non-trivial case in `hJV_disj` is the `J vs (V \ W)`
--   branch where both Finsets route through `unsplit`; there the
--   injectivity of `unsplit` reduces the obligation to
--   `G.hJV_disj`.
--
-- * **`hL_irrefl` and `hL_symm` transport pointwise from `G`.**
--   For irreflexivity: if `(toCopy0 W v_1, toCopy0 W v_2)` is the
--   lift of `(v_1, v_2) ∈ G.L`, then `v_1 ≠ v_2` by `G.hL_irrefl`,
--   and `toCopy0 W` is injective on `Node` (a per-`W` case-split
--   verification: distinct constructors for `v ∈ W` vs `v ∉ W`,
--   and constructor injectivity within each branch), so
--   `toCopy0 W v_1 ≠ toCopy0 W v_2`.  For symmetry: `G.L`'s
--   `hL_symm` swaps the underlying pair, and the image under
--   `toCopy0` commutes with the swap.
--
-- * **Argument order `(G : CDMG Node) (W : Finset Node) (hW : …)`.**
--   Matches the convention of every chapter-3 predicate
--   (`G.tuh`, `G.huh`, `G.adjacent`, `G.hardInterventionOn`),
--   enabling dot-notation `G.nodeSplittingOn W hW`.  `W` precedes
--   `hW` so the call site reads left-to-right like the LN's "Let
--   `W ⊆ V` be a subset".
--
-- * **`where` syntax with named fields, not anonymous-constructor
--   `⟨ … ⟩`.**  The `CDMG` `structure` has nine fields; an
--   anonymous-constructor form would interleave data and proof
--   obligations in a positional list, making the correspondence
--   with `def_3_1`'s `structure` opaque.  `where … J := … V := …`
--   keeps every field labelled and lets the proof obligations sit
--   next to the data they refer to.
--
-- * **Downstream consumers.**  SWIG `def_3_12` (the composition of
--   node splitting with hard intervention on the `W^1`-copies),
--   `claim_3_6` SplitTopologicalOrder (a topological order on the
--   acyclic, self-loop-free `G` induces one on `G_{\spl(W)}`),
--   `claim_3_12` HardInterventionNodeSplit (the interaction between
--   node splitting and disjoint hard intervention).  Each of these
--   rests on the four field assignments above; the tagged-sum
--   carrier `SplitNode Node` is the contract those rows rely on.
--
-- * **Property-checked on representative instances.**  The
--   construction has been validated by the `verify_with_examples`
--   worker on five concrete CDMG instances (PASS).  Two of these
--   are direct stress tests of the working-phase wording-check
--   subtleties surfaced for this row: (a) a self-loop input
--   `(w, w) ∈ G.E` for `w ∈ W` correctly yields the 2-cycle
--   `w^0 → w^1 → w^0` in `E_{\spl(W)}` via the combined first /
--   second clause of item iii (the wording-check
--   `spl_self_loop_creates_two_cycle_in_split`); (b) a bidirected
--   input `(w_1, w_2) ∈ G.L` for `w_1, w_2 ∈ W` correctly yields
--   only the `W^0`-side incidence
--   `(.copy0 w_1, .copy0 w_2) ∈ L_{\spl(W)}` with no `.copy1 w`
--   endpoint anywhere in `L_{\spl(W)}` (the wording-check
--   `spl_L_attached_to_W0_only_silently`).  The four field
--   assignments above are the contract those examples validate;
--   any future structural change to this `def` should be re-run
--   against the same instances.
-- `hW` is bound on the signature for LN-faithfulness ("Let
-- `W ⊆ V`") but is not consumed by any of the five obligations — the
-- type-level distinction of `SplitNode`'s three constructors and
-- `G`'s own axioms discharge them.  The `set_option` keeps the
-- linter quiet without dropping the binder from the signature
-- (which is part of the LN-faithful encoding and the call-site
-- contract `G.nodeSplittingOn W hW`).
set_option linter.unusedVariables false in
-- def_3_11 -- start statement
def nodeSplittingOn (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) :
    CDMG (SplitNode Node) where
  J := G.J.image SplitNode.unsplit
  V := (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
        ∪ W.image SplitNode.copy1
  hJV_disj := nodeSplittingOn_hJV_disj G W
  E := G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))
        ∪ W.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
  hE_subset := by exact nodeSplittingOn_hE_subset G W
  L := G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2))
  hL_subset := by exact nodeSplittingOn_hL_subset G W
  hL_irrefl := by exact nodeSplittingOn_hL_irrefl G W
  hL_symm := by exact nodeSplittingOn_hL_symm G W
-- def_3_11 -- end statement

end CDMG

end Causality
