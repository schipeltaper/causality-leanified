import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_2.ExtendingCDMGsWithInterventionNodes

-- TeX proof: tex/claim_3_13_proof_AcyclicityUnderIntervention.tex

/-!
# Acyclicity and topological orders survive extension with intervention nodes (claim_3_13)

This file formalises the lecture notes' remark immediately following
the definition of the extension `G_{\doit(I_W)}` (def_3_13): if `G`
is acyclic, then so is `G.extendingCDMGWithInterventionNodes W hW`;
furthermore, a topological order of the extended graph restricts to
one of `G` (via the `Sum.inl` embedding), and any topological order
of `G` extends to one of the extended graph (e.g. by placing all the
fresh `I_w` nodes first). See
`lecture-notes/lecture_notes/graphs.tex` Rem at lines 821 -- 829.

The LN bundles *three* distinct mathematical statements under one
`\Rem` block; we split them into three theorems plus one named
construction. Each theorem carries different hypotheses and different
downstream consumers; the named construction `extensionOrder` packages
the LN's "put all `I_w` first" recipe so that downstream chapters can
quote it by name (mirroring `splitOrder` from claim_3_6 in
`SplitTopologicalOrder.lean`):

* `isAcyclic_extendingCDMGWithInterventionNodes` -- acyclicity
  preservation. A directed cycle in the extended graph cannot use any
  fresh `I_w → w` edge: the only edges with target `Sum.inr ⟨w, _⟩`
  would be needed to close a cycle through that fresh node, but
  `mem_extendingCDMGWithInterventionNodes_E` shows every edge of the
  extended graph has target `Sum.inl _`. So a hypothetical cycle uses
  only `Sum.inl`-lifted edges of `G.E` and lifts back to a cycle in
  `G`, contradicting `h : G.IsAcyclic`.

* `extensionOrder` -- the LN's "put all `I_w` first" recipe, encoded
  as a four-case pattern match on the Sum carrier `α ⊕ ↑S`. The
  parameter `S : Set α` is the index set of fresh `Sum.inr` nodes
  (`W \ G.J` at the use site of claim_3_13, but the definition
  composes with arbitrary subtypes). Cross-case `(Sum.inr, Sum.inl)`
  is `True` and `(Sum.inl, Sum.inr)` is `False`, encoding "every
  `I_w` precedes every original node"; same-side cases inherit the
  underlying relation `r` on `α`.

* `isTopologicalOrder_extendingCDMGWithInterventionNodes_extend` --
  the **constructive extension** direction of the LN remark: from a
  topological order `r` of `G`, produce `extensionOrder (S := W \ G.J)
  r` as a topological order of the extended graph. This is the LN's
  "putting all the `I_w` nodes first" recipe; binder choices follow
  `isTopologicalOrder_nodeSplittingOn` (claim_3_6).

* `isTopologicalOrder_extendingCDMGWithInterventionNodes_restrict` --
  the **restriction** direction: a topological order of the extended
  graph, restricted along the `Sum.inl` embedding, is a topological
  order of `G`. The LN's "a topological order for `G_{\doit(I_W)}` is
  also one for `G`". Inverse-direction companion to the extension
  theorem; field-by-field transport using `extendingCDMGWithInterventionNodes_J`
  / `_V` (membership of `Sum.inl v` in the extended graph iff
  `v ∈ G`) and `mem_extendingCDMGWithInterventionNodes_E` first
  disjunct (`Sum.inl`-lifted edges are edges of the extended graph).

## Where this gets used downstream

* **claim_3_14** (`graphs.tex` Lem at 832, "adding intervention nodes
  commutes with disjoint hard interventions") -- iterating
  `extendingCDMGWithInterventionNodes` and composing it with
  `hardInterventionOn` is acyclicity-preserving by this row, allowing
  the commutation lemma's CADMG side conditions to be discharged.
* **claim_3_15** (`graphs.tex`, "adding intervention nodes commutes
  with disjoint node-splitting hard intervention") -- analogous: the
  composite remains acyclic, and the named `extensionOrder` plugs
  into the SWIG topological-order construction.
* **Chapters 4 -- 6 (CBNs, do-calculus, ID algorithm)** -- the
  ID-algorithm and the soundness of do-calculus rules manipulate
  CDMGs by composing hard interventions with intervention-node
  extensions; the extended graph inherits acyclicity from `G` by this
  row, and the named `extensionOrder` is the canonical topological
  order downstream proofs pattern-match against.
* **Chapters 8 -- 10 (iSCMs, SWIGs, counterfactuals)** -- iSCM
  intervention semantics evaluate mechanisms along a topological
  order of the underlying CDMG; when the iSCM's graph is extended
  with intervention nodes (chapter 9), the topological order along
  which the recursion proceeds is exactly `extensionOrder r` for the
  base order `r` of the un-extended graph.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

/-! ### Edge-target / walk-lifting helpers for Part A

These private helpers encode the acyclicity argument's two ingredients:
(i) every edge of the extended graph has target `Sum.inl _` (the
key source--target asymmetry of def_3_13: only fresh edges have
`Sum.inr` *sources*, never `Sum.inr` *targets*); (ii) for walks that
both *start* and *end* at `Sum.inl _`, every intermediate vertex is
also `Sum.inl _` (because intermediates are targets of edges), so
every step is a piece-1 `Sum.inl × Sum.inl`-lift of a `G.E`-edge and
the walk projects step-by-step to a `Walk G` of the same length. -/

/-- Helper for Part A: every directed edge of
`G.extendingCDMGWithInterventionNodes W hW` has target `Sum.inl _`.
This is the source--target asymmetry of def_3_13: fresh edges
contribute `Sum.inr` *sources* but the target is always
`Sum.inl w`, and piece-1 edges are double-`Sum.inl`-lifted from
`G.E`. -/
private lemma extendingCDMGWithInterventionNodes_target_isInl
    {G : CDMG α} {W : Set α} {hW : W ⊆ G.J ∪ G.V}
    {a b : α ⊕ ↑(W \ G.J)}
    (h : (a, b) ∈ (G.extendingCDMGWithInterventionNodes W hW).E) :
    ∃ x : α, b = Sum.inl x := by
  rw [mem_extendingCDMGWithInterventionNodes_E] at h
  rcases h with ⟨_, v₂, _, h_eq⟩ | ⟨w', h_eq⟩
  · rw [Prod.mk.injEq] at h_eq; exact ⟨v₂, h_eq.2⟩
  · rw [Prod.mk.injEq] at h_eq; exact ⟨(w' : α), h_eq.2⟩

/-- Helper for Part A: a directed walk in
`G.extendingCDMGWithInterventionNodes W hW` of positive length ends at
a `Sum.inl _` vertex. By induction: a single-step walk ends at the
target of its only step, which is `Sum.inl _` by
`extendingCDMGWithInterventionNodes_target_isInl`; a longer walk's
end is the end of its tail (which is also a positive-length directed
walk). -/
private lemma walkEnd_isInl
    {G : CDMG α} {W : Set α} {hW : W ⊆ G.J ∪ G.V} :
    ∀ {a b : α ⊕ ↑(W \ G.J)}
      (π : Walk (G.extendingCDMGWithInterventionNodes W hW) a b),
      π.IsDirected → 1 ≤ π.length → ∃ x : α, b = Sum.inl x := by
  intro a b π
  induction π with
  | nil _ => intros _ h; simp at h
  | @cons _ _ _ s p ih =>
    intros h_dir _
    cases s with
    | forward he =>
      cases p with
      | nil _ => exact extendingCDMGWithInterventionNodes_target_isInl he
      | cons s' p' =>
        have h_dir_p : (Walk.cons s' p').IsDirected := h_dir
        exact ih h_dir_p (by simp)
    | backward _ => simp at h_dir
    | bidir _ => simp at h_dir

/-- Helper for Part A: a directed walk in
`G.extendingCDMGWithInterventionNodes W hW` from `Sum.inl v` to
`Sum.inl w` lifts to a directed walk in `G` from `v` to `w` of the
same length. Every step is piece-1 (the `Sum.inl × Sum.inl`-lift of
some `(v', w') ∈ G.E`), because piece-2 fresh edges have `Sum.inr`
source and the walk's first vertex is `Sum.inl v`; the recursive call
maintains the `Sum.inl`-only invariant because intermediate vertices
are targets of edges (hence `Sum.inl` by
`extendingCDMGWithInterventionNodes_target_isInl`). -/
private lemma walkLiftExtendingCDMGWithInterventionNodes
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.J ∪ G.V) :
    ∀ {a b : α ⊕ ↑(W \ G.J)}
      (π : Walk (G.extendingCDMGWithInterventionNodes W hW) a b),
      π.IsDirected →
      ∀ (v w : α), a = Sum.inl v → b = Sum.inl w →
      ∃ ρ : Walk G v w, ρ.IsDirected ∧ ρ.length = π.length := by
  intro a b π
  induction π with
  | nil x =>
    intros _ v w hav hbw
    subst hav
    have hvw : v = w := Sum.inl_injective hbw
    subst hvw
    exact ⟨Walk.nil v, by simp, rfl⟩
  | @cons _ m _ s p ih =>
    intros h_dir v w hav hbw
    subst hav
    cases s with
    | forward he =>
      have he_ext : (Sum.inl v, m) ∈
          (G.extendingCDMGWithInterventionNodes W hW).E := he
      rw [mem_extendingCDMGWithInterventionNodes_E] at he_ext
      rcases he_ext with ⟨v₁, v₂, hE, h_eq⟩ | ⟨w', h_eq⟩
      · -- piece 1: original edge, both endpoints `Sum.inl`.
        rw [Prod.mk.injEq] at h_eq
        obtain ⟨ha_eq, hm_eq⟩ := h_eq
        have hv_eq : v = v₁ := Sum.inl_injective ha_eq
        subst hv_eq
        subst hm_eq
        have h_dir_p : p.IsDirected := h_dir
        obtain ⟨ρ_p, h_ρ_p_dir, h_ρ_p_len⟩ := ih h_dir_p v₂ w rfl hbw
        refine ⟨Walk.cons (.forward hE) ρ_p, ?_, ?_⟩
        · simp only [Walk.isDirected_cons_forward]; exact h_ρ_p_dir
        · simp [h_ρ_p_len]
      · -- piece 2: source `Sum.inl v` would have to equal `Sum.inr w'`, impossible.
        rw [Prod.mk.injEq] at h_eq
        exact nomatch h_eq.1
    | backward _ => simp at h_dir
    | bidir _ => simp at h_dir

-- claim_3_13 (part A)
-- title: AcyclicityUnderIntervention -- acyclicity preserved
--
-- If `G` is acyclic, then so is `G.extendingCDMGWithInterventionNodes
-- W hW`. The mathematical content: a directed cycle in the extended
-- graph would have to close on itself, but the only edges incident
-- to a fresh node `Sum.inr ⟨w, _⟩` are the fresh `I_w → w` edges
-- (`mem_extendingCDMGWithInterventionNodes_E` second disjunct), and
-- those have `Sum.inr ⟨w, _⟩` as *source*, never as *target*. So a
-- cycle through a fresh node is impossible: there is no way to
-- "return" to a `Sum.inr` source. Equivalently, every edge of the
-- extended graph has target `Sum.inl _`, so any directed walk lives
-- entirely in `Sum.inl`-lifted edges from step 2 onwards, and (by
-- the same first-step reasoning at the cycle closure) entirely in
-- such edges. The walk then projects to a directed walk in `G` of
-- the same length, contradicting `G.IsAcyclic`.
--
-- The precondition `hW : W ⊆ G.J ∪ G.V` is inherited from
-- `extendingCDMGWithInterventionNodes` itself (def_3_13): it is the
-- well-typedness condition that pins each fresh edge's target
-- `Sum.inl w` into `Sum.inl '' G.V`. It is *not* used in the
-- acyclicity reasoning itself -- only in the def -- so it appears
-- here for type-checking, not as a mathematical hypothesis. This
-- mirrors `isAcyclic_nodeSplittingOn` (claim_3_6 part B), which
-- inherits `hW : W ⊆ G.V` from `nodeSplittingOn` for the same
-- reason.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(Rem 821 -- 829; first sentence):

\begin{claimmark}
\begin{Rem}
    If a CDMG $G=(J,V,E,L)$ is acyclic then also $G_{\doit(I_W)}$ is
    acyclic and a topological order for $G_{\doit(I_W)}$ is also one
    for $G$.
    Any topological order of $G$ can be extended to one for
    $G_{\doit(I_W)}$, e.g.\ by putting all the $I_w$ nodes first in
    the ordering.
\end{Rem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **Why a separate theorem from the topological-order halves.**
--   The LN bundles three statements (acyclicity + restriction +
--   extension) into a single `\Rem`. We split for the same reasons
--   claim_3_3 splits its two-statement `\Rem`: different downstream
--   consumers need different halves on their own. claim_3_14 /
--   claim_3_15 (commutation with disjoint hard interventions /
--   node-splitting) need acyclicity *alone* to discharge the CADMG
--   side conditions of their composite operators; bundling would
--   force them to either project a conjunction or to drag in a
--   topological-order witness they do not have. The two
--   topological-order theorems are similarly factored from each
--   other so that callers asking for the *restriction* direction
--   (Lean-only artefact: the LN's "a topological order for
--   `G_{do(I_W)}` is also one for `G`") and the *extension*
--   direction (LN's "any topological order of `G` can be extended")
--   each get a theorem with their own hypothesis profile.
--   *Carrier-change driver of the split.* claim_3_3's analogue
--   keeps the carrier fixed at `α` under `hardInterventionOn`, so
--   its two topological-order directions are tautologically the
--   *same relation* `r : α → α → Prop` -- there is no separate
--   "restrict" theorem to write. Here the carrier *changes* under
--   `extendingCDMGWithInterventionNodes` (from `α` to `α ⊕ ↑(W \
--   G.J)`), so a topological order of `G` and a topological order
--   of the extended graph live on *different types* and the LN's
--   two clauses ("is also one for `G`" / "can be extended") are
--   genuinely two transports between distinct relation spaces.
--   That carrier shift -- shared with claim_3_6
--   (`nodeSplittingOn`, carrier `α ⊕ ↑W`) -- is the structural
--   reason the split is *forced*, not merely convenient.
--
-- * **`{G}, {W}, hW, h` binder choice.** `G` and `W` are implicit
--   because they are unifiable from `hW : W ⊆ G.J ∪ G.V` and from
--   the conclusion `(G.extendingCDMGWithInterventionNodes W
--   hW).IsAcyclic`. `hW` is *explicit* because
--   `extendingCDMGWithInterventionNodes` demands it as an
--   explicit argument at the def-level (its presence is structural;
--   see def_3_13 design notes). `h : G.IsAcyclic` is *explicit*
--   because it is the mathematical hypothesis we transport; no
--   chance for Lean to unify it elsewhere. Matches
--   `isAcyclic_nodeSplittingOn` (claim_3_6) binder layout.
--
-- * **No `[Finite α]` instance hypothesis.** The walk-lifting
--   argument is purely structural and finiteness-free, just like
--   `isAcyclic_hardInterventionOn` (claim_3_3 part A) and
--   `isAcyclic_nodeSplittingOn` (claim_3_6 part B). Downstream uses
--   in the iSCM chapters (working over not-yet-finitised vertex
--   types) inherit this directly.
--
-- * **Naming `isAcyclic_extendingCDMGWithInterventionNodes`.**
--   Follows Mathlib's `<conclusion>_<construction>` convention; the
--   long form of the construction name matches the def_3_13 def
--   name verbatim, mirroring `isAcyclic_hardInterventionOn` /
--   `isAcyclic_nodeSplittingOn`. The "intervention nodes" suffix is
--   what distinguishes this row from claim_3_3
--   (`isAcyclic_hardInterventionOn`, the hard-intervention analogue
--   in `AcyclicUnderIntervention.lean`) -- the new file name
--   `AcyclicityUnderInterventionNodes.lean` likewise picks up the
--   distinguishing "Nodes" suffix.
--
-- * **Proof-phase road map (hint to the prover, not a proof).**
--   Sketch: assume a non-trivial directed walk `π : Walk (G.ext... W
--   hW) v v` with `π.IsDirected ∧ 1 ≤ π.length`. The LN's argument
--   is "no edge of the extended graph has `Sum.inr` as target", so
--   any first step starting at a `Sum.inr` source has the *same*
--   `Sum.inr` source still appearing as the second vertex of any
--   later step closing the cycle -- contradiction with the fresh
--   edge's target being `Sum.inl`. More concretely: define a private
--   walk lift that compresses each fresh `Sum.inl w → Sum.inr ⟨w, _⟩
--   ` step (wait, *no* -- the fresh edges go `Sum.inr ⟨w, _⟩ →
--   Sum.inl w`, i.e. *from* fresh to original; in a *directed cycle*
--   closing on `v`, if any step is a fresh edge, the cycle endpoint
--   `v = Sum.inr ⟨w, _⟩` would need an incoming edge, but no edge
--   has `Sum.inr ⟨w, _⟩` as target). So every step is a piece-1
--   edge (`Sum.inl × Sum.inl`-lift of some `(v', w') ∈ G.E`),
--   pattern-match on which yields a cycle in `G`. The walk-lifting
--   helper analogous to `walkLiftHardInterventionOn` in
--   `AcyclicUnderIntervention.lean` would be the cleanest packaging;
--   leave that as a private helper introduced by the prover.

/-- claim_3_13 part A: if `G` is acyclic and `W ⊆ G.J ∪ G.V`, then
`G.extendingCDMGWithInterventionNodes W hW` is acyclic. Mirrors the
acyclicity half of the `\Rem` immediately after def_3_13 in
`lecture-notes/lecture_notes/graphs.tex` (lines 821 -- 829).

The mathematical content is that every edge of the extended graph
has target `Sum.inl _` (`mem_extendingCDMGWithInterventionNodes_E`:
either it is a `Sum.inl × Sum.inl`-lift of some `(v', w') ∈ G.E`, or
it is a fresh `Sum.inr ⟨w, _⟩ → Sum.inl w`, so the target is
`Sum.inl _` in both cases), so a directed cycle cannot pass through
a `Sum.inr` vertex -- there is no edge into a `Sum.inr` vertex. The
cycle therefore lives entirely in `Sum.inl`-lifted edges and
projects to a directed cycle in `G` of the same length,
contradicting `G.IsAcyclic`. See the per-theorem comment block above
for the walk-lifting plan; the precondition `hW : W ⊆ G.J ∪ G.V`
appears for *typing* reasons only (it is the well-typedness
condition of `extendingCDMGWithInterventionNodes`), not as a
mathematical hypothesis of acyclicity preservation.

`G` and `W` are implicit because they are unifiable from `hW` and
from the conclusion; `hW` is explicit because
`extendingCDMGWithInterventionNodes` requires it explicitly at every
call site; `h : G.IsAcyclic` is the mathematical hypothesis under
transport. Naming follows Mathlib's `<conclusion>_<construction>`
convention, consistent with `isAcyclic_hardInterventionOn`
(claim_3_3 part A) and `isAcyclic_nodeSplittingOn` (claim_3_6 part
B). -/
theorem isAcyclic_extendingCDMGWithInterventionNodes
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.J ∪ G.V) (h : G.IsAcyclic) :
    (G.extendingCDMGWithInterventionNodes W hW).IsAcyclic := by
  -- Mirrors `tex/claim_3_13_proof_AcyclicityUnderIntervention.tex` Part A.
  -- Step 1: a cycle's start vertex `v` is the target of its closing step, so
  -- by `extendingCDMGWithInterventionNodes_target_isInl` it is
  -- `Sum.inl _`. Step 2: lift the cycle to a directed walk in `G` of the
  -- same length via `walkLiftExtendingCDMGWithInterventionNodes`.
  -- Step 3: contradict `G.IsAcyclic` at the projected vertex.
  rintro v _hv ⟨π, h_dir, h_pos⟩
  -- The end vertex `v` of the cycle is the target of the closing step,
  -- hence `Sum.inl _` by `walkEnd_isInl`.
  obtain ⟨v', hv'⟩ := walkEnd_isInl π h_dir h_pos
  subst hv'
  -- Lift the whole cycle to a directed walk in `G` of the same length.
  obtain ⟨ρ, h_ρ_dir, h_ρ_len⟩ :=
    walkLiftExtendingCDMGWithInterventionNodes hW π h_dir v' v' rfl rfl
  have hρ_pos : 1 ≤ ρ.length := by rw [h_ρ_len]; exact h_pos
  -- `v' ∈ G` follows from the first step of `π`: by piece-1 of
  -- `mem_extendingCDMGWithInterventionNodes_E`, the underlying edge
  -- `(v', x) ∈ G.E` puts `v' ∈ G` via `G.E_subset`.
  have hv'_G : v' ∈ G := by
    cases π with
    | nil _ => simp at h_pos
    | @cons _ m _ s _ =>
      cases s with
      | forward he =>
        have he_ext : (Sum.inl v', m) ∈
            (G.extendingCDMGWithInterventionNodes W hW).E := he
        rw [mem_extendingCDMGWithInterventionNodes_E] at he_ext
        rcases he_ext with ⟨v₁, _, hE, h_eq⟩ | ⟨w', h_eq⟩
        · rw [Prod.mk.injEq] at h_eq
          have hv_eq : v' = v₁ := Sum.inl_injective h_eq.1
          subst hv_eq
          exact CDMG.mem_iff.mpr (Set.mem_prod.mp (G.E_subset hE)).1
        · rw [Prod.mk.injEq] at h_eq
          exact nomatch h_eq.1
      | backward _ => simp at h_dir
      | bidir _ => simp at h_dir
  exact h v' hv'_G ⟨ρ, h_ρ_dir, hρ_pos⟩

-- claim_3_13 (named construction, used by part C)
-- title: AcyclicityUnderIntervention -- the "put all I_w first" order
--
-- The LN's "putting all the `I_w` nodes first in the ordering" recipe
-- (lines 826 -- 827), encoded as a relation on the Sum carrier
-- `α ⊕ ↑S`. Parameterised on a generic `S : Set α` (at the use site
-- in claim_3_13, `S = W \ G.J`, the index set of fresh `Sum.inr`
-- nodes) so the definition composes with arbitrary subtypes, not
-- just the one minted by `extendingCDMGWithInterventionNodes`.
--
-- The four cases of the pattern match correspond to the four
-- `(Sum.inl/inr, Sum.inl/inr)` corner pairs:
--   * `(Sum.inl v₁, Sum.inl v₂)` -- both endpoints are original;
--     inherit `r v₁ v₂` from the base relation. Natural restriction.
--   * `(Sum.inr ⟨w₁, _⟩, Sum.inr ⟨w₂, _⟩)` -- both endpoints are
--     fresh; the fresh nodes are *strictly* `Sum.inr`-only, but we
--     still need to order them among themselves. The LN's recipe
--     "put all `I_w` first" doesn't say what order *within* the
--     fresh block; we take the natural choice of inheriting `r w₁ w₂`
--     from the underlying `α`-values. Any choice would work for
--     `parent_lt` (the only edges between fresh nodes are *none* --
--     `mem_extendingCDMGWithInterventionNodes_E` shows fresh edges
--     have `Sum.inl` target, never `Sum.inr`), so this conventional
--     inheritance gives the cleanest `trichotomous`/`trans`
--     transport.
--   * `(Sum.inr _, Sum.inl _)` -- fresh-then-original cross case;
--     `True` encodes "every `I_w` precedes every original node".
--   * `(Sum.inl _, Sum.inr _)` -- original-then-fresh cross case;
--     `False` is the contrapositive of the previous case (no
--     original node precedes any `I_w`). This is what makes the
--     order *strict*: trichotomy on a cross pair always lands in
--     one of the two `True` slots, never the other.
/-
The LN does not give this construction a name; it appears as a
*recipe* in the second sentence of the `\Rem` block (lines 826 --
827 of `lecture-notes/lecture_notes/graphs.tex`):

  Any topological order of $G$ can be extended to one for
  $G_{\doit(I_W)}$, e.g.\ by putting all the $I_w$ nodes first in
  the ordering.
-/
--
-- ## Design choice
--
-- * **Standalone helper rather than an inlined `match`.** The
--   `extensionOrder` relation is the LN's named "e.g." construction.
--   Downstream rows (claim_3_14 / claim_3_15 commutation; the
--   iSCM / do-calculus chapters quoting "the topological order of
--   the extended graph") can talk about this exact relation by
--   name rather than re-deriving the four-case match each time.
--   Mirrors `splitOrder` (claim_3_6) -- the structural sibling for
--   `nodeSplittingOn` -- which is also a standalone `noncomputable
--   def` referred to by name in later rows.
-- * **Parameter `S : Set α`, not `W : Set α` with a `G.J` exclusion
--   hard-coded.** The LN's prose "$I_W$" suggests indexing by `W`,
--   but the *fresh* node set is `W \ G.J` (see def_3_13). Naming
--   the parameter `S` and leaving its identity abstract makes the
--   construction agnostic to whether we are extending by all of
--   `W`, by `W \ G.J`, or by any other subtype carrier. At the use
--   site in `isTopologicalOrder_extendingCDMGWithInterventionNodes_extend`
--   we write `extensionOrder (S := W \ G.J) r` to pin `S` to the
--   right carrier explicitly.
-- * **No `G : CDMG α` argument.** The relation is defined purely
--   on the carrier `α ⊕ ↑S` and is parameterised by `S : Set α` and
--   `r : α → α → Prop`. It does not need to inspect any structure
--   of `G`; the `G`-dependence enters only when we ask
--   `(G.extendingCDMGWithInterventionNodes W hW).IsTopologicalOrder
--   (extensionOrder (S := W \ G.J) r)`. Matches `splitOrder`'s
--   binder layout.
-- * **`Sum`-shaped pattern match, not `dite` on `v ∈ S`.** The
--   carrier `α ⊕ ↑S` already encodes the "fresh vs. original"
--   distinction at the type level (via the `Sum.inl` / `Sum.inr`
--   constructors), so a pattern match is the natural shape. A
--   `dite v ∈ S` approach would force every case to
--   `Classical.propDecidable` the membership and would lose the
--   structural recursion that `Sum.casesOn` provides "for free".
--   Matches the `splitOrder` design.
-- * **`Sum.inr` cross case `True`, `Sum.inl` cross case `False`.**
--   The LN's recipe is *asymmetric*: every fresh `I_w` precedes
--   every original node, never the other way around. Encoding the
--   cross cases as `True` / `False` makes the asymmetry directly
--   visible in the def and makes both `trichotomous` and `trans`
--   transport trivially on cross pairs (one disjunct of trichotomy
--   is always available; transitivity through a cross step is
--   `True ∧ True → True` or absorbed into the same-side cases).
-- * **Same-side cases inherit `r`.** Both `(Sum.inl, Sum.inl)` and
--   `(Sum.inr ⟨w₁, _⟩, Sum.inr ⟨w₂, _⟩)` inherit `r v₁ v₂` / `r w₁
--   w₂` from the underlying `α`-values. For the original-original
--   case this is the natural "restriction"; for the fresh-fresh
--   case, the choice is free (no edges between fresh nodes), but
--   inheriting `r` is the cleanest choice that keeps the relation
--   total / transitive / irreflexive without needing a side relation
--   on `↑S`.
-- * **`noncomputable`.** The relation `r` is `Prop`-valued and need
--   not be decidable. Marking `extensionOrder` `noncomputable` keeps
--   the construction consistent with `splitOrder` (claim_3_6) and
--   with `extendingCDMGWithInterventionNodes` (def_3_13) itself;
--   downstream uses are all `Prop`-valued (membership in
--   `IsTopologicalOrder`), so the choice has no observable cost.

/-- The *extension order* `extensionOrder r` on the carrier `α ⊕ ↑S`,
induced by a base relation `r : α → α → Prop` and a parameter
set `S : Set α`. This is the LN's "putting all `I_w` nodes first"
recipe from claim_3_13: every `Sum.inr ⟨w, _⟩` precedes every
`Sum.inl v`, and same-side pairs inherit `r` from the underlying
`α`-values. The four cases of the pattern match correspond to the
four `(Sum.inl/inr, Sum.inl/inr)` corner pairs; see the design
block above and the file-level docstring.

`S` is implicit because it is recovered from the relation's domain
type `α ⊕ ↑S` at the call site; in
`isTopologicalOrder_extendingCDMGWithInterventionNodes_extend` we
spell it `extensionOrder (S := W \ G.J) r` to make the choice
explicit. `noncomputable` because we do not assume any decidability
on `r`; downstream uses are all `Prop`-valued so the classical
choice has no observable cost. Used by
`isTopologicalOrder_extendingCDMGWithInterventionNodes_extend`
(this file) and quoted by name in claim_3_14 / claim_3_15
(commutation) and the iSCM / do-calculus chapters that recurse
along a topological order of an extended CDMG. -/
noncomputable def extensionOrder {S : Set α} (r : α → α → Prop) :
    (α ⊕ ↑S) → (α ⊕ ↑S) → Prop
  | Sum.inl v₁, Sum.inl v₂ => r v₁ v₂
  | Sum.inr ⟨w₁, _⟩, Sum.inr ⟨w₂, _⟩ => r w₁ w₂
  | Sum.inr _, Sum.inl _ => True
  | Sum.inl _, Sum.inr _ => False

-- claim_3_13 (part C: extension)
-- title: AcyclicityUnderIntervention -- topological order extended
--
-- The LN's "any topological order of `G` can be extended to one for
-- `G_{do(I_W)}`, e.g. by putting all the `I_w` nodes first" -- the
-- *constructive extension* direction. From a topological order `r`
-- of `G` and the precondition `hW : W ⊆ G.J ∪ G.V` (required by
-- `extendingCDMGWithInterventionNodes` itself), produce
-- `extensionOrder (S := W \ G.J) r` as a topological order of the
-- extended graph. The construction follows the LN's "put all
-- `I_w` first" recipe verbatim, via the four-case `extensionOrder`
-- pattern match above.
--
-- Proof sketch (for the prover): the four `IsTopologicalOrder`
-- fields discharge field-by-field:
--   * `irrefl`: pattern-match on `v : α ⊕ ↑(W \ G.J)`. The
--     `Sum.inl` case reduces `extensionOrder r v v` to `r v' v'` for
--     `v' = v ∈ G` (membership transported via
--     `extendingCDMGWithInterventionNodes_J` / `_V`), closed by
--     `hr.irrefl`. The `Sum.inr` case reduces to `r w w` for `w =
--     v.val`, closed by `hr.irrefl` once we know `w ∈ G` -- which
--     follows from `hW` applied to `w ∈ W` and the case split that
--     `w ∉ G.J` forces `w ∈ G.V`. (Same membership lift as
--     `extendingCDMGWithInterventionNodes_E_subset`.)
--   * `trans` / `trichotomous`: case-split on all three / both
--     endpoints; each pattern-match case reduces to `hr.trans` or
--     `hr.trichotomous` on the underlying `α`-values, with cross
--     cases absorbed into the `True` / `False` slots of
--     `extensionOrder`.
--   * `parent_lt`: case-split on the two pieces of
--     `mem_extendingCDMGWithInterventionNodes_E`. Piece 1
--     (`Sum.inl`-lift of `(v₁, v₂) ∈ G.E`): the `(Sum.inl, Sum.inl)`
--     case of `extensionOrder` fires, and the result reduces to
--     `hr.parent_lt ⟨hv₁_G, hE⟩`. Piece 2 (fresh edge
--     `Sum.inr ⟨w, _⟩ → Sum.inl w`): the `(Sum.inr, Sum.inl)` cross
--     case fires with `True`, no `hr` needed -- this is exactly the
--     payoff of the `True` slot chosen in `extensionOrder`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(Rem 821 -- 829; second sentence):

\begin{claimmark}
\begin{Rem}
    If a CDMG $G=(J,V,E,L)$ is acyclic then also $G_{\doit(I_W)}$ is
    acyclic and a topological order for $G_{\doit(I_W)}$ is also one
    for $G$.
    Any topological order of $G$ can be extended to one for
    $G_{\doit(I_W)}$, e.g.\ by putting all the $I_w$ nodes first in
    the ordering.
\end{Rem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **`(S := W \ G.J)` made explicit at the conclusion.** The
--   carrier of `extendingCDMGWithInterventionNodes G W hW` is
--   `α ⊕ ↑(W \ G.J)`, so `extensionOrder`'s implicit `S` parameter
--   is unifiable from the conclusion's relation type. Still, we
--   spell `(S := W \ G.J)` at the call site for two reasons:
--   (i) downstream callers (claim_3_14 / claim_3_15 commutation
--   proofs) want to recognise *which* `S` was chosen without
--   re-typecheck; (ii) it matches the `splitOrder W r` precedent of
--   claim_3_6 where `W` is the explicit fresh-node set.
-- * **`{G}, {W}, hW, {r}, hr` binder choice.** `G`, `W`, and `r`
--   are implicit because they are unifiable from `hW` and `hr`. `hW`
--   is explicit because `extendingCDMGWithInterventionNodes`
--   demands it. `hr : G.IsTopologicalOrder r` is explicit because it
--   is the mathematical hypothesis under transport. Matches
--   `isTopologicalOrder_nodeSplittingOn` (claim_3_6 part A) binder
--   layout exactly.
-- * **No `[Finite α]` instance hypothesis.** The construction is
--   purely relational and the four `IsTopologicalOrder` fields
--   transport via the `@[simp]` membership lemmas of
--   `ExtendingCDMGsWithInterventionNodes.lean`, neither of which
--   needs finiteness. Downstream callers in iSCM chapters working
--   over not-yet-finitised vertex types inherit this directly.
-- * **Naming
--   `isTopologicalOrder_extendingCDMGWithInterventionNodes_extend`.**
--   Follows Mathlib's `<conclusion>_<construction>_<direction>`
--   convention. The `_extend` suffix distinguishes this extension
--   direction from the restriction direction (`_restrict` below).
--   Mirrors `isTopologicalOrder_nodeSplittingOn` (claim_3_6) for
--   the construction prefix.
-- * **"For instance" (LN hedge) preserved.** The LN writes "e.g.\
--   by putting all the `I_w` nodes first in the ordering" -- the
--   recipe is *one* concrete extension, not the canonical one. Any
--   other valid placement (e.g. interleaving each `I_w` directly
--   before `w` rather than putting all `I_w` first) would yield a
--   different relation, equally a topological order. Our theorem
--   proves that `extensionOrder` is *a* topological order; it does
--   not claim uniqueness. This is the second reason we factor
--   `extensionOrder` as a standalone named `def` (alongside the
--   reuse reason): downstream callers that quote "the topological
--   order from claim_3_13" work with *this specific* construction
--   by name while remaining free to instantiate
--   `IsTopologicalOrder` differently when their context favours a
--   different recipe.

/-- claim_3_13 part C: if `W ⊆ G.J ∪ G.V` and `r` is a topological
order of `G`, then `extensionOrder (S := W \ G.J) r` is a topological
order of `G.extendingCDMGWithInterventionNodes W hW`. Mirrors the
constructive extension direction of the `\Rem` immediately after
def_3_13 in `lecture-notes/lecture_notes/graphs.tex` (lines 821 --
829), with the LN's "put all the `I_w` nodes first" recipe encoded
as the four-case `extensionOrder` pattern match.

The `W ⊆ G.J ∪ G.V` precondition is structurally required by
`extendingCDMGWithInterventionNodes` itself (def_3_13) -- the fresh
edge `Sum.inr ⟨w, _⟩ → Sum.inl w` needs its target `Sum.inl w` to
live in the extended graph's `V`-set, which is true only when
`w ∈ G.V` for `w ∈ W \ G.J`. This is not a topological-order
condition; it is the def_3_13 condition transported.

See `isTopologicalOrder_extendingCDMGWithInterventionNodes_restrict`
below for the inverse-direction companion (a topological order of
the extended graph restricts to one of `G`),
`isAcyclic_extendingCDMGWithInterventionNodes` above for the
acyclicity half, and the file-level docstring for the rationale
behind splitting the LN's single `\Rem` into three theorems plus
one named construction. -/
theorem isTopologicalOrder_extendingCDMGWithInterventionNodes_extend
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.J ∪ G.V)
    {r : α → α → Prop} (hr : G.IsTopologicalOrder r) :
    (G.extendingCDMGWithInterventionNodes W hW).IsTopologicalOrder
      (extensionOrder (S := W \ G.J) r) := by
  -- Mirrors `tex/claim_3_13_proof_AcyclicityUnderIntervention.tex` Part C.
  -- The four `IsTopologicalOrder` fields discharge by case-splitting on the
  -- `Sum.inl/inr` carrier; same-side cases reduce to `hr`-fields on
  -- underlying `α`-values, cross cases land in the `True`/`False` slots
  -- of `extensionOrder`. `parent_lt` for piece-2 fresh edges lands
  -- directly in the cross-case `True` slot, no `hr` needed.
  -- Helper: `Sum.inl v ∈ G.ext W hW ↔ v ∈ G`.
  have mem_inl : ∀ {v : α},
      (Sum.inl v : α ⊕ ↑(W \ G.J)) ∈
        G.extendingCDMGWithInterventionNodes W hW ↔ v ∈ G := by
    intro v
    simp only [CDMG.mem_iff, extendingCDMGWithInterventionNodes_J,
      extendingCDMGWithInterventionNodes_V, Set.mem_union, Set.mem_image,
      Set.mem_range]
    constructor
    · rintro ((⟨j, hj, hjv⟩ | ⟨w, hw⟩) | ⟨v', hv', hvv'⟩)
      · cases Sum.inl_injective hjv; exact Or.inl hj
      · exact nomatch hw
      · cases Sum.inl_injective hvv'; exact Or.inr hv'
    · rintro (hJ | hV)
      · exact Or.inl (Or.inl ⟨v, hJ, rfl⟩)
      · exact Or.inr ⟨v, hV, rfl⟩
  -- Helper: every fresh `w' : ↑(W \ G.J)` underlies a node of `G`.
  -- (`w' ∈ W` via `hW : W ⊆ G.J ∪ G.V`; `w' ∉ G.J` forces `w' ∈ G.V`.)
  have inr_mem_G : ∀ w' : ↑(W \ G.J), (w' : α) ∈ G := by
    intro w'
    have hwW : (w' : α) ∈ W := w'.property.1
    have hwJ : (w' : α) ∉ G.J := w'.property.2
    rcases hW hwW with hJ | hV
    · exact absurd hJ hwJ
    · exact Or.inr hV
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- irrefl: case-split on the carrier; both branches collapse
    -- `extensionOrder r v v` to `r v' v'` for `v' ∈ G`.
    rintro (v | ⟨w, hw⟩) hv
    · exact hr.irrefl v (mem_inl.mp hv)
    · exact hr.irrefl (w : α) (inr_mem_G ⟨w, hw⟩)
  · -- trans: case-split on all three carrier shapes (8 cases). The cross
    -- cases `O → F` are `False`, so any case using such a step as a premise
    -- is vacuous. The remaining cases collapse to `hr.trans` on the
    -- underlying `α`-values; the `F → O` cross slot is `True` and absorbs.
    rintro (a | ⟨a, ha⟩) h_a (b | ⟨b, hb⟩) h_b (c | ⟨c, hc⟩) h_c
    · -- (inl a, inl b, inl c)
      intro h_ab h_bc
      exact hr.trans a (mem_inl.mp h_a) b (mem_inl.mp h_b) c (mem_inl.mp h_c)
        h_ab h_bc
    · -- (inl a, inl b, inr c): h_bc : extensionOrder r (inl b) (inr c) = False
      intro _h_ab h_bc
      exact h_bc.elim
    · -- (inl a, inr b, inl c): h_ab : extensionOrder r (inl a) (inr b) = False
      intro h_ab _
      exact h_ab.elim
    · -- (inl a, inr b, inr c): h_ab : extensionOrder r (inl a) (inr b) = False
      intro h_ab _
      exact h_ab.elim
    · -- (inr a, inl b, inl c): h_ab : extensionOrder r (inr a) (inl b) = True;
      -- conclusion: extensionOrder r (inr a) (inl c) = True.
      intro _ _
      trivial
    · -- (inr a, inl b, inr c): h_bc : extensionOrder r (inl b) (inr c) = False
      intro _h_ab h_bc
      exact h_bc.elim
    · -- (inr a, inr b, inl c): conclusion is the cross `True` slot.
      intro _ _
      trivial
    · -- (inr a, inr b, inr c): all three fresh; reduces to `hr.trans` on `(α)`.
      intro h_ab h_bc
      exact hr.trans (a : α) (inr_mem_G ⟨a, ha⟩) b (inr_mem_G ⟨b, hb⟩)
        c (inr_mem_G ⟨c, hc⟩) h_ab h_bc
  · -- trichotomous: case-split on both endpoints (4 cases). Each same-side
    -- case reduces to `hr.trichotomous` on the underlying `α`-values; cross
    -- cases land in the `True` slot.
    rintro (a | ⟨a, ha⟩) h_a (b | ⟨b, hb⟩) h_b
    · -- (inl a, inl b)
      rcases hr.trichotomous a (mem_inl.mp h_a) b (mem_inl.mp h_b) with
        h | rfl | h
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    · -- (inl a, inr b): the cross slot `(inl, inr)` is False, so the only
      -- live disjuncts are middle `=` (impossible by constructor) and the
      -- `(inr, inl)` `True` slot.
      exact Or.inr (Or.inr trivial)
    · -- (inr a, inl b): the cross slot `(inr, inl)` is True.
      exact Or.inl trivial
    · -- (inr a, inr b)
      rcases hr.trichotomous (a : α) (inr_mem_G ⟨a, ha⟩) (b : α)
        (inr_mem_G ⟨b, hb⟩) with h | h_eq | h
      · exact Or.inl h
      · refine Or.inr (Or.inl ?_)
        exact congrArg Sum.inr (Subtype.ext h_eq)
      · exact Or.inr (Or.inr h)
  · -- parent_lt: case-split on the two pieces of
    -- `mem_extendingCDMGWithInterventionNodes_E`.
    intro v w h_pa
    obtain ⟨_, h_vw_E⟩ := h_pa
    change (v, w) ∈ (G.extendingCDMGWithInterventionNodes W hW).E at h_vw_E
    rw [mem_extendingCDMGWithInterventionNodes_E] at h_vw_E
    rcases h_vw_E with ⟨v₁, v₂, hE, h_eq⟩ | ⟨w', h_eq⟩
    · -- Piece 1: (v, w) = (Sum.inl v₁, Sum.inl v₂) with (v₁, v₂) ∈ G.E.
      -- `extensionOrder` fires the `(inl, inl)` case, reducing to `hr.parent_lt`.
      rw [Prod.mk.injEq] at h_eq
      obtain ⟨hv_eq, hw_eq⟩ := h_eq
      subst hv_eq
      subst hw_eq
      have hv₁_G : v₁ ∈ G :=
        CDMG.mem_iff.mpr (Set.mem_prod.mp (G.E_subset hE)).1
      exact hr.parent_lt ⟨hv₁_G, hE⟩
    · -- Piece 2: (v, w) = (Sum.inr w', Sum.inl w'.val). The `(inr, inl)`
      -- cross case of `extensionOrder` fires with `True` -- no `hr` needed.
      rw [Prod.mk.injEq] at h_eq
      obtain ⟨hv_eq, hw_eq⟩ := h_eq
      subst hv_eq
      subst hw_eq
      trivial

-- claim_3_13 (part B: restriction)
-- title: AcyclicityUnderIntervention -- topological order restricted
--
-- The LN's "a topological order for `G_{\doit(I_W)}` is also one for
-- `G`" -- the *restriction* direction. From a topological order `r`
-- of the extended graph, produce the topological order
-- `fun v w => r (Sum.inl v) (Sum.inl w)` of `G`, obtained by
-- restricting `r` along the canonical `Sum.inl` embedding
-- `α → α ⊕ ↑(W \ G.J)`.
--
-- Proof sketch (for the prover): inverse-direction companion to the
-- extension theorem; field-by-field transport using the fact that
-- (a) `Sum.inl` embedding takes `G`'s nodes into the extended graph's
-- nodes (`extendingCDMGWithInterventionNodes_J` /
-- `extendingCDMGWithInterventionNodes_V` make this precise -- every
-- `v ∈ G.J` shows up as `Sum.inl v ∈ Sum.inl '' G.J`, and similarly
-- for `G.V`), and (b) every directed edge `(v, w) ∈ G.E` lifts to a
-- directed edge `(Sum.inl v, Sum.inl w)` of the extended graph (the
-- first disjunct of `mem_extendingCDMGWithInterventionNodes_E`). The
-- four `IsTopologicalOrder` fields discharge by transporting each
-- through these two lifts:
--   * `irrefl` / `trans` / `trichotomous`: apply
--     `hr.{irrefl, trans, trichotomous}` at `Sum.inl v`-images of
--     the original `G`-nodes, using
--     `extendingCDMGWithInterventionNodes_J` / `_V` to lift
--     `v ∈ G` to `Sum.inl v ∈ G.extendingCDMGWithInterventionNodes
--     W hW`.
--   * `parent_lt`: a parent in `Pa G w` lifts to a parent of `Sum.inl
--     w` in the extended graph via
--     `mem_extendingCDMGWithInterventionNodes_E`'s first disjunct;
--     then `hr.parent_lt` finishes.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(Rem 821 -- 829; first sentence, second clause):

\begin{claimmark}
\begin{Rem}
    If a CDMG $G=(J,V,E,L)$ is acyclic then also $G_{\doit(I_W)}$ is
    acyclic and a topological order for $G_{\doit(I_W)}$ is also one
    for $G$.
    ...
\end{Rem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **Restriction encoded as `fun v w => r (Sum.inl v) (Sum.inl
--   w)`, not as a quotient or projection.** The `Sum.inl` embedding
--   is the canonical lift of `G`'s carrier into the extended graph's
--   carrier `α ⊕ ↑(W \ G.J)`, so restricting `r` along this lift is
--   the natural inverse of the `extensionOrder` recipe (which leaves
--   the `(Sum.inl, Sum.inl)` quadrant inheriting `r` verbatim). The
--   restriction-then-extension round trip is an identity on the
--   `(Sum.inl, Sum.inl)` quadrant; the extension-then-restriction
--   round trip is exactly the identity on `r` (cross-case data is
--   discarded by the restriction).
-- * **`{G}, {W}, hW, {r}, hr` binder choice.** `G` and `W` are
--   implicit because unifiable from `hW`. `r` is implicit because
--   it is unifiable from `hr : (G.extendingCDMGWithInterventionNodes
--   W hW).IsTopologicalOrder r`. `hW` is explicit because
--   `extendingCDMGWithInterventionNodes` demands it. `hr` is the
--   mathematical hypothesis under transport. Matches the extension
--   direction's binder layout.
-- * **No `[Finite α]` instance hypothesis.** Same reason as the
--   acyclicity and extension parts -- the transport is purely
--   structural via the `@[simp]` membership lemmas of
--   `ExtendingCDMGsWithInterventionNodes.lean`.
-- * **Naming
--   `isTopologicalOrder_extendingCDMGWithInterventionNodes_restrict`.**
--   The `_restrict` suffix is the companion of `_extend`; together
--   they witness the two directions of the LN's "a topological order
--   for `G_{do(I_W)}` is also one for `G`" / "any topological order
--   of `G` can be extended to one for `G_{do(I_W)}`" prose. The
--   restriction theorem is the *Lean-only artefact* that does not
--   appear explicitly in the LN's `\Rem` text (the LN only states
--   the implication "TO-of-extended ⇒ TO-of-G", which is exactly the
--   restriction direction; we name it explicitly here because Lean's
--   statement layer requires a separate identifier for each
--   directed implication).
-- * **Why include this Lean-only artefact at all.** The brief
--   identifies *three* distinct mathematical statements in the LN
--   `\Rem`, and the restriction direction is the second of them.
--   Without it, the LN's "a topological order for `G_{do(I_W)}` is
--   also one for `G`" would be left implicit and downstream
--   consumers (claim_3_14 / claim_3_15; the iSCM identification
--   theory) that want to transport a topological order *back* to
--   `G` from a CADMG-side computation would have to re-derive the
--   restriction by hand each time. Naming it once here saves that
--   work.
-- * **Contrast with claim_3_3 -- why "is also one for `G`" reads
--   as trivial in the LN but is a genuine theorem here.** In the
--   hard-intervention analogue (claim_3_3,
--   `isTopologicalOrder_hardInterventionOn`), the carrier stays
--   `α`, so the LN's "a topological order for `G_{do(W)}` is also
--   one for `G`" is the *very same relation* `r : α → α → Prop`
--   on the *very same type*; no new transport, no inverse-direction
--   companion is needed. The LN's analogous sentence here ("a
--   topological order for `G_{do(I_W)}` is also one for `G`") sits
--   in the *same sentence* of prose -- yet because
--   `extendingCDMGWithInterventionNodes` *changes* the carrier
--   `α ↦ α ⊕ ↑(W \ G.J)`, the relation on the extended graph and
--   the relation on `G` live on different types, and a literal
--   `Sum.inl`-restriction must be performed to land in the right
--   space. That makes this theorem *substantive content*, not a
--   syntactic relabelling -- a non-obvious point a reader coming
--   in from claim_3_3 might otherwise miss.

/-- claim_3_13 part B: if `W ⊆ G.J ∪ G.V` and `r` is a topological
order of `G.extendingCDMGWithInterventionNodes W hW`, then the
restriction `fun v w => r (Sum.inl v) (Sum.inl w)` is a topological
order of `G`. Mirrors the restriction direction of the `\Rem`
immediately after def_3_13 in
`lecture-notes/lecture_notes/graphs.tex` (lines 821 -- 829, first
sentence second clause: "a topological order for `G_{\doit(I_W)}` is
also one for `G`").

The `W ⊆ G.J ∪ G.V` precondition is structurally required by
`extendingCDMGWithInterventionNodes` itself (def_3_13), not by the
restriction direction per se; see
`isTopologicalOrder_extendingCDMGWithInterventionNodes_extend` for
the matching extension direction and the file-level docstring for
the rationale behind splitting the LN's single `\Rem` into three
theorems plus one named construction.

Inverse-direction companion to the extension theorem: field-by-field
transport using the fact that `Sum.inl` embedding takes `G`'s nodes
into the extended graph's nodes
(`extendingCDMGWithInterventionNodes_J` /
`extendingCDMGWithInterventionNodes_V` make this precise) and
`Sum.inl`-images of `G.E` are edges of the extended graph
(`mem_extendingCDMGWithInterventionNodes_E` first disjunct). -/
theorem isTopologicalOrder_extendingCDMGWithInterventionNodes_restrict
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.J ∪ G.V)
    {r : (α ⊕ ↑(W \ G.J)) → (α ⊕ ↑(W \ G.J)) → Prop}
    (hr : (G.extendingCDMGWithInterventionNodes W hW).IsTopologicalOrder r) :
    G.IsTopologicalOrder (fun v w => r (Sum.inl v) (Sum.inl w)) := by
  -- Mirrors `tex/claim_3_13_proof_AcyclicityUnderIntervention.tex` Part B.
  -- Inverse-direction companion to Part C: field-by-field transport
  -- applying `hr.{irrefl, trans, trichotomous}` at `Sum.inl`-lifted nodes
  -- (membership transported via `extendingCDMGWithInterventionNodes_J`
  -- / `_V`); `parent_lt` lifts `(v, w) ∈ G.E` to `(Sum.inl v, Sum.inl w)
  -- ∈ G_ext.E` via the first disjunct of
  -- `mem_extendingCDMGWithInterventionNodes_E`.
  -- Helper: `Sum.inl v ∈ G.ext W hW` whenever `v ∈ G`.
  have mem_inl : ∀ {v : α}, v ∈ G →
      (Sum.inl v : α ⊕ ↑(W \ G.J)) ∈
        G.extendingCDMGWithInterventionNodes W hW := by
    intro v hv
    simp only [CDMG.mem_iff, extendingCDMGWithInterventionNodes_J,
      extendingCDMGWithInterventionNodes_V, Set.mem_union, Set.mem_image,
      Set.mem_range]
    rcases hv with hJ | hV
    · exact Or.inl (Or.inl ⟨v, hJ, rfl⟩)
    · exact Or.inr ⟨v, hV, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- irrefl: transport `hr.irrefl` at `Sum.inl v`.
    intro v hv
    exact hr.irrefl (Sum.inl v) (mem_inl hv)
  · -- trans: transport via `hr.trans` at the three `Sum.inl`-lifted vertices.
    intro v hv w hw x hx
    exact hr.trans (Sum.inl v) (mem_inl hv) (Sum.inl w) (mem_inl hw)
      (Sum.inl x) (mem_inl hx)
  · -- trichotomous: transport via `hr.trichotomous`; the middle disjunct
    -- `Sum.inl v = Sum.inl w` collapses to `v = w` by `Sum.inl_injective`.
    intro v hv w hw
    rcases hr.trichotomous (Sum.inl v) (mem_inl hv) (Sum.inl w) (mem_inl hw)
      with h | h_eq | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Sum.inl_injective h_eq))
    · exact Or.inr (Or.inr h)
  · -- parent_lt: lift `(v, w) ∈ G.E` to a `Sum.inl × Sum.inl`-lifted edge
    -- of the extended graph via piece 1 of
    -- `mem_extendingCDMGWithInterventionNodes_E`; then `hr.parent_lt`.
    intro v w h_pa
    obtain ⟨hv_G, h_vw_E⟩ := h_pa
    have h_lifted : (Sum.inl v, Sum.inl w) ∈
        (G.extendingCDMGWithInterventionNodes W hW).E := by
      rw [mem_extendingCDMGWithInterventionNodes_E]
      exact Or.inl ⟨v, w, h_vw_E, rfl⟩
    exact hr.parent_lt ⟨mem_inl hv_G, h_lifted⟩

end CDMG

end Causality
