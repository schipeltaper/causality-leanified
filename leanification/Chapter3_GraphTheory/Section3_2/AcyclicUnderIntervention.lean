import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_2.HardInterventionOn

-- TeX proof: tex/claim_3_3_proof_AcyclicUnderIntervention.tex

/-!
# Acyclicity and topological orders survive hard intervention (claim_3_3)

This file formalises the lecture notes' remark immediately following
the definition of the hard intervention `G_{\doit(W)}` (def_3_10): if
`G` is acyclic, then so is `G.hardInterventionOn W`, and any
topological order of `G` is also a topological order of
`G.hardInterventionOn W`. See
`lecture-notes/lecture_notes/graphs.tex` Rem at lines 308 -- 313.

The LN bundles two distinct mathematical statements under one `\Rem`
block; we split them into two theorems because they carry different
hypotheses (see the per-theorem design notes below):

* `isAcyclic_hardInterventionOn` -- acyclicity is preserved with **no
  precondition** on `W`. Every directed edge of the intervened graph
  is a directed edge of `G` (by `mem_hardInterventionOn_E`), so every
  directed walk in `G.hardInterventionOn W` lifts to a directed walk
  in `G` of the same length; a cycle would therefore lift back to one
  in `G`. New input vertices in `W \ (G.J ∪ G.V)` participate in no
  edges (by `G.E_subset` / `G.L_subset`) and are vacuously safe.

* `isTopologicalOrder_hardInterventionOn` -- the topological order is
  preserved under the **precondition** `W ⊆ G.J ∪ G.V`. With the
  precondition the node set `(G.hardInterventionOn W).J ∪
  (G.hardInterventionOn W).V` equals `G.J ∪ G.V`, so the four
  `IsTopologicalOrder` fields (`irrefl` / `trans` / `trichotomous` /
  `parent_lt`) transport verbatim from `hr : G.IsTopologicalOrder r`.
  Without the precondition a vertex in `W \ (G.J ∪ G.V)` would sit in
  the intervened graph's node set but be unconstrained by `hr`,
  breaking `irrefl` / `trichotomous` in general.

## Where this gets used downstream

* **claim_3_4** (`graphs.tex` Lem 317, "hard interventions commute")
  -- uses the acyclicity preservation when iterating
  `(G.hardInterventionOn W₁).hardInterventionOn W₂`.
* **claim_3_5** (`graphs.tex` Prp 360) -- bifurcation
  characterisations via `Anc^{G_{\doit(w)}}(v)` need `G_{\doit(w)}`
  acyclic to talk about topological orders on it.
* **claim_3_8 / claim_3_11** -- disjoint hard interventions inherit
  acyclicity from this row by iteration.
* **Chapters 4 -- 6 (CBNs, do-calculus, ID-algorithm)** -- the
  soundness arguments take a CADMG `G` with a topological order `<`
  and rewrite identification problems via `G_{\doit(W)}`; the
  topological order on `G_{\doit(W)}` is read off as the same `<`
  thanks to `isTopologicalOrder_hardInterventionOn`.
* **Chapters 8 -- 10 (iSCMs)** -- the unique-solution theory of
  intervened iSCMs recurses along a topological order of the
  intervened graph; that order is the *same* relation as the original
  by this row.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

/-! ### Edge-shrinkage walk-lifting helpers

These private helpers are the *single engine* of both halves of
`claim_3_3`: hard intervention only ever shrinks the edge sets
(`(G.hardInterventionOn W).E ⊆ G.E` via `mem_hardInterventionOn_E`,
`(G.hardInterventionOn W).L ⊆ G.L` via `mem_hardInterventionOn_L`),
so every step / walk in `G.hardInterventionOn W` can be lifted to a
step / walk in `G` by re-typing the underlying adjacency proof.

Part A uses the walk lift to transport a hypothetical directed
cycle in `G.hardInterventionOn W` back to `G`; Part B uses the
edge-step half of the same machinery to transport `parent_lt`.

The lift is length- and `IsDirected`-preserving (the two lemmas
below). Kept `private` because they encode the edge-shrinkage idiom
for *this* row's proof; future rows that need the same lift from a
more general edge-subgraph (e.g. claim_3_4's iterated intervention)
can promote them to public lemmas when the use case actually
arrives. -/

/-- Lift a `WalkStep` in `G.hardInterventionOn W` to a `WalkStep`
in `G`. Each constructor's underlying adjacency proof is a member of
the strictly larger base edge / latent set, so the lift is just a
re-typing -- the `(G.hardInterventionOn W).E ⊆ G.E` /
`(G.hardInterventionOn W).L ⊆ G.L` inclusions are *definitional* set
differences, so `.1` extracts the `G.E` / `G.L` membership directly. -/
private def stepLiftHardInterventionOn {G : CDMG α} {W : Set α} {v w : α} :
    WalkStep (G.hardInterventionOn W) v w → WalkStep G v w
  | .forward h => .forward h.1
  | .backward h => .backward h.1
  | .bidir h => .bidir h.1

/-- Lift an entire `Walk` in `G.hardInterventionOn W` to a `Walk`
in `G` of the same length, by applying `stepLiftHardInterventionOn`
to each step. The vertex sequence (and hence the trivial-walk
recogniser) is preserved exactly. -/
private def walkLiftHardInterventionOn {G : CDMG α} {W : Set α} :
    {v w : α} → Walk (G.hardInterventionOn W) v w → Walk G v w
  | _, _, .nil v => .nil v
  | _, _, .cons s p =>
      .cons (stepLiftHardInterventionOn s) (walkLiftHardInterventionOn p)

private lemma walkLiftHardInterventionOn_length {G : CDMG α} {W : Set α}
    {v w : α} (π : Walk (G.hardInterventionOn W) v w) :
    (walkLiftHardInterventionOn π).length = π.length := by
  induction π with
  | nil _ => rfl
  | cons _ _ ih => simp [walkLiftHardInterventionOn, ih]

private lemma walkLiftHardInterventionOn_isDirected {G : CDMG α} {W : Set α}
    {v w : α} (π : Walk (G.hardInterventionOn W) v w) (h : π.IsDirected) :
    (walkLiftHardInterventionOn π).IsDirected := by
  induction π with
  | nil _ => simp [walkLiftHardInterventionOn]
  | cons s _ ih =>
    cases s with
    | forward _ =>
      simp only [walkLiftHardInterventionOn, stepLiftHardInterventionOn,
        Walk.isDirected_cons_forward] at h ⊢
      exact ih h
    | backward _ => simp at h
    | bidir _ => simp at h

-- claim_3_3 (part A)
-- title: AcyclicUnderIntervention -- acyclicity preserved
--
-- If `G` is acyclic, then so is `G.hardInterventionOn W`, with **no**
-- `W ⊆ G.J ∪ G.V` precondition. The LN's `\Rem` block does not state
-- such a precondition (it was already given at def_3_10), and the
-- mathematical content does not need it: directed edges of the
-- intervened graph are a subset of `G.E` (`mem_hardInterventionOn_E`),
-- so any directed walk in the intervened graph lifts to one in `G` of
-- the same length, hence any acyclicity-violating witness in the
-- intervened graph would witness a cycle in `G`. Vertices in
-- `W \ (G.J ∪ G.V)` get promoted to inputs but participate in no
-- edges (by `G.E_subset` on the source / `G.L_subset` on both
-- endpoints), so they cannot host a directed cycle either.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Rem 308 -- 313):

\begin{claimmark}
\begin{Rem}
    If $G$ is acyclic then also $G_{\doit(W)}$ is acyclic and a
    topological order for $G$ is also one for $G_{\doit(W)}$.
\end{Rem}
\end{claimmark}
-/
/-- claim_3_3 part A: if `G` is acyclic then so is
`G.hardInterventionOn W`, for *any* `W : Set α`. Mirrors the first
half of the `\Rem` immediately after def_3_10 in
`lecture-notes/lecture_notes/graphs.tex` (line 311).

We split the LN's single `\Rem` into two theorems because the
acyclicity and topological-order halves carry different
hypotheses, and different downstream consumers pattern-match on
different halves. `claim_3_4` ("hard interventions commute") and
the iSCM uniqueness theory of chapters 8 -- 10 need acyclicity of
the intervened graph *alone* -- they have no named topological
order on hand, so a bundled conjunction would force them either
to project, or to drag in the `W ⊆ G.J ∪ G.V` precondition that
part B (`isTopologicalOrder_hardInterventionOn`) requires but
part A does not. The downstream consumers of part B in
`do_calculus.tex` / `id_algorithm.tex` carry a named `<` through
long proofs and likewise prefer the relation-level form on its
own, without the acyclicity conjunct.

No `W ⊆ G.J ∪ G.V` precondition appears here because every
directed edge of `G.hardInterventionOn W` is a directed edge of
`G` (by `mem_hardInterventionOn_E` in `HardInterventionOn.lean`),
so directed walks in the intervened graph lift to walks of the
same length in `G` and any cycle would lift to a cycle in `G`.
Spurious vertices in `W \ (G.J ∪ G.V)` participate in no edges
at all (by `G.E_subset` on the source / `G.L_subset` on both
endpoints), so they cannot host a cycle either. For the same
reason no `[Finite α]` instance is required -- the walk-lifting
argument is purely structural (edges shrink under intervention),
and adding finiteness would block downstream use in iSCM
chapters working over not-yet-finitised vertex types. `W` is an
*explicit* binder because consumers (claim_3_4, claim_3_5,
iSCMs) typically have a specific `W` in mind that is not
unifiable from elsewhere, while `G` is implicit because it is
recovered from `(G.hardInterventionOn W).IsAcyclic`. The name
follows Mathlib's `<conclusion>_<construction>` convention --
the `IsAcyclic` predicate first, then the `hardInterventionOn`
construction we are showing preserves it. -/
theorem isAcyclic_hardInterventionOn
    {G : CDMG α} (W : Set α) (h : G.IsAcyclic) :
    (G.hardInterventionOn W).IsAcyclic := by
  -- Mirrors `tex/claim_3_3_proof_AcyclicUnderIntervention.tex` Part A.
  -- A non-trivial directed walk `v → ⋯ → v` in `G.hardInterventionOn W`
  -- lifts step-by-step (via `walkLiftHardInterventionOn`) to a non-trivial
  -- directed walk in `G`. Its first step witnesses `v ∈ G` via `G.E_subset`
  -- (def_3_1), contradicting `G.IsAcyclic`.
  rintro v _hv ⟨π, h_dir, h_pos⟩
  cases π with
  | nil _ => simp at h_pos
  | cons s p =>
    cases s with
    | forward h_e =>
      have h_e_G : (v, _) ∈ G.E := h_e.1
      have hv_G : v ∈ G :=
        CDMG.mem_iff.mpr (Set.mem_prod.mp (G.E_subset h_e_G)).1
      refine h v hv_G
        ⟨walkLiftHardInterventionOn (Walk.cons (.forward h_e) p), ?_, ?_⟩
      · exact walkLiftHardInterventionOn_isDirected _ h_dir
      · rw [walkLiftHardInterventionOn_length]; exact h_pos
    | backward _ => simp at h_dir
    | bidir _ => simp at h_dir

-- claim_3_3 (part B)
-- title: AcyclicUnderIntervention -- topological order preserved
--
-- If `r` is a topological order of `G` and `W ⊆ G.J ∪ G.V`, then `r`
-- is also a topological order of `G.hardInterventionOn W`. The
-- `W ⊆ G.J ∪ G.V` precondition is essential here even though it is
-- *not* needed for part A: `IsTopologicalOrder G' r` quantifies over
-- nodes of `G'`, and the intervened graph's node set is
-- `(G.J ∪ W) ∪ (G.V \ W)`. With the precondition this collapses to
-- `G.J ∪ G.V`, so the four `IsTopologicalOrder` fields transport
-- directly from `hr`. Without it, a vertex in `W \ (G.J ∪ G.V)` would
-- be a node of the intervened graph but `hr.irrefl` / `hr.trichotomous`
-- would say nothing about it, so the conclusion would fail in general.
-- The `parent_lt` field also transports because edges shrink under
-- intervention: `Pa (G.hardInterventionOn W) w ⊆ Pa G w` (a directed
-- edge of the intervened graph is a directed edge of `G`, by
-- `mem_hardInterventionOn_E`).
/-- claim_3_3 part B: if `W ⊆ G.J ∪ G.V` and `r` is a topological
order of `G`, then `r` is also a topological order of
`G.hardInterventionOn W`. Mirrors the second half of the `\Rem`
immediately after def_3_10 in
`lecture-notes/lecture_notes/graphs.tex` (line 311); see
`isAcyclic_hardInterventionOn` above for the rationale behind
splitting that `\Rem` into two theorems and for the downstream
consumers of the acyclicity half.

The `W ⊆ G.J ∪ G.V` precondition that was *absent* in part A is
*essential* here: `IsTopologicalOrder G' r` quantifies its four
fields (`irrefl` / `trans` / `trichotomous` / `parent_lt`) over
the nodes of `G'`, and `(G.hardInterventionOn W).J ∪
(G.hardInterventionOn W).V = (G.J ∪ W) ∪ (G.V \ W)` collapses to
`G.J ∪ G.V` only when `W ⊆ G.J ∪ G.V`. Without the precondition
a vertex `v ∈ W \ (G.J ∪ G.V)` would be a node of the intervened
graph that `hr.irrefl` / `hr.trichotomous` say nothing about,
breaking those fields in general. Part A escaped this issue
because its walk-lifting argument only touches
`(G.hardInterventionOn W).E ⊆ G.E`, never the node set of the
intervened graph.

`W` and `r` are both implicit because they are unifiable from the
hypotheses (`hW : W ⊆ G.J ∪ G.V` and
`hr : G.IsTopologicalOrder r`) and from the conclusion
`.IsTopologicalOrder r`; downstream callers in
`do_calculus.tex` / `id_algorithm.tex` carry a fixed named `<`
through long proofs and pass it through `hr`, so they never need
to spell `r` (or `W`) at the call site -- they simply write
`isTopologicalOrder_hardInterventionOn hW hr`. `G` is implicit
for the same reason it is in part A. Naming follows Mathlib's
`<conclusion>_<construction>` convention, consistent with part A
and with the `IsTopologicalOrder` predicate's own naming in
`Section3_1/TopologicalOrder.lean`. -/
theorem isTopologicalOrder_hardInterventionOn
    {G : CDMG α} {W : Set α} {r : α → α → Prop}
    (hW : W ⊆ G.J ∪ G.V) (hr : G.IsTopologicalOrder r) :
    (G.hardInterventionOn W).IsTopologicalOrder r := by
  -- Mirrors `tex/claim_3_3_proof_AcyclicUnderIntervention.tex` Part B.
  -- (Step 1) Under `hW`, the node sets of `G` and `G.hardInterventionOn W`
  -- agree: `(G.J ∪ W) ∪ (G.V \ W) = G.J ∪ G.V`. (Steps 2 & 3) The four
  -- `IsTopologicalOrder` fields then transport directly from `hr`, with
  -- `parent_lt` additionally using the edge inclusion
  -- `(G.hardInterventionOn W).E ⊆ G.E` (`mem_hardInterventionOn_E`).
  have hnodes : ∀ v, v ∈ G.hardInterventionOn W ↔ v ∈ G := by
    intro v
    simp only [CDMG.mem_iff, hardInterventionOn_J, hardInterventionOn_V,
      Set.mem_union, Set.mem_diff]
    refine ⟨?_, ?_⟩
    · rintro ((hJ | hW') | ⟨hV, _⟩)
      · exact Or.inl hJ
      · exact hW hW'
      · exact Or.inr hV
    · rintro (hJ | hV)
      · exact Or.inl (Or.inl hJ)
      · by_cases hW' : v ∈ W
        · exact Or.inl (Or.inr hW')
        · exact Or.inr ⟨hV, hW'⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- irrefl: node set agrees, transport from `hr.irrefl`.
    intro v hv
    exact hr.irrefl v ((hnodes v).mp hv)
  · -- trans: transport via `hr.trans`.
    intro v hv w hw x hx
    exact hr.trans v ((hnodes v).mp hv) w ((hnodes w).mp hw) x ((hnodes x).mp hx)
  · -- trichotomous: transport via `hr.trichotomous`.
    intro v hv w hw
    exact hr.trichotomous v ((hnodes v).mp hv) w ((hnodes w).mp hw)
  · -- parent_lt: edge inclusion + `G.E_subset` reduce to `hr.parent_lt`.
    intro v w hvw
    obtain ⟨_, h_edge⟩ := hvw
    have h_edge_G : (v, w) ∈ G.E := h_edge.1
    have hv_G : v ∈ G :=
      CDMG.mem_iff.mpr (Set.mem_prod.mp (G.E_subset h_edge_G)).1
    exact hr.parent_lt ⟨hv_G, h_edge_G⟩

end CDMG

end Causality
