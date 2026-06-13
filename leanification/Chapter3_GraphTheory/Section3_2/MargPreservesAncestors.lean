import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.Walks
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_2.MarginalizationAK

namespace Causality

/-!
# Marginalization preserves ancestors, bifurcations, and acyclicity
(`claim_3_16`)

This file formalises the LN remark `claim_3_16`
(`MargPreservesAncestors` in `graphs.tex`, section 3.2,
`\label{rem:marg_preserves_ancestors_bifurcations_acyclicity}`):

> Marginalization preserves ancestral relations, bifurcations and
> acyclicity:
>   i.   For `v_1, v_2 ∈ G` with `v_1, v_2 ∉ W`:
>        `v_1 ∈ Anc^G(v_2) ⟺ v_1 ∈ Anc^{G^{∖W}}(v_2)`.
>   ii.  For `v_1, v_2 ∈ G ∖ W` (and, optionally, `v_3 ∈ G ∖ W`):
>        there is a bifurcation between `v_1` and `v_2` (with source
>        `v_3`) in `G` iff there is one in `G^{∖W}`.
>   iii. If `G` is acyclic then so is `G^{∖W}`, and a topological
>        order of `G` induces a topological order of `G^{∖W}` (by
>        just ignoring the nodes from `W`).

The authoritative spec is the canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_16_statement_MargPreservesAncestors.tex`, equivalent to
the LN block plus the `addition_to_the_LN` clarifications.  The
`addition_to_the_LN` clarifies the ambiguous "(and, optionally,
`v_3 ∈ G ∖ W`)" parenthetical of item ii as **two separate
biconditionals** — once with the parenthetical clauses omitted (the
sourceless form (a)) and once with them included (the sourced form
(b)).  Sub-claim iii is unfolded into two sub-assertions: (a)
preservation of acyclicity, and (b) restriction of any topological
order of `G` to a topological order of `G^{∖W}`.

Two subtleties in the LN's wording are made explicit by the
canonical tex:

* The "(and, optionally, `v_3 ∈ G ∖ W`)" parenthetical is resolved
  by the `addition_to_the_LN` clauses (a) and (b) above: the
  literal LN asserts two biconditionals, not one.
* Under the sourceless reading, the LHS's existential over the
  source ranges over `J ∪ V` (including `W`), while the RHS's
  ranges over `J ∪ (V ∖ W)`.  The biconditional silently relies on
  `Walk.IsBifurcation` admitting the `n = 1` direct bidirected edge
  case (so that a `Y`-fork through `W` collapses to a bidirected
  edge in `G^{∖W}`); this is exactly what the chapter-init addition
  `[bifurcation_index_boundary_excludes_natural_cases]` of
  `def_3_4` `IsBifurcation` admits.

The remark bundles five sub-assertions — three primary sub-claims,
two of which split further — under one `\begin{Rem}`.
This file states each as its **own top-level theorem**:

* `marginalize_preserves_ancestors` (sub-claim i): the ancestral-
  relation biconditional.
* `marginalize_preserves_bifurcation` (sub-claim ii(a),
  *sourceless* form per `addition_to_the_LN`): the
  "exists a bifurcation between `v_1` and `v_2`" biconditional.
* `marginalize_preserves_bifurcation_with_source` (sub-claim ii(b),
  *sourced* form per `addition_to_the_LN`): the
  "exists a bifurcation between `v_1` and `v_2` with source `v_3`"
  biconditional.
* `marginalize_preserves_acyclic` (sub-claim iii(a)): preservation
  of acyclicity.
* `marginalize_restricts_topological_order` (sub-claim iii(b)):
  the same `lt : Node → Node → Prop` that is a topological order of
  `G` is also a topological order of `G^{∖W}` (the restriction is
  invisible at the type level because marginalization keeps the
  original `Node` carrier; the `∀ v ∈ G^{∖W}, …` quantification
  inside `IsTopologicalOrder` already restricts the order's
  effective domain to `J ∪ (V ∖ W)`).

The proof bodies follow the TeX proof at
`tex/claim_3_16_proof_MargPreservesAncestors.tex`.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  Both fixtures are load-bearing for this
--   row's statements: every theorem signature references `CDMG Node`
--   (`def_3_1`), `G.marginalize W hW` (`def_3_14`) producing another
--   `CDMG Node`, and one of `G.Anc` (`def_3_5`), `Walk.IsBifurcation`
--   / `Walk.IsBifurcationSource` (`def_3_4`), `G.IsAcyclic`
--   (`def_3_6`), or `G.IsTopologicalOrder` (`def_3_8`) — each of
--   which threads `DecidableEq Node` through its `Finset` /
--   `Walk` / `Membership` plumbing.  Stronger instances (`Fintype`,
--   `LinearOrder`) are not needed at the statement level and are
--   deferred to use sites that consume them (e.g.\ the proof phase
--   may need them to case-split on walk length).
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  Matches the convention in every sibling
--   file in `Section3_2/` (`AcyclicHardInterventionTopologicalOrder.lean`,
--   `SwigAcyclic.lean`, `SplitTopologicalOrder.lean`,
--   `MarginalizationAK.lean`).  The two-dash marker is reserved for
--   declarations whose body is the formalised LN content of the row;
--   this `variable` line is statement-typing infrastructure binding
--   the implicit `Node` type and its `DecidableEq` instance that all
--   five main theorems' signatures reference.
-- claim_3_16 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_16 --- end helper

-- ## Proof-only helpers (NOT statement markers).
--
-- The walk-level plumbing below is generic infrastructure used by the
-- five proof bodies that follow.  It mirrors the `private` walk
-- helpers in `Section3_1/AcyclicIffTopologicalOrder.lean` and
-- `Section3_2/BifurcationAlternative.lean`; we re-declare here
-- because those siblings keep them `private`.  Every helper is also
-- marked `private`, restricted to this file's proofs of
-- `claim_3_16`'s five sub-assertions.

/-- Concatenate two walks `p : u → v` and `q : v → w` into a walk
`u → w`. -/
private def Walk.comp {G : CDMG Node} :
    ∀ {u v w : Node}, Walk G u v → Walk G v w → Walk G u w
  | _, _, _, .nil _ _, q => q
  | _, _, _, .cons v a h p, q => .cons v a h (p.comp q)

private lemma Walk.length_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).length = p.length + q.length
  | _, _, _, .nil _ _, q => by simp [Walk.comp, Walk.length]
  | _, _, _, .cons _ _ _ p, q => by
      simp [Walk.comp, Walk.length, Walk.length_comp p q,
            Nat.add_comm, Nat.add_left_comm]

private lemma Walk.isDirectedWalk_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      p.IsDirectedWalk → q.IsDirectedWalk → (p.comp q).IsDirectedWalk
  | _, _, _, .nil _ _, _, _, hq => hq
  | _, _, _, .cons _ _ _ p, q, hp, hq => by
      obtain ⟨h1, h2, h3⟩ := hp
      exact ⟨h1, h2, Walk.isDirectedWalk_comp p q h3 hq⟩

/-- A walk's vertex list is non-empty (`nil` gives `[v]`, `cons`
prepends). -/
private lemma Walk.vertices_ne_nil {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices ≠ []
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ _ => by simp [Walk.vertices]

/-- The source of a walk is in its vertex list. -/
private lemma Walk.head_mem_vertices {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), u ∈ p.vertices
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ _ => by simp [Walk.vertices]

private lemma Walk.vertices_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).vertices = p.vertices.dropLast ++ q.vertices
  | _, _, _, .nil _ _, _ => rfl
  | _, _, _, .cons _ _ _ p, q => by
      have hne : p.vertices ≠ [] := Walk.vertices_ne_nil p
      simp [Walk.comp, Walk.vertices, Walk.vertices_comp p q,
            List.dropLast_cons_of_ne_nil hne]

/-- The source vertex of a `WalkStep` lies in `G`. -/
private lemma WalkStep.source_mem {G : CDMG Node} {u v : Node}
    {a : Node × Node} (h : G.WalkStep u a v) : u ∈ G := by
  change u ∈ G.J ∪ G.V
  rcases h with ⟨ha_eq, ha_or⟩ | ⟨ha_eq, ha_E⟩
  · rcases ha_or with ha_E | ha_L
    · have h1 := (G.hE_subset ha_E).1
      rw [ha_eq] at h1
      exact h1
    · have h1 := (G.hL_subset ha_L).1
      rw [ha_eq] at h1
      exact Finset.mem_union_right _ h1
  · have h1 := (G.hE_subset ha_E).2
    rw [ha_eq] at h1
    exact Finset.mem_union_right _ h1

/-- Every vertex of a walk lies in the underlying CDMG. -/
private lemma Walk.mem_of_mem_vertices {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) {x : Node}, x ∈ p.vertices → x ∈ G
  | _, _, .nil v hv, x, hx => by
      change x ∈ [v] at hx
      rw [List.mem_singleton] at hx
      exact hx ▸ hv
  | _, _, .cons _ _ hStep p', x, hx => by
      change x ∈ _ :: p'.vertices at hx
      rcases List.mem_cons.mp hx with rfl | h_in
      · exact WalkStep.source_mem hStep
      · exact Walk.mem_of_mem_vertices p' h_in

/-- The source of a non-trivial directed walk lies in `G`. -/
private lemma Walk.source_in_G_of_directedWalk_pos {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → u ∈ G
  | _, _, .nil _ _, _, hlen => by simp [Walk.length] at hlen
  | _, _, .cons _ _ _ _, hp, _ => by
      obtain ⟨ha_eq, ha_E, _⟩ := hp
      have h_edge : (_, _) ∈ G.E := ha_eq ▸ ha_E
      exact (G.hE_subset h_edge).1

/-- The target of a non-trivial directed walk lies in `G.V`. -/
private lemma Walk.target_in_GV_of_directedWalk_pos {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → v ∈ G.V := by
  intro u v p
  induction p with
  | nil _ _ => intro _ hlen; simp [Walk.length] at hlen
  | @cons u w v a h q ih =>
      intro hdir _
      obtain ⟨ha_eq, ha_E, hq_dir⟩ := hdir
      have h_edge : (u, v) ∈ G.E := ha_eq ▸ ha_E
      by_cases hq_len : q.length ≥ 1
      · exact ih hq_dir hq_len
      · -- q is trivial; v = w forced by `Walk.nil`
        have hlen0 : q.length = 0 := by omega
        match q, hq_dir, hlen0 with
        | .nil _ _, _, _ => exact (G.hE_subset h_edge).2

private lemma Walk.target_in_G_of_directedWalk_pos {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → v ∈ G := by
  intro u v p hdir hlen
  exact Finset.mem_union_right _
    (Walk.target_in_GV_of_directedWalk_pos p hdir hlen)


/-- Lift node membership from the marginalized CDMG back to `G`. -/
private lemma mem_of_mem_marginalize {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.V} {v : Node} (h : v ∈ G.marginalize W hW) : v ∈ G := by
  change v ∈ G.J ∪ (G.V \ W) at h
  change v ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp h with hJ | hVW
  · exact Finset.mem_union_left _ hJ
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hVW).1


/-- A node in `G.marginalize W hW` is outside `W` (uses `hJV_disj`
to handle the `J`-disjunct). -/
private lemma notW_of_mem_marginalize {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.V) {v : Node} (h : v ∈ G.marginalize W hW) : v ∉ W := by
  intro hv_W
  change v ∈ G.J ∪ (G.V \ W) at h
  rcases Finset.mem_union.mp h with hJ | hVW
  · have hv_V : v ∈ G.V := hW hv_W
    exact Finset.disjoint_left.mp G.hJV_disj hJ hv_V
  · exact (Finset.mem_sdiff.mp hVW).2 hv_W

/-- Along a non-trivial directed walk in `G`, parent-precedence plus
transitivity force `lt` between source and target.  This is the
chained version of `IsTopologicalOrder`'s parent clause for sub-claim
iii(b)'s parent-precedence verification. -/
private lemma Walk.lt_of_directedWalk_pos {G : CDMG Node}
    {lt : Node → Node → Prop}
    (h_trans : ∀ u ∈ G, ∀ v ∈ G, ∀ w ∈ G, lt u v → lt v w → lt u w)
    (h_parent : ∀ v w, v ∈ G.Pa w → lt v w) :
    ∀ {x y : Node} (p : Walk G x y),
      p.IsDirectedWalk → p.length ≥ 1 → lt x y := by
  intro x y p
  induction p with
  | nil _ _ => intro _ hlen; simp [Walk.length] at hlen
  | @cons u w v a h q ih =>
      intro hdir _
      obtain ⟨ha_eq, ha_E, hq_dir⟩ := hdir
      have h_edge : (u, v) ∈ G.E := ha_eq ▸ ha_E
      have hu : u ∈ G := (G.hE_subset h_edge).1
      have hv : v ∈ G := Finset.mem_union_right _ (G.hE_subset h_edge).2
      have hlt_uv : lt u v := h_parent u v ⟨hu, h_edge⟩
      by_cases hq_len : q.length ≥ 1
      · have hw : w ∈ G :=
          Walk.target_in_G_of_directedWalk_pos q hq_dir hq_len
        have hlt_vw : lt v w := ih hq_dir hq_len
        exact h_trans u hu v hv w hw hlt_uv hlt_vw
      · have hlen0 : q.length = 0 := by omega
        match q, hq_dir, hlen0 with
        | .nil _ _, _, _ => exact hlt_uv

-- ## Walk expansion: lift a directed walk from `G.marginalize W hW`
-- back to a directed walk in `G`.  Each `marg`-edge expands via the
-- `Φ_E` witness to a directed walk in `G` of length `≥ 1` with
-- intermediates in `W`; the lifted walk concatenates these
-- expansions.  Used by sub-claim i `(⟸)`, sub-claim iii(a), and as
-- a step in sub-claim ii(b) `(⟸)`.

/-- Every walk's vertex list factors as `source :: tail`. -/
private lemma Walk.vertices_eq_head_cons_tail {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices = u :: p.vertices.tail
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ _ => rfl

/-- The vertex list's tail of a walk of length `≥ 1` is non-empty. -/
private lemma Walk.tail_vertices_ne_nil_of_pos {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.length ≥ 1 → p.vertices.tail ≠ []
  | _, _, .nil _ _, h => by simp [Walk.length] at h
  | _, _, .cons _ _ _ p', _ => Walk.vertices_ne_nil p'


/-- Lift a directed walk in the marginalized CDMG to a directed walk
in the ambient `G`, with length at least the original AND vertex
bounds linking the expansion's vertices to the marg-walk's vertices
plus `W`.  Each marg-edge expands via the `Φ_E` witness (whose
intermediates lie in `W`); the concatenation of expansions preserves
directedness and is at least as long as the marg-walk. -/
private lemma expand_directed_walk_marginalize {G : CDMG Node}
    {W : Finset Node} {hW : W ⊆ G.V} :
    ∀ {u v : Node} (p : Walk (G.marginalize W hW) u v),
      p.IsDirectedWalk →
      ∃ (q : Walk G u v),
        q.IsDirectedWalk ∧ q.length ≥ p.length ∧
        (∀ x ∈ q.vertices, x ∈ p.vertices ∨ x ∈ W) ∧
        (∀ x ∈ q.vertices.dropLast, x ∈ p.vertices.dropLast ∨ x ∈ W) := by
  intro u v p
  induction p with
  | nil v hv =>
      intro _
      have hv_g : v ∈ G := mem_of_mem_marginalize hv
      refine ⟨Walk.nil v hv_g, trivial, by simp [Walk.length], ?_, ?_⟩
      · intro x hx
        change x ∈ [v] at hx
        change x ∈ [v] ∨ x ∈ W
        exact Or.inl hx
      · intro x hx
        change x ∈ ([v] : List Node).dropLast at hx
        simp [List.dropLast] at hx
  | @cons u v_end vMid a hStep p' ih =>
      intro hp_dir
      obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := hp_dir
      have ha_mem' : (u, vMid) ∈ (G.marginalize W hW).E := ha_eq ▸ ha_mem
      have ha_filter : (u, vMid) ∈
            ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
              (fun e => G.MarginalizationΦE W e.1 e.2) := ha_mem'
      have ha_phi : G.MarginalizationΦE W u vMid :=
        (Finset.mem_filter.mp ha_filter).2
      obtain ⟨q_edge, hq_edge_dir, hq_edge_pos, hq_edge_inter⟩ := ha_phi
      obtain ⟨q_tail, hq_tail_dir, hq_tail_len, hq_tail_sub, hq_tail_drop_sub⟩ :=
        ih hp'_dir
      have hq_edge_vs : q_edge.vertices = u :: q_edge.vertices.tail :=
        Walk.vertices_eq_head_cons_tail q_edge
      have h_qe_tail_ne : q_edge.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos q_edge hq_edge_pos
      have h_qt_vs_ne : q_tail.vertices ≠ [] := Walk.vertices_ne_nil q_tail
      have hp'_vs_ne : p'.vertices ≠ [] := Walk.vertices_ne_nil p'
      refine ⟨q_edge.comp q_tail,
              Walk.isDirectedWalk_comp q_edge q_tail hq_edge_dir hq_tail_dir,
              ?_, ?_, ?_⟩
      · rw [Walk.length_comp]
        change q_edge.length + q_tail.length ≥ p'.length + 1
        omega
      · -- (q_edge.comp q_tail).vertices ⊆ p.vertices ∪ W.
        intro x hx
        rw [Walk.vertices_comp] at hx
        change x ∈ u :: p'.vertices ∨ x ∈ W
        rcases List.mem_append.mp hx with hx_edge | hx_tail
        · rw [hq_edge_vs] at hx_edge
          rw [List.dropLast_cons_of_ne_nil h_qe_tail_ne] at hx_edge
          rcases List.mem_cons.mp hx_edge with rfl | hx_in_qe_t_d
          · exact Or.inl List.mem_cons_self
          · exact Or.inr (hq_edge_inter x hx_in_qe_t_d)
        · rcases hq_tail_sub x hx_tail with h_p' | h_w
          · exact Or.inl (List.mem_cons.mpr (Or.inr h_p'))
          · exact Or.inr h_w
      · -- (q_edge.comp q_tail).vertices.dropLast ⊆ p.vertices.dropLast ∪ W.
        intro x hx
        have h_vs_comp : (q_edge.comp q_tail).vertices
            = q_edge.vertices.dropLast ++ q_tail.vertices :=
          Walk.vertices_comp q_edge q_tail
        rw [h_vs_comp] at hx
        rw [List.dropLast_append_of_ne_nil h_qt_vs_ne] at hx
        -- (cons u a hStep p').vertices = u :: p'.vertices.
        -- (u :: p'.vertices).dropLast = u :: p'.vertices.dropLast.
        change x ∈ (u :: p'.vertices).dropLast ∨ x ∈ W
        rw [List.dropLast_cons_of_ne_nil hp'_vs_ne]
        rcases List.mem_append.mp hx with hx_edge | hx_tail_drop
        · rw [hq_edge_vs] at hx_edge
          rw [List.dropLast_cons_of_ne_nil h_qe_tail_ne] at hx_edge
          rcases List.mem_cons.mp hx_edge with rfl | hx_in_qe_t_d
          · exact Or.inl List.mem_cons_self
          · exact Or.inr (hq_edge_inter x hx_in_qe_t_d)
        · rcases hq_tail_drop_sub x hx_tail_drop with h_p' | h_w
          · exact Or.inl (List.mem_cons.mpr (Or.inr h_p'))
          · exact Or.inr h_w

-- ## Walk projection: given a directed walk in `G` whose target lies
-- outside `W`, find the first non-`W` vertex along the walk (other
-- than the source) and split the walk into a head segment ending at
-- that vertex (length `≥ 1`, intermediates in `W`) and a tail.  Used
-- as the building block of `project_directed_walk_aux` below, which
-- iteratively peels off such head segments to construct the
-- marg-walk.

/-- Find the first non-`W` vertex strictly after the source of a
non-trivial directed walk whose target is outside `W`, and split the
walk at that vertex.  Additionally guarantees that
`p.vertices = head.vertices.dropLast ++ tail.vertices`, i.e.\ the
split factors `p` exactly as a `Walk.comp`. -/
private lemma find_first_non_W_directed {G : CDMG Node} (W : Finset Node) :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → v ∉ W →
      ∃ (m : Node) (head : Walk G u m) (tail : Walk G m v),
        head.IsDirectedWalk ∧ tail.IsDirectedWalk ∧
        head.length ≥ 1 ∧ m ∉ W ∧
        (∀ x ∈ head.vertices.tail.dropLast, x ∈ W) ∧
        head.length + tail.length = p.length ∧
        p.vertices = head.vertices.dropLast ++ tail.vertices := by
  intro u v p
  induction p with
  | nil v hv =>
      intros _ hp_pos _
      simp [Walk.length] at hp_pos
  | @cons u v_end vMid a hStep p' ih =>
      intros hp_dir _ hv_notW
      obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := hp_dir
      by_cases hvMid_W : vMid ∈ W
      · -- vMid ∈ W: recurse on p'
        have hp'_pos : p'.length ≥ 1 := by
          by_contra hp'_nonpos
          have hp'_zero : p'.length = 0 := by omega
          match p', hp'_zero with
          | .nil _ _, _ => exact hv_notW hvMid_W
        obtain ⟨m, head_p', tail, h_head_p'_dir, h_tail_dir, h_head_p'_pos,
                hm_notW, h_head_p'_inter, h_lens, h_p'_eq⟩ :=
          ih hp'_dir hp'_pos hv_notW
        refine ⟨m, Walk.cons vMid a hStep head_p', tail,
                ⟨ha_eq, ha_mem, h_head_p'_dir⟩, h_tail_dir, ?_, hm_notW,
                ?_, ?_, ?_⟩
        · change head_p'.length + 1 ≥ 1; omega
        · -- (cons u a hStep head_p').vertices.tail.dropLast ⊆ W
          intro x hx
          change x ∈ head_p'.vertices.dropLast at hx
          rw [Walk.vertices_eq_head_cons_tail head_p'] at hx
          have h_tail_ne : head_p'.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos head_p' h_head_p'_pos
          rw [List.dropLast_cons_of_ne_nil h_tail_ne] at hx
          rcases List.mem_cons.mp hx with rfl | hx_rest
          · exact hvMid_W
          · exact h_head_p'_inter x hx_rest
        · change head_p'.length + 1 + tail.length = p'.length + 1; omega
        · -- p.vertices = (cons _ _ _ head_p').vertices.dropLast ++ tail.vertices
          -- p.vertices = u :: p'.vertices = u :: (head_p'.vertices.dropLast ++ tail.vertices).
          -- (cons u _ _ head_p').vertices = u :: head_p'.vertices.
          -- Its dropLast = u :: head_p'.vertices.dropLast (since head_p' has length ≥ 1
          -- so head_p'.vertices is non-empty).
          change u :: p'.vertices
                = (u :: head_p'.vertices).dropLast ++ tail.vertices
          have h_hp'_ne : head_p'.vertices ≠ [] := Walk.vertices_ne_nil head_p'
          rw [List.dropLast_cons_of_ne_nil h_hp'_ne]
          rw [List.cons_append]
          rw [h_p'_eq]
      · -- vMid ∉ W: head := single-edge walk to vMid; tail := p'.
        have hvMid_g : vMid ∈ G :=
          Finset.mem_union_right _ (G.hE_subset (ha_eq ▸ ha_mem)).2
        refine ⟨vMid, Walk.cons vMid a hStep (Walk.nil vMid hvMid_g), p',
                ⟨ha_eq, ha_mem, trivial⟩, hp'_dir, by simp [Walk.length],
                hvMid_W, ?_, ?_, ?_⟩
        · intro x hx
          simp [Walk.vertices] at hx
        · change 1 + p'.length = p'.length + 1; omega
        · -- LHS: u :: p'.vertices; RHS: [u] ++ p'.vertices.
          change u :: p'.vertices = [u] ++ p'.vertices
          rfl


/-- Project a directed walk from `G` to the marginalized CDMG, given
both endpoints lie in `G.marginalize W hW`.  Constructed by
strong induction on walk length: iteratively peel off a head segment
from `v₁` to the first non-`W` vertex, witness the corresponding
`marg`-edge via the `Φ_E` predicate, and recurse on the tail.  The
projected walk is shorter than the original (a single `marg`-edge
absorbs an arbitrary `W`-traversal). -/
private lemma project_directed_walk_aux {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.V} :
    ∀ (n : ℕ) {v₁ v₂ : Node} (p : Walk G v₁ v₂),
      p.length ≤ n →
      p.IsDirectedWalk →
      v₁ ∈ G.marginalize W hW →
      v₂ ∈ G.marginalize W hW →
      ∃ (q : Walk (G.marginalize W hW) v₁ v₂), q.IsDirectedWalk := by
  intro n
  induction n with
  | zero =>
      intros v₁ v₂ p hp_len _ hv₁ _
      have hp_zero : p.length = 0 := by omega
      match p, hp_zero with
      | .nil v _, _ => exact ⟨Walk.nil v hv₁, trivial⟩
  | succ k ih =>
      intros v₁ v₂ p hp_len hp_dir hv₁ hv₂
      by_cases hp_zero : p.length = 0
      · match p, hp_zero with
        | .nil v _, _ => exact ⟨Walk.nil v hv₁, trivial⟩
      · have hp_pos : p.length ≥ 1 := Nat.one_le_iff_ne_zero.mpr hp_zero
        have hv₂_notW : v₂ ∉ W := notW_of_mem_marginalize hW hv₂
        obtain ⟨m, head, tail, h_head_dir, h_tail_dir, h_head_pos,
                hm_notW, h_head_inter, h_lens, _⟩ :=
          find_first_non_W_directed W p hp_dir hp_pos hv₂_notW
        -- m ∈ G.V (target of a directed walk of length ≥ 1).
        have hm_V : m ∈ G.V :=
          Walk.target_in_GV_of_directedWalk_pos head h_head_dir h_head_pos
        have hm_marg : m ∈ G.marginalize W hW := by
          change m ∈ G.J ∪ (G.V \ W)
          exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hm_V, hm_notW⟩)
        -- Project the tail.
        have h_tail_len : tail.length ≤ k := by omega
        obtain ⟨q_tail, hq_tail_dir⟩ :=
          ih tail h_tail_len h_tail_dir hm_marg hv₂
        by_cases hv₁_eq_m : v₁ = m
        · -- Self-loop / degenerate case: head is a `v₁ → ... → v₁` cycle
          -- through `W`.  Return `q_tail` directly (with `v₁ = m` on
          -- the type level).
          subst hv₁_eq_m
          exact ⟨q_tail, hq_tail_dir⟩
        · -- v₁ ≠ m: build a single `marg`-edge from v₁ to m, then
          -- prepend to the projected tail.
          have h_edge_marg : (v₁, m) ∈ (G.marginalize W hW).E := by
            change (v₁, m) ∈ ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
                  (fun e => G.MarginalizationΦE W e.1 e.2)
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · refine Finset.mem_product.mpr ⟨hv₁, ?_⟩
              exact Finset.mem_sdiff.mpr ⟨hm_V, hm_notW⟩
            · -- `Φ_E W v₁ m`: the head walk itself witnesses it.
              exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩
          have hStep_marg : (G.marginalize W hW).WalkStep v₁ (v₁, m) m :=
            Or.inl ⟨rfl, Or.inl h_edge_marg⟩
          exact ⟨Walk.cons m (v₁, m) hStep_marg q_tail,
                 ⟨rfl, h_edge_marg, hq_tail_dir⟩⟩


/-- Convenience wrapper: project a directed walk from `G` to
`G.marginalize W hW`, with both endpoints in the marg-carrier. -/
private lemma project_directed_walk_marginalize {G : CDMG Node}
    {W : Finset Node} {hW : W ⊆ G.V}
    {v₁ v₂ : Node} (p : Walk G v₁ v₂) (hp_dir : p.IsDirectedWalk)
    (hv₁ : v₁ ∈ G.marginalize W hW) (hv₂ : v₂ ∈ G.marginalize W hW) :
    ∃ (q : Walk (G.marginalize W hW) v₁ v₂), q.IsDirectedWalk :=
  project_directed_walk_aux (hW := hW) p.length p le_rfl hp_dir hv₁ hv₂


/-- Strengthened projection: project a directed walk in `G` (between
two marg-nodes of `G.marginalize W hW`) to a directed walk
in the same marg, with the additional guarantees:
  - every vertex of the projected walk appears in the original;
  - every vertex of the projected walk's `dropLast` appears in the
    original's `dropLast` (i.e.\ excluding-target sub-list);
  - every vertex of the projected walk's `tail` appears in the
    original's `tail` (i.e.\ excluding-source sub-list).
Used by sub-claim ii(b) `(⟹)`'s end-node uniqueness bookkeeping. -/
private lemma project_directed_walk_with_vertex_subset_aux
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.V} :
    ∀ (n : ℕ) {v₁ v₂ : Node} (p : Walk G v₁ v₂),
      p.length ≤ n →
      p.IsDirectedWalk →
      v₁ ∈ G.marginalize W hW →
      v₂ ∈ G.marginalize W hW →
      ∃ (q : Walk (G.marginalize W hW) v₁ v₂),
        q.IsDirectedWalk ∧
        (∀ x ∈ q.vertices, x ∈ p.vertices) ∧
        (∀ x ∈ q.vertices.dropLast, x ∈ p.vertices.dropLast) ∧
        (∀ x ∈ q.vertices.tail, x ∈ p.vertices.tail) := by
  intro n
  induction n with
  | zero =>
      intros v₁ v₂ p hp_len _ hv₁ _
      have hp_zero : p.length = 0 := by omega
      match p, hp_zero with
      | .nil v _, _ =>
          refine ⟨Walk.nil v hv₁, trivial, ?_, ?_, ?_⟩
          · intro x hx
            change x ∈ [v] at hx
            change x ∈ [v]
            exact hx
          · intro x hx
            change x ∈ ([v] : List Node).dropLast at hx
            simp [List.dropLast] at hx
          · intro x hx
            change x ∈ ([v] : List Node).tail at hx
            simp [List.tail] at hx
  | succ k ih =>
      intros v₁ v₂ p hp_len hp_dir hv₁ hv₂
      by_cases hp_zero : p.length = 0
      · match p, hp_zero with
        | .nil v _, _ =>
            refine ⟨Walk.nil v hv₁, trivial, ?_, ?_, ?_⟩
            · intro x hx
              change x ∈ [v] at hx
              change x ∈ [v]
              exact hx
            · intro x hx
              change x ∈ ([v] : List Node).dropLast at hx
              simp [List.dropLast] at hx
            · intro x hx
              change x ∈ ([v] : List Node).tail at hx
              simp [List.tail] at hx
      · have hp_pos : p.length ≥ 1 := Nat.one_le_iff_ne_zero.mpr hp_zero
        have hv₂_notW : v₂ ∉ W := notW_of_mem_marginalize hW hv₂
        obtain ⟨m, head, tail, h_head_dir, h_tail_dir, h_head_pos,
                hm_notW, h_head_inter, h_lens, h_p_eq⟩ :=
          find_first_non_W_directed W p hp_dir hp_pos hv₂_notW
        have hm_V : m ∈ G.V :=
          Walk.target_in_GV_of_directedWalk_pos head h_head_dir h_head_pos
        have hm_marg : m ∈ G.marginalize W hW := by
          change m ∈ G.J ∪ (G.V \ W)
          exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hm_V, hm_notW⟩)
        have h_tail_len : tail.length ≤ k := by omega
        obtain ⟨q_tail, hq_tail_dir, hq_tail_sub, hq_tail_drop, hq_tail_tail⟩ :=
          ih tail h_tail_len h_tail_dir hm_marg hv₂
        -- Bookkeeping: head.vertices = v₁ :: head.vertices.tail, with
        -- non-empty tail.
        have h_head_drop_ne : head.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos head h_head_pos
        have h_head_vs : head.vertices = v₁ :: head.vertices.tail :=
            Walk.vertices_eq_head_cons_tail head
        have h_v1_in_drop : v₁ ∈ head.vertices.dropLast := by
          rw [h_head_vs]
          rw [List.dropLast_cons_of_ne_nil h_head_drop_ne]
          exact List.mem_cons_self
        have h_head_drop_vs : head.vertices.dropLast =
            v₁ :: head.vertices.tail.dropLast := by
          rw [h_head_vs]
          exact List.dropLast_cons_of_ne_nil h_head_drop_ne
        -- p.vertices.dropLast: derived from p.vertices = head.dropLast ++ tail.
        have h_tail_vs_ne : tail.vertices ≠ [] := Walk.vertices_ne_nil tail
        have h_p_drop : p.vertices.dropLast =
            head.vertices.dropLast ++ tail.vertices.dropLast := by
          rw [h_p_eq]
          exact List.dropLast_append_of_ne_nil h_tail_vs_ne
        have h_p_tail : p.vertices.tail =
            head.vertices.dropLast.tail ++ tail.vertices := by
          rw [h_p_eq, h_head_drop_vs]
          rfl
        by_cases hv₁_eq_m : v₁ = m
        · -- Self-loop case: return `q_tail` directly (with `v₁ = m` on
          -- the type level).
          subst hv₁_eq_m
          refine ⟨q_tail, hq_tail_dir, ?_, ?_, ?_⟩
          · -- q_tail.vertices ⊆ p.vertices.
            intro x hx
            rw [h_p_eq]
            exact List.mem_append.mpr (Or.inr (hq_tail_sub x hx))
          · -- q_tail.vertices.dropLast ⊆ p.vertices.dropLast.
            intro x hx
            rw [h_p_drop]
            exact List.mem_append.mpr (Or.inr (hq_tail_drop x hx))
          · -- q_tail.vertices.tail ⊆ p.vertices.tail.
            intro x hx
            rw [h_p_tail]
            have hx_t : x ∈ tail.vertices.tail := hq_tail_tail x hx
            exact List.mem_append.mpr (Or.inr (List.mem_of_mem_tail hx_t))
        · -- Non-self-loop case: build single marg-edge.
          have h_edge_marg : (v₁, m) ∈ (G.marginalize W hW).E := by
            change (v₁, m) ∈ ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
                  (fun e => G.MarginalizationΦE W e.1 e.2)
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · refine Finset.mem_product.mpr ⟨hv₁, ?_⟩
              exact Finset.mem_sdiff.mpr ⟨hm_V, hm_notW⟩
            · -- `Φ_E W v₁ m`: the head walk itself witnesses it.
              exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩
          have hStep_marg : (G.marginalize W hW).WalkStep v₁ (v₁, m) m :=
            Or.inl ⟨rfl, Or.inl h_edge_marg⟩
          refine ⟨Walk.cons m (v₁, m) hStep_marg q_tail,
                  ⟨rfl, h_edge_marg, hq_tail_dir⟩, ?_, ?_, ?_⟩
          · -- q.vertices ⊆ p.vertices.
            intro x hx
            change x ∈ v₁ :: q_tail.vertices at hx
            rw [h_p_eq]
            rcases List.mem_cons.mp hx with hx_v1 | hx_tail
            · subst hx_v1
              exact List.mem_append.mpr (Or.inl h_v1_in_drop)
            · exact List.mem_append.mpr (Or.inr (hq_tail_sub x hx_tail))
          · -- q.vertices.dropLast ⊆ p.vertices.dropLast.
            -- q.vertices = v₁ :: q_tail.vertices.  q_tail.vertices is non-empty,
            -- so q.vertices.dropLast = v₁ :: q_tail.vertices.dropLast.
            intro x hx
            have h_qt_vs_ne : q_tail.vertices ≠ [] := Walk.vertices_ne_nil q_tail
            change x ∈ (v₁ :: q_tail.vertices).dropLast at hx
            rw [List.dropLast_cons_of_ne_nil h_qt_vs_ne] at hx
            rw [h_p_drop]
            rcases List.mem_cons.mp hx with hx_v1 | hx_qtl
            · subst hx_v1
              exact List.mem_append.mpr (Or.inl h_v1_in_drop)
            · exact List.mem_append.mpr (Or.inr (hq_tail_drop x hx_qtl))
          · -- q.vertices.tail ⊆ p.vertices.tail.
            -- q.vertices = v₁ :: q_tail.vertices.  q.vertices.tail = q_tail.vertices.
            intro x hx
            change x ∈ q_tail.vertices at hx
            rw [h_p_tail]
            -- p.vertices.tail = head.vertices.dropLast.tail ++ tail.vertices.
            -- q_tail.vertices ⊆ tail.vertices ⊆ p.vertices.tail.
            exact List.mem_append.mpr (Or.inr (hq_tail_sub x hx))


/-- Convenience wrapper for the strong projection: project a directed
walk `p : Walk G v₁ v₂` (between marg-nodes of `G.marginalize W hW`)
to a directed walk `q : Walk marg v₁ v₂` with the three vertex-subset
clauses. -/
private lemma project_directed_walk_strong {G : CDMG Node}
    {W : Finset Node} {hW : W ⊆ G.V}
    {v₁ v₂ : Node} (p : Walk G v₁ v₂) (hp_dir : p.IsDirectedWalk)
    (hv₁ : v₁ ∈ G.marginalize W hW) (hv₂ : v₂ ∈ G.marginalize W hW) :
    ∃ (q : Walk (G.marginalize W hW) v₁ v₂),
      q.IsDirectedWalk ∧
      (∀ x ∈ q.vertices, x ∈ p.vertices) ∧
      (∀ x ∈ q.vertices.dropLast, x ∈ p.vertices.dropLast) ∧
      (∀ x ∈ q.vertices.tail, x ∈ p.vertices.tail) :=
  project_directed_walk_with_vertex_subset_aux
    (hW := hW) p.length p le_rfl hp_dir hv₁ hv₂

/-- A walk between distinct endpoints has length `≥ 1`. -/
private lemma Walk.length_pos_of_ne {G : CDMG Node} {u v : Node}
    (p : Walk G u v) (h : u ≠ v) : p.length ≥ 1 := by
  cases p with
  | nil _ _ => exact absurd rfl h
  | cons _ _ _ _ => exact Nat.succ_le_succ (Nat.zero_le _)

-- ## Walk reversal + mkBifurcation infrastructure (verbatim copies
-- of the corresponding `private` declarations in
-- `BifurcationAlternative.lean`, re-declared here because the
-- siblings are `private`).  Used by sub-claim ii(b) `(⟹)` and `(⟸)`
-- to assemble the projected / expanded bifurcation walks.

/-- Reverse a directed walk. -/
private def Walk.reverseDirected {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v), qv.IsDirectedWalk → Walk G v c
  | _, _, .nil w hw, _ => Walk.nil w hw
  | c, _, .cons _ a hStep qv', hqv_dir =>
      (Walk.reverseDirected qv' hqv_dir.2.2).comp
        (Walk.cons c a (Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩)
          (Walk.nil c (WalkStep.source_mem hStep)))

private lemma Walk.length_reverseDirected {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk),
      (Walk.reverseDirected qv hqv_dir).length = qv.length
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ _ _ qv', hqv_dir => by
      change ((Walk.reverseDirected qv' hqv_dir.2.2).comp _).length
            = qv'.length + 1
      rw [Walk.length_comp, Walk.length_reverseDirected qv' hqv_dir.2.2]
      rfl

private lemma Walk.vertices_reverseDirected {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk),
      (Walk.reverseDirected qv hqv_dir).vertices = qv.vertices.reverse
  | _, _, .nil _ _, _ => rfl
  | c, _, .cons vMid _ _ qv', hqv_dir => by
      have ih := Walk.vertices_reverseDirected qv' hqv_dir.2.2
      have h_head : qv'.vertices = vMid :: qv'.vertices.tail :=
        Walk.vertices_eq_head_cons_tail qv'
      change ((Walk.reverseDirected qv' hqv_dir.2.2).comp _).vertices
            = (c :: qv'.vertices).reverse
      rw [Walk.vertices_comp, ih]
      conv_lhs => rw [h_head]
      conv_rhs => rw [h_head]
      simp [Walk.vertices, List.reverse_cons]

/-- The bifurcation-walk constructor. -/
private def Walk.mkBifurcation {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (_hqv_pos : qv.length ≥ 1) (qw : Walk G c w) : Walk G v w :=
  (Walk.reverseDirected qv hqv_dir).comp qw

private lemma Walk.length_mkBifurcation {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1) (qw : Walk G c w) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).length
      = qv.length + qw.length := by
  change ((Walk.reverseDirected qv hqv_dir).comp qw).length
        = qv.length + qw.length
  rw [Walk.length_comp, Walk.length_reverseDirected qv hqv_dir]

private lemma Walk.vertices_mkBifurcation {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1) (qw : Walk G c w) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).vertices
      = qv.vertices.reverse.dropLast ++ qw.vertices := by
  change ((Walk.reverseDirected qv hqv_dir).comp qw).vertices
        = qv.vertices.reverse.dropLast ++ qw.vertices
  rw [Walk.vertices_comp, Walk.vertices_reverseDirected qv hqv_dir]

private lemma Walk.comp_assoc {G : CDMG Node} :
    ∀ {u₁ u₂ u₃ u₄ : Node} (p : Walk G u₁ u₂) (q : Walk G u₂ u₃)
      (r : Walk G u₃ u₄),
      (p.comp q).comp r = p.comp (q.comp r)
  | _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, .cons _ a hStep p, q, r => by
      change Walk.cons _ a hStep ((p.comp q).comp r)
            = Walk.cons _ a hStep (p.comp (q.comp r))
      rw [Walk.comp_assoc p q r]

private lemma Walk.isBifurcationDirectedHinge_cons_backward_of_directed
    {G : CDMG Node} {u v w : Node}
    (a : Node × Node) (h : G.WalkStep u a v) (p : Walk G v w)
    (hp_dir : p.IsDirectedWalk) (ha_eq : a = (v, u)) (ha_mem : a ∈ G.E)
    (hp_nonempty : p.length ≥ 1) :
    (Walk.cons v a h p).IsBifurcationDirectedHingeWithSplit 0 := by
  cases p with
  | nil _ _ => simp [Walk.length] at hp_nonempty
  | cons _ _ _ _ => exact ⟨ha_eq, ha_mem, hp_dir⟩

private lemma Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
    {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
      {w : Node} (rest : Walk G c w) (k : ℕ)
      (_hrest : rest.IsBifurcationDirectedHingeWithSplit k),
      Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv hqv_dir).comp rest) (qv.length + k)
  | _, _, .nil w hw, _, _, rest, k, hrest => by
      simp only [Walk.reverseDirected, Walk.comp, Walk.length, Nat.zero_add]
      exact hrest
  | c, _, .cons vMid a hStep qv', hqv_dir, _, rest, k, hrest => by
      have backStep : G.WalkStep vMid a c :=
        Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩
      have h_cons : Walk.IsBifurcationDirectedHingeWithSplit
          (Walk.cons c a backStep rest) (k + 1) := by
        simp only [Walk.IsBifurcationDirectedHingeWithSplit]
        exact ⟨hqv_dir.1, hqv_dir.2.1, hrest⟩
      have ih := Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
        qv' hqv_dir.2.2 (Walk.cons c a backStep rest) (k + 1) h_cons
      change Walk.IsBifurcationDirectedHingeWithSplit
        (((Walk.reverseDirected qv' hqv_dir.2.2).comp
            (Walk.cons c a backStep
              (Walk.nil c (WalkStep.source_mem hStep)))).comp rest)
        (qv'.length + 1 + k)
      rw [Walk.comp_assoc]
      change Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv' hqv_dir.2.2).comp
          (Walk.cons c a backStep rest))
        (qv'.length + 1 + k)
      have hidx : qv'.length + 1 + k = qv'.length + (k + 1) := by omega
      rw [hidx]
      exact ih

private lemma Walk.isBifurcationDirectedHinge_mkBifurcation
    {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1)
    (qw : Walk G c w) (hqw_dir : qw.IsDirectedWalk)
    (hqw_pos : qw.length ≥ 1) :
    Walk.IsBifurcationDirectedHingeWithSplit
      (Walk.mkBifurcation qv hqv_dir hqv_pos qw) (qv.length - 1) := by
  change Walk.IsBifurcationDirectedHingeWithSplit
    ((Walk.reverseDirected qv hqv_dir).comp qw) (qv.length - 1)
  match qv, hqv_dir, hqv_pos with
  | .nil _ _, _, hpos => simp [Walk.length] at hpos
  | .cons vMid a hStep qv', hqv_dir, _ =>
      have backStep : G.WalkStep vMid a c :=
        Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩
      have h_base : Walk.IsBifurcationDirectedHingeWithSplit
          (Walk.cons c a backStep qw) 0 :=
        Walk.isBifurcationDirectedHinge_cons_backward_of_directed
          a backStep qw hqw_dir hqv_dir.1 hqv_dir.2.1 hqw_pos
      have ih := Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux
        qv' hqv_dir.2.2 (Walk.cons c a backStep qw) 0 h_base
      change Walk.IsBifurcationDirectedHingeWithSplit
        (((Walk.reverseDirected qv' hqv_dir.2.2).comp
            (Walk.cons c a backStep
              (Walk.nil c (WalkStep.source_mem hStep)))).comp qw)
        (qv'.length + 1 - 1)
      rw [Walk.comp_assoc]
      change Walk.IsBifurcationDirectedHingeWithSplit
        ((Walk.reverseDirected qv' hqv_dir.2.2).comp
          (Walk.cons c a backStep qw))
        (qv'.length + 1 - 1)
      have hidx : qv'.length + 1 - 1 = qv'.length + 0 := by omega
      rw [hidx]
      exact ih

-- ## Walk.mkBifurcationBidir: bidirected-hinge bifurcation constructor
--
-- Mirror of `Walk.mkBifurcation` (directed hinge) but with a
-- *bidirected* hinge edge `(vL, vR) ∈ G.L` instead of a directed
-- hinge.  Constructed by composing `reverseDirected L` (the
-- reverse-directed left arm) with a cons-cell carrying the
-- bidirected edge `(vL, vR) ∈ G.L`, followed by the right arm `R`.
-- Used by sub-claim ii(a)'s `(⟹)` direction's Region (H.A) (the
-- bidirected-hinge projection case) and `(⟸)` direction's bidirected
-- hinge expansion case.
--
-- The `L.length ≥ 0` (any length) is admitted — when `L = nil`,
-- `vL = v1` and the walk degenerates to `cons vR (vL, vR) hStep R`,
-- which still satisfies `IsBifurcationWithSplit 0` via the
-- bidirected alternative of the predicate's `cons _ _ _ (cons _ _ _ _),
-- 0` (or `cons _ _ _ (nil _ _), 0`) cases.

/-- Vertex-list re-expression: `L.vertices.reverse.dropLast =
L.vertices.tail.reverse`. -/
private lemma Walk.vertices_reverse_dropLast {G : CDMG Node} {u v : Node}
    (p : Walk G u v) :
    p.vertices.reverse.dropLast = p.vertices.tail.reverse := by
  conv_lhs => rw [Walk.vertices_eq_head_cons_tail p]
  rw [List.reverse_cons]
  exact List.dropLast_concat

/-- The bidirected-hinge bifurcation walk constructor. -/
private def Walk.mkBifurcationBidir {G : CDMG Node} {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2)
    (hLR : (vL, vR) ∈ G.L) : Walk G v1 v2 :=
  (Walk.reverseDirected L hL_dir).comp
    (Walk.cons vR (vL, vR) (Or.inl ⟨rfl, Or.inr hLR⟩) R)

private lemma Walk.length_mkBifurcationBidir
    {G : CDMG Node} {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2) (hLR : (vL, vR) ∈ G.L) :
    (Walk.mkBifurcationBidir L hL_dir R hLR).length
      = L.length + R.length + 1 := by
  change ((Walk.reverseDirected L hL_dir).comp _).length = _
  rw [Walk.length_comp, Walk.length_reverseDirected]
  change L.length + (R.length + 1) = L.length + R.length + 1
  omega

private lemma Walk.vertices_mkBifurcationBidir
    {G : CDMG Node} {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2) (hLR : (vL, vR) ∈ G.L) :
    (Walk.mkBifurcationBidir L hL_dir R hLR).vertices
      = L.vertices.reverse.dropLast ++ (vL :: R.vertices) := by
  change ((Walk.reverseDirected L hL_dir).comp _).vertices = _
  rw [Walk.vertices_comp, Walk.vertices_reverseDirected]
  rfl

/-- Bidirected analog of `Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux`. -/
private lemma Walk.isBifurcationWithSplit_comp_reverseDirected_bidir_aux
    {G : CDMG Node} :
    ∀ {c v : Node} (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
      {w : Node} (rest : Walk G c w) (k : ℕ)
      (_hrest : rest.IsBifurcationWithSplit k),
      Walk.IsBifurcationWithSplit
        ((Walk.reverseDirected qv hqv_dir).comp rest) (qv.length + k)
  | _, _, .nil w hw, _, _, rest, k, hrest => by
      simp only [Walk.reverseDirected, Walk.comp, Walk.length, Nat.zero_add]
      exact hrest
  | c, _, .cons vMid a hStep qv', hqv_dir, _, rest, k, hrest => by
      have backStep : G.WalkStep vMid a c :=
        Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩
      have h_cons : Walk.IsBifurcationWithSplit
          (Walk.cons c a backStep rest) (k + 1) := by
        simp only [Walk.IsBifurcationWithSplit]
        exact ⟨hqv_dir.1, hqv_dir.2.1, hrest⟩
      have ih := Walk.isBifurcationWithSplit_comp_reverseDirected_bidir_aux
        qv' hqv_dir.2.2 (Walk.cons c a backStep rest) (k + 1) h_cons
      change Walk.IsBifurcationWithSplit
        (((Walk.reverseDirected qv' hqv_dir.2.2).comp
            (Walk.cons c a backStep
              (Walk.nil c (WalkStep.source_mem hStep)))).comp rest)
        (qv'.length + 1 + k)
      rw [Walk.comp_assoc]
      change Walk.IsBifurcationWithSplit
        ((Walk.reverseDirected qv' hqv_dir.2.2).comp
          (Walk.cons c a backStep rest))
        (qv'.length + 1 + k)
      have hidx : qv'.length + 1 + k = qv'.length + (k + 1) := by omega
      rw [hidx]
      exact ih

/-- Right-extension: appending a directed walk `D` to the right of a
bifurcation walk `M` preserves the `IsBifurcationWithSplit` predicate
at the same index. -/
private lemma Walk.isBifurcationWithSplit_comp_right_directed
    {G : CDMG Node} :
    ∀ {u v : Node} (M : Walk G u v) (k : ℕ),
      M.IsBifurcationWithSplit k →
      ∀ {w : Node} (D : Walk G v w), D.IsDirectedWalk →
      (M.comp D).IsBifurcationWithSplit k := by
  intro u v M
  induction M with
  | nil _ _ => intro k hM _ _ _; exact hM.elim
  | @cons _u _v_end _vMid _a _hStep M' ih =>
      intro k hM _w D hD
      match k, M', hM, D, hD with
      | 0, .nil _ _, hM, .nil _ _, _ =>
          -- M.comp D = M. Predicate unchanged. (single bidirected edge case)
          exact hM
      | 0, .nil _ _, hM, .cons _ _ _ _, hD =>
          -- M was single bidirected edge; appending cons D makes hinge cons-cons-0.
          exact ⟨Or.inr hM, hD⟩
      | 0, .cons _ _ _ M'', hM, D, hD =>
          -- M had cons-cons-0 hinge structure; appending D extends the right arm.
          obtain ⟨h_alt, h_inner_dir⟩ := hM
          obtain ⟨ha'_eq, ha'_mem, hM''_dir⟩ := h_inner_dir
          have hM''_compD_dir : (M''.comp D).IsDirectedWalk :=
            Walk.isDirectedWalk_comp M'' D hM''_dir hD
          exact ⟨h_alt, ⟨ha'_eq, ha'_mem, hM''_compD_dir⟩⟩
      | k' + 1, _, hM, D, hD =>
          -- M's first edge is part of the left arm; recurse on M'.
          simp only [Walk.IsBifurcationWithSplit] at hM
          obtain ⟨ha_eq, ha_E, h_rec⟩ := hM
          simp only [Walk.comp, Walk.IsBifurcationWithSplit]
          exact ⟨ha_eq, ha_E, ih k' h_rec D hD⟩

/-- `mkBifurcationBidir L hL_dir R hLR` realises `IsBifurcationWithSplit`
at index `L.length` (the position of the bidirected hinge). -/
private lemma Walk.isBifurcationWithSplit_mkBifurcationBidir
    {G : CDMG Node} {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2) (hR_dir : R.IsDirectedWalk)
    (hLR : (vL, vR) ∈ G.L) :
    (Walk.mkBifurcationBidir L hL_dir R hLR).IsBifurcationWithSplit L.length := by
  change Walk.IsBifurcationWithSplit
    ((Walk.reverseDirected L hL_dir).comp _) L.length
  -- The cons-cell with the bidirected hinge at i = 0.
  have h_base : Walk.IsBifurcationWithSplit
      (Walk.cons vR (vL, vR) (Or.inl ⟨rfl, Or.inr hLR⟩) R) 0 := by
    cases R with
    | nil _ _ =>
        -- For nil: predicate is `a = (u, v) ∧ a ∈ G.L`.
        exact ⟨rfl, hLR⟩
    | cons _ _ _ _ =>
        -- For cons: predicate is `(alternatives) ∧ p.IsDirectedWalk`.
        exact ⟨Or.inr ⟨rfl, hLR⟩, hR_dir⟩
  have ih := Walk.isBifurcationWithSplit_comp_reverseDirected_bidir_aux
    L hL_dir _ 0 h_base
  have hidx : L.length + 0 = L.length := by omega
  rw [hidx] at ih
  exact ih

/-- Generic IsBifurcation lemma for `mkBifurcationBidir`.  Mirrors
`Walk.mkBifurcation_isBifurcationSource` but conclusion is the
*sourceless* `IsBifurcation` (since the hinge is bidirected, there
is no source vertex).  Handles both `L.length ≥ 1` and `L = nil`
(degenerate "no left arm" case where `vL = v1`). -/
private lemma Walk.mkBifurcationBidir_isBifurcation
    {G : CDMG Node} {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2) (hR_dir : R.IsDirectedWalk)
    (hLR : (vL, vR) ∈ G.L)
    (hv1v2_ne : v1 ≠ v2)
    (hv1_notin_L_drop : v1 ∉ L.vertices.dropLast)
    (hv1_notin_R : v1 ∉ R.vertices)
    (hv2_notin_L : v2 ∉ L.vertices)
    (hv2_notin_R_drop : v2 ∉ R.vertices.dropLast) :
    (Walk.mkBifurcationBidir L hL_dir R hLR).IsBifurcation := by
  have h_mk_vs := Walk.vertices_mkBifurcationBidir L hL_dir R hLR
  -- Auxiliary: l.reverse.tail = l.dropLast.reverse for any list `l`.
  have h_aux : ∀ (l : List Node), l.reverse.tail = l.dropLast.reverse := by
    intro l
    induction l with
    | nil => rfl
    | cons a rest ih =>
        by_cases h : rest = []
        · subst h; rfl
        · rw [List.reverse_cons, List.dropLast_cons_of_ne_nil h]
          rw [List.reverse_cons]
          rw [List.tail_append_of_ne_nil]
          · rw [ih]
          · intro hr_empty
            exact h (List.reverse_eq_nil_iff.mp hr_empty)
  -- Auxiliary: L.vertices.reverse.dropLast = L.vertices.tail.reverse.
  have h_L_rev_drop : L.vertices.reverse.dropLast = L.vertices.tail.reverse :=
    Walk.vertices_reverse_dropLast L
  -- R.vertices is non-empty (always).
  have h_R_vs_ne : R.vertices ≠ [] := Walk.vertices_ne_nil R
  -- vL is in L.vertices (always — it's the source).
  have h_vL_in_L_vs : vL ∈ L.vertices := Walk.head_mem_vertices L
  refine ⟨hv1v2_ne, ?_, ?_, L.length, ?_⟩
  · -- v1 ∉ walk.vertices.tail.
    intro hv1_in_tail
    rw [h_mk_vs] at hv1_in_tail
    by_cases hL_drop_empty : L.vertices.reverse.dropLast = []
    · -- L is trivial: L = nil, vL = v1.
      rw [hL_drop_empty, List.nil_append] at hv1_in_tail
      -- hv1_in_tail : v1 ∈ (vL :: R.vertices).tail = R.vertices.
      change v1 ∈ R.vertices at hv1_in_tail
      exact hv1_notin_R hv1_in_tail
    · -- L has length ≥ 1.
      rw [List.tail_append_of_ne_nil hL_drop_empty] at hv1_in_tail
      rcases List.mem_append.mp hv1_in_tail with hv1_L_drop_tail | hv1_vL_R
      · -- v1 ∈ L.vertices.reverse.dropLast.tail = L.vertices.tail.dropLast.reverse.
        rw [h_L_rev_drop] at hv1_L_drop_tail
        rw [h_aux] at hv1_L_drop_tail
        have hv1_t_drop : v1 ∈ L.vertices.tail.dropLast :=
          List.mem_reverse.mp hv1_L_drop_tail
        -- L.vertices.tail.dropLast = L.vertices.dropLast.tail (when L.length ≥ 1).
        have h_L_tail_ne : L.vertices.tail ≠ [] := by
          intro h
          apply hL_drop_empty
          rw [h_L_rev_drop, h]; rfl
        have h_t_drop_eq : L.vertices.tail.dropLast = L.vertices.dropLast.tail := by
          rw [Walk.vertices_eq_head_cons_tail L]
          simp only [List.tail_cons]
          rw [List.dropLast_cons_of_ne_nil h_L_tail_ne]
          rfl
        rw [h_t_drop_eq] at hv1_t_drop
        exact hv1_notin_L_drop (List.mem_of_mem_tail hv1_t_drop)
      · -- v1 ∈ vL :: R.vertices.
        rcases List.mem_cons.mp hv1_vL_R with h_v1_eq_vL | hv1_R
        · -- v1 = vL.  Derive vL ∈ L.vertices.dropLast for contradiction.
          have h_L_tail_ne : L.vertices.tail ≠ [] := by
            intro h
            apply hL_drop_empty
            rw [h_L_rev_drop, h]
            rfl
          have hvL_in_drop : vL ∈ L.vertices.dropLast := by
            rw [Walk.vertices_eq_head_cons_tail L]
            rw [List.dropLast_cons_of_ne_nil h_L_tail_ne]
            exact List.mem_cons_self
          exact hv1_notin_L_drop (h_v1_eq_vL ▸ hvL_in_drop)
        · exact hv1_notin_R hv1_R
  · -- v2 ∉ walk.vertices.dropLast.
    intro hv2_in_drop
    rw [h_mk_vs] at hv2_in_drop
    -- walk.vertices.dropLast = L.vertices.reverse.dropLast ++ (vL :: R.vertices).dropLast
    --   (since vL :: R.vertices is non-empty).
    have h_vLR_ne : (vL :: R.vertices) ≠ [] := by simp
    rw [List.dropLast_append_of_ne_nil h_vLR_ne] at hv2_in_drop
    rcases List.mem_append.mp hv2_in_drop with hv2_L_rev | hv2_vLR
    · -- v2 ∈ L.vertices.reverse.dropLast = L.vertices.tail.reverse.
      rw [h_L_rev_drop] at hv2_L_rev
      have hv2_tail : v2 ∈ L.vertices.tail := List.mem_reverse.mp hv2_L_rev
      exact hv2_notin_L (List.mem_of_mem_tail hv2_tail)
    · -- v2 ∈ (vL :: R.vertices).dropLast.
      rw [List.dropLast_cons_of_ne_nil h_R_vs_ne] at hv2_vLR
      rcases List.mem_cons.mp hv2_vLR with rfl | hv2_R_drop
      · -- v2 = vL.  vL ∈ L.vertices, contradicts hv2_notin_L.
        exact hv2_notin_L h_vL_in_L_vs
      · exact hv2_notin_R_drop hv2_R_drop
  · -- IsBifurcationWithSplit at L.length.
    exact Walk.isBifurcationWithSplit_mkBifurcationBidir L hL_dir R hR_dir hLR

-- ## Bifurcation arm extractor (strong version)
--
-- Given a walk `p : Walk G v w` together with
-- `p.IsBifurcationDirectedHingeWithSplit i`, extract the source
-- vertex `c = p.vertices[i + 1]`, a *left arm* `L : Walk G c v` and
-- a *right arm* `R : Walk G c w` together with vertex-membership
-- bounds linking each arm to `p`'s vertex list.  Verbatim copy of
-- `BifurcationAlternative.lean`'s same-named `private` lemma, with
-- *two extra conjuncts* — `L.vertices.dropLast ⊆ p.vertices.tail`
-- and `R.vertices.tail ⊆ p.vertices.dropLast` — that the end-node
-- uniqueness bookkeeping of sub-claims ii(b) and ii(a) needs.

private lemma Walk.exists_arms_of_bifurcation_directed_hinge_strong
    {G : CDMG Node} {v w : Node} (p : Walk G v w) :
    ∀ (i : ℕ), p.IsBifurcationDirectedHingeWithSplit i →
      ∃ (c : Node) (L : Walk G c v) (R : Walk G c w),
        L.IsDirectedWalk ∧ R.IsDirectedWalk ∧
        L.length ≥ 1 ∧ R.length ≥ 1 ∧
        p.vertices[i + 1]? = some c ∧
        (∀ x ∈ L.vertices, x ∈ p.vertices.dropLast) ∧
        (∀ x ∈ R.vertices, x ∈ p.vertices.tail) ∧
        (∀ x ∈ L.vertices.dropLast, x ∈ p.vertices.tail) ∧
        (∀ x ∈ R.vertices.dropLast, x ∈ p.vertices.dropLast) := by
  induction p with
  | nil v hv =>
      intro i h_hinge
      exact h_hinge.elim
  | @cons u w vMid a hStep p' ih =>
      intro i h_hinge
      cases i with
      | zero =>
          cases p' with
          | nil v_p' h_p' =>
              exact h_hinge.elim
          | cons vMid' a' hStep' p'' =>
              have h_unfold :
                  a = (vMid, u) ∧ a ∈ G.E ∧
                    (Walk.cons vMid' a' hStep' p'').IsDirectedWalk :=
                h_hinge
              obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := h_unfold
              have hu_in_G : u ∈ G := WalkStep.source_mem hStep
              let forwardStep : G.WalkStep vMid a u :=
                Or.inl ⟨ha_eq, Or.inl ha_mem⟩
              refine ⟨vMid,
                      Walk.cons u a forwardStep (Walk.nil u hu_in_G),
                      Walk.cons vMid' a' hStep' p'',
                      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact ⟨ha_eq, ha_mem, trivial⟩
              · exact hp'_dir
              · change 0 + 1 ≥ 1; exact Nat.le_refl 1
              · change p''.length + 1 ≥ 1
                exact Nat.succ_le_succ (Nat.zero_le _)
              · rfl
              · intro x hx
                have hxv : x = vMid ∨ x = u := by
                  rcases List.mem_cons.mp hx with rfl | hx2
                  · exact Or.inl rfl
                  · rcases List.mem_cons.mp hx2 with rfl | hx3
                    · exact Or.inr rfl
                    · simp at hx3
                have hp'_ne : (Walk.cons vMid' a' hStep' p'').vertices ≠ [] :=
                  Walk.vertices_ne_nil _
                have hp''_ne : p''.vertices ≠ [] := Walk.vertices_ne_nil _
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp'_ne]
                change x ∈ u :: (vMid :: p''.vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp''_ne]
                rcases hxv with rfl | rfl
                · exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
                · exact List.mem_cons_self
              · intro x hx
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).tail
                exact hx
              · -- L.vertices.dropLast ⊆ p.vertices.tail
                -- L.vertices = [vMid, u]. L.vertices.dropLast = [vMid].
                -- p.vertices.tail = vMid :: p''.vertices.  So vMid is in.
                intro x hx
                change x ∈ ([vMid, u] : List Node).dropLast at hx
                change x ∈ vMid :: p''.vertices
                simp [List.dropLast] at hx
                subst hx
                exact List.mem_cons_self
              · -- R.vertices.dropLast ⊆ p.vertices.dropLast
                -- R.vertices = vMid :: p''.vertices.
                -- R.vertices.dropLast = (vMid :: p''.vertices).dropLast.
                -- p.vertices.dropLast = u :: vMid :: p''.vertices.dropLast.
                intro x hx
                have hp''_ne : p''.vertices ≠ [] := Walk.vertices_ne_nil _
                change x ∈ (vMid :: p''.vertices).dropLast at hx
                rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx
                -- hx : x ∈ vMid :: p''.vertices.dropLast
                have hp'_ne : (Walk.cons vMid' a' hStep' p'').vertices ≠ [] :=
                  Walk.vertices_ne_nil _
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp'_ne]
                change x ∈ u :: (vMid :: p''.vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp''_ne]
                exact List.mem_cons.mpr (Or.inr hx)
      | succ k =>
          cases p' with
          | nil vNil hNil =>
              obtain ⟨_, _, h_rec⟩ := h_hinge
              exact h_rec.elim
          | cons vMid' a' hStep' p'' =>
              obtain ⟨ha_eq, ha_mem, h_rec⟩ := h_hinge
              obtain ⟨c, L', R, hL'_dir, hR_dir, _hL'_pos, hR_pos, h_idx_p',
                      hL'_sub, hR_sub, hL'_drop_sub, hR_drop_sub⟩ :=
                ih k h_rec
              have hu_in_G : u ∈ G := WalkStep.source_mem hStep
              let forwardStep : G.WalkStep vMid a u :=
                Or.inl ⟨ha_eq, Or.inl ha_mem⟩
              let single : Walk G vMid u :=
                Walk.cons u a forwardStep (Walk.nil u hu_in_G)
              have hsingle_dir : single.IsDirectedWalk :=
                ⟨ha_eq, ha_mem, trivial⟩
              -- Vertex-list facts about the composed L_new = L'.comp single.
              have hL_new_vs : (L'.comp single).vertices
                  = L'.vertices.dropLast ++ [vMid, u] := by
                rw [Walk.vertices_comp]; rfl
              -- p'.vertices = (cons vMid' a' hStep' p'').vertices
              --             = vMid :: p''.vertices.
              have hp'_vs : (Walk.cons vMid' a' hStep' p'').vertices
                  = vMid :: p''.vertices := rfl
              have hp'_ne : (Walk.cons vMid' a' hStep' p'').vertices ≠ [] :=
                Walk.vertices_ne_nil _
              have hp''_ne : p''.vertices ≠ [] := Walk.vertices_ne_nil _
              refine ⟨c, L'.comp single, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact Walk.isDirectedWalk_comp L' single hL'_dir hsingle_dir
              · exact hR_dir
              · rw [Walk.length_comp]
                change L'.length + 1 ≥ 1
                exact Nat.succ_le_succ (Nat.zero_le _)
              · exact hR_pos
              · change (u :: (Walk.cons vMid' a' hStep' p'').vertices)[k + 1 + 1]?
                      = some c
                simpa using h_idx_p'
              · -- L_new.vertices ⊆ p.vertices.dropLast
                intro x hx
                rw [hL_new_vs] at hx
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp'_ne]
                change x ∈ u :: (vMid :: p''.vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp''_ne]
                rcases List.mem_append.mp hx with hL'_drop | h_in_tail
                · -- x ∈ L'.vertices.dropLast → x ∈ L'.vertices → x ∈ p'.vertices.dropLast.
                  have hx_L'_vs : x ∈ L'.vertices :=
                    List.mem_of_mem_dropLast hL'_drop
                  have hx_p' : x ∈ (Walk.cons vMid' a' hStep' p'').vertices.dropLast :=
                    hL'_sub x hx_L'_vs
                  rw [hp'_vs] at hx_p'
                  rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx_p'
                  exact List.mem_cons.mpr (Or.inr hx_p')
                · rcases List.mem_cons.mp h_in_tail with rfl | hx_in2
                  · exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
                  · rcases List.mem_cons.mp hx_in2 with rfl | hx_empty
                    · exact List.mem_cons_self
                    · simp at hx_empty
              · -- R.vertices ⊆ p.vertices.tail
                intro x hx
                have hx_p'_tail : x ∈ (Walk.cons vMid' a' hStep' p'').vertices.tail :=
                  hR_sub x hx
                have hx_p' : x ∈ (Walk.cons vMid' a' hStep' p'').vertices :=
                  List.mem_of_mem_tail hx_p'_tail
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).tail
                exact hx_p'
              · -- L_new.vertices.dropLast ⊆ p.vertices.tail
                -- L_new.vertices = L'.vertices.dropLast ++ [vMid, u].
                -- L_new.vertices.dropLast = L'.vertices.dropLast ++ [vMid].
                intro x hx
                have hL_new_drop : (L'.comp single).vertices.dropLast
                    = L'.vertices.dropLast ++ [vMid] := by
                  rw [hL_new_vs]
                  simp [List.dropLast]
                rw [hL_new_drop] at hx
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).tail
                change x ∈ (Walk.cons vMid' a' hStep' p'').vertices
                rw [hp'_vs]
                rcases List.mem_append.mp hx with hL'_drop | h_in_tail
                · -- x ∈ L'.vertices.dropLast → x ∈ p'.vertices.tail (from IH's strong claim).
                  have hx_p'_tail : x ∈ (Walk.cons vMid' a' hStep' p'').vertices.tail :=
                    hL'_drop_sub x hL'_drop
                  exact List.mem_of_mem_tail hx_p'_tail
                · -- x = vMid.
                  rcases List.mem_cons.mp h_in_tail with rfl | hx_empty
                  · exact List.mem_cons_self
                  · simp at hx_empty
              · -- R.vertices.dropLast ⊆ p.vertices.dropLast
                intro x hx
                have hx_p'_drop : x ∈ (Walk.cons vMid' a' hStep' p'').vertices.dropLast :=
                  hR_drop_sub x hx
                rw [hp'_vs] at hx_p'_drop
                rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx_p'_drop
                change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp'_ne]
                change x ∈ u :: (vMid :: p''.vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil hp''_ne]
                exact List.mem_cons.mpr (Or.inr hx_p'_drop)

/-- If a walk `qv : Walk G c v` of length `≥ 1` together with
`qw : Walk G c w` of length `≥ 1` satisfy the end-node uniqueness
conditions, then `mkBifurcation qv qw` realises
`IsBifurcationSource c`. -/
private lemma Walk.mkBifurcation_isBifurcationSource
    {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk) (hqv_pos : qv.length ≥ 1)
    (qw : Walk G c w) (hqw_dir : qw.IsDirectedWalk) (hqw_pos : qw.length ≥ 1)
    (hvw_ne : v ≠ w)
    (hv_qv_drop : v ∉ qv.vertices.dropLast)
    (hv_qw : v ∉ qw.vertices)
    (hw_qv : w ∉ qv.vertices)
    (hw_qw_drop : w ∉ qw.vertices.dropLast) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).IsBifurcationSource c := by
  have h_mk_vs :
      (Walk.mkBifurcation qv hqv_dir hqv_pos qw).vertices
        = qv.vertices.reverse.dropLast ++ qw.vertices :=
    Walk.vertices_mkBifurcation qv hqv_dir hqv_pos qw
  have h_qv_rev_drop : qv.vertices.reverse.dropLast = qv.vertices.tail.reverse :=
    Walk.vertices_reverse_dropLast qv
  -- Non-emptiness of various sub-lists.
  have h_qv_tail_ne : qv.vertices.tail ≠ [] :=
    Walk.tail_vertices_ne_nil_of_pos qv hqv_pos
  have h_qv_rev_drop_ne : qv.vertices.reverse.dropLast ≠ [] := by
    rw [h_qv_rev_drop]
    intro hempty
    apply h_qv_tail_ne
    have : qv.vertices.tail = qv.vertices.tail.reverse.reverse := by
      rw [List.reverse_reverse]
    rw [this, hempty]; rfl
  have h_qw_vs_ne : qw.vertices ≠ [] := Walk.vertices_ne_nil qw
  have h_qw_drop_ne : qw.vertices.dropLast ≠ [] := by
    have h_qw_t_ne : qw.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos qw hqw_pos
    intro hempty
    rw [Walk.vertices_eq_head_cons_tail qw] at hempty
    rw [List.dropLast_cons_of_ne_nil h_qw_t_ne] at hempty
    exact (List.cons_ne_nil _ _) hempty
  refine ⟨hvw_ne, ?_, ?_, ?_⟩
  · -- v ∉ mkBif.vertices.tail.
    intro hv_in_tail
    rw [h_mk_vs] at hv_in_tail
    rw [List.tail_append_of_ne_nil h_qv_rev_drop_ne] at hv_in_tail
    rcases List.mem_append.mp hv_in_tail with hv_qv | hv_qw'
    · -- v ∈ qv.vertices.reverse.dropLast.tail.
      rw [h_qv_rev_drop] at hv_qv
      -- v ∈ qv.vertices.tail.reverse.tail.
      -- Identity: l.reverse.tail = l.dropLast.reverse.
      have h_aux : ∀ (l : List Node), l.reverse.tail = l.dropLast.reverse := by
        intro l
        induction l with
        | nil => rfl
        | cons a rest ih =>
            by_cases h : rest = []
            · subst h; rfl
            · rw [List.reverse_cons, List.dropLast_cons_of_ne_nil h]
              rw [List.reverse_cons]
              rw [List.tail_append_of_ne_nil]
              · rw [ih]
              · intro hr_empty
                exact h (List.reverse_eq_nil_iff.mp hr_empty)
      have h_t_rev_t : qv.vertices.tail.reverse.tail
          = qv.vertices.tail.dropLast.reverse :=
        h_aux qv.vertices.tail
      rw [h_t_rev_t] at hv_qv
      have hv_t_drop : v ∈ qv.vertices.tail.dropLast := List.mem_reverse.mp hv_qv
      -- qv.vertices.tail.dropLast ⊆ qv.vertices.dropLast (via List.mem_of_mem_tail etc.).
      have h_t_drop_eq : qv.vertices.tail.dropLast = qv.vertices.dropLast.tail := by
        rw [Walk.vertices_eq_head_cons_tail qv]
        simp only [List.tail_cons]
        rw [List.dropLast_cons_of_ne_nil h_qv_tail_ne]
        rfl
      rw [h_t_drop_eq] at hv_t_drop
      exact hv_qv_drop (List.mem_of_mem_tail hv_t_drop)
    · exact hv_qw hv_qw'
  · -- w ∉ mkBif.vertices.dropLast.
    intro hw_in_drop
    rw [h_mk_vs] at hw_in_drop
    rw [List.dropLast_append_of_ne_nil h_qw_vs_ne] at hw_in_drop
    rcases List.mem_append.mp hw_in_drop with hw_qv' | hw_qw_d
    · -- w ∈ qv.vertices.reverse.dropLast.
      rw [h_qv_rev_drop] at hw_qv'
      have hw_t : w ∈ qv.vertices.tail := List.mem_reverse.mp hw_qv'
      exact hw_qv (List.mem_of_mem_tail hw_t)
    · exact hw_qw_drop hw_qw_d
  · -- ∃ i, IsBifurcationDirectedHinge ∧ vertices[i+1]? = some c.
    refine ⟨qv.length - 1, ?_, ?_⟩
    · exact Walk.isBifurcationDirectedHinge_mkBifurcation
        qv hqv_dir hqv_pos qw hqw_dir hqw_pos
    · rw [h_mk_vs]
      have h_idx : qv.length - 1 + 1 = qv.length := by omega
      rw [h_idx]
      -- mkBif.vertices[qv.length]? = (qv.vertices.reverse.dropLast ++ qw.vertices)[qv.length]?
      -- qv.vertices.reverse.dropLast has length qv.length.
      have h_rev_drop_len :
          qv.vertices.reverse.dropLast.length = qv.length := by
        rw [h_qv_rev_drop]
        rw [List.length_reverse]
        rw [Walk.vertices_eq_head_cons_tail qv]
        simp only [List.tail_cons]
        -- length qv.vertices.tail. qv.vertices = c :: tail, so length = 1 + tail.length.
        -- qv.length + 1 = qv.vertices.length = 1 + qv.vertices.tail.length.
        have h_len : qv.vertices.length = qv.length + 1 := by
          clear * -
          induction qv with
          | nil _ _ => simp [Walk.vertices, Walk.length]
          | @cons _ _ _ _ _ p' ih => simp [Walk.vertices, Walk.length]; omega
        rw [Walk.vertices_eq_head_cons_tail qv] at h_len
        simp only [List.length_cons] at h_len
        omega
      rw [List.getElem?_append_right (by omega), h_rev_drop_len]
      simp
      rw [Walk.vertices_eq_head_cons_tail qw]
      simp

-- ## Helpers for sub-claim ii(a): hinge type conversion + bidirected arm extractor.

/-- A directed-hinge bifurcation walk is also a (generic, sourceless)
bifurcation walk at the same split index. -/
private lemma Walk.isBifurcationDirectedHingeWithSplit_to_isBifurcationWithSplit
    {G : CDMG Node} {u v : Node} :
    ∀ (p : Walk G u v) (i : ℕ),
      p.IsBifurcationDirectedHingeWithSplit i → p.IsBifurcationWithSplit i := by
  intro p
  induction p with
  | nil _ _ => intro i h; exact h
  | @cons u w vMid a hStep p' ih =>
      intro i h
      cases i with
      | zero =>
          cases p' with
          | nil _ _ => exact h.elim
          | cons _ _ _ _ =>
              obtain ⟨ha_eq, ha_E, hp_dir⟩ := h
              exact ⟨Or.inl ⟨ha_eq, ha_E⟩, hp_dir⟩
      | succ k =>
          simp only [Walk.IsBifurcationDirectedHingeWithSplit] at h
          obtain ⟨ha_eq, ha_E, h_rest⟩ := h
          simp only [Walk.IsBifurcationWithSplit]
          exact ⟨ha_eq, ha_E, ih k h_rest⟩

/-- `IsBifurcationSource` implies `IsBifurcation`: just drop the
source-tracking conjunct. -/
private lemma Walk.isBifurcationSource_to_isBifurcation
    {G : CDMG Node} {u v : Node} (p : Walk G u v) (c : Node)
    (h : p.IsBifurcationSource c) : p.IsBifurcation := by
  obtain ⟨huv_ne, hu_tail, hv_drop, i, hh_dir, _⟩ := h
  refine ⟨huv_ne, hu_tail, hv_drop, i, ?_⟩
  exact Walk.isBifurcationDirectedHingeWithSplit_to_isBifurcationWithSplit p i hh_dir

/-- A single bidirected edge `(u, v) ∈ G.L` gives a length-1 walk
`u → v` whose `IsBifurcation` predicate is satisfied (the `n = 1`
direct bidirected edge boundary case of `def_3_4` item~vi). -/
private lemma Walk.singleEdge_isBifurcation_of_bidir {G : CDMG Node}
    {u v : Node} (hu : u ∈ G) (hv : v ∈ G)
    (hLR : (u, v) ∈ G.L) (huv : u ≠ v) :
    let hStep : G.WalkStep u (u, v) v := Or.inl ⟨rfl, Or.inr hLR⟩
    (Walk.cons v (u, v) hStep (Walk.nil v hv)).IsBifurcation := by
  refine ⟨huv, ?_, ?_, 0, ?_⟩
  · intro h_in_tail
    change u ∈ [v] at h_in_tail
    rw [List.mem_singleton] at h_in_tail
    exact huv h_in_tail
  · intro h_in_drop
    change v ∈ ([u, v] : List Node).dropLast at h_in_drop
    simp [List.dropLast] at h_in_drop
    exact huv.symm h_in_drop
  · -- IsBifurcationWithSplit 0: `cons _ _ _ (nil _ _), 0` case requires
    -- `a = (u, v) ∧ a ∈ G.L`.
    exact ⟨rfl, hLR⟩

/-- Bidirected arm extractor (sourceless mirror of
`Walk.exists_arms_of_bifurcation_directed_hinge_strong`).  Given a walk
`p : Walk G v w` together with `IsBifurcationWithSplit i` AND
`¬ IsBifurcationDirectedHingeWithSplit i`, extract the *bidirected*
hinge endpoints `vL = p.vertices[i]` and `vR = p.vertices[i+1]`,
together with the left arm `L : Walk G vL v` (directed, possibly
length 0) and the right arm `R : Walk G vR w` (directed, possibly
length 0).  The hinge edge `(vL, vR) ∈ G.L`. -/
private lemma Walk.exists_arms_of_bifurcation_bidir_hinge_strong
    {G : CDMG Node} {v w : Node} (p : Walk G v w) :
    ∀ (i : ℕ), p.IsBifurcationWithSplit i →
      ¬ p.IsBifurcationDirectedHingeWithSplit i →
      ∃ (vL vR : Node) (L : Walk G vL v) (R : Walk G vR w),
        L.IsDirectedWalk ∧ R.IsDirectedWalk ∧
        (vL, vR) ∈ G.L ∧
        p.vertices[i + 1]? = some vR ∧
        (∀ x ∈ L.vertices, x ∈ p.vertices.dropLast) ∧
        (∀ x ∈ R.vertices, x ∈ p.vertices.tail) ∧
        (∀ x ∈ L.vertices.dropLast, x ∈ p.vertices.tail) ∧
        (∀ x ∈ R.vertices.dropLast, x ∈ p.vertices.dropLast) := by
  induction p with
  | nil _ _ =>
      intro i h_bif _
      exact h_bif.elim
  | @cons u w vMid a hStep p' ih =>
      intro i h_bif h_not_dir
      -- Use term-mode `match` on p' (and h_bif, h_not_dir) to avoid the
      -- `cases` tactic's name-scoping issues with dependent constructors.
      match i, p', h_bif, h_not_dir with
      | 0, .nil v_nil hv_nil, h_bif, _ =>
          -- n=1 bidirected single edge case.
          -- h_bif : a = (u, v_nil) ∧ a ∈ G.L.
          obtain ⟨ha_eq, ha_L⟩ := h_bif
          have hu_g : u ∈ G := WalkStep.source_mem hStep
          have hv_nil_V : v_nil ∈ G.V := (G.hL_subset (ha_eq ▸ ha_L)).2
          have hv_nil_g : v_nil ∈ G := Finset.mem_union_right _ hv_nil_V
          refine ⟨u, v_nil, Walk.nil u hu_g, Walk.nil v_nil hv_nil_g,
                  trivial, trivial, ha_eq ▸ ha_L, ?_, ?_, ?_, ?_, ?_⟩
          · -- p.vertices[1]? = some v_nil.  p.vertices = [u, v_nil].
            rfl
          · -- L.vertices = [u] ⊆ p.vertices.dropLast = [u].
            intro x hx
            change x ∈ [u] at hx
            rw [List.mem_singleton] at hx
            rw [hx]
            change u ∈ ([u, v_nil] : List Node).dropLast
            simp [List.dropLast]
          · -- R.vertices = [v_nil] ⊆ p.vertices.tail = [v_nil].
            intro x hx
            change x ∈ [v_nil] at hx
            rw [List.mem_singleton] at hx
            rw [hx]
            change v_nil ∈ ([u, v_nil] : List Node).tail
            simp [List.tail]
          · -- L.vertices.dropLast = [].dropLast = [], vacuously ⊆.
            intro x hx
            change x ∈ ([u] : List Node).dropLast at hx
            simp [List.dropLast] at hx
          · -- R.vertices.dropLast = [].dropLast = [], vacuously ⊆.
            intro x hx
            change x ∈ ([v_nil] : List Node).dropLast at hx
            simp [List.dropLast] at hx
      | 0, .cons vMid' a' hStep' p'', h_bif, h_not_dir =>
          -- n≥2 case, hinge at index 0.
          -- h_bif : ((a = (vMid, u) ∧ a ∈ G.E) ∨ (a = (u, vMid) ∧ a ∈ G.L))
          --         ∧ (cons vMid' a' hStep' p'').IsDirectedWalk.
          obtain ⟨h_alt, hp'_dir⟩ := h_bif
          have h_bidir : a = (u, vMid) ∧ a ∈ G.L := by
            rcases h_alt with h_E | h_L
            · exfalso
              apply h_not_dir
              exact ⟨h_E.1, h_E.2, hp'_dir⟩
            · exact h_L
          obtain ⟨ha_eq, ha_L⟩ := h_bidir
          have hu_g : u ∈ G := WalkStep.source_mem hStep
          have hvMid_V : vMid ∈ G.V := (G.hL_subset (ha_eq ▸ ha_L)).2
          have hvMid_g : vMid ∈ G := Finset.mem_union_right _ hvMid_V
          refine ⟨u, vMid, Walk.nil u hu_g, Walk.cons vMid' a' hStep' p'',
                  trivial, hp'_dir, ha_eq ▸ ha_L, ?_, ?_, ?_, ?_, ?_⟩
          · -- p.vertices[1]? = some vMid.
            rfl
          · -- L.vertices = [u] ⊆ p.vertices.dropLast.
            intro x hx
            change x ∈ [u] at hx
            rw [List.mem_singleton] at hx
            rw [hx]
            have hp'_ne : (Walk.cons vMid' a' hStep' p'').vertices ≠ [] :=
              Walk.vertices_ne_nil _
            change u ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).dropLast
            rw [List.dropLast_cons_of_ne_nil hp'_ne]
            exact List.mem_cons_self
          · -- R.vertices ⊆ p.vertices.tail = (cons ...).vertices.
            intro x hx
            change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).tail
            exact hx
          · -- L.vertices.dropLast = [].dropLast = [], vacuously ⊆.
            intro x hx
            change x ∈ ([u] : List Node).dropLast at hx
            simp [List.dropLast] at hx
          · -- R.vertices.dropLast ⊆ p.vertices.dropLast.
            intro x hx
            have hp''_ne : p''.vertices ≠ [] := Walk.vertices_ne_nil _
            change x ∈ (vMid :: p''.vertices).dropLast at hx
            rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx
            have hp'_ne : (Walk.cons vMid' a' hStep' p'').vertices ≠ [] :=
              Walk.vertices_ne_nil _
            change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).dropLast
            rw [List.dropLast_cons_of_ne_nil hp'_ne]
            change x ∈ u :: (vMid :: p''.vertices).dropLast
            rw [List.dropLast_cons_of_ne_nil hp''_ne]
            exact List.mem_cons.mpr (Or.inr hx)
      | k+1, .nil _ _, h_bif, _ =>
          -- p'.IsBifurcationWithSplit k = nil.IsBifurcationWithSplit k = False.
          obtain ⟨_, _, h_rec⟩ := h_bif
          exact h_rec.elim
      | k+1, .cons vMid' a' hStep' p'', h_bif, h_not_dir =>
          -- h_bif : a = (vMid, u) ∧ a ∈ G.E ∧ p'.IsBifurcationWithSplit k.
          obtain ⟨ha_eq, ha_E, h_rec⟩ := h_bif
          -- Recurse on p' with index k.
          -- For ¬ DirectedHinge at succ k: the predicate reduces to
          --   a = (vMid, u) ∧ a ∈ G.E ∧ p'.IsBifurcationDirectedHingeWithSplit k.
          -- We need to derive ¬ p'.IsBifurcationDirectedHingeWithSplit k.
          have h_rec_not_dir :
              ¬ (Walk.cons vMid' a' hStep' p'').IsBifurcationDirectedHingeWithSplit k := by
            intro h_dir_rec
            apply h_not_dir
            exact ⟨ha_eq, ha_E, h_dir_rec⟩
          obtain ⟨vL, vR, L', R, hL'_dir, hR_dir, hLR_L, h_idx_p',
                  hL'_sub, hR_sub, hL'_drop_sub, hR_drop_sub⟩ :=
            ih k h_rec h_rec_not_dir
          -- Build L = L'.comp (single forward edge from vMid to u).
          have hu_in_G : u ∈ G := WalkStep.source_mem hStep
          let forwardStep : G.WalkStep vMid a u :=
            Or.inl ⟨ha_eq, Or.inl ha_E⟩
          let single : Walk G vMid u :=
            Walk.cons u a forwardStep (Walk.nil u hu_in_G)
          have hsingle_dir : single.IsDirectedWalk :=
            ⟨ha_eq, ha_E, trivial⟩
          have hL_new_vs : (L'.comp single).vertices
              = L'.vertices.dropLast ++ [vMid, u] := by
            rw [Walk.vertices_comp]; rfl
          have hp'_vs : (Walk.cons vMid' a' hStep' p'').vertices
              = vMid :: p''.vertices := rfl
          have hp'_ne : (Walk.cons vMid' a' hStep' p'').vertices ≠ [] :=
            Walk.vertices_ne_nil _
          have hp''_ne : p''.vertices ≠ [] := Walk.vertices_ne_nil _
          refine ⟨vL, vR, L'.comp single, R, ?_, hR_dir, hLR_L, ?_, ?_, ?_, ?_, ?_⟩
          · exact Walk.isDirectedWalk_comp L' single hL'_dir hsingle_dir
          · -- p.vertices[k+1+1]? = some vR.
            change (u :: (Walk.cons vMid' a' hStep' p'').vertices)[k + 1 + 1]?
                  = some vR
            simpa using h_idx_p'
          · -- L_new.vertices ⊆ p.vertices.dropLast.
            intro x hx
            rw [hL_new_vs] at hx
            change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).dropLast
            rw [List.dropLast_cons_of_ne_nil hp'_ne]
            change x ∈ u :: (vMid :: p''.vertices).dropLast
            rw [List.dropLast_cons_of_ne_nil hp''_ne]
            rcases List.mem_append.mp hx with hL'_drop | h_in_tail
            · have hx_L'_vs : x ∈ L'.vertices :=
                List.mem_of_mem_dropLast hL'_drop
              have hx_p' : x ∈ (Walk.cons vMid' a' hStep' p'').vertices.dropLast :=
                hL'_sub x hx_L'_vs
              rw [hp'_vs] at hx_p'
              rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx_p'
              exact List.mem_cons.mpr (Or.inr hx_p')
            · rcases List.mem_cons.mp h_in_tail with rfl | hx_in2
              · exact List.mem_cons.mpr (Or.inr List.mem_cons_self)
              · rcases List.mem_cons.mp hx_in2 with rfl | hx_empty
                · exact List.mem_cons_self
                · simp at hx_empty
          · -- R.vertices ⊆ p.vertices.tail.
            intro x hx
            have hx_p'_tail : x ∈ (Walk.cons vMid' a' hStep' p'').vertices.tail :=
              hR_sub x hx
            have hx_p' : x ∈ (Walk.cons vMid' a' hStep' p'').vertices :=
              List.mem_of_mem_tail hx_p'_tail
            change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).tail
            exact hx_p'
          · -- L_new.vertices.dropLast ⊆ p.vertices.tail.
            intro x hx
            have hL_new_drop : (L'.comp single).vertices.dropLast
                = L'.vertices.dropLast ++ [vMid] := by
              rw [hL_new_vs]
              simp [List.dropLast]
            rw [hL_new_drop] at hx
            change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).tail
            change x ∈ (Walk.cons vMid' a' hStep' p'').vertices
            rw [hp'_vs]
            rcases List.mem_append.mp hx with hL'_drop | h_in_tail
            · have hx_p'_tail : x ∈ (Walk.cons vMid' a' hStep' p'').vertices.tail :=
                hL'_drop_sub x hL'_drop
              exact List.mem_of_mem_tail hx_p'_tail
            · rcases List.mem_cons.mp h_in_tail with rfl | hx_empty
              · exact List.mem_cons_self
              · simp at hx_empty
          · -- R.vertices.dropLast ⊆ p.vertices.dropLast.
            intro x hx
            have hx_p'_drop : x ∈ (Walk.cons vMid' a' hStep' p'').vertices.dropLast :=
              hR_drop_sub x hx
            rw [hp'_vs] at hx_p'_drop
            rw [List.dropLast_cons_of_ne_nil hp''_ne] at hx_p'_drop
            change x ∈ (u :: (Walk.cons vMid' a' hStep' p'').vertices).dropLast
            rw [List.dropLast_cons_of_ne_nil hp'_ne]
            change x ∈ u :: (vMid :: p''.vertices).dropLast
            rw [List.dropLast_cons_of_ne_nil hp''_ne]
            exact List.mem_cons.mpr (Or.inr hx_p'_drop)

-- ## Helper: forward direction of sub-claim ii(b) for one orientation.


private lemma marg_preserves_bifSource_forward (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.V) {u w v₃ : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (hv₃ : v₃ ∈ G.marginalize W hW)
    (h : ∃ p : Walk G u w, p.IsBifurcationSource v₃) :
    ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcationSource v₃ := by
  obtain ⟨p, hp_src⟩ := h
  obtain ⟨huw_ne, hu_tail, hw_drop, i, hhinge, hsrc⟩ := hp_src
  obtain ⟨c, L, R, hL_dir, hR_dir, hL_pos, hR_pos, hidx,
          hL_sub, hR_sub, hL_drop_sub, hR_drop_sub⟩ :=
    Walk.exists_arms_of_bifurcation_directed_hinge_strong p i hhinge
  have hc_eq_v3 : c = v₃ := by
    rw [hidx] at hsrc
    exact Option.some.inj hsrc
  -- v₃ ≠ u via L.vertices.dropLast ⊆ p.vertices.tail + hu_tail.
  have hv3_ne_u : v₃ ≠ u := by
    intro heq
    have h_c_drop : c ∈ L.vertices.dropLast := by
      have hL_vs : L.vertices = c :: L.vertices.tail :=
        Walk.vertices_eq_head_cons_tail L
      have h_t_ne : L.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L hL_pos
      rw [hL_vs]
      rw [List.dropLast_cons_of_ne_nil h_t_ne]
      exact List.mem_cons_self
    have h_c_p_tail : c ∈ p.vertices.tail := hL_drop_sub c h_c_drop
    have hc_eq_u : c = u := hc_eq_v3.trans heq
    exact hu_tail (hc_eq_u ▸ h_c_p_tail)
  have hv3_ne_w : v₃ ≠ w := by
    intro heq
    have h_c_drop : c ∈ R.vertices.dropLast := by
      have hR_vs : R.vertices = c :: R.vertices.tail :=
        Walk.vertices_eq_head_cons_tail R
      have h_t_ne : R.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R hR_pos
      rw [hR_vs]
      rw [List.dropLast_cons_of_ne_nil h_t_ne]
      exact List.mem_cons_self
    have h_c_p_drop : c ∈ p.vertices.dropLast := hR_drop_sub c h_c_drop
    have hc_eq_w : c = w := hc_eq_v3.trans heq
    exact hw_drop (hc_eq_w ▸ h_c_p_drop)
  have hc_marg : c ∈ G.marginalize W hW := hc_eq_v3 ▸ hv₃
  obtain ⟨L', hL'_dir, hL'_sub, hL'_drop, _⟩ :=
    project_directed_walk_strong L hL_dir hc_marg hu
  obtain ⟨R', hR'_dir, hR'_sub, hR'_drop, _⟩ :=
    project_directed_walk_strong R hR_dir hc_marg hw
  have hL'_pos : L'.length ≥ 1 :=
    Walk.length_pos_of_ne L' (hc_eq_v3 ▸ hv3_ne_u)
  have hR'_pos : R'.length ≥ 1 :=
    Walk.length_pos_of_ne R' (hc_eq_v3 ▸ hv3_ne_w)
  -- Verify the four vertex-bound conditions for the generic mkBif lemma.
  have hu_notin_L'_drop : u ∉ L'.vertices.dropLast := fun h_u =>
    hu_tail (hL_drop_sub u (hL'_drop u h_u))
  have hu_notin_R' : u ∉ R'.vertices := fun h_u =>
    hu_tail (hR_sub u (hR'_sub u h_u))
  have hw_notin_L' : w ∉ L'.vertices := fun h_w =>
    hw_drop (hL_sub w (hL'_sub w h_w))
  have hw_notin_R'_drop : w ∉ R'.vertices.dropLast := fun h_w =>
    hw_drop (hR_drop_sub w (hR'_drop w h_w))
  refine ⟨Walk.mkBifurcation L' hL'_dir hL'_pos R', ?_⟩
  have h_bif_src :=
    Walk.mkBifurcation_isBifurcationSource L' hL'_dir hL'_pos R' hR'_dir hR'_pos
      huw_ne hu_notin_L'_drop hu_notin_R' hw_notin_L' hw_notin_R'_drop
  exact hc_eq_v3 ▸ h_bif_src

-- ## Helper: backward direction of sub-claim ii(b) for one orientation.


private lemma marg_preserves_bifSource_backward (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.V) {u w v₃ : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (hv₃ : v₃ ∈ G.marginalize W hW)
    (h : ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcationSource v₃) :
    ∃ p : Walk G u w, p.IsBifurcationSource v₃ := by
  obtain ⟨q, hq_src⟩ := h
  obtain ⟨huw_ne, hu_tail, hw_drop, i, hhinge, hsrc⟩ := hq_src
  obtain ⟨c, Lq, Rq, hLq_dir, hRq_dir, hLq_pos, hRq_pos, hidx,
          hLq_sub, hRq_sub, hLq_drop_sub, hRq_drop_sub⟩ :=
    Walk.exists_arms_of_bifurcation_directed_hinge_strong q i hhinge
  have hc_eq_v3 : c = v₃ := by
    rw [hidx] at hsrc
    exact Option.some.inj hsrc
  -- v₃ ≠ u, v₃ ≠ w (analogous to forward direction).
  have hv3_ne_u : v₃ ≠ u := by
    intro heq
    have h_c_drop : c ∈ Lq.vertices.dropLast := by
      have hLq_vs : Lq.vertices = c :: Lq.vertices.tail :=
        Walk.vertices_eq_head_cons_tail Lq
      have h_t_ne : Lq.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos Lq hLq_pos
      rw [hLq_vs]
      rw [List.dropLast_cons_of_ne_nil h_t_ne]
      exact List.mem_cons_self
    have h_c_q_tail : c ∈ q.vertices.tail := hLq_drop_sub c h_c_drop
    have hc_eq_u : c = u := hc_eq_v3.trans heq
    exact hu_tail (hc_eq_u ▸ h_c_q_tail)
  have hv3_ne_w : v₃ ≠ w := by
    intro heq
    have h_c_drop : c ∈ Rq.vertices.dropLast := by
      have hRq_vs : Rq.vertices = c :: Rq.vertices.tail :=
        Walk.vertices_eq_head_cons_tail Rq
      have h_t_ne : Rq.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos Rq hRq_pos
      rw [hRq_vs]
      rw [List.dropLast_cons_of_ne_nil h_t_ne]
      exact List.mem_cons_self
    have h_c_q_drop : c ∈ q.vertices.dropLast := hRq_drop_sub c h_c_drop
    have hc_eq_w : c = w := hc_eq_v3.trans heq
    exact hw_drop (hc_eq_w ▸ h_c_q_drop)
  -- Expand Lq and Rq to walks in G.
  obtain ⟨L, hL_dir, hL_len, hL_sub_W, hL_drop_sub_W⟩ :=
    expand_directed_walk_marginalize Lq hLq_dir
  obtain ⟨R, hR_dir, hR_len, hR_sub_W, hR_drop_sub_W⟩ :=
    expand_directed_walk_marginalize Rq hRq_dir
  have hL_pos : L.length ≥ 1 := by omega
  have hR_pos : R.length ≥ 1 := by omega
  -- Auxiliary: c ∉ W (since c = v₃ ∈ marg).
  have hc_notW : c ∉ W := by
    rw [hc_eq_v3]
    exact notW_of_mem_marginalize hW hv₃
  have hu_notW : u ∉ W := notW_of_mem_marginalize hW hu
  have hw_notW : w ∉ W := notW_of_mem_marginalize hW hw
  -- Verify the four conditions.
  have hu_notin_L_drop : u ∉ L.vertices.dropLast := by
    intro h_u
    rcases hL_drop_sub_W u h_u with h_Lq_drop | h_u_W
    · -- u ∈ Lq.vertices.dropLast → u ∈ q.vertices.tail. But u ∉ q.vertices.tail.
      exact hu_tail (hLq_drop_sub u h_Lq_drop)
    · exact hu_notW h_u_W
  have hu_notin_R : u ∉ R.vertices := by
    intro h_u
    rcases hR_sub_W u h_u with h_Rq | h_u_W
    · -- u ∈ Rq.vertices → u ∈ q.vertices.tail.
      exact hu_tail (hRq_sub u h_Rq)
    · exact hu_notW h_u_W
  have hw_notin_L : w ∉ L.vertices := by
    intro h_w
    rcases hL_sub_W w h_w with h_Lq | h_w_W
    · exact hw_drop (hLq_sub w h_Lq)
    · exact hw_notW h_w_W
  have hw_notin_R_drop : w ∉ R.vertices.dropLast := by
    intro h_w
    rcases hR_drop_sub_W w h_w with h_Rq_drop | h_w_W
    · exact hw_drop (hRq_drop_sub w h_Rq_drop)
    · exact hw_notW h_w_W
  refine ⟨Walk.mkBifurcation L hL_dir hL_pos R, ?_⟩
  have h_bif_src :=
    Walk.mkBifurcation_isBifurcationSource L hL_dir hL_pos R hR_dir hR_pos
      huw_ne hu_notin_L_drop hu_notin_R hw_notin_L hw_notin_R_drop
  exact hc_eq_v3 ▸ h_bif_src

-- ## Helper: forward direction — directed-hinge with source in marg.
--
-- Sub-case (H.B) of the TeX proof: the directed hinge's source lies
-- outside W (so in marg).  Reduces to sub-claim ii(b)'s forward helper
-- followed by the conversion `IsBifurcationSource → IsBifurcation`.

private lemma marg_bif_forward_dir_hinge_src_marg
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {p : Walk G u w} (hp : p.IsBifurcation)
    {i : ℕ} (h_dir : p.IsBifurcationDirectedHingeWithSplit i)
    {c : Node} (hidx : p.vertices[i + 1]? = some c)
    (hc_marg : c ∈ G.marginalize W hW) :
    ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hp
  have hp_src : p.IsBifurcationSource c :=
    ⟨huw_ne, hu_tail, hw_drop, i, h_dir, hidx⟩
  obtain ⟨q, hq_src⟩ :=
    marg_preserves_bifSource_forward G W hW hu hw hc_marg ⟨p, hp_src⟩
  exact ⟨q, Walk.isBifurcationSource_to_isBifurcation q c hq_src⟩

-- ## Helper: backward direction — directed-hinge marg-bifurcation.
--
-- Any directed-hinge marg-bifurcation has its source automatically in
-- marg (since the source is a vertex of the marg walk and all vertices
-- of a marg walk lie in marg).  Reduces to sub-claim ii(b)'s backward
-- helper followed by the conversion `IsBifurcationSource → IsBifurcation`.

private lemma marg_bif_backward_dir_hinge
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {q : Walk (G.marginalize W hW) u w} (hq : q.IsBifurcation)
    {i : ℕ} (h_dir : q.IsBifurcationDirectedHingeWithSplit i) :
    ∃ p : Walk G u w, p.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hq
  obtain ⟨c, _, _, _, _, _, _, hidx, _, _, _, _⟩ :=
    Walk.exists_arms_of_bifurcation_directed_hinge_strong q i h_dir
  have hc_in_q : c ∈ q.vertices := List.mem_of_getElem? hidx
  have hc_marg : c ∈ G.marginalize W hW := Walk.mem_of_mem_vertices q hc_in_q
  have hq_src : q.IsBifurcationSource c :=
    ⟨huw_ne, hu_tail, hw_drop, i, h_dir, hidx⟩
  obtain ⟨p, hp_src⟩ :=
    marg_preserves_bifSource_backward G W hW hu hw hc_marg ⟨q, hq_src⟩
  exact ⟨p, Walk.isBifurcationSource_to_isBifurcation p c hp_src⟩

/-- The last vertex of any walk equals its target. -/
private lemma Walk.vertices_getLast {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.vertices.getLast (Walk.vertices_ne_nil p) = v
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ p' => by
      simp only [Walk.vertices]
      rw [List.getLast_cons (Walk.vertices_ne_nil p')]
      exact Walk.vertices_getLast p'

/-- For a walk with `length ≥ 1`, its vertex list's tail is non-empty
and ends at the target. -/
private lemma Walk.tail_getLast_of_pos {G : CDMG Node} {u v : Node}
    (p : Walk G u v) (hp_pos : p.length ≥ 1) :
    p.vertices.tail.getLast (Walk.tail_vertices_ne_nil_of_pos p hp_pos) = v := by
  cases p with
  | nil _ _ => simp [Walk.length] at hp_pos
  | @cons u' v' vMid a hStep p' =>
      show p'.vertices.getLast _ = v
      exact Walk.vertices_getLast p'

/-- `M.IsBifurcation → M.length ≥ 1`. -/
private lemma Walk.length_pos_of_isBifurcation {G : CDMG Node} {u v : Node}
    {M : Walk G u v} (hM : M.IsBifurcation) : M.length ≥ 1 := by
  obtain ⟨_, _, _, _, h_split⟩ := hM
  cases M with
  | nil _ _ => exact h_split.elim
  | cons _ _ _ _ => exact Nat.succ_le_succ (Nat.zero_le _)

/-- Helper for the backward bidirected case:
`arm.vertices.dropLast ⊆ W`, given direct bounds on arm.vertices.dropLast
into both M.vertices.tail and M.vertices.dropLast.  Used uniformly across
all four sub-cases (the user derives the two bounds from M's arm extractor
clauses, which differ by L/R orientation). -/
private lemma Walk.arm_dropLast_in_W {G : CDMG Node} {a b : Node}
    {M : Walk G a b} (hM_bif : M.IsBifurcation)
    {W : Finset Node} (hM_W : ∀ x ∈ M.vertices.tail.dropLast, x ∈ W)
    {c d : Node} {arm : Walk G c d}
    (h_arm_drop_in_tail : ∀ x ∈ arm.vertices.dropLast, x ∈ M.vertices.tail)
    (h_arm_drop_in_drop : ∀ x ∈ arm.vertices.dropLast, x ∈ M.vertices.dropLast) :
    ∀ x ∈ arm.vertices.dropLast, x ∈ W := by
  intro x hx
  have hM_pos : M.length ≥ 1 := Walk.length_pos_of_isBifurcation hM_bif
  have h_M_tail_ne : M.vertices.tail ≠ [] :=
    Walk.tail_vertices_ne_nil_of_pos M hM_pos
  have h_M_tail_last : M.vertices.tail.getLast h_M_tail_ne = b :=
    Walk.tail_getLast_of_pos M hM_pos
  have h_M_tail_decomp :
      M.vertices.tail = M.vertices.tail.dropLast ++ [b] := by
    have := List.dropLast_append_getLast h_M_tail_ne
    rw [h_M_tail_last] at this
    exact this.symm
  have h_M_vs_eq : M.vertices = a :: M.vertices.tail :=
    Walk.vertices_eq_head_cons_tail M
  have h_M_drop_decomp :
      M.vertices.dropLast = a :: M.vertices.tail.dropLast := by
    conv_lhs => rw [h_M_vs_eq]
    rw [List.dropLast_cons_of_ne_nil h_M_tail_ne]
  have hx_M_tail : x ∈ M.vertices.tail := h_arm_drop_in_tail x hx
  have hx_M_drop : x ∈ M.vertices.dropLast := h_arm_drop_in_drop x hx
  rw [h_M_tail_decomp] at hx_M_tail
  rcases List.mem_append.mp hx_M_tail with h_in_interior | h_eq_b
  · exact hM_W x h_in_interior
  · rw [List.mem_singleton] at h_eq_b
    -- x = b.  Use hx_M_drop to derive contradiction or x ∈ W.
    rw [h_M_drop_decomp] at hx_M_drop
    rcases List.mem_cons.mp hx_M_drop with h_eq_a | h_in_interior
    · -- x = a AND x = b → a = b.  But M.IsBifurcation says a ≠ b.
      have : a = b := h_eq_a.symm.trans h_eq_b
      exact absurd this hM_bif.1
    · exact hM_W x h_in_interior

-- ## Helper: backward direction — bidirected hinge marg-bifurcation.
--
-- The marg-walk `q` has a bidirected hinge `(vL, vR) ∈ marg.L`.  Unfold
-- marg.L's filter to obtain a Φ_L witness `M`: a G-bifurcation between
-- vL and vR (in either orientation) with intermediate vertices in W.
-- Apply M's own bifurcation arm extractor (directed or bidirected based
-- on M's hinge type), splice the extracted arms with the expanded L_g
-- and R_g (which themselves come from `expand_directed_walk_marginalize`
-- applied to L_marg and R_marg), then assemble via `mkBifurcation` (if
-- M's hinge is directed) or `mkBifurcationBidir` (if M's hinge is
-- bidirected).  Vertex-bound conditions are dispatched via
-- `Walk.arm_dropLast_in_W` and the expansion helpers.

private lemma marg_bif_backward_bidir_hinge
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {q : Walk (G.marginalize W hW) u w} (hq : q.IsBifurcation)
    {i : ℕ} (h_split : q.IsBifurcationWithSplit i)
    (h_not_dir : ¬ q.IsBifurcationDirectedHingeWithSplit i) :
    ∃ p : Walk G u w, p.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hq
  obtain ⟨vL, vR, L_marg, R_marg, hL_marg_dir, hR_marg_dir, hLR_marg, hidx,
          hL_marg_sub, hR_marg_sub, hL_marg_drop_sub, hR_marg_drop_sub⟩ :=
    Walk.exists_arms_of_bifurcation_bidir_hinge_strong q i h_split h_not_dir
  -- Unfold marg.L's filter.
  have hLR_filter : (vL, vR) ∈ ((G.V \ W) ×ˢ (G.V \ W)).filter
                                (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2) :=
    hLR_marg
  rw [Finset.mem_filter, Finset.mem_product] at hLR_filter
  obtain ⟨⟨hvL_VW, hvR_VW⟩, _, h_phi_L⟩ := hLR_filter
  have hvL_notW : vL ∉ W := (Finset.mem_sdiff.mp hvL_VW).2
  have hvR_notW : vR ∉ W := (Finset.mem_sdiff.mp hvR_VW).2
  have hu_notW : u ∉ W := notW_of_mem_marginalize hW hu
  have hw_notW : w ∉ W := notW_of_mem_marginalize hW hw
  -- Show vR ∈ q.vertices.tail (vR is at position i+1 of q.vertices, which is
  -- ≥ 1, so vR sits in the tail).
  have hvR_in_q_tail : vR ∈ q.vertices.tail := by
    have h_vs_eq : q.vertices = u :: q.vertices.tail :=
      Walk.vertices_eq_head_cons_tail q
    rw [h_vs_eq] at hidx
    have h_tail_idx : q.vertices.tail[i]? = some vR := by simpa using hidx
    exact List.mem_of_getElem? h_tail_idx
  have hu_ne_vR : u ≠ vR := fun heq => hu_tail (heq ▸ hvR_in_q_tail)
  -- Show w ≠ vL (since vL is at position i in q.vertices.dropLast).
  have hvL_in_q_drop : vL ∈ q.vertices.dropLast :=
    hL_marg_sub vL (Walk.head_mem_vertices L_marg)
  have hw_ne_vL : w ≠ vL := fun heq => hw_drop (heq ▸ hvL_in_q_drop)
  -- Expand L_marg, R_marg to G-walks.
  obtain ⟨L_g, hL_g_dir, _hL_g_len, hL_g_sub_W, hL_g_drop_sub_W⟩ :=
    expand_directed_walk_marginalize L_marg hL_marg_dir
  obtain ⟨R_g, hR_g_dir, _hR_g_len, hR_g_sub_W, hR_g_drop_sub_W⟩ :=
    expand_directed_walk_marginalize R_marg hR_marg_dir
  -- Vertex-bound facts for L_g and R_g (inline chains).
  have hu_notin_L_g_drop : u ∉ L_g.vertices.dropLast := fun h_in =>
    (hL_g_drop_sub_W u h_in).elim
      (fun h_marg => hu_tail (hL_marg_drop_sub u h_marg)) hu_notW
  have hu_notin_R_g : u ∉ R_g.vertices := fun h_in =>
    (hR_g_sub_W u h_in).elim
      (fun h_marg => hu_tail (hR_marg_sub u h_marg)) hu_notW
  have hw_notin_L_g : w ∉ L_g.vertices := fun h_in =>
    (hL_g_sub_W w h_in).elim
      (fun h_marg => hw_drop (hL_marg_sub w h_marg)) hw_notW
  have hw_notin_R_g_drop : w ∉ R_g.vertices.dropLast := fun h_in =>
    (hR_g_drop_sub_W w h_in).elim
      (fun h_marg => hw_drop (hR_marg_drop_sub w h_marg)) hw_notW
  -- Case-split on Φ_L orientation.
  rcases h_phi_L with ⟨M, hM_bif, hM_W⟩ | ⟨M, hM_bif, hM_W⟩
  · -- inl case: M : Walk G vL vR.
    have hM_split_ex : ∃ i, M.IsBifurcationWithSplit i := hM_bif.2.2.2
    obtain ⟨k_M, hM_split⟩ := hM_split_ex
    by_cases h_M_dir : M.IsBifurcationDirectedHingeWithSplit k_M
    · -- Inl + directed M-hinge.
      obtain ⟨c_M, M_L, M_R, hM_L_dir, hM_R_dir, hM_L_pos, hM_R_pos, _,
              hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
        Walk.exists_arms_of_bifurcation_directed_hinge_strong M k_M h_M_dir
      -- qv (c_M → u) = M_L.comp(L_g), qw (c_M → w) = M_R.comp(R_g).
      have hqv_dir : (M_L.comp L_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_L L_g hM_L_dir hL_g_dir
      have hqw_dir : (M_R.comp R_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_R R_g hM_R_dir hR_g_dir
      have hqv_len : (M_L.comp L_g).length = M_L.length + L_g.length :=
        Walk.length_comp M_L L_g
      have hqw_len : (M_R.comp R_g).length = M_R.length + R_g.length :=
        Walk.length_comp M_R R_g
      have hqv_pos : (M_L.comp L_g).length ≥ 1 := by rw [hqv_len]; omega
      have hqw_pos : (M_R.comp R_g).length ≥ 1 := by rw [hqw_len]; omega
      -- Vertex-bound checks (chained through arm_dropLast_in_W + expansion).
      have hu_notin_M_L_drop : u ∉ M_L.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) u h_in)
      have hu_notin_M_R_drop : u ∉ M_R.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub u h_in)
      have hw_notin_M_L_drop : w ∉ M_L.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) w h_in)
      have hw_notin_M_R_drop : w ∉ M_R.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub w h_in)
      -- qv = M_L.comp L_g.  qv.vertices = M_L.vertices.dropLast ++ L_g.vertices.
      have h_qv_vs : (M_L.comp L_g).vertices = M_L.vertices.dropLast ++ L_g.vertices :=
        Walk.vertices_comp M_L L_g
      have h_qw_vs : (M_R.comp R_g).vertices = M_R.vertices.dropLast ++ R_g.vertices :=
        Walk.vertices_comp M_R R_g
      have h_L_g_ne : L_g.vertices ≠ [] := Walk.vertices_ne_nil L_g
      have h_R_g_ne : R_g.vertices ≠ [] := Walk.vertices_ne_nil R_g
      have h_qv_drop :
          (M_L.comp L_g).vertices.dropLast = M_L.vertices.dropLast ++ L_g.vertices.dropLast := by
        rw [h_qv_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
      have h_qw_drop :
          (M_R.comp R_g).vertices.dropLast = M_R.vertices.dropLast ++ R_g.vertices.dropLast := by
        rw [h_qw_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
      have hu_notin_qv_drop : u ∉ (M_L.comp L_g).vertices.dropLast := by
        rw [h_qv_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hu_notin_M_L_drop h_M
        · exact hu_notin_L_g_drop h_L
      have hu_notin_qw : u ∉ (M_R.comp R_g).vertices := by
        rw [h_qw_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hu_notin_M_R_drop h_M
        · exact hu_notin_R_g h_R
      have hw_notin_qv : w ∉ (M_L.comp L_g).vertices := by
        rw [h_qv_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hw_notin_M_L_drop h_M
        · exact hw_notin_L_g h_L
      have hw_notin_qw_drop : w ∉ (M_R.comp R_g).vertices.dropLast := by
        rw [h_qw_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hw_notin_M_R_drop h_M
        · exact hw_notin_R_g_drop h_R
      refine ⟨Walk.mkBifurcation (M_L.comp L_g) hqv_dir hqv_pos (M_R.comp R_g), ?_⟩
      have h_bif_src :=
        Walk.mkBifurcation_isBifurcationSource (M_L.comp L_g) hqv_dir hqv_pos
          (M_R.comp R_g) hqw_dir hqw_pos
          huw_ne hu_notin_qv_drop hu_notin_qw hw_notin_qv hw_notin_qw_drop
      exact Walk.isBifurcationSource_to_isBifurcation _ c_M h_bif_src
    · -- Inl + bidirected M-hinge.
      obtain ⟨vML, vMR, M_L, M_R, hM_L_dir, hM_R_dir, hMLR, _,
              hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
        Walk.exists_arms_of_bifurcation_bidir_hinge_strong M k_M hM_split h_M_dir
      -- M_L : Walk G vML vL (M's left arm ending at M's source vL).
      -- M_R : Walk G vMR vR (M's right arm ending at M's target vR).
      -- (vML, vMR) ∈ G.L.
      -- L_combined = M_L.comp L_g : Walk G vML u.
      -- R_combined = M_R.comp R_g : Walk G vMR w.
      have hLc_dir : (M_L.comp L_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_L L_g hM_L_dir hL_g_dir
      have hRc_dir : (M_R.comp R_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_R R_g hM_R_dir hR_g_dir
      have hu_notin_M_L_drop : u ∉ M_L.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) u h_in)
      have hu_notin_M_R_drop : u ∉ M_R.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub u h_in)
      have hw_notin_M_L_drop : w ∉ M_L.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) w h_in)
      have hw_notin_M_R_drop : w ∉ M_R.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub w h_in)
      have h_Lc_vs : (M_L.comp L_g).vertices = M_L.vertices.dropLast ++ L_g.vertices :=
        Walk.vertices_comp M_L L_g
      have h_Rc_vs : (M_R.comp R_g).vertices = M_R.vertices.dropLast ++ R_g.vertices :=
        Walk.vertices_comp M_R R_g
      have h_L_g_ne : L_g.vertices ≠ [] := Walk.vertices_ne_nil L_g
      have h_R_g_ne : R_g.vertices ≠ [] := Walk.vertices_ne_nil R_g
      have h_Lc_drop :
          (M_L.comp L_g).vertices.dropLast = M_L.vertices.dropLast ++ L_g.vertices.dropLast := by
        rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
      have h_Rc_drop :
          (M_R.comp R_g).vertices.dropLast = M_R.vertices.dropLast ++ R_g.vertices.dropLast := by
        rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
      have hu_notin_Lc_drop : u ∉ (M_L.comp L_g).vertices.dropLast := by
        rw [h_Lc_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hu_notin_M_L_drop h_M
        · exact hu_notin_L_g_drop h_L
      have hu_notin_Rc : u ∉ (M_R.comp R_g).vertices := by
        rw [h_Rc_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hu_notin_M_R_drop h_M
        · exact hu_notin_R_g h_R
      have hw_notin_Lc : w ∉ (M_L.comp L_g).vertices := by
        rw [h_Lc_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hw_notin_M_L_drop h_M
        · exact hw_notin_L_g h_L
      have hw_notin_Rc_drop : w ∉ (M_R.comp R_g).vertices.dropLast := by
        rw [h_Rc_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hw_notin_M_R_drop h_M
        · exact hw_notin_R_g_drop h_R
      refine ⟨Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir (M_R.comp R_g) hMLR, ?_⟩
      exact Walk.mkBifurcationBidir_isBifurcation (M_L.comp L_g) hLc_dir
        (M_R.comp R_g) hRc_dir hMLR huw_ne hu_notin_Lc_drop hu_notin_Rc
        hw_notin_Lc hw_notin_Rc_drop
  · -- inr case: M : Walk G vR vL.
    have hM_split_ex : ∃ i, M.IsBifurcationWithSplit i := hM_bif.2.2.2
    obtain ⟨k_M, hM_split⟩ := hM_split_ex
    by_cases h_M_dir : M.IsBifurcationDirectedHingeWithSplit k_M
    · -- Inr + directed M-hinge.
      obtain ⟨c_M, M_L, M_R, hM_L_dir, hM_R_dir, hM_L_pos, hM_R_pos, _,
              hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
        Walk.exists_arms_of_bifurcation_directed_hinge_strong M k_M h_M_dir
      -- M_L : Walk G c_M vR (M's source), M_R : Walk G c_M vL (M's target).
      -- qv (c_M → u) = M_R.comp(L_g) [M_R ends at vL, L_g starts at vL].
      -- qw (c_M → w) = M_L.comp(R_g) [M_L ends at vR, R_g starts at vR].
      have hqv_dir : (M_R.comp L_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_R L_g hM_R_dir hL_g_dir
      have hqw_dir : (M_L.comp R_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_L R_g hM_L_dir hR_g_dir
      have hqv_pos : (M_R.comp L_g).length ≥ 1 := by
        rw [Walk.length_comp]; omega
      have hqw_pos : (M_L.comp R_g).length ≥ 1 := by
        rw [Walk.length_comp]; omega
      have hu_notin_M_L_drop : u ∉ M_L.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) u h_in)
      have hu_notin_M_R_drop : u ∉ M_R.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub u h_in)
      have hw_notin_M_L_drop : w ∉ M_L.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) w h_in)
      have hw_notin_M_R_drop : w ∉ M_R.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub w h_in)
      have h_qv_vs : (M_R.comp L_g).vertices = M_R.vertices.dropLast ++ L_g.vertices :=
        Walk.vertices_comp M_R L_g
      have h_qw_vs : (M_L.comp R_g).vertices = M_L.vertices.dropLast ++ R_g.vertices :=
        Walk.vertices_comp M_L R_g
      have h_L_g_ne : L_g.vertices ≠ [] := Walk.vertices_ne_nil L_g
      have h_R_g_ne : R_g.vertices ≠ [] := Walk.vertices_ne_nil R_g
      have h_qv_drop :
          (M_R.comp L_g).vertices.dropLast = M_R.vertices.dropLast ++ L_g.vertices.dropLast := by
        rw [h_qv_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
      have h_qw_drop :
          (M_L.comp R_g).vertices.dropLast = M_L.vertices.dropLast ++ R_g.vertices.dropLast := by
        rw [h_qw_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
      have hu_notin_qv_drop : u ∉ (M_R.comp L_g).vertices.dropLast := by
        rw [h_qv_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hu_notin_M_R_drop h_M
        · exact hu_notin_L_g_drop h_L
      have hu_notin_qw : u ∉ (M_L.comp R_g).vertices := by
        rw [h_qw_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hu_notin_M_L_drop h_M
        · exact hu_notin_R_g h_R
      have hw_notin_qv : w ∉ (M_R.comp L_g).vertices := by
        rw [h_qv_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hw_notin_M_R_drop h_M
        · exact hw_notin_L_g h_L
      have hw_notin_qw_drop : w ∉ (M_L.comp R_g).vertices.dropLast := by
        rw [h_qw_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hw_notin_M_L_drop h_M
        · exact hw_notin_R_g_drop h_R
      refine ⟨Walk.mkBifurcation (M_R.comp L_g) hqv_dir hqv_pos (M_L.comp R_g), ?_⟩
      have h_bif_src :=
        Walk.mkBifurcation_isBifurcationSource (M_R.comp L_g) hqv_dir hqv_pos
          (M_L.comp R_g) hqw_dir hqw_pos
          huw_ne hu_notin_qv_drop hu_notin_qw hw_notin_qv hw_notin_qw_drop
      exact Walk.isBifurcationSource_to_isBifurcation _ c_M h_bif_src
    · -- Inr + bidirected M-hinge.
      obtain ⟨vML, vMR, M_L, M_R, hM_L_dir, hM_R_dir, hMLR, _,
              hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
        Walk.exists_arms_of_bifurcation_bidir_hinge_strong M k_M hM_split h_M_dir
      -- M_L : Walk G vML vR (M's source), M_R : Walk G vMR vL (M's target).
      -- (vML, vMR) ∈ G.L.
      -- L_combined = M_R.comp(L_g) [M_R ends at vL, L_g starts at vL]: Walk G vMR u.
      -- R_combined = M_L.comp(R_g) [M_L ends at vR, R_g starts at vR]: Walk G vML w.
      -- Hinge: (vMR, vML) ∈ G.L (by hL_symm on (vML, vMR) ∈ G.L).
      have hMLR_sym : (vMR, vML) ∈ G.L := G.hL_symm hMLR
      have hLc_dir : (M_R.comp L_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_R L_g hM_R_dir hL_g_dir
      have hRc_dir : (M_L.comp R_g).IsDirectedWalk :=
        Walk.isDirectedWalk_comp M_L R_g hM_L_dir hR_g_dir
      have hu_notin_M_L_drop : u ∉ M_L.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) u h_in)
      have hu_notin_M_R_drop : u ∉ M_R.vertices.dropLast := fun h_in =>
        hu_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub u h_in)
      have hw_notin_M_L_drop : w ∉ M_L.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx)) w h_in)
      have hw_notin_M_R_drop : w ∉ M_R.vertices.dropLast := fun h_in =>
        hw_notW (Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub w h_in)
      have h_Lc_vs : (M_R.comp L_g).vertices = M_R.vertices.dropLast ++ L_g.vertices :=
        Walk.vertices_comp M_R L_g
      have h_Rc_vs : (M_L.comp R_g).vertices = M_L.vertices.dropLast ++ R_g.vertices :=
        Walk.vertices_comp M_L R_g
      have h_L_g_ne : L_g.vertices ≠ [] := Walk.vertices_ne_nil L_g
      have h_R_g_ne : R_g.vertices ≠ [] := Walk.vertices_ne_nil R_g
      have h_Lc_drop :
          (M_R.comp L_g).vertices.dropLast = M_R.vertices.dropLast ++ L_g.vertices.dropLast := by
        rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
      have h_Rc_drop :
          (M_L.comp R_g).vertices.dropLast = M_L.vertices.dropLast ++ R_g.vertices.dropLast := by
        rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
      have hu_notin_Lc_drop : u ∉ (M_R.comp L_g).vertices.dropLast := by
        rw [h_Lc_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hu_notin_M_R_drop h_M
        · exact hu_notin_L_g_drop h_L
      have hu_notin_Rc : u ∉ (M_L.comp R_g).vertices := by
        rw [h_Rc_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hu_notin_M_L_drop h_M
        · exact hu_notin_R_g h_R
      have hw_notin_Lc : w ∉ (M_R.comp L_g).vertices := by
        rw [h_Lc_vs]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_L
        · exact hw_notin_M_R_drop h_M
        · exact hw_notin_L_g h_L
      have hw_notin_Rc_drop : w ∉ (M_L.comp R_g).vertices.dropLast := by
        rw [h_Rc_drop]
        intro h_in
        rcases List.mem_append.mp h_in with h_M | h_R
        · exact hw_notin_M_L_drop h_M
        · exact hw_notin_R_g_drop h_R
      refine ⟨Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir (M_L.comp R_g) hMLR_sym, ?_⟩
      exact Walk.mkBifurcationBidir_isBifurcation (M_R.comp L_g) hLc_dir
        (M_L.comp R_g) hRc_dir hMLR_sym huw_ne hu_notin_Lc_drop hu_notin_Rc
        hw_notin_Lc hw_notin_Rc_drop

-- ## Helper: forward direction — bidirected hinge in `p`, both hinge
-- endpoints outside `W`.
--
-- Sub-case (H.A) of the TeX proof, simplest sub-form: the bidirected
-- hinge `(vL, vR) ∈ G.L` has both endpoints in `marg`.  The marg-`L`
-- edge `(vL, vR) ∈ (G.marginalize W hW).L` is witnessed by the single
-- bidirected G-edge directly (`Φ_L` with no W-interior).  The arms are
-- projected to marg directly via `project_directed_walk_strong`.

private lemma marg_bif_forward_bidir_both_notW
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {p : Walk G u w} (hp : p.IsBifurcation)
    {vL vR : Node}
    (hvL_notW : vL ∉ W) (hvR_notW : vR ∉ W)
    (L_g : Walk G vL u) (R_g : Walk G vR w)
    (hL_dir : L_g.IsDirectedWalk) (hR_dir : R_g.IsDirectedWalk)
    (hLR_G : (vL, vR) ∈ G.L)
    (hL_sub : ∀ x ∈ L_g.vertices, x ∈ p.vertices.dropLast)
    (hR_sub : ∀ x ∈ R_g.vertices, x ∈ p.vertices.tail)
    (hL_drop_sub : ∀ x ∈ L_g.vertices.dropLast, x ∈ p.vertices.tail)
    (hR_drop_sub : ∀ x ∈ R_g.vertices.dropLast, x ∈ p.vertices.dropLast) :
    ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hp
  -- vL, vR ∈ G.V via hL_subset on bidirected G-edge.
  have hvL_GV : vL ∈ G.V := (G.hL_subset hLR_G).1
  have hvR_GV : vR ∈ G.V := (G.hL_subset hLR_G).2
  -- vL, vR ∈ G (J ∪ V).
  have hvL_g : vL ∈ G := Finset.mem_union_right _ hvL_GV
  have hvR_g : vR ∈ G := Finset.mem_union_right _ hvR_GV
  -- vL, vR ∈ G.V \ W.
  have hvL_VW : vL ∈ G.V \ W := Finset.mem_sdiff.mpr ⟨hvL_GV, hvL_notW⟩
  have hvR_VW : vR ∈ G.V \ W := Finset.mem_sdiff.mpr ⟨hvR_GV, hvR_notW⟩
  -- vL, vR ∈ marg.
  have hvL_marg : vL ∈ G.marginalize W hW := by
    change vL ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvL_VW
  have hvR_marg : vR ∈ G.marginalize W hW := by
    change vR ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvR_VW
  -- vL ≠ vR via hL_irrefl.
  have hvLvR_ne : vL ≠ vR := G.hL_irrefl hLR_G
  -- Construct single-edge witness for Φ_L.
  let hStep : G.WalkStep vL (vL, vR) vR := Or.inl ⟨rfl, Or.inr hLR_G⟩
  let single : Walk G vL vR := Walk.cons vR (vL, vR) hStep (Walk.nil vR hvR_g)
  have h_single_bif : single.IsBifurcation :=
    Walk.singleEdge_isBifurcation_of_bidir hvL_g hvR_g hLR_G hvLvR_ne
  have h_single_W : ∀ x ∈ single.vertices.tail.dropLast, x ∈ W := by
    intro x hx
    change x ∈ ([vL, vR] : List Node).tail.dropLast at hx
    simp at hx
  -- (vL, vR) ∈ marg.L via Φ_L.
  have hLR_marg : (vL, vR) ∈ (G.marginalize W hW).L := by
    change (vL, vR) ∈ ((G.V \ W) ×ˢ (G.V \ W)).filter
                      (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2)
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hvL_VW, hvR_VW⟩, hvLvR_ne, ?_⟩
    exact Or.inl ⟨single, h_single_bif, h_single_W⟩
  -- Project L_g, R_g to marg.
  obtain ⟨L_marg, hL_marg_dir, hL_marg_sub, hL_marg_drop_sub, hL_marg_tail_sub⟩ :=
    project_directed_walk_strong L_g hL_dir hvL_marg hu
  obtain ⟨R_marg, hR_marg_dir, hR_marg_sub, hR_marg_drop_sub, hR_marg_tail_sub⟩ :=
    project_directed_walk_strong R_g hR_dir hvR_marg hw
  -- Verify the four vertex-bound conditions for mkBifurcationBidir_isBifurcation.
  have hu_notin_L_drop : u ∉ L_marg.vertices.dropLast := fun h_in =>
    hu_tail (hL_drop_sub u (hL_marg_drop_sub u h_in))
  have hu_notin_R : u ∉ R_marg.vertices := fun h_in =>
    hu_tail (hR_sub u (hR_marg_sub u h_in))
  have hw_notin_L : w ∉ L_marg.vertices := fun h_in =>
    hw_drop (hL_sub w (hL_marg_sub w h_in))
  have hw_notin_R_drop : w ∉ R_marg.vertices.dropLast := fun h_in =>
    hw_drop (hR_drop_sub w (hR_marg_drop_sub w h_in))
  -- Assemble the marg bifurcation.
  refine ⟨Walk.mkBifurcationBidir L_marg hL_marg_dir R_marg hLR_marg, ?_⟩
  exact Walk.mkBifurcationBidir_isBifurcation
    L_marg hL_marg_dir R_marg hR_marg_dir hLR_marg
    huw_ne hu_notin_L_drop hu_notin_R hw_notin_L hw_notin_R_drop

-- ## Helper: assemble a marg bidirected-hinge bifurcation from the two
-- "marg-segment" arms and a Φ_L witness.
--
-- Common back-end for Cases 2 and 3.B of the forward direction.  Takes
-- the two exit vertices `vL_exit, vR_exit ∉ W` and the marg-segment arms
-- (`L_marg_seg : Walk G vL_exit u`, `R_marg_seg : Walk G vR_exit w`), plus
-- a Φ_L witness for `(vL_exit, vR_exit) ∈ marg.L`, and assembles via
-- `mkBifurcationBidir_isBifurcation`.

private lemma marg_bif_forward_assemble_bidirected
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (huw_ne : u ≠ w)
    {vL_exit vR_exit : Node}
    (hvL_exit_VW : vL_exit ∈ G.V \ W) (hvR_exit_VW : vR_exit ∈ G.V \ W)
    (hvL_vR_exit_eq : vL_exit ≠ vR_exit)
    (hPhi_L : G.MarginalizationΦL W vL_exit vR_exit)
    {L_marg_seg : Walk G vL_exit u} (hL_marg_dir : L_marg_seg.IsDirectedWalk)
    {R_marg_seg : Walk G vR_exit w} (hR_marg_dir : R_marg_seg.IsDirectedWalk)
    (hu_notin_L_drop : u ∉ L_marg_seg.vertices.dropLast)
    (hu_notin_R : u ∉ R_marg_seg.vertices)
    (hw_notin_L : w ∉ L_marg_seg.vertices)
    (hw_notin_R_drop : w ∉ R_marg_seg.vertices.dropLast) :
    ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcation := by
  have hvL_marg : vL_exit ∈ G.marginalize W hW := by
    change vL_exit ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvL_exit_VW
  have hvR_marg : vR_exit ∈ G.marginalize W hW := by
    change vR_exit ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvR_exit_VW
  have hLR_marg : (vL_exit, vR_exit) ∈ (G.marginalize W hW).L := by
    change (vL_exit, vR_exit) ∈ ((G.V \ W) ×ˢ (G.V \ W)).filter
                              (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W e.1 e.2)
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hvL_exit_VW, hvR_exit_VW⟩, hvL_vR_exit_eq, hPhi_L⟩
  obtain ⟨L_marg_proj, hL_marg_proj_dir, hL_marg_proj_sub,
          hL_marg_proj_drop_sub, _⟩ :=
    project_directed_walk_strong L_marg_seg hL_marg_dir hvL_marg hu
  obtain ⟨R_marg_proj, hR_marg_proj_dir, hR_marg_proj_sub,
          hR_marg_proj_drop_sub, _⟩ :=
    project_directed_walk_strong R_marg_seg hR_marg_dir hvR_marg hw
  have hu_notin_L_proj_drop : u ∉ L_marg_proj.vertices.dropLast := fun h_in =>
    hu_notin_L_drop (hL_marg_proj_drop_sub u h_in)
  have hu_notin_R_proj : u ∉ R_marg_proj.vertices := fun h_in =>
    hu_notin_R (hR_marg_proj_sub u h_in)
  have hw_notin_L_proj : w ∉ L_marg_proj.vertices := fun h_in =>
    hw_notin_L (hL_marg_proj_sub w h_in)
  have hw_notin_R_proj_drop : w ∉ R_marg_proj.vertices.dropLast := fun h_in =>
    hw_notin_R_drop (hR_marg_proj_drop_sub w h_in)
  refine ⟨Walk.mkBifurcationBidir L_marg_proj hL_marg_proj_dir
            R_marg_proj hLR_marg, ?_⟩
  exact Walk.mkBifurcationBidir_isBifurcation L_marg_proj hL_marg_proj_dir
    R_marg_proj hR_marg_proj_dir hLR_marg huw_ne
    hu_notin_L_proj_drop hu_notin_R_proj hw_notin_L_proj hw_notin_R_proj_drop

-- ## Helper (forward Case 2) — directed hinge with source `c ∈ W`.

private lemma marg_bif_forward_dir_hinge_src_W
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {p : Walk G u w} (hp : p.IsBifurcation)
    {i : ℕ} (h_dir : p.IsBifurcationDirectedHingeWithSplit i)
    {c : Node} (hidx : p.vertices[i + 1]? = some c)
    (hc_notin_marg : c ∉ G.marginalize W hW) :
    ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hp
  obtain ⟨c', L_p, R_p, hL_p_dir, hR_p_dir, hL_p_pos, hR_p_pos, hidx',
          hL_p_sub, hR_p_sub, hL_p_drop_sub, hR_p_drop_sub⟩ :=
    Walk.exists_arms_of_bifurcation_directed_hinge_strong p i h_dir
  have hc_eq : c = c' := by
    rw [hidx] at hidx'; exact Option.some.inj hidx'
  subst hc_eq
  have hu_notW : u ∉ W := notW_of_mem_marginalize hW hu
  have hw_notW : w ∉ W := notW_of_mem_marginalize hW hw
  have hc_in_p : c ∈ p.vertices := List.mem_of_getElem? hidx
  have hc_g : c ∈ G := Walk.mem_of_mem_vertices p hc_in_p
  have hc_W : c ∈ W := by
    by_contra hc_notW
    apply hc_notin_marg
    change c ∈ G.J ∪ (G.V \ W)
    rcases Finset.mem_union.mp hc_g with hc_J | hc_V
    · exact Finset.mem_union_left _ hc_J
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hc_V, hc_notW⟩)
  obtain ⟨vL_exit, L_W_seg, L_marg_seg, hL_W_dir, hL_marg_dir, hL_W_pos,
          hvL_exit_notW, hL_W_inter, _hL_lens_eq, hL_p_vs_eq⟩ :=
    find_first_non_W_directed W L_p hL_p_dir hL_p_pos hu_notW
  obtain ⟨vR_exit, R_W_seg, R_marg_seg, hR_W_dir, hR_marg_dir, hR_W_pos,
          hvR_exit_notW, hR_W_inter, _hR_lens_eq, hR_p_vs_eq⟩ :=
    find_first_non_W_directed W R_p hR_p_dir hR_p_pos hw_notW
  have hvL_exit_GV : vL_exit ∈ G.V :=
    Walk.target_in_GV_of_directedWalk_pos L_W_seg hL_W_dir hL_W_pos
  have hvR_exit_GV : vR_exit ∈ G.V :=
    Walk.target_in_GV_of_directedWalk_pos R_W_seg hR_W_dir hR_W_pos
  have hvL_exit_VW : vL_exit ∈ G.V \ W :=
    Finset.mem_sdiff.mpr ⟨hvL_exit_GV, hvL_exit_notW⟩
  have hvR_exit_VW : vR_exit ∈ G.V \ W :=
    Finset.mem_sdiff.mpr ⟨hvR_exit_GV, hvR_exit_notW⟩
  have hL_marg_ne : L_marg_seg.vertices ≠ [] := Walk.vertices_ne_nil L_marg_seg
  have hR_marg_ne : R_marg_seg.vertices ≠ [] := Walk.vertices_ne_nil R_marg_seg
  -- L_marg_seg vertex bounds (chained through L_p ⊆ p).
  have hL_marg_sub_L_p : ∀ x ∈ L_marg_seg.vertices, x ∈ L_p.vertices := by
    intro x hx; rw [hL_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
  have hR_marg_sub_R_p : ∀ x ∈ R_marg_seg.vertices, x ∈ R_p.vertices := by
    intro x hx; rw [hR_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
  have hL_marg_drop_sub_L_p_drop :
      ∀ x ∈ L_marg_seg.vertices.dropLast, x ∈ L_p.vertices.dropLast := by
    intro x hx
    rw [hL_p_vs_eq, List.dropLast_append_of_ne_nil hL_marg_ne]
    exact List.mem_append.mpr (Or.inr hx)
  have hR_marg_drop_sub_R_p_drop :
      ∀ x ∈ R_marg_seg.vertices.dropLast, x ∈ R_p.vertices.dropLast := by
    intro x hx
    rw [hR_p_vs_eq, List.dropLast_append_of_ne_nil hR_marg_ne]
    exact List.mem_append.mpr (Or.inr hx)
  have hu_notin_L_marg_drop : u ∉ L_marg_seg.vertices.dropLast := fun h_in =>
    hu_tail (hL_p_drop_sub u (hL_marg_drop_sub_L_p_drop u h_in))
  have hu_notin_R_marg : u ∉ R_marg_seg.vertices := fun h_in =>
    hu_tail (hR_p_sub u (hR_marg_sub_R_p u h_in))
  have hw_notin_L_marg : w ∉ L_marg_seg.vertices := fun h_in =>
    hw_drop (hL_p_sub w (hL_marg_sub_L_p w h_in))
  have hw_notin_R_marg_drop : w ∉ R_marg_seg.vertices.dropLast := fun h_in =>
    hw_drop (hR_p_drop_sub w (hR_marg_drop_sub_R_p_drop w h_in))
  -- L_W_seg vertex bounds.
  have hL_W_sub_L_p : ∀ x ∈ L_W_seg.vertices, x ∈ L_p.vertices := by
    intro x hx
    rw [hL_p_vs_eq]
    by_cases h_drop : x ∈ L_W_seg.vertices.dropLast
    · exact List.mem_append.mpr (Or.inl h_drop)
    · have h_x_last : x = vL_exit := by
        have h_W_seg_ne : L_W_seg.vertices ≠ [] := Walk.vertices_ne_nil L_W_seg
        have h_W_seg_last : L_W_seg.vertices.getLast h_W_seg_ne = vL_exit :=
          Walk.vertices_getLast L_W_seg
        have := List.dropLast_append_getLast h_W_seg_ne
        rw [h_W_seg_last] at this
        have hx_in : x ∈ L_W_seg.vertices.dropLast ++ [vL_exit] := by rw [this]; exact hx
        rcases List.mem_append.mp hx_in with h | h
        · exact absurd h h_drop
        · exact List.mem_singleton.mp h
      rw [h_x_last]
      apply List.mem_append.mpr
      right
      exact Walk.head_mem_vertices L_marg_seg
  have hR_W_sub_R_p : ∀ x ∈ R_W_seg.vertices, x ∈ R_p.vertices := by
    intro x hx
    rw [hR_p_vs_eq]
    by_cases h_drop : x ∈ R_W_seg.vertices.dropLast
    · exact List.mem_append.mpr (Or.inl h_drop)
    · have h_x_last : x = vR_exit := by
        have h_W_seg_ne : R_W_seg.vertices ≠ [] := Walk.vertices_ne_nil R_W_seg
        have h_W_seg_last : R_W_seg.vertices.getLast h_W_seg_ne = vR_exit :=
          Walk.vertices_getLast R_W_seg
        have := List.dropLast_append_getLast h_W_seg_ne
        rw [h_W_seg_last] at this
        have hx_in : x ∈ R_W_seg.vertices.dropLast ++ [vR_exit] := by rw [this]; exact hx
        rcases List.mem_append.mp hx_in with h | h
        · exact absurd h h_drop
        · exact List.mem_singleton.mp h
      rw [h_x_last]
      apply List.mem_append.mpr
      right
      exact Walk.head_mem_vertices R_marg_seg
  -- For both L_W and R_W: vertices.tail ⊆ W ∪ {vL_exit / vR_exit}.
  -- The walks' interior (vertices.tail.dropLast) is ⊆ W (from find_first_non_W).
  by_cases hvL_vR_exit_eq : vL_exit = vR_exit
  · -- Degenerate case: vL_exit = vR_exit = v*.  Construct a sourced
    -- G-bifurcation with source v* ∉ W, then apply ii(b) forward + convert.
    subst hvL_vR_exit_eq
    -- L_marg_seg.length ≥ 1 (since vL_exit ≠ u, because vL_exit ∉ p.vertices.tail
    -- isn't true... let me think differently).
    -- Actually we DON'T know L_marg_seg.length ≥ 1 in general.
    -- For the degenerate case to work, we need both L_marg_seg and R_marg_seg lengths ≥ 1.
    -- If L_marg_seg.length = 0 (so vL_exit = u): can this happen?
    -- vL_exit ∈ p.vertices (via L_p). And vR_exit ∈ R_p.vertices ⊆ p.vertices.tail.
    -- If vL_exit = vR_exit = u: vR_exit = u ∈ p.vertices.tail. But u ∉ p.vertices.tail. Contradiction.
    -- So vL_exit ≠ u in the degenerate case.  Hence L_marg_seg.length ≥ 1.
    have hvL_exit_ne_u : vL_exit ≠ u := by
      intro h_eq
      have hvL_in_R_p_tail : vL_exit ∈ R_p.vertices := hR_marg_sub_R_p _
        (Walk.head_mem_vertices R_marg_seg)
      have hvL_in_p_tail : vL_exit ∈ p.vertices.tail := hR_p_sub _ hvL_in_R_p_tail
      exact hu_tail (h_eq ▸ hvL_in_p_tail)
    have hvL_exit_ne_w : vL_exit ≠ w := by
      intro h_eq
      have hvL_in_L_p : vL_exit ∈ L_p.vertices := hL_marg_sub_L_p _
        (Walk.head_mem_vertices L_marg_seg)
      have hvL_in_p_drop : vL_exit ∈ p.vertices.dropLast := hL_p_sub _ hvL_in_L_p
      exact hw_drop (h_eq ▸ hvL_in_p_drop)
    have hL_marg_pos : L_marg_seg.length ≥ 1 :=
      Walk.length_pos_of_ne L_marg_seg hvL_exit_ne_u
    have hR_marg_pos : R_marg_seg.length ≥ 1 :=
      Walk.length_pos_of_ne R_marg_seg hvL_exit_ne_w
    have hvL_marg : vL_exit ∈ G.marginalize W hW := by
      change vL_exit ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvL_exit_VW
    -- Build sourced G-bifurcation: mkBifurcation L_marg_seg R_marg_seg.
    have h_src : (Walk.mkBifurcation L_marg_seg hL_marg_dir hL_marg_pos
                    R_marg_seg).IsBifurcationSource vL_exit :=
      Walk.mkBifurcation_isBifurcationSource L_marg_seg hL_marg_dir hL_marg_pos
        R_marg_seg hR_marg_dir hR_marg_pos huw_ne
        hu_notin_L_marg_drop hu_notin_R_marg hw_notin_L_marg hw_notin_R_marg_drop
    obtain ⟨q, hq_src⟩ := marg_preserves_bifSource_forward G W hW hu hw hvL_marg
      ⟨_, h_src⟩
    exact ⟨q, Walk.isBifurcationSource_to_isBifurcation q vL_exit hq_src⟩
  · -- Non-degenerate case: vL_exit ≠ vR_exit.
    -- Build Φ_L witness as mkBifurcation L_W_seg R_W_seg.
    -- Need vertex bounds for the mkBifurcation (vL_exit ∉ L_W_seg.vertices.dropLast etc.).
    -- vL_exit ∉ L_W_seg.vertices.dropLast: L_W_seg.vertices.dropLast = c :: L_W_seg.vertices.tail.dropLast
    --   (when L_W_seg.length ≥ 1, so L_W_seg.vertices.tail non-empty).
    -- vertices.tail.dropLast ⊆ W (from hL_W_inter). c ∈ W. vL_exit ∉ W.
    have hvL_notin_L_W_drop : vL_exit ∉ L_W_seg.vertices.dropLast := by
      intro h_in
      have h_W_seg_ne : L_W_seg.vertices ≠ [] := Walk.vertices_ne_nil L_W_seg
      have h_W_seg_tail_ne : L_W_seg.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L_W_seg hL_W_pos
      -- L_W_seg.vertices.dropLast = c :: L_W_seg.vertices.tail.dropLast.
      have h_vs_eq : L_W_seg.vertices = c :: L_W_seg.vertices.tail :=
        Walk.vertices_eq_head_cons_tail L_W_seg
      rw [h_vs_eq, List.dropLast_cons_of_ne_nil h_W_seg_tail_ne] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · exact hvL_exit_notW (h_eq ▸ hc_W)
      · exact hvL_exit_notW (hL_W_inter vL_exit h_rest)
    have hvR_notin_R_W_drop : vR_exit ∉ R_W_seg.vertices.dropLast := by
      intro h_in
      have h_W_seg_tail_ne : R_W_seg.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R_W_seg hR_W_pos
      have h_vs_eq : R_W_seg.vertices = c :: R_W_seg.vertices.tail :=
        Walk.vertices_eq_head_cons_tail R_W_seg
      rw [h_vs_eq, List.dropLast_cons_of_ne_nil h_W_seg_tail_ne] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · exact hvR_exit_notW (h_eq ▸ hc_W)
      · exact hvR_exit_notW (hR_W_inter vR_exit h_rest)
    -- vL_exit ∉ R_W_seg.vertices: R_W_seg = c :: R_W_seg.tail.
    -- R_W_seg.tail = R_W_seg.tail.dropLast ++ [vR_exit] (last is target).
    -- For x ∈ R_W_seg.vertices: x = c or x ∈ R_W_seg.tail.
    -- x ∈ R_W_seg.tail → x ∈ W (interior) or x = vR_exit.
    have h_R_W_target : R_W_seg.vertices.tail.getLast
        (Walk.tail_vertices_ne_nil_of_pos R_W_seg hR_W_pos) = vR_exit :=
      Walk.tail_getLast_of_pos R_W_seg hR_W_pos
    have h_L_W_target : L_W_seg.vertices.tail.getLast
        (Walk.tail_vertices_ne_nil_of_pos L_W_seg hL_W_pos) = vL_exit :=
      Walk.tail_getLast_of_pos L_W_seg hL_W_pos
    have hvL_notin_R_W : vL_exit ∉ R_W_seg.vertices := by
      intro h_in
      have h_R_W_tail_ne : R_W_seg.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R_W_seg hR_W_pos
      have h_vs_eq : R_W_seg.vertices = c :: R_W_seg.vertices.tail :=
        Walk.vertices_eq_head_cons_tail R_W_seg
      rw [h_vs_eq] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · exact hvL_exit_notW (h_eq ▸ hc_W)
      · -- vL_exit ∈ R_W_seg.vertices.tail.
        -- R_W_seg.vertices.tail = R_W_seg.vertices.tail.dropLast ++ [vR_exit].
        have h_tail_decomp : R_W_seg.vertices.tail
            = R_W_seg.vertices.tail.dropLast ++ [vR_exit] := by
          have := List.dropLast_append_getLast h_R_W_tail_ne
          rw [h_R_W_target] at this
          exact this.symm
        rw [h_tail_decomp] at h_rest
        rcases List.mem_append.mp h_rest with h_W | h_eq2
        · exact hvL_exit_notW (hR_W_inter vL_exit h_W)
        · rw [List.mem_singleton] at h_eq2
          exact hvL_vR_exit_eq h_eq2
    have hvR_notin_L_W : vR_exit ∉ L_W_seg.vertices := by
      intro h_in
      have h_L_W_tail_ne : L_W_seg.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L_W_seg hL_W_pos
      have h_vs_eq : L_W_seg.vertices = c :: L_W_seg.vertices.tail :=
        Walk.vertices_eq_head_cons_tail L_W_seg
      rw [h_vs_eq] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · exact hvR_exit_notW (h_eq ▸ hc_W)
      · have h_tail_decomp : L_W_seg.vertices.tail
            = L_W_seg.vertices.tail.dropLast ++ [vL_exit] := by
          have := List.dropLast_append_getLast h_L_W_tail_ne
          rw [h_L_W_target] at this
          exact this.symm
        rw [h_tail_decomp] at h_rest
        rcases List.mem_append.mp h_rest with h_W | h_eq2
        · exact hvR_exit_notW (hL_W_inter vR_exit h_W)
        · rw [List.mem_singleton] at h_eq2
          exact hvL_vR_exit_eq h_eq2.symm
    -- The mkBifurcation L_W_seg R_W_seg has IsBifurcationSource c.
    have h_phi_src : (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos
                        R_W_seg).IsBifurcationSource c :=
      Walk.mkBifurcation_isBifurcationSource L_W_seg hL_W_dir hL_W_pos
        R_W_seg hR_W_dir hR_W_pos hvL_vR_exit_eq
        hvL_notin_L_W_drop hvL_notin_R_W hvR_notin_L_W hvR_notin_R_W_drop
    have h_phi_bif : (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos
                        R_W_seg).IsBifurcation :=
      Walk.isBifurcationSource_to_isBifurcation _ c h_phi_src
    -- Verify the Φ_L witness's interior is in W.
    -- vertices = L_W_seg.vertices.reverse.dropLast ++ R_W_seg.vertices.
    -- vertices.tail.dropLast = (drop first and last of vertices).
    -- We need to show all interior is in W.
    have h_phi_W : ∀ x ∈ (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos
                            R_W_seg).vertices.tail.dropLast, x ∈ W := by
      intro x hx
      -- vertices = L_W_seg.vertices.reverse.dropLast ++ R_W_seg.vertices.
      have h_vs : (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos R_W_seg).vertices
          = L_W_seg.vertices.reverse.dropLast ++ R_W_seg.vertices :=
        Walk.vertices_mkBifurcation L_W_seg hL_W_dir hL_W_pos R_W_seg
      -- L_W_seg.vertices.reverse.dropLast = L_W_seg.vertices.tail.reverse.
      have h_rev_drop : L_W_seg.vertices.reverse.dropLast = L_W_seg.vertices.tail.reverse :=
        Walk.vertices_reverse_dropLast L_W_seg
      -- L_W_seg.vertices.tail starts at the 2nd vertex of L_W_seg and ends at vL_exit.
      -- L_W_seg.vertices.tail = L_W_seg.vertices.tail.dropLast ++ [vL_exit].
      have h_L_W_tail_decomp : L_W_seg.vertices.tail
          = L_W_seg.vertices.tail.dropLast ++ [vL_exit] := by
        have h_tail_ne : L_W_seg.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos L_W_seg hL_W_pos
        have := List.dropLast_append_getLast h_tail_ne
        rw [h_L_W_target] at this
        exact this.symm
      -- Reverse: L_W_seg.vertices.tail.reverse = vL_exit :: L_W_seg.vertices.tail.dropLast.reverse.
      have h_L_W_rev_eq : L_W_seg.vertices.tail.reverse
          = vL_exit :: L_W_seg.vertices.tail.dropLast.reverse := by
        conv_lhs => rw [h_L_W_tail_decomp]
        simp [List.reverse_append]
      rw [h_vs, h_rev_drop, h_L_W_rev_eq] at hx
      -- hx : x ∈ (vL_exit :: L_W_seg.vertices.tail.dropLast.reverse ++ R_W_seg.vertices).tail.dropLast.
      -- Hmm wait, the .tail.dropLast operates on the full appended list.
      -- Let me work through this more carefully.
      -- (vL_exit :: L_W_seg.vertices.tail.dropLast.reverse) ++ R_W_seg.vertices
      --   = vL_exit :: (L_W_seg.vertices.tail.dropLast.reverse ++ R_W_seg.vertices).
      -- .tail = L_W_seg.vertices.tail.dropLast.reverse ++ R_W_seg.vertices.
      -- .tail.dropLast = L_W_seg.vertices.tail.dropLast.reverse ++ R_W_seg.vertices.dropLast (if R_W_seg.vertices non-empty).
      have h_R_W_ne : R_W_seg.vertices ≠ [] := Walk.vertices_ne_nil R_W_seg
      rw [List.cons_append] at hx
      change x ∈ (L_W_seg.vertices.tail.dropLast.reverse ++ R_W_seg.vertices).dropLast at hx
      rw [List.dropLast_append_of_ne_nil h_R_W_ne] at hx
      rcases List.mem_append.mp hx with h_L | h_R
      · -- x ∈ L_W_seg.vertices.tail.dropLast.reverse → x ∈ L_W_seg.vertices.tail.dropLast → in W.
        rw [List.mem_reverse] at h_L
        exact hL_W_inter x h_L
      · -- x ∈ R_W_seg.vertices.dropLast.
        -- R_W_seg.vertices.dropLast = c :: R_W_seg.vertices.tail.dropLast.
        have h_R_W_tail_ne : R_W_seg.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos R_W_seg hR_W_pos
        have h_R_W_vs_eq : R_W_seg.vertices = c :: R_W_seg.vertices.tail :=
          Walk.vertices_eq_head_cons_tail R_W_seg
        rw [h_R_W_vs_eq, List.dropLast_cons_of_ne_nil h_R_W_tail_ne] at h_R
        rcases List.mem_cons.mp h_R with h_eq | h_rest
        · exact h_eq ▸ hc_W
        · exact hR_W_inter x h_rest
    -- Φ_L witness for (vL_exit, vR_exit) ∈ marg.L: the inl disjunct.
    have hPhi_L : G.MarginalizationΦL W vL_exit vR_exit := by
      left
      exact ⟨_, h_phi_bif, h_phi_W⟩
    exact marg_bif_forward_assemble_bidirected G W hW hu hw huw_ne
      hvL_exit_VW hvR_exit_VW hvL_vR_exit_eq hPhi_L hL_marg_dir hR_marg_dir
      hu_notin_L_marg_drop hu_notin_R_marg hw_notin_L_marg hw_notin_R_marg_drop

-- ## Helper: given W-segments and marg-segments, finish Case 3.B by
-- either constructing a sourced G-bifurcation (degenerate `vL_exit =
-- vR_exit`) or assembling via `mkBifurcationBidir` + assembly helper.
--
-- Linked hypothesis `hL_W_link`: either (L_W_part.length ≥ 1 AND vL ∈ W)
-- or (L_W_part.length = 0 AND vL = vL_exit).  This precludes the
-- pathological "L_W_part has cycle at vL ∉ W" case.

private lemma marg_bif_forward_bidir_finish
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (huw_ne : u ≠ w)
    {vL vR vL_exit vR_exit : Node}
    (hvL_g : vL ∈ G) (hvR_g : vR ∈ G)
    (hLR_G : (vL, vR) ∈ G.L) (hvL_vR_ne : vL ≠ vR)
    (hvL_exit_VW : vL_exit ∈ G.V \ W) (hvR_exit_VW : vR_exit ∈ G.V \ W)
    (L_W_part : Walk G vL vL_exit)
    (hL_W_dir : L_W_part.IsDirectedWalk)
    (hL_W_inter : ∀ x ∈ L_W_part.vertices.tail.dropLast, x ∈ W)
    (hL_W_link : (L_W_part.length ≥ 1 ∧ vL ∈ W) ∨
                 (L_W_part.length = 0 ∧ vL = vL_exit))
    (R_W_part : Walk G vR vR_exit)
    (hR_W_dir : R_W_part.IsDirectedWalk)
    (hR_W_inter : ∀ x ∈ R_W_part.vertices.tail.dropLast, x ∈ W)
    (hR_W_link : (R_W_part.length ≥ 1 ∧ vR ∈ W) ∨
                 (R_W_part.length = 0 ∧ vR = vR_exit))
    (L_marg_part : Walk G vL_exit u) (hL_marg_dir : L_marg_part.IsDirectedWalk)
    (R_marg_part : Walk G vR_exit w) (hR_marg_dir : R_marg_part.IsDirectedWalk)
    (hu_notin_L_marg_drop : u ∉ L_marg_part.vertices.dropLast)
    (hu_notin_R_marg : u ∉ R_marg_part.vertices)
    (hw_notin_L_marg : w ∉ L_marg_part.vertices)
    (hw_notin_R_marg_drop : w ∉ R_marg_part.vertices.dropLast)
    (hvR_exit_ne_u : vR_exit ≠ u) (hvL_exit_ne_w : vL_exit ≠ w) :
    ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcation := by
  have hvL_exit_notW : vL_exit ∉ W := (Finset.mem_sdiff.mp hvL_exit_VW).2
  have hvR_exit_notW : vR_exit ∉ W := (Finset.mem_sdiff.mp hvR_exit_VW).2
  by_cases hvL_vR_exit_eq : vL_exit = vR_exit
  · -- Degenerate case: build sourced G-bifurcation.
    subst hvL_vR_exit_eq
    have hvL_exit_ne_u : vL_exit ≠ u := hvR_exit_ne_u
    have hL_marg_pos : L_marg_part.length ≥ 1 :=
      Walk.length_pos_of_ne L_marg_part hvL_exit_ne_u
    have hR_marg_pos : R_marg_part.length ≥ 1 :=
      Walk.length_pos_of_ne R_marg_part hvL_exit_ne_w
    have hvL_exit_marg : vL_exit ∈ G.marginalize W hW := by
      change vL_exit ∈ G.J ∪ (G.V \ W); exact Finset.mem_union_right _ hvL_exit_VW
    have h_src : (Walk.mkBifurcation L_marg_part hL_marg_dir hL_marg_pos
                    R_marg_part).IsBifurcationSource vL_exit :=
      Walk.mkBifurcation_isBifurcationSource L_marg_part hL_marg_dir hL_marg_pos
        R_marg_part hR_marg_dir hR_marg_pos huw_ne
        hu_notin_L_marg_drop hu_notin_R_marg hw_notin_L_marg hw_notin_R_marg_drop
    obtain ⟨q, hq_src⟩ := marg_preserves_bifSource_forward G W hW hu hw
      hvL_exit_marg ⟨_, h_src⟩
    exact ⟨q, Walk.isBifurcationSource_to_isBifurcation q vL_exit hq_src⟩
  · -- Non-degenerate case: build Φ_L witness via mkBifurcationBidir.
    -- Vertex bounds for mkBifurcationBidir_isBifurcation.
    have hvL_exit_notin_L_W_drop : vL_exit ∉ L_W_part.vertices.dropLast := by
      intro h_in
      rcases hL_W_link with ⟨hL_W_pos, hvL_W⟩ | ⟨hL_W_zero, _⟩
      · have h_tail_ne : L_W_part.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos L_W_part hL_W_pos
        have h_vs_eq : L_W_part.vertices = vL :: L_W_part.vertices.tail :=
          Walk.vertices_eq_head_cons_tail L_W_part
        rw [h_vs_eq, List.dropLast_cons_of_ne_nil h_tail_ne] at h_in
        rcases List.mem_cons.mp h_in with h_eq | h_rest
        · exact hvL_exit_notW (h_eq ▸ hvL_W)
        · exact hvL_exit_notW (hL_W_inter vL_exit h_rest)
      · cases L_W_part with
        | nil _ _ => simp [Walk.vertices, List.dropLast] at h_in
        | cons _ _ _ _ => simp [Walk.length] at hL_W_zero
    have hvR_exit_notin_R_W_drop : vR_exit ∉ R_W_part.vertices.dropLast := by
      intro h_in
      rcases hR_W_link with ⟨hR_W_pos, hvR_W⟩ | ⟨hR_W_zero, _⟩
      · have h_tail_ne : R_W_part.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos R_W_part hR_W_pos
        have h_vs_eq : R_W_part.vertices = vR :: R_W_part.vertices.tail :=
          Walk.vertices_eq_head_cons_tail R_W_part
        rw [h_vs_eq, List.dropLast_cons_of_ne_nil h_tail_ne] at h_in
        rcases List.mem_cons.mp h_in with h_eq | h_rest
        · exact hvR_exit_notW (h_eq ▸ hvR_W)
        · exact hvR_exit_notW (hR_W_inter vR_exit h_rest)
      · cases R_W_part with
        | nil _ _ => simp [Walk.vertices, List.dropLast] at h_in
        | cons _ _ _ _ => simp [Walk.length] at hR_W_zero
    have hvL_exit_notin_R_W : vL_exit ∉ R_W_part.vertices := by
      intro h_in
      have h_vs_eq : R_W_part.vertices = vR :: R_W_part.vertices.tail :=
        Walk.vertices_eq_head_cons_tail R_W_part
      rw [h_vs_eq] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · -- vL_exit = vR.
        rcases hR_W_link with ⟨_, hvR_W⟩ | ⟨_, hvR_eq⟩
        · exact hvL_exit_notW (h_eq ▸ hvR_W)
        · exact hvL_vR_exit_eq (h_eq.trans hvR_eq)
      · -- vL_exit ∈ R_W_part.vertices.tail.
        rcases hR_W_link with ⟨hR_W_pos, _⟩ | ⟨hR_W_zero, _⟩
        · -- R_W_part.length ≥ 1: tail = tail.dropLast ++ [vR_exit].
          have h_R_W_tail_ne : R_W_part.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos R_W_part hR_W_pos
          have h_R_W_target : R_W_part.vertices.tail.getLast h_R_W_tail_ne = vR_exit :=
            Walk.tail_getLast_of_pos R_W_part hR_W_pos
          have h_tail_decomp : R_W_part.vertices.tail
              = R_W_part.vertices.tail.dropLast ++ [vR_exit] := by
            have := List.dropLast_append_getLast h_R_W_tail_ne
            rw [h_R_W_target] at this; exact this.symm
          rw [h_tail_decomp] at h_rest
          rcases List.mem_append.mp h_rest with h_W | h_eq2
          · exact hvL_exit_notW (hR_W_inter vL_exit h_W)
          · rw [List.mem_singleton] at h_eq2
            exact hvL_vR_exit_eq h_eq2
        · -- R_W_part.length = 0: tail = [].
          cases R_W_part with
          | nil _ _ => simp [Walk.vertices, List.tail] at h_rest
          | cons _ _ _ _ => simp [Walk.length] at hR_W_zero
    have hvR_exit_notin_L_W : vR_exit ∉ L_W_part.vertices := by
      intro h_in
      have h_vs_eq : L_W_part.vertices = vL :: L_W_part.vertices.tail :=
        Walk.vertices_eq_head_cons_tail L_W_part
      rw [h_vs_eq] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_rest
      · rcases hL_W_link with ⟨_, hvL_W⟩ | ⟨_, hvL_eq⟩
        · exact hvR_exit_notW (h_eq ▸ hvL_W)
        · exact hvL_vR_exit_eq (hvL_eq.symm.trans h_eq.symm)
      · rcases hL_W_link with ⟨hL_W_pos, _⟩ | ⟨hL_W_zero, _⟩
        · have h_L_W_tail_ne : L_W_part.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos L_W_part hL_W_pos
          have h_L_W_target : L_W_part.vertices.tail.getLast h_L_W_tail_ne = vL_exit :=
            Walk.tail_getLast_of_pos L_W_part hL_W_pos
          have h_tail_decomp : L_W_part.vertices.tail
              = L_W_part.vertices.tail.dropLast ++ [vL_exit] := by
            have := List.dropLast_append_getLast h_L_W_tail_ne
            rw [h_L_W_target] at this; exact this.symm
          rw [h_tail_decomp] at h_rest
          rcases List.mem_append.mp h_rest with h_W | h_eq2
          · exact hvR_exit_notW (hL_W_inter vR_exit h_W)
          · rw [List.mem_singleton] at h_eq2
            exact hvL_vR_exit_eq h_eq2.symm
        · cases L_W_part with
          | nil _ _ => simp [Walk.vertices, List.tail] at h_rest
          | cons _ _ _ _ => simp [Walk.length] at hL_W_zero
    -- Construct Φ_L witness.
    have h_phi_bif : (Walk.mkBifurcationBidir L_W_part hL_W_dir
                        R_W_part hLR_G).IsBifurcation :=
      Walk.mkBifurcationBidir_isBifurcation L_W_part hL_W_dir
        R_W_part hR_W_dir hLR_G hvL_vR_exit_eq
        hvL_exit_notin_L_W_drop hvL_exit_notin_R_W
        hvR_exit_notin_L_W hvR_exit_notin_R_W_drop
    -- Interior in W.
    have h_phi_W : ∀ x ∈ (Walk.mkBifurcationBidir L_W_part hL_W_dir
                            R_W_part hLR_G).vertices.tail.dropLast, x ∈ W := by
      intro x hx
      have h_vs : (Walk.mkBifurcationBidir L_W_part hL_W_dir R_W_part hLR_G).vertices
          = L_W_part.vertices.reverse.dropLast ++ (vL :: R_W_part.vertices) :=
        Walk.vertices_mkBifurcationBidir L_W_part hL_W_dir R_W_part hLR_G
      rw [h_vs] at hx
      have h_R_W_vs_eq : R_W_part.vertices = vR :: R_W_part.vertices.tail :=
        Walk.vertices_eq_head_cons_tail R_W_part
      have h_R_W_cons_ne : (vL :: R_W_part.vertices) ≠ [] := by simp
      -- Case-split on whether L_W_part is nil or non-nil.
      rcases hL_W_link with ⟨hL_W_pos, hvL_W⟩ | ⟨hL_W_zero, _⟩
      · -- L_W_part has length ≥ 1.
        have h_L_W_rev_drop : L_W_part.vertices.reverse.dropLast
            = L_W_part.vertices.tail.reverse :=
          Walk.vertices_reverse_dropLast L_W_part
        rw [h_L_W_rev_drop] at hx
        have h_L_W_tail_ne : L_W_part.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos L_W_part hL_W_pos
        have h_L_W_rev_ne : L_W_part.vertices.tail.reverse ≠ [] := by
          intro h
          apply h_L_W_tail_ne
          have := List.reverse_eq_nil_iff.mp h
          exact this
        rw [List.tail_append_of_ne_nil h_L_W_rev_ne,
            List.dropLast_append_of_ne_nil h_R_W_cons_ne] at hx
        rcases List.mem_append.mp hx with h_L | h_R
        · -- x ∈ L_W_part.vertices.tail.reverse.tail.
          have h_L_W_target : L_W_part.vertices.tail.getLast h_L_W_tail_ne = vL_exit :=
            Walk.tail_getLast_of_pos L_W_part hL_W_pos
          have h_L_W_tail_decomp : L_W_part.vertices.tail
              = L_W_part.vertices.tail.dropLast ++ [vL_exit] := by
            have := List.dropLast_append_getLast h_L_W_tail_ne
            rw [h_L_W_target] at this; exact this.symm
          have h_L_W_rev_eq : L_W_part.vertices.tail.reverse
              = vL_exit :: L_W_part.vertices.tail.dropLast.reverse := by
            conv_lhs => rw [h_L_W_tail_decomp]
            simp [List.reverse_append]
          rw [h_L_W_rev_eq, List.tail_cons] at h_L
          have h_in_dropLast : x ∈ L_W_part.vertices.tail.dropLast := by
            have := h_L
            rwa [List.mem_reverse] at this
          exact hL_W_inter x h_in_dropLast
        · -- x ∈ (vL :: R_W_part.vertices).dropLast.
          rw [List.dropLast_cons_of_ne_nil (Walk.vertices_ne_nil R_W_part)] at h_R
          rcases List.mem_cons.mp h_R with h_eq | h_in_R_drop
          · exact h_eq ▸ hvL_W
          · -- x ∈ R_W_part.vertices.dropLast.
            rcases hR_W_link with ⟨hR_W_pos, hvR_W⟩ | ⟨hR_W_zero, _⟩
            · -- R_W_part.length ≥ 1.
              have h_R_tail_ne : R_W_part.vertices.tail ≠ [] :=
                Walk.tail_vertices_ne_nil_of_pos R_W_part hR_W_pos
              have h_R_vs_eq : R_W_part.vertices = vR :: R_W_part.vertices.tail :=
                Walk.vertices_eq_head_cons_tail R_W_part
              rw [h_R_vs_eq, List.dropLast_cons_of_ne_nil h_R_tail_ne] at h_in_R_drop
              rcases List.mem_cons.mp h_in_R_drop with h_eq | h_rest
              · exact h_eq ▸ hvR_W
              · exact hR_W_inter x h_rest
            · cases R_W_part with
              | nil _ _ => simp [Walk.vertices, List.dropLast] at h_in_R_drop
              | cons _ _ _ _ => simp [Walk.length] at hR_W_zero
      · -- L_W_part is nil.  L_W_part.vertices.reverse.dropLast = [].
        have h_L_W_drop_empty : L_W_part.vertices.reverse.dropLast = [] := by
          cases L_W_part with
          | nil _ _ => rfl
          | cons _ _ _ _ => simp [Walk.length] at hL_W_zero
        rw [h_L_W_drop_empty, List.nil_append, List.tail_cons] at hx
        -- hx : x ∈ R_W_part.vertices.dropLast.
        rcases hR_W_link with ⟨hR_W_pos, hvR_W⟩ | ⟨hR_W_zero, _⟩
        · have h_R_tail_ne : R_W_part.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos R_W_part hR_W_pos
          have h_R_vs_eq : R_W_part.vertices = vR :: R_W_part.vertices.tail :=
            Walk.vertices_eq_head_cons_tail R_W_part
          rw [h_R_vs_eq, List.dropLast_cons_of_ne_nil h_R_tail_ne] at hx
          rcases List.mem_cons.mp hx with h_eq | h_rest
          · exact h_eq ▸ hvR_W
          · exact hR_W_inter x h_rest
        · cases R_W_part with
          | nil _ _ => simp [Walk.vertices, List.dropLast] at hx
          | cons _ _ _ _ => simp [Walk.length] at hR_W_zero
    have hPhi_L : G.MarginalizationΦL W vL_exit vR_exit := by
      left; exact ⟨_, h_phi_bif, h_phi_W⟩
    exact marg_bif_forward_assemble_bidirected G W hW hu hw huw_ne
      hvL_exit_VW hvR_exit_VW hvL_vR_exit_eq hPhi_L hL_marg_dir hR_marg_dir
      hu_notin_L_marg_drop hu_notin_R_marg hw_notin_L_marg hw_notin_R_marg_drop

-- ## Helper (forward Case 3.B) — bidirected hinge with at least one
-- endpoint in W.

private lemma marg_bif_forward_bidir_with_W
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    {p : Walk G u w} (hp : p.IsBifurcation)
    {vL vR : Node}
    (hvL_or_vR_W : vL ∈ W ∨ vR ∈ W)
    (L_g : Walk G vL u) (R_g : Walk G vR w)
    (hL_dir : L_g.IsDirectedWalk) (hR_dir : R_g.IsDirectedWalk)
    (hLR_G : (vL, vR) ∈ G.L)
    (hL_sub : ∀ x ∈ L_g.vertices, x ∈ p.vertices.dropLast)
    (hR_sub : ∀ x ∈ R_g.vertices, x ∈ p.vertices.tail)
    (hL_drop_sub : ∀ x ∈ L_g.vertices.dropLast, x ∈ p.vertices.tail)
    (hR_drop_sub : ∀ x ∈ R_g.vertices.dropLast, x ∈ p.vertices.dropLast) :
    ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcation := by
  obtain ⟨huw_ne, hu_tail, hw_drop, _, _⟩ := hp
  have hu_notW : u ∉ W := notW_of_mem_marginalize hW hu
  have hw_notW : w ∉ W := notW_of_mem_marginalize hW hw
  have hvL_GV : vL ∈ G.V := (G.hL_subset hLR_G).1
  have hvR_GV : vR ∈ G.V := (G.hL_subset hLR_G).2
  have hvL_g : vL ∈ G := Finset.mem_union_right _ hvL_GV
  have hvR_g : vR ∈ G := Finset.mem_union_right _ hvR_GV
  have hvL_vR_ne : vL ≠ vR := G.hL_irrefl hLR_G
  -- Case-split on (vL ∈ W, vR ∈ W).  In each sub-case, set up:
  -- vL_exit, vR_exit, L_W_part, R_W_part, L_marg_part, R_marg_part.
  -- After setup, share the by_cases on degenerate (vL_exit = vR_exit).
  by_cases hvL_W : vL ∈ W
  · -- vL ∈ W: find_first_non_W on L_g.
    have hL_g_pos : L_g.length ≥ 1 :=
      Walk.length_pos_of_ne L_g (fun heq => hu_notW (heq ▸ hvL_W))
    obtain ⟨vL_exit, L_W_part, L_marg_part, hL_W_dir, hL_marg_dir, hL_W_pos,
            hvL_exit_notW, hL_W_inter, _, hL_g_vs_eq⟩ :=
      find_first_non_W_directed W L_g hL_dir hL_g_pos hu_notW
    have hvL_exit_GV : vL_exit ∈ G.V :=
      Walk.target_in_GV_of_directedWalk_pos L_W_part hL_W_dir hL_W_pos
    have hvL_exit_VW : vL_exit ∈ G.V \ W :=
      Finset.mem_sdiff.mpr ⟨hvL_exit_GV, hvL_exit_notW⟩
    have hL_marg_ne : L_marg_part.vertices ≠ [] := Walk.vertices_ne_nil L_marg_part
    have hL_marg_sub_L_g : ∀ x ∈ L_marg_part.vertices, x ∈ L_g.vertices := fun x hx =>
      by rw [hL_g_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
    have hL_marg_drop_sub_L_g_drop :
        ∀ x ∈ L_marg_part.vertices.dropLast, x ∈ L_g.vertices.dropLast := fun x hx => by
      rw [hL_g_vs_eq, List.dropLast_append_of_ne_nil hL_marg_ne]
      exact List.mem_append.mpr (Or.inr hx)
    have hu_notin_L_marg_drop : u ∉ L_marg_part.vertices.dropLast := fun h_in =>
      hu_tail (hL_drop_sub u (hL_marg_drop_sub_L_g_drop u h_in))
    have hw_notin_L_marg : w ∉ L_marg_part.vertices := fun h_in =>
      hw_drop (hL_sub w (hL_marg_sub_L_g w h_in))
    by_cases hvR_W : vR ∈ W
    · -- Sub-case (C): vL ∈ W AND vR ∈ W.  Apply find_first_non_W on R_g.
      have hR_g_pos : R_g.length ≥ 1 :=
        Walk.length_pos_of_ne R_g (fun heq => hw_notW (heq ▸ hvR_W))
      obtain ⟨vR_exit, R_W_part, R_marg_part, hR_W_dir, hR_marg_dir, hR_W_pos,
              hvR_exit_notW, hR_W_inter, _, hR_g_vs_eq⟩ :=
        find_first_non_W_directed W R_g hR_dir hR_g_pos hw_notW
      have hvR_exit_GV : vR_exit ∈ G.V :=
        Walk.target_in_GV_of_directedWalk_pos R_W_part hR_W_dir hR_W_pos
      have hvR_exit_VW : vR_exit ∈ G.V \ W :=
        Finset.mem_sdiff.mpr ⟨hvR_exit_GV, hvR_exit_notW⟩
      have hR_marg_ne : R_marg_part.vertices ≠ [] := Walk.vertices_ne_nil R_marg_part
      have hR_marg_sub_R_g : ∀ x ∈ R_marg_part.vertices, x ∈ R_g.vertices := fun x hx =>
        by rw [hR_g_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
      have hR_marg_drop_sub_R_g_drop :
          ∀ x ∈ R_marg_part.vertices.dropLast, x ∈ R_g.vertices.dropLast := fun x hx => by
        rw [hR_g_vs_eq, List.dropLast_append_of_ne_nil hR_marg_ne]
        exact List.mem_append.mpr (Or.inr hx)
      have hu_notin_R_marg : u ∉ R_marg_part.vertices := fun h_in =>
        hu_tail (hR_sub u (hR_marg_sub_R_g u h_in))
      have hw_notin_R_marg_drop : w ∉ R_marg_part.vertices.dropLast := fun h_in =>
        hw_drop (hR_drop_sub w (hR_marg_drop_sub_R_g_drop w h_in))
      have hvR_exit_ne_u : vR_exit ≠ u := fun heq =>
        hu_tail (hR_sub _ (hR_marg_sub_R_g _ (heq ▸ Walk.head_mem_vertices R_marg_part)))
      have hvL_exit_ne_w : vL_exit ≠ w := fun heq =>
        hw_drop (hL_sub _ (hL_marg_sub_L_g _ (heq ▸ Walk.head_mem_vertices L_marg_part)))
      exact marg_bif_forward_bidir_finish G W hW hu hw huw_ne
        hvL_g hvR_g hLR_G hvL_vR_ne hvL_exit_VW hvR_exit_VW
        L_W_part hL_W_dir hL_W_inter (Or.inl ⟨hL_W_pos, hvL_W⟩)
        R_W_part hR_W_dir hR_W_inter (Or.inl ⟨hR_W_pos, hvR_W⟩)
        L_marg_part hL_marg_dir R_marg_part hR_marg_dir
        hu_notin_L_marg_drop hu_notin_R_marg hw_notin_L_marg hw_notin_R_marg_drop
        hvR_exit_ne_u hvL_exit_ne_w
    · -- Sub-case (A): vL ∈ W, vR ∉ W.  R_W_part = nil at vR, vR_exit = vR.
      have hvR_exit_VW : vR ∈ G.V \ W := Finset.mem_sdiff.mpr ⟨hvR_GV, hvR_W⟩
      have hu_notin_R_g : u ∉ R_g.vertices := fun h_in => hu_tail (hR_sub u h_in)
      have hw_notin_R_g_drop : w ∉ R_g.vertices.dropLast := fun h_in =>
        hw_drop (hR_drop_sub w h_in)
      have hvR_ne_u : vR ≠ u := fun heq =>
        hu_tail (hR_sub _ (heq ▸ Walk.head_mem_vertices R_g))
      have hvL_exit_ne_w : vL_exit ≠ w := fun heq =>
        hw_drop (hL_sub _ (hL_marg_sub_L_g _ (heq ▸ Walk.head_mem_vertices L_marg_part)))
      have h_nil_R : (Walk.nil vR hvR_g : Walk G vR vR).length = 0 := rfl
      exact marg_bif_forward_bidir_finish G W hW hu hw huw_ne
        hvL_g hvR_g hLR_G hvL_vR_ne hvL_exit_VW hvR_exit_VW
        L_W_part hL_W_dir hL_W_inter (Or.inl ⟨hL_W_pos, hvL_W⟩)
        (Walk.nil vR hvR_g) trivial
        (by intro x hx; simp [Walk.vertices, List.tail, List.dropLast] at hx)
        (Or.inr ⟨h_nil_R, rfl⟩)
        L_marg_part hL_marg_dir R_g hR_dir
        hu_notin_L_marg_drop hu_notin_R_g hw_notin_L_marg hw_notin_R_g_drop
        hvR_ne_u hvL_exit_ne_w
  · -- vL ∉ W, so vR ∈ W.
    have hvR_W : vR ∈ W := hvL_or_vR_W.resolve_left hvL_W
    have hvL_VW : vL ∈ G.V \ W := Finset.mem_sdiff.mpr ⟨hvL_GV, hvL_W⟩
    have hR_g_pos : R_g.length ≥ 1 :=
      Walk.length_pos_of_ne R_g (fun heq => hw_notW (heq ▸ hvR_W))
    obtain ⟨vR_exit, R_W_part, R_marg_part, hR_W_dir, hR_marg_dir, hR_W_pos,
            hvR_exit_notW, hR_W_inter, _, hR_g_vs_eq⟩ :=
      find_first_non_W_directed W R_g hR_dir hR_g_pos hw_notW
    have hvR_exit_GV : vR_exit ∈ G.V :=
      Walk.target_in_GV_of_directedWalk_pos R_W_part hR_W_dir hR_W_pos
    have hvR_exit_VW : vR_exit ∈ G.V \ W :=
      Finset.mem_sdiff.mpr ⟨hvR_exit_GV, hvR_exit_notW⟩
    have hR_marg_ne : R_marg_part.vertices ≠ [] := Walk.vertices_ne_nil R_marg_part
    have hR_marg_sub_R_g : ∀ x ∈ R_marg_part.vertices, x ∈ R_g.vertices := fun x hx =>
      by rw [hR_g_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
    have hR_marg_drop_sub_R_g_drop :
        ∀ x ∈ R_marg_part.vertices.dropLast, x ∈ R_g.vertices.dropLast := fun x hx => by
      rw [hR_g_vs_eq, List.dropLast_append_of_ne_nil hR_marg_ne]
      exact List.mem_append.mpr (Or.inr hx)
    have hu_notin_R_marg : u ∉ R_marg_part.vertices := fun h_in =>
      hu_tail (hR_sub u (hR_marg_sub_R_g u h_in))
    have hw_notin_R_marg_drop : w ∉ R_marg_part.vertices.dropLast := fun h_in =>
      hw_drop (hR_drop_sub w (hR_marg_drop_sub_R_g_drop w h_in))
    have hu_notin_L_g_drop : u ∉ L_g.vertices.dropLast := fun h_in =>
      hu_tail (hL_drop_sub u h_in)
    have hw_notin_L_g : w ∉ L_g.vertices := fun h_in =>
      hw_drop (hL_sub w h_in)
    have hvR_exit_ne_u : vR_exit ≠ u := fun heq =>
      hu_tail (hR_sub _ (hR_marg_sub_R_g _ (heq ▸ Walk.head_mem_vertices R_marg_part)))
    have hvL_ne_w : vL ≠ w := fun heq =>
      hw_drop (hL_sub _ (heq ▸ Walk.head_mem_vertices L_g))
    have h_nil_L : (Walk.nil vL hvL_g : Walk G vL vL).length = 0 := rfl
    exact marg_bif_forward_bidir_finish G W hW hu hw huw_ne
      hvL_g hvR_g hLR_G hvL_vR_ne hvL_VW hvR_exit_VW
      (Walk.nil vL hvL_g) trivial
      (by intro x hx; simp [Walk.vertices, List.tail, List.dropLast] at hx)
      (Or.inr ⟨h_nil_L, rfl⟩)
      R_W_part hR_W_dir hR_W_inter (Or.inl ⟨hR_W_pos, hvR_W⟩)
      L_g hL_dir R_marg_part hR_marg_dir
      hu_notin_L_g_drop hu_notin_R_marg hw_notin_L_g hw_notin_R_marg_drop
      hvR_exit_ne_u hvL_ne_w


private lemma marg_preserves_bif_forward
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (h : ∃ p : Walk G u w, p.IsBifurcation) :
    ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcation := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨i, hp_split⟩ := hp.2.2.2
  by_cases h_dir : p.IsBifurcationDirectedHingeWithSplit i
  · obtain ⟨c, _, _, _, _, _, _, hidx, _, _, _, _⟩ :=
      Walk.exists_arms_of_bifurcation_directed_hinge_strong p i h_dir
    by_cases hc_marg : c ∈ G.marginalize W hW
    · exact marg_bif_forward_dir_hinge_src_marg G W hW hu hw hp h_dir hidx hc_marg
    · exact marg_bif_forward_dir_hinge_src_W G W hW hu hw hp h_dir hidx hc_marg
  · obtain ⟨vL, vR, L_g, R_g, hL_dir, hR_dir, hLR_G, _,
            hL_sub, hR_sub, hL_drop_sub, hR_drop_sub⟩ :=
      Walk.exists_arms_of_bifurcation_bidir_hinge_strong p i hp_split h_dir
    by_cases hvL_W : vL ∈ W
    · exact marg_bif_forward_bidir_with_W G W hW hu hw hp (Or.inl hvL_W)
        L_g R_g hL_dir hR_dir hLR_G hL_sub hR_sub hL_drop_sub hR_drop_sub
    · by_cases hvR_W : vR ∈ W
      · exact marg_bif_forward_bidir_with_W G W hW hu hw hp (Or.inr hvR_W)
          L_g R_g hL_dir hR_dir hLR_G hL_sub hR_sub hL_drop_sub hR_drop_sub
      · exact marg_bif_forward_bidir_both_notW G W hW hu hw hp
          hvL_W hvR_W L_g R_g hL_dir hR_dir hLR_G
          hL_sub hR_sub hL_drop_sub hR_drop_sub

-- ## Wrapper: backward direction (case-splits on hinge type).

private lemma marg_preserves_bif_backward
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.V) {u w : Node}
    (hu : u ∈ G.marginalize W hW) (hw : w ∈ G.marginalize W hW)
    (h : ∃ q : Walk (G.marginalize W hW) u w, q.IsBifurcation) :
    ∃ p : Walk G u w, p.IsBifurcation := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨i, hq_split⟩ := hq.2.2.2
  by_cases h_dir : q.IsBifurcationDirectedHingeWithSplit i
  · exact marg_bif_backward_dir_hinge G W hW hu hw hq h_dir
  · exact marg_bif_backward_bidir_hinge G W hW hu hw hq hq_split h_dir

-- ref: claim_3_16 (sub-claim i, preservation of ancestral relations)
--
-- For a CDMG `G`, a subset `W ⊆ G.V`, and two nodes `v₁, v₂` both
-- in the marginalized carrier `J ∪ (V ∖ W)` (i.e.\ in the carrier of
-- `G.marginalize W hW`), `v₁` is an ancestor of `v₂` in `G` iff
-- `v₁` is an ancestor of `v₂` in the marginalization `G^{∖W}`.
--
-- The biconditional is the LN's literal sub-claim i: marginalizing
-- away the nodes of `W` does not change ancestral relations between
-- *remaining* nodes — every directed `G`-walk between two non-`W`
-- nodes maps to a directed `G^{∖W}`-walk (collapsing each maximal
-- `W`-segment into a single `E^{∖W}`-edge per `def_3_14` item iii),
-- and conversely.
/-
LN tex (sub-claim i, from the canonical statement):

  i.) Preservation of ancestral relations.  For every pair of nodes
      `v_1, v_2 ∈ (J ∪ V) ∖ W = J ∪ (V ∖ W)`, the biconditional
        `v_1 ∈ Anc^G(v_2)  ⟺  v_1 ∈ Anc^{G^{∖W}}(v_2)`
      holds, where `Anc^G(v_2)` is the ancestor set of `v_2` in `G`
      in the sense of def \ref{def_3_5}, item~iv, evaluated on the
      carrier `J ∪ V`, and `Anc^{G^{∖W}}(v_2)` is the ancestor set
      of `v_2` in `G^{∖W}`, also in the sense of def \ref{def_3_5},
      item~iv, applied to the CDMG `G^{∖W}` and so evaluated on the
      carrier `J ∪ (V ∖ W)`.
-/
-- ## Design choice
--
-- *Five separate theorems (one per sub-assertion), mirroring the
--   `extAcyclic` / `extRestrictsTopologicalOrder` /
--   `extExtendsTopologicalOrder` split in
--   `AcyclicHardInterventionTopologicalOrder.lean` and the
--   `splAcyclic` / `splTopologicalOrder` /
--   `swigAcyclic` / `swigTopologicalOrder` precedents.*  See the
--   shared "five theorems vs.\ one bundled conjunction" bullet on
--   the last theorem of this file (`marginalize_restricts_topological_order`)
--   for the full rationale.  The short version: the five sub-claims
--   have *different hypotheses* (only iii needs `G.IsAcyclic` or a
--   topological-order witness `lt`) and *different conclusions*
--   (ancestor / bifurcation / acyclicity / topological-order), so
--   bundling them into one theorem would force every consumer to
--   take all the additional hypotheses it does not need, or to
--   destructure a product type at every call site.  The LN-faithful
--   reading "the remark holds" is preserved because all five
--   theorems live under the same `-- ref: claim_3_16` heading.
--
-- *Hypotheses ordered `(G, W, hW, v₁, v₂, hv₁, hv₂)`.*  The shared
--   prefix `(G, W, hW)` matches `def_3_14 marginalize`'s binder
--   ordering exactly and is reused across all five theorems below.
--   `v₁` precedes `v₂` to match the LN's reading `v_1 ∈ Anc^G(v_2)`
--   (`v_1` is the ancestor, `v_2` is the descendant).  The
--   membership hypotheses `hv₁`, `hv₂` come last to mirror
--   `bifurcationAlternative`'s convention
--   (`(G) (v w c) (hv) (hw) (hc) : …`).
--
-- *`v₁ v₂` as explicit positional binders, not implicit.*  The LN
--   universally quantifies over `v_1, v_2 ∈ (J ∪ V) ∖ W`, and
--   downstream consumers typically apply this theorem to specific
--   `v₁, v₂` they have in hand (e.g.\ a do-calculus identification
--   argument's "for this particular outcome node `Y` and this
--   particular ancestor `X`").  Implicit binders would force every
--   such call site to bracket-apply via `@`.  Matches the explicit
--   convention of `bifurcationAlternative`.
--
-- *Membership hypothesis `v₁ ∈ G.marginalize W hW` (not the
--   set-theoretic `v₁ ∈ G ∧ v₁ ∉ W` spelling).*  Both denote the
--   same set `G.J ∪ (G.V ∖ W)`, but the marginalize-pointing form
--   (i) reads directly as "in the carrier of `G^{∖W}`" — the LN's
--   `v_1 ∈ G^{∖W}` reading; (ii) lifts cleanly through
--   `Membership Node (CDMG Node)` (`def_3_2`) without unfolding
--   `marginalize`'s field assignments at every use site; (iii) is
--   ergonomic for downstream consumers that pass through other CDMG
--   operators (e.g.\ `(G.marginalize W₁ hW₁).marginalize W₂ hW₂` in
--   `claim_3_17`).  The set-theoretic form is recovered on demand
--   by `unfold CDMG.marginalize` plus `Finset.mem_union`,
--   `Finset.mem_sdiff`.
--
-- *Conclusion `v₁ ∈ G.Anc v₂ ↔ v₁ ∈ (G.marginalize W hW).Anc v₂`.*
--   The two sides differ in which CDMG's `Anc` is invoked, exactly
--   mirroring the LN's `Anc^G(v_2)` vs `Anc^{G^{∖W}}(v_2)`.
--   `Set`-membership `v₁ ∈ G.Anc v₂` lifts from `def_3_5` `Anc`'s
--   `Set Node` return type without any coercion noise.
--
-- *No `v₁ ≠ v₂` precondition.*  The LN does not impose `v_1 ≠ v_2`;
--   in fact `v_1 = v_2` is admitted and the biconditional holds
--   tautologically (`v₁ ∈ G.Anc v₁` is *true* by `Anc`'s self-
--   membership note from `def_3_5` addition
--   `[self_membership_notes_require_length_zero_walks]`, witnessed
--   by the trivial walk `Walk.nil v₁ hv₁`; same for the
--   marginalized side).  Imposing `v₁ ≠ v₂` would silently weaken
--   the LN's universal quantifier.

-- claim_3_16 -- start statement
theorem marginalize_preserves_ancestors (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) (v₁ v₂ : Node)
    (hv₁ : v₁ ∈ G.marginalize W hW) (hv₂ : v₂ ∈ G.marginalize W hW) :
    v₁ ∈ G.Anc v₂ ↔ v₁ ∈ (G.marginalize W hW).Anc v₂
-- claim_3_16 -- end statement
  := by
  -- Sub-claim i: the projection / expansion duality on directed walks
  -- (`def_3_5` item iv) under marginalization.  Each direction unfolds
  -- `Anc` (`def_3_5`) to "exists a directed walk", then
  -- projects (⟹) via `project_directed_walk_marginalize` or expands
  -- (⟸) via `expand_directed_walk_marginalize`.
  constructor
  · -- (⟹) forward direction: project the directed `G`-walk.
    rintro ⟨_, p, hp_dir⟩
    refine ⟨hv₁, ?_⟩
    exact project_directed_walk_marginalize p hp_dir hv₁ hv₂
  · -- (⟸) converse direction: expand the directed marg-walk.
    rintro ⟨_, p, hp_dir⟩
    refine ⟨mem_of_mem_marginalize hv₁, ?_⟩
    obtain ⟨q, hq_dir, _, _, _⟩ := expand_directed_walk_marginalize p hp_dir
    exact ⟨q, hq_dir⟩

-- ref: claim_3_16 (sub-claim ii(a), preservation of bifurcations — sourceless)
--
-- For a CDMG `G`, a subset `W ⊆ G.V`, and two nodes `v₁, v₂` both
-- in the marginalized carrier `J ∪ (V ∖ W)`, there exists a
-- bifurcation between `v₁` and `v₂` in `G` (per `def_3_4` item~vi)
-- iff there exists a bifurcation between `v₁` and `v₂` in
-- `G^{∖W}`.  This is the *sourceless* reading of the LN's
-- parenthetical phrase, made explicit by `addition_to_the_LN`
-- clause (a) — see the file-header note.
--
-- The bifurcation existential is encoded *symmetrically* in `(v₁,
-- v₂)` as a disjunction `(∃ p : Walk H v₁ v₂, p.IsBifurcation) ∨
-- (∃ p : Walk H v₂ v₁, p.IsBifurcation)`, mirroring the convention
-- of `MarginalizationΦL` in `def_3_14` (`MarginalizationAK.lean`).
-- The LN's `{w_0, w_n} = {v_1, v_2}` set-equality on walk endpoints
-- admits either orientation; in Lean, `Walk H u v` and `Walk H v u`
-- are distinct types, so the symmetric existential takes a
-- disjunction over the two walk-directions.  Semantically both
-- disjuncts agree (a bifurcation is graph-theoretically symmetric
-- in its endpoints), so the `∨` does not strengthen / weaken the
-- predicate.
/-
LN tex (sub-claim ii(a), from the canonical statement):

  ii.) (a) Sourceless biconditional.  For every pair of nodes
       `v_1, v_2 ∈ (J ∪ V) ∖ W`, the following two propositions
       are equivalent:
       * There exists a bifurcation between `v_1` and `v_2` in `G`
         in the sense of def \ref{def:walks}, item~vi: i.e.\ there
         exist an integer `n ≥ 1`, an index `k ∈ {1, …, n}`, and a
         walk `p = (w_0, a_0, w_1, …, a_{n-1}, w_n)` in `G` with
         `{w_0, w_n} = {v_1, v_2}` satisfying clauses (a)–(e).
       * The analogous existential in `G^{∖W}`, with `E` and `L`
         read against `E^{∖W}` and `L^{∖W}`.
-/
-- ## Design choice
--
-- *Symmetric disjunction over walk orientations.*  Mirrors
--   `def_3_14` `MarginalizationΦL`'s shape:
--     `(∃ p : Walk H v₁ v₂, p.IsBifurcation) ∨
--      (∃ p : Walk H v₂ v₁, p.IsBifurcation)`.
--   `Walk.IsBifurcation` (per `def_3_4`'s addition
--   `[bifurcation_index_boundary_excludes_natural_cases]`) admits
--   `n = 1` (direct bidirected edge), `n = 2, k = 1` (Y-fork), and
--   `n = 2, k = n` (mirror Y) as boundary cases, which is exactly
--   what the LN's "in the sense of def_3_4 item~vi" requires.
--   The two disjuncts are semantically equivalent — a bifurcation
--   is symmetric in its endpoints — so the disjunction does not
--   weaken or strengthen the predicate; it makes the symmetry
--   *evident* at the type level, which the proof phase will
--   exploit when invoking `Or.comm` / `Or.symm` to swap
--   orientations.
--
-- *Load-bearing boundary case for the LHS→RHS direction (against
--   the LN-critic corner case
--   `bifurcation_no_source_existential_admits_w_source`).*  The
--   previous bullet cites the `n = 1` direct-bidirected-edge
--   case as a *what* — it is also a *why*: it is precisely what
--   makes the sourceless biconditional sound, and without it the
--   `→` direction would fail.  Concrete corner case (resolved
--   subtlety 2 in the file-header docstring): suppose
--   `v₁, v₂ ∈ V ∖ W` and the *only* bifurcation between them in
--   `G` is the `Y`-fork `v₁ ← w → v₂` with `w ∈ W` — no other
--   common-source vertex in `J ∪ V`, no bidirected edge
--   `{v₁, v₂} ∈ G.L`.  The LHS is witnessed by the walk
--   `(v₁, (w, v₁), w, (w, v₂), v₂)` of length `n = 2, k = 1`.
--   `def_3_14`'s `MarginalizationΦL` predicate (definitionally:
--   "`∃` `IsBifurcation` walk whose interior vertices all lie in
--   `W`") fires on exactly this walk, so `marginalize` inserts
--   `{v₁, v₂} ∈ L^{∖W}` via the `marg_L` field's `Finset.filter`
--   over `MarginalizationΦL`.  The *only* `G^{∖W}` witness for
--   the RHS is then the bidirected walk
--   `(v₁, {v₁, v₂}, v₂)` of length `n' = 1, k' = 1` — and were
--   `n = 1` excluded from `Walk.IsBifurcation`, the LHS→RHS
--   direction would falsify on this case (no length-`≥ 2`
--   counterpart exists in `G^{∖W}`, since marginalization
--   removed the hinge `w`).  The chapter-init addition
--   `[bifurcation_index_boundary_excludes_natural_cases]` of
--   `def_3_4` was authored precisely to admit this `n = 1`
--   boundary case (alongside the symmetric `n = 2` Y-fork
--   cases); the biconditional therefore *requires* that addition
--   for soundness, and any future refactor of `Walk.IsBifurcation`
--   that tightens the boundary (e.g.\ a strict three-vertex-fork
--   reading of `def_3_4` item~vi) would silently break this
--   theorem.  The corner case does *not* arise for the sourced
--   form (b) below: there the source `v₃` is named on both sides
--   of the biconditional and required to lie in `J ∪ (V ∖ W)`,
--   so a Y-fork with marginalized hinge `w ∈ W` cannot be a
--   sourced witness with `v₃ = w` (it would demand `w ∉ W`,
--   contradiction).
--
-- *No helper predicate `existsBifurcationBetween`.*  Considered
--   and rejected.  The two-disjunct existential is short enough
--   to read inline; introducing a helper would duplicate
--   information already encoded in `Walk.IsBifurcation` (which
--   the canonical tex points to as "the sense of def_3_4 item~vi"),
--   without serving downstream consumers — `claim_3_17`
--   (marginalizations commute), `claim_3_18` (marg-vs-intervention),
--   and `claim_3_19` (empty marginalization) all reason directly
--   on `Walk.IsBifurcation`, not on a derived "exists-between"
--   wrapper.  Should a future row (e.g.\ a sigma-AMP reduction
--   referencing bifurcations between two named nodes) require the
--   wrapper, it can be added there without retroactively touching
--   this file.
--
-- *Membership hypotheses `hv₁, hv₂` on `G.marginalize W hW`.*
--   Same rationale as for `marginalize_preserves_ancestors`.  The
--   LN's literal "for $v_1, v_2 \in G \sm W$" reads as
--   `v_1, v_2 ∈ J ∪ (V ∖ W)`, the carrier of `G.marginalize W hW`.
--   Input-node endpoints (`v_1 ∈ J`) are admitted by the LN's
--   outer quantifier; per the canonical tex's "Reading of the
--   precondition" paragraph, clauses (b) and (c) of
--   `def_3_4` item~vi automatically force the bifurcation walk's
--   endpoints into `G.V`, so an input-node endpoint simply makes
--   both sides of the biconditional vacuously false.  The
--   broader outer quantifier `(J ∪ V) ∖ W` is LN-faithful and the
--   biconditional remains correct on input-node endpoints
--   (vacuously true).

-- claim_3_16 -- start statement
theorem marginalize_preserves_bifurcation (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) (v₁ v₂ : Node)
    (hv₁ : v₁ ∈ G.marginalize W hW) (hv₂ : v₂ ∈ G.marginalize W hW) :
    ((∃ p : Walk G v₁ v₂, p.IsBifurcation) ∨
        (∃ p : Walk G v₂ v₁, p.IsBifurcation))
      ↔
    ((∃ p : Walk (G.marginalize W hW) v₁ v₂, p.IsBifurcation) ∨
        (∃ p : Walk (G.marginalize W hW) v₂ v₁, p.IsBifurcation))
-- claim_3_16 -- end statement
  := by
  -- Sub-claim ii(a) (sourceless bifurcation biconditional).
  -- Wires up the per-direction helpers, which themselves dispatch to the
  -- per-case leaf helpers (forward directed-hinge × source ∈ marg / W,
  -- forward bidirected-hinge × vL/vR ∈ W mix, backward directed-hinge /
  -- bidirected-hinge).
  constructor
  · rintro (⟨p, hp⟩ | ⟨p, hp⟩)
    · exact Or.inl (marg_preserves_bif_forward G W hW hv₁ hv₂ ⟨p, hp⟩)
    · exact Or.inr (marg_preserves_bif_forward G W hW hv₂ hv₁ ⟨p, hp⟩)
  · rintro (⟨q, hq⟩ | ⟨q, hq⟩)
    · exact Or.inl (marg_preserves_bif_backward G W hW hv₁ hv₂ ⟨q, hq⟩)
    · exact Or.inr (marg_preserves_bif_backward G W hW hv₂ hv₁ ⟨q, hq⟩)

-- ref: claim_3_16 (sub-claim ii(b), preservation of bifurcations — sourced)
--
-- For a CDMG `G`, a subset `W ⊆ G.V`, and three nodes
-- `v₁, v₂, v₃` all in the marginalized carrier `J ∪ (V ∖ W)`,
-- there exists a bifurcation between `v₁` and `v₂` with source
-- `v₃` in `G` (per `def_3_4` item~vi's "Source of the
-- bifurcation" paragraph, encoded by `Walk.IsBifurcationSource`)
-- iff there exists one in `G^{∖W}`.  This is the *sourced*
-- reading of the LN's parenthetical phrase, made explicit by
-- `addition_to_the_LN` clause (b) — see the file-header note.
/-
LN tex (sub-claim ii(b), from the canonical statement):

  ii.) (b) Sourced biconditional.  For every triple of nodes
       `v_1, v_2, v_3 ∈ (J ∪ V) ∖ W`, the following two
       propositions are equivalent:
       * There exists a bifurcation between `v_1` and `v_2` with
         source `v_3` in `G`, in the sense of def \ref{def:walks},
         item~vi, and its closing paragraph "Source of the
         bifurcation": i.e.\ a walk `p` with
         `{w_0, w_n} = {v_1, v_2}` satisfying clauses (a)–(e), and
         clause (d) realised at index `k` by the directed alternative
         `a_{k-1} = (w_k, w_{k-1}) ∈ E` with `w_k = v_3`.
       * The analogous existential in `G^{∖W}`.
-/
-- ## Design choice
--
-- *Symmetric disjunction over walk orientations.*  Same rationale
--   as for `marginalize_preserves_bifurcation` above: the LN's
--   "between `v_1` and `v_2`" reading admits either walk
--   orientation, and `Walk H u v` vs `Walk H v u` are distinct
--   types in Lean.  The source `v₃` is fixed across both
--   disjuncts.
--
-- *`p.IsBifurcationSource v₃`, not a pair `p.IsBifurcation ∧
--   p.IsBifurcationSource v₃`.*  `Walk.IsBifurcationSource`
--   (`def_3_4` `Walks.lean:1124`) already includes every conjunct
--   of `Walk.IsBifurcation` (the `u ≠ v`, end-node-uniqueness, and
--   "exists a split index" clauses) and additionally pins the
--   split index's hinge to a *directed* alternative with `v₃` at
--   the hinge's interior position.  The two-conjunct spelling
--   would be a redundant strengthening, since
--   `IsBifurcationSource → IsBifurcation` is a one-line corollary
--   the proof phase can derive on demand.
--
-- *Source `v₃` may be an input node `v₃ ∈ J`.*  The canonical
--   tex's "Reading of the precondition" paragraph is explicit:
--   while the bifurcation endpoints `v₁, v₂` are automatically
--   forced into `G.V` by clauses (b) and (c) of `def_3_4`
--   item~vi (so an input-node endpoint makes both sides
--   vacuously false), the source `v₃ = w_k` is *not* so forced.
--   Clause (d)'s directed alternative `a_{k-1} = (w_k, w_{k-1}) ∈
--   E` together with `E ⊆ (J ∪ V) × V` only implies
--   `w_{k-1} ∈ V`; `w_k` itself may lie in `J`.  This matches
--   `claim_3_5`'s `bifurcationAlternative` typing
--   `c ∈ J ∪ V` for the source.  Hence the broader outer
--   quantifier `(J ∪ V) ∖ W` on `v₃` is non-vacuously needed —
--   a genuinely useful generality, not a vacuous artifact.
--
-- *Three membership hypotheses `hv₁, hv₂, hv₃`.*  Per the LN's
--   "for every triple `v_1, v_2, v_3 ∈ (J ∪ V) ∖ W`".  The
--   hypotheses are independent of each other (no `v_i ≠ v_j`
--   conjuncts) — `Walk.IsBifurcationSource` already encodes the
--   structural distinctness (the source is automatically an
--   interior vertex distinct from both endpoints by clause (e),
--   plus `u ≠ v` for the endpoints), so adding `v_i ≠ v_j`
--   preconditions would silently weaken the LN's universal
--   quantifier on degenerate triples (which the biconditional
--   handles vacuously).

-- claim_3_16 -- start statement
theorem marginalize_preserves_bifurcation_with_source (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.V) (v₁ v₂ v₃ : Node)
    (hv₁ : v₁ ∈ G.marginalize W hW) (hv₂ : v₂ ∈ G.marginalize W hW)
    (hv₃ : v₃ ∈ G.marginalize W hW) :
    ((∃ p : Walk G v₁ v₂, p.IsBifurcationSource v₃) ∨
        (∃ p : Walk G v₂ v₁, p.IsBifurcationSource v₃))
      ↔
    ((∃ p : Walk (G.marginalize W hW) v₁ v₂, p.IsBifurcationSource v₃) ∨
        (∃ p : Walk (G.marginalize W hW) v₂ v₁, p.IsBifurcationSource v₃))
-- claim_3_16 -- end statement
  := by
  -- Apply the forward/backward orientation-helpers to each disjunct.
  constructor
  · rintro (h12 | h21)
    · exact Or.inl (marg_preserves_bifSource_forward G W hW hv₁ hv₂ hv₃ h12)
    · exact Or.inr (marg_preserves_bifSource_forward G W hW hv₂ hv₁ hv₃ h21)
  · rintro (h12 | h21)
    · exact Or.inl (marg_preserves_bifSource_backward G W hW hv₁ hv₂ hv₃ h12)
    · exact Or.inr (marg_preserves_bifSource_backward G W hW hv₂ hv₁ hv₃ h21)

-- ref: claim_3_16 (sub-claim iii(a), preservation of acyclicity)
--
-- If `G` is acyclic in the sense of `def_3_6`, then so is the
-- marginalization `G.marginalize W hW`.  No topological-order
-- witness is required for this sub-claim; the conclusion
-- `(G.marginalize W hW).IsAcyclic` is a universal statement
-- ranging over `v ∈ G.marginalize W hW`.
--
-- *Why acyclicity is preserved.*  Every directed walk in
-- `G^{∖W}` lifts to a directed walk in `G` (each `E^{∖W}`-edge
-- expands to a directed walk-through-`W` in `G` by
-- `MarginalizationΦE`; concatenating the expanded walks of a
-- `G^{∖W}`-cycle yields a `G`-cycle of length `≥ 1`).  So any
-- non-trivial directed cycle in `G^{∖W}` would induce one in
-- `G`, contradicting `G.IsAcyclic`.
/-
LN tex (sub-claim iii(a), from the canonical statement):

  iii.) (a) Acyclicity is preserved.  `G^{∖W}` is acyclic in the
        sense of def \ref{def-acylic}, evaluated on the carrier
        `J ∪ (V ∖ W)` of `G^{∖W}`: explicitly, for every
        `v ∈ J ∪ (V ∖ W)`, there does not exist any non-trivial
        directed walk from `v` to `v` in `G^{∖W}`.
-/
-- ## Design choice
--
-- *Single-theorem statement (sub-claim iii(a) only), separated
--   from iii(b).*  Matches the `extAcyclic` /
--   `extRestrictsTopologicalOrder` split in
--   `AcyclicHardInterventionTopologicalOrder.lean` and the
--   `splAcyclic` / `splTopologicalOrder` split in
--   `SplitTopologicalOrder.lean`.  The two sub-claims have
--   *different downstream consumers*: the do-calculus /
--   counterfactual chapters typically need `(G.marginalize W
--   hW).IsAcyclic` to lift the CDMG-typed result to a CADMG and
--   invoke chapter-4 / 5 CBN-shaped results — without ever
--   mentioning a chosen topological order.  Bundling
--   `IsAcyclic` and `IsTopologicalOrder` into one theorem would
--   force every such consumer to take a topological-order
--   argument it does not use.  Separate theorems keep each
--   statement focused.
--
-- *`G.IsAcyclic` hypothesis, not `G.IsCADMG`.*  Sub-claim iii(a)
--   reads "If `G` is acyclic ..." — `def_3_6`'s `IsAcyclic`, not
--   `def_3_7`'s richer `IsCADMG` (= `IsAcyclic ∧ <bidirected
--   restrictions>`).  Marginalization does *not* require the
--   CADMG-style bidirected-edge constraints to preserve
--   acyclicity; only directed-walk preservation is at stake.
--   Tightening the hypothesis to `G.IsCADMG` would be
--   over-committed and would force downstream consumers that
--   have only an `IsAcyclic` witness (e.g.\ from `claim_3_2`'s
--   `acyclic_iff_topological_order`) to first lift to `IsCADMG`
--   before applying this theorem.
--
-- *Hypotheses ordered `(G, W, hW, hAcyc)`.*  Matches the
--   `extAcyclic` ordering on the shared `(G, W, hW)` prefix and
--   appends `hAcyc` at the end — the *additional* hypothesis
--   this sub-claim needs.  Same as the
--   `swigAcyclic` / `splAcyclic` convention.
--
-- *Conclusion via dot-notation `(G.marginalize W hW).IsAcyclic`.*
--   Reads as "the marginalization is acyclic"; matches the
--   chapter convention.
--
-- *Downstream consumers.*  `claim_3_17` (marginalizations
--   commute), `claim_3_18` (marginalization vs hard
--   intervention), `claim_3_19` (empty marginalization), and
--   downstream chapter-5 do-calculus / counterfactual
--   identification arguments that build CBN factorisations on
--   `G^{∖W}` consume this theorem to upgrade `G.marginalize W
--   hW : CDMG Node` to an `IsCADMG` graph.

-- claim_3_16 -- start statement
theorem marginalize_preserves_acyclic (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.V) (hAcyc : G.IsAcyclic) :
    (G.marginalize W hW).IsAcyclic
-- claim_3_16 -- end statement
  := by
  -- Sub-claim iii(a): a non-trivial directed cycle in `G^{∖W}` would
  -- lift to a non-trivial directed cycle in `G` via
  -- `expand_directed_walk_marginalize`, contradicting `G.IsAcyclic`.
  intro v hv_marg ⟨p, hp_dir, hp_pos⟩
  have hv_g : v ∈ G := mem_of_mem_marginalize hv_marg
  obtain ⟨q, hq_dir, hq_len, _, _⟩ := expand_directed_walk_marginalize p hp_dir
  have hq_pos : q.length ≥ 1 := by omega
  exact hAcyc v hv_g ⟨q, hq_dir, hq_pos⟩

-- ref: claim_3_16 (sub-claim iii(b), topological order via restriction)
--
-- For a CDMG `G`, a subset `W ⊆ G.V`, and any topological order
-- `lt` of `G` in the sense of `def_3_8`, the *same* relation
-- `lt : Node → Node → Prop` is a topological order of the
-- marginalization `G.marginalize W hW`.
--
-- *Why "the same `lt`" realises the LN's "induces by just
--   ignoring the nodes from `W`" prose.*  The LN's restriction
-- operation reads: define `<_{G^{∖W}}` on `J ∪ (V ∖ W)` by
-- `v_1 <_{G^{∖W}} v_2 :⟺ v_1 <_G v_2` for `v_1, v_2 ∈ J ∪ (V ∖
-- W)`.  In Lean's encoding, `def_3_8` `IsTopologicalOrder`
-- already uses the membership idiom `∀ v ∈ G, …` everywhere
-- (irreflexivity, transitivity, trichotomy, parent-precedence),
-- so the *same* `lt : Node → Node → Prop` evaluated against
-- `G.marginalize W hW` automatically restricts its quantifiers
-- to the smaller carrier `J ∪ (V ∖ W)`.  No syntactic
-- "restriction operation" on the relation is needed —
-- restriction is *invisible at the type level* because
-- marginalization keeps the original `Node` carrier (unlike
-- `claim_3_13` `AcyclicHardInterventionTopologicalOrder`, whose
-- `extOrder` / `restrictOrder` helpers bridge the tagged-sum
-- carrier change `Node ↔ IntExtNode Node`).
/-
LN tex (sub-claim iii(b), from the canonical statement):

  iii.) (b) Topological order is induced by restriction.  For
        every binary relation `<_G` on `J ∪ V` that is a
        topological order of `G` in the sense of def
        \ref{def-topological-order}, the binary relation
        `<_{G^{∖W}}` on `J ∪ (V ∖ W)` defined by restriction of
        `<_G` to the smaller carrier, namely
          ∀ v_1, v_2 ∈ J ∪ (V ∖ W) :
            v_1 <_{G^{∖W}} v_2  :⟺  v_1 <_G v_2,
        is a topological order of `G^{∖W}` in the sense of def
        \ref{def-topological-order}, evaluated on the carrier
        `J ∪ (V ∖ W)` of `G^{∖W}`.
-/
-- ## Design choice
--
-- *Five theorems vs.\ one bundled conjunction — picked FIVE.*
--   The LN bundles i, ii(a), ii(b), iii(a), iii(b) inside one
--   `\begin{Rem}`, but the five sub-assertions have *different
--   hypotheses* and *different conclusions*:
--     · i takes only `(G, W, hW, v₁, v₂, hv₁, hv₂)` and
--       concludes a biconditional on `Anc`;
--     · ii(a) takes `(G, W, hW, v₁, v₂, hv₁, hv₂)` and concludes
--       a biconditional on `∃ Walk … IsBifurcation`;
--     · ii(b) takes the same prefix plus `(v₃, hv₃)` and
--       concludes a biconditional on `∃ Walk … IsBifurcationSource`;
--     · iii(a) takes `(G, W, hW, hAcyc)` and concludes
--       `(G.marginalize W hW).IsAcyclic`;
--     · iii(b) takes `(G, W, hW, lt, hlt)` and concludes
--       `(G.marginalize W hW).IsTopologicalOrder lt`.
--   Bundling them into one conjunction theorem would force every
--   consumer to take all the additional hypotheses (acyclicity,
--   `lt`, and per-node membership) it does not need, or to
--   project through `.1` / `.2` / `.2.1` / `.2.2` / `.2.2.1` /
--   `.2.2.2` with substantial use-site noise.  Five separate
--   theorems keep each statement focused and let downstream
--   consumers cite the sub-claim they need by name.  Matches the
--   `claim_3_13` (`extAcyclic` / `extRestrictsTopologicalOrder` /
--   `extExtendsTopologicalOrder`) split exactly (carrier change
--   case) and the `claim_3_6` / `claim_3_9`
--   (`splAcyclic` / `splTopologicalOrder` /
--   `swigAcyclic` / `swigTopologicalOrder`) split (no carrier
--   change here, so no `extOrder` / `restrictOrder` helpers
--   needed — see below).
--
-- *Same `lt : Node → Node → Prop` for both `G` and
--   `G.marginalize W hW`, not a restricted relation `lt' :
--   (J ∪ (V ∖ W)) → (J ∪ (V ∖ W)) → Prop` or a
--   `restrictOrder`-style helper.*  Marginalization keeps the
--   original `Node` carrier (per `def_3_14`'s "Carrier of the
--   result is `Node`, NOT a tagged-sum carrier" design bullet),
--   so the LN's restriction operation
--   `v_1 <_{G^{∖W}} v_2 :⟺ v_1 <_G v_2` on `v_1, v_2 ∈ J ∪
--   (V ∖ W)` is realised in Lean by *literally the same `lt`*
--   passed to `IsTopologicalOrder` against the smaller graph
--   `G.marginalize W hW`.  `IsTopologicalOrder`'s
--   `∀ v ∈ G^{∖W}, …` quantifier (`def_3_8`) automatically
--   restricts the effective domain.  Contrast with `claim_3_13`
--   `AcyclicHardInterventionTopologicalOrder`'s
--   `restrictOrder lt' v1 v2 := lt' (.unsplit v1) (.unsplit v2)`,
--   which bridges the *carrier change* `Node ↔ IntExtNode Node`
--   via the `.unsplit` inclusion — that machinery is irrelevant
--   here because marginalization has no such carrier change.
--
-- *No `extOrder` / `restrictOrder` helper needed.*
--   `IsTopologicalOrder` uses the membership-side-condition idiom
--   (`∀ v ∈ G, …`), so the LN's restriction transports verbatim
--   with no auxiliary helper.  Introducing one would add noise
--   without changing the statement's content; future downstream
--   rows that need a Prop-level restriction operator on relations
--   can define it locally where needed.
--
-- *`lt` and `hlt` as explicit positional arguments, not bundled
--   into an inner `∀ lt, …` quantifier.*  Same rationale as
--   `extRestrictsTopologicalOrder` / `extExtendsTopologicalOrder`
--   in `AcyclicHardInterventionTopologicalOrder.lean` and
--   `swigTopologicalOrder` in `SwigAcyclic.lean`: outer binders
--   read more naturally at the call site
--   (`G.marginalize_restricts_topological_order W hW lt hlt`
--   reads left-to-right) and avoid forcing consumers to
--   destructure an inner forall.
--
-- *`lt` typed as a bare `Node → Node → Prop`, not as a
--   `[LT Node]` / `[LinearOrder Node]` typeclass instance.*
--   Same rationale as `def_3_8`'s `IsTopologicalOrder` and every
--   sibling `*TopologicalOrder` theorem in chapter 3: the LN's
--   "for every topological order `<_G` of `G`" universally
--   quantifies over an arbitrary relation, not over a
--   typeclass-resolved canonical order.  Encoding `lt` as a
--   positional argument and `hlt` as a hypothesis matches that
--   reading.
--
-- *Hypotheses ordered `(G, W, hW, lt, hlt)`.*  Matches the
--   `marginalize_preserves_acyclic` ordering on the shared
--   `(G, W, hW)` prefix and appends `(lt, hlt)` — the
--   *additional* hypotheses sub-claim iii(b) needs over the bare
--   marginalize signature.  Mirrors
--   `extRestrictsTopologicalOrder` and `swigTopologicalOrder`.
--
-- *No `G.IsAcyclic` hypothesis.*  Sub-claim iii(b) does not
--   require `G.IsAcyclic` directly — the parent-precedence /
--   total-order properties of `lt` transport pointwise from
--   `G` to `G.marginalize W hW` via the carrier inclusion
--   `J ∪ (V ∖ W) ⊆ J ∪ V`.  In practice, the existence of a
--   topological order on `G` *implies* `G.IsAcyclic` (via
--   `claim_3_2` `acyclic_iff_topological_order`), so `hlt`
--   already entails what `G.IsAcyclic` would have provided.
--   Mirrors `extRestrictsTopologicalOrder` / `swigTopologicalOrder`
--   which also drop the explicit acyclicity hypothesis at this
--   sub-claim.
--
-- *Downstream consumers.*  Chapter-5 do-calculus and chapter-9–10
--   counterfactual identification arguments that build a joint
--   distribution on the marginalized graph and need to factorise
--   along `<` — including the LN's frequent "consider the
--   reverse topological order on `G^{∖W}`" pattern — consume
--   this theorem to lift an `lt` from `G` to a topological
--   order on `G.marginalize W hW` without re-proving any
--   total-order / parent-precedence content from scratch.

-- claim_3_16 -- start statement
theorem marginalize_restricts_topological_order (G : CDMG Node)
    (W : Finset Node) (hW : W ⊆ G.V)
    (lt : Node → Node → Prop) (hlt : G.IsTopologicalOrder lt) :
    (G.marginalize W hW).IsTopologicalOrder lt
-- claim_3_16 -- end statement
  := by
  -- Sub-claim iii(b): pointwise transport via the carrier inclusion
  -- `J ∪ (V ∖ W) ⊆ J ∪ V`.  For the parent-precedence clause, lift
  -- the marginalized parent witness through `Φ_E^{∖W}` to a directed
  -- walk in `G` and chain `lt` along it via
  -- `Walk.lt_of_directedWalk_pos`.
  obtain ⟨⟨h_irrefl, h_trans, h_total⟩, h_parent⟩ := hlt
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- Irreflexivity on the smaller carrier.
    intro v hv
    exact h_irrefl v (mem_of_mem_marginalize hv)
  · -- Transitivity on the smaller carrier.
    intro u hu v hv w hw huv hvw
    exact h_trans u (mem_of_mem_marginalize hu)
                  v (mem_of_mem_marginalize hv)
                  w (mem_of_mem_marginalize hw) huv hvw
  · -- Trichotomy on the smaller carrier.
    intro v hv w hw
    exact h_total v (mem_of_mem_marginalize hv) w (mem_of_mem_marginalize hw)
  · -- Parent precedence in `G.marginalize W hW`: unfold the marg-parent
    -- predicate to a `Φ_E` witness, then chain `lt` along the
    -- witnessing directed `G`-walk via `Walk.lt_of_directedWalk_pos`.
    intro v w hvw_parent
    obtain ⟨hv_marg, hvw_edge⟩ := hvw_parent
    -- `hvw_edge : (v, w) ∈ (G.marginalize W hW).E`.  Unfold to the
    -- `Finset.filter` form, extract the `Φ_E` witness.
    have hvw_filter : (v, w) ∈ ((G.J ∪ (G.V \ W)) ×ˢ (G.V \ W)).filter
          (fun e => G.MarginalizationΦE W e.1 e.2) := hvw_edge
    have hvw_phi : G.MarginalizationΦE W v w :=
      (Finset.mem_filter.mp hvw_filter).2
    obtain ⟨p, hp_dir, hp_pos, _⟩ := hvw_phi
    exact Walk.lt_of_directedWalk_pos h_trans h_parent p hp_dir hp_pos

end CDMG

end Causality
