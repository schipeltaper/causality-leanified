import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_2.MarginalizationAK
import Chapter3_GraphTheory.Section3_2.MargPreservesAncestors

-- TeX proof: claim_3_17_proof_MarginalizationsCommute.tex
--
-- The walk-algebra plumbing this file consumes (Walk.comp,
-- Walk.reverseDirected, Walk.mkBifurcation,
-- expand_directed_walk_marginalize, find_first_non_W_directed,
-- exists_arms_of_bifurcation_*, etc.) lives one file over in
-- `MargPreservesAncestors.lean`.  Those helpers were the proof
-- infrastructure for `claim_3_16` and have been promoted from
-- `private` so this row's proof can import them as a single source
-- of truth (the `expand` / `find_first_non_W` / `mkBifurcation`
-- patterns powering claim_3_16 reappear verbatim in claim_3_17 with
-- only the W-tracking strengthened).
namespace Causality

/-!
# Marginalizations commute (`claim_3_17`)

This file formalises the LN lemma `claim_3_17`
(`\label{marginalizations-commute}` in `graphs.tex`):

> Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ V` two disjoint
> subsets of output nodes.  Then
> `(G^{∖W₁})^{∖W₂} = (G^{∖W₂})^{∖W₁} = G^{∖(W₁ ∪ W₂)}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_17_statement_MarginalizationsCommute.tex`, verified equivalent
to the LN block.  `addition_to_the_LN` is empty for this row.  The
rewritten tex decomposes the LN's displayed triple equality into the
conjunction of two binary equalities:

* (a) `(G^{∖W₁})^{∖W₂} = G^{∖(W₁ ∪ W₂)}`,
* (b) `(G^{∖W₂})^{∖W₁} = G^{∖(W₁ ∪ W₂)}`.

Transitivity of equality recovers the LN's "swap symmetry" reading
`(G^{∖W₁})^{∖W₂} = (G^{∖W₂})^{∖W₁}` from (a) ∧ (b).

The disjointness hypothesis `W₁ ∩ W₂ = ∅` is load-bearing for the
*typing* of the iterated marginalisations: `def_3_14`
(`MarginalizationAK.lean`) requires its `W` argument to be a subset of
the input CDMG's output-node set `V`, and the inner marginalisation
`G.marginalize W₁ hW₁` has output-node set `G.V \ W₁`; the outer
marginalisation by `W₂` is therefore well-typed iff
`W₂ ⊆ G.V \ W₁`, which follows from `W₂ ⊆ G.V` plus
`Disjoint W₁ W₂`.  Symmetric for the mirror.  The joint
marginalisation needs only `W₁ ∪ W₂ ⊆ G.V`, immediate from `hW₁`
and `hW₂` via `Finset.union_subset` (disjointness is *not* needed on
the joint side).

The body is filled in by `prove_claim_in_lean` (Manager B), following
the to-be-written tex proof at
`tex/claim_3_17_proof_MarginalizationsCommute.tex`.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`) and `def_3_14` (`MarginalizationAK.lean`).
--   Both fixtures are load-bearing for this row's statement because
--   the signature references `CDMG Node` and `G.marginalize`
--   (`def_3_14`), each of which depends on `[DecidableEq Node]` through
--   the `Finset`-backed membership and filter operations on `G.V`,
--   `G.E`, `G.L`, and the marginalised `G.V \ W` carrier.  Stronger
--   instances (`Fintype`, `LinearOrder`) are not needed at the
--   statement level and are deferred to the proof body's use sites.
-- claim_3_17 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_17 --- end helper

-- ## Helper — disjoint-subset transport into the marginalised carrier
--
-- The main theorem signature evaluates `(G.marginalize W₁ hW₁).marginalize
-- W₂ ?_`, which per `def_3_14`'s signature (`MarginalizationAK.lean`)
-- requires
-- `?_ : W₂ ⊆ (G.marginalize W₁ hW₁).V`,
-- and `(G.marginalize W₁ hW₁).V` reduces definitionally to `G.V \ W₁`
-- (item ii of `def_3_14`).  The rewritten tex's "Well-typedness of the
-- iterated and joint marginalizations" paragraph derives this from the
-- two hypotheses `W₂ ⊆ G.V` and `Disjoint W₁ W₂` via the standard
-- set identity "`A ⊆ B \ C ↔ A ⊆ B ∧ A ∩ C = ∅`".  We expose the
-- transport as a stand-alone helper lemma so the theorem signature
-- stays free of inline term-mode plumbing.
--
-- ## Design choice
--
-- *Wrapped with `--- start helper` so the rendered statement on the
--   website is self-contained.*  The main theorem signature consumes
--   this lemma twice — once for the inner-`hW` of the
--   `W₁`-then-`W₂` composition (with `S = W₂`, `T = W₁`), once for the
--   inner-`hW` of the `W₂`-then-`W₁` composition (with `S = W₁`,
--   `T = W₂`).  Without the helper, both inner subset-arguments would
--   inline a `Finset.subset_sdiff.mpr ⟨…, …⟩` term, bloating the
--   rendered theorem and forcing a reader to know the lemma's iff
--   shape.  Mirrors the helper pattern in the sibling
--   `HardInterventionsCommute.lean` (`claim_3_4`).
--
-- *Phrased as `S ⊆ G.V → Disjoint T S → S ⊆ G.V \ T`, the form the
--   call site consumes directly.*  Equivalent reformulations
--   considered and rejected:
--   * A bare `Finset.subset_sdiff` rewrite (`S ⊆ G.V \ T ↔ S ⊆ G.V ∧
--     Disjoint S T`) was rejected because it would force every call
--     site to apply `.mpr` and rearrange the conjunction's
--     disjointness orientation.
--   * A version pinned to a specific `(G : CDMG Node)` was rejected
--     because the lemma is purely about `Finset` set-difference; the
--     `G.V` instantiation happens at the call site.
--
-- *Implicit `S`, `T`; explicit `hS`, `hDisj`.*  At the call sites
--   `subset_sdiff_of_disjoint hW₂ hDisj.symm` and
--   `subset_sdiff_of_disjoint hW₁ hDisj`, the implicit `S` and `T`
--   are synthesised from the goal and the calls read left-to-right
--   as "the carrier-subset hypothesis is `hS`; the disjointness
--   witness is `hDisj`/`hDisj.symm`".
--
-- *Note on `Disjoint` orientation.*  `Finset.subset_sdiff` packages
--   the disjointness as `Disjoint S T` (the *transported* set vs the
--   *removed* set).  For the `W₁`-then-`W₂` composition we have
--   `hDisj : Disjoint W₁ W₂` and need `Disjoint W₂ W₁`, so the call
--   site passes `hDisj.symm`.  For the swapped composition we need
--   `Disjoint W₁ W₂` directly, so the call site passes `hDisj`.
--
-- *Hypothesis shape `Disjoint S T`, not `S ∩ T = ∅`.*  The two are
--   semantically equivalent on `Finset Node`
--   (`Finset.disjoint_iff_inter_eq_empty`), but `Finset.subset_sdiff`
--   is phrased natively against the `Disjoint` typeclass — taking
--   the literal-`∩ = ∅` form here would force every call site to
--   thread an `Iff.mp` / `Iff.mpr` rewrite through the equivalence.
--   `Disjoint` is also the chapter-3-wide canonical shape
--   (`def_3_1`'s `hJV_disj`, `def_3_14`'s `marginalize_hJV_disj`,
--   and the analogous disjointness binder on the main theorem
--   below), so the helper's API parses uniformly with its
--   surroundings.  Semantic content is identical to the LN's literal
--   "$W_1 \cap W_2 = \emptyset$".
--
-- *Term-mode one-liner `Finset.subset_sdiff.mpr ⟨hS, hDisj⟩`, not a
--   tactic proof.*  The conclusion `S ⊆ U \ T` is a direct
--   restatement of the mathlib iff
--   `Finset.subset_sdiff : S ⊆ U \ T ↔ S ⊆ U ∧ Disjoint S T`; a
--   `by`-block (`by rw [Finset.subset_sdiff]; exact ⟨hS, hDisj⟩`)
--   would add tactic-state noise for zero readability gain, would
--   inflate the rendered helper on the website, and would obscure
--   that the helper is *literally* one direction of a named mathlib
--   iff (so a maintainer can pattern-match it on sight).
--
-- *`private`.*  Localises the lemma to this file.  Future rows that
--   compose marginalisations (or any operator producing a `V \ W`
--   carrier) should re-introduce the same helper at their use site
--   rather than reach across files; if a chapter-wide reuse pattern
--   emerges, the helper can be promoted in a later refactor.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: subset_sdiff_of_disjoint
-- claim_3_17 --- start helper
private lemma subset_sdiff_of_disjoint {S T : Finset Node}
    {U : Finset Node} (hS : S ⊆ U) (hDisj : Disjoint S T) :
    S ⊆ U \ T
-- claim_3_17 --- end helper
:= Finset.subset_sdiff.mpr ⟨hS, hDisj⟩
-- REFACTOR-BLOCK-ORIGINAL-END: subset_sdiff_of_disjoint

-- ## Proof helpers (no markers — proof-only).

-- *Project a directed walk through `W` to a marg-walk with length
-- `≥ 1` and interior tracked.*  Unlike `project_directed_walk_aux`
-- (which returns `q_tail` directly when `u = m`, losing length), this
-- version *always* includes the single-edge `(u, m) ∈ marg.E`
-- corresponding to the head segment.  The result has length `≥ 1` and
-- its interior is `⊆ T` whenever the source walk's interior is
-- `⊆ S ∪ T` and the endpoints lie outside `S ∪ T`.
private lemma project_walk_marg_with_interior_aux {G : CDMG Node}
    {S T : Finset Node} {hS : S ⊆ G.V} :
    ∀ (n : ℕ) {u v : Node} (p : Walk G u v),
      p.length ≤ n →
      p.IsDirectedWalk → p.length ≥ 1 →
      u ∈ G.marginalize S hS → v ∈ G.marginalize S hS →
      (∀ x ∈ p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T) →
      ∃ (q : Walk (G.marginalize S hS) u v),
        q.IsDirectedWalk ∧ q.length ≥ 1 ∧
        (∀ x ∈ q.vertices.tail.dropLast, x ∈ T) := by
  intro n
  induction n with
  | zero =>
      intros u v p hp_len _ hp_pos _ _ _
      omega
  | succ k ih =>
      intros u v p hp_len hp_dir hp_pos hu hv h_inter
      have hv_notS : v ∉ S := notW_of_mem_marginalize hS hv
      obtain ⟨m, head, tail, h_head_dir, h_tail_dir, h_head_pos,
              hm_notS, h_head_inter, h_lens, h_p_eq⟩ :=
        find_first_non_W_directed S p hp_dir hp_pos hv_notS
      have hm_V : m ∈ G.V :=
        Walk.target_in_GV_of_directedWalk_pos head h_head_dir h_head_pos
      have hm_marg : m ∈ G.marginalize S hS := by
        change m ∈ G.J ∪ (G.V \ S)
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hm_V, hm_notS⟩)
      have h_edge : (u, m) ∈ (G.marginalize S hS).E := by
        change (u, m) ∈ ((G.J ∪ (G.V \ S)) ×ˢ (G.V \ S)).filter
              (fun e => G.MarginalizationΦE S e.1 e.2)
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨hu, ?_⟩
          exact Finset.mem_sdiff.mpr ⟨hm_V, hm_notS⟩
        · exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩
      have hStepMarg : (G.marginalize S hS).WalkStep u (u, m) m :=
        Or.inl ⟨rfl, Or.inl h_edge⟩
      have h_head_drop_ne : head.vertices.dropLast ≠ [] := by
        rw [Walk.vertices_eq_head_cons_tail head]
        have h_h_t_ne : head.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos head h_head_pos
        rw [List.dropLast_cons_of_ne_nil h_h_t_ne]
        simp
      have h_tail_vs_ne : tail.vertices ≠ [] := Walk.vertices_ne_nil tail
      by_cases h_tail_pos : tail.length ≥ 1
      · have h_tail_t_ne : tail.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos tail h_tail_pos
        have h_tail_vs : tail.vertices = m :: tail.vertices.tail :=
          Walk.vertices_eq_head_cons_tail tail
        have hm_in_p_int : m ∈ p.vertices.tail.dropLast := by
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne,
              List.dropLast_append_of_ne_nil h_tail_vs_ne]
          apply List.mem_append.mpr
          right
          rw [h_tail_vs, List.dropLast_cons_of_ne_nil h_tail_t_ne]
          exact List.mem_cons_self
        have hm_in_T : m ∈ T := by
          rcases h_inter m hm_in_p_int with h_S | h_T
          · exact absurd h_S hm_notS
          · exact h_T
        have h_tail_inter :
            ∀ x ∈ tail.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
          intro x hx
          apply h_inter
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne,
              List.dropLast_append_of_ne_nil h_tail_vs_ne]
          apply List.mem_append.mpr
          right
          rw [h_tail_vs, List.dropLast_cons_of_ne_nil h_tail_t_ne]
          exact List.mem_cons_of_mem _ hx
        have h_tail_len : tail.length ≤ k := by omega
        obtain ⟨q_tail, hq_tail_dir, hq_tail_pos, hq_tail_inter⟩ :=
          ih tail h_tail_len h_tail_dir h_tail_pos hm_marg hv h_tail_inter
        refine ⟨Walk.cons m (u, m) hStepMarg q_tail,
                ⟨rfl, h_edge, hq_tail_dir⟩, ?_, ?_⟩
        · change q_tail.length + 1 ≥ 1; omega
        · intro x hx
          change x ∈ (u :: q_tail.vertices).tail.dropLast at hx
          rw [List.tail_cons] at hx
          have h_qtv : q_tail.vertices = m :: q_tail.vertices.tail :=
            Walk.vertices_eq_head_cons_tail q_tail
          rw [h_qtv] at hx
          have h_qtt_ne : q_tail.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos q_tail hq_tail_pos
          rw [List.dropLast_cons_of_ne_nil h_qtt_ne] at hx
          rcases List.mem_cons.mp hx with rfl | hx_inner
          · exact hm_in_T
          · exact hq_tail_inter x hx_inner
      · have h_tail_zero : tail.length = 0 := by omega
        match tail, h_tail_zero with
        | .nil m' hm', _ =>
            refine ⟨Walk.cons m' (u, m') hStepMarg
                      (Walk.nil m' hv),
                    ⟨rfl, h_edge, trivial⟩, ?_, ?_⟩
            · change 1 ≥ 1; omega
            · intro x hx
              change x ∈ (u :: [m'] : List Node).tail.dropLast at hx
              simp at hx

private lemma project_walk_marg_with_interior {G : CDMG Node}
    {S T : Finset Node} {hS : S ⊆ G.V}
    {u v : Node} (p : Walk G u v)
    (hp_dir : p.IsDirectedWalk) (hp_pos : p.length ≥ 1)
    (hu : u ∈ G.marginalize S hS) (hv : v ∈ G.marginalize S hS)
    (h_inter : ∀ x ∈ p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T) :
    ∃ (q : Walk (G.marginalize S hS) u v),
      q.IsDirectedWalk ∧ q.length ≥ 1 ∧
      (∀ x ∈ q.vertices.tail.dropLast, x ∈ T) :=
  project_walk_marg_with_interior_aux (S := S) (T := T) (hS := hS)
    p.length p le_rfl hp_dir hp_pos hu hv h_inter

-- Strengthened projection: returns both vertex bounds (vertices ⊆ source's vertices,
-- and respective .dropLast / .tail bounds) AND T-interior bound.
private lemma project_walk_marg_full_aux {G : CDMG Node}
    {S T : Finset Node} {hS : S ⊆ G.V} :
    ∀ (n : ℕ) {u v : Node} (p : Walk G u v),
      p.length ≤ n →
      p.IsDirectedWalk → p.length ≥ 1 →
      u ∈ G.marginalize S hS → v ∈ G.marginalize S hS →
      (∀ x ∈ p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T) →
      ∃ (q : Walk (G.marginalize S hS) u v),
        q.IsDirectedWalk ∧ q.length ≥ 1 ∧
        (∀ x ∈ q.vertices, x ∈ p.vertices) ∧
        (∀ x ∈ q.vertices.dropLast, x ∈ p.vertices.dropLast) ∧
        (∀ x ∈ q.vertices.tail, x ∈ p.vertices.tail) ∧
        (∀ x ∈ q.vertices.tail.dropLast, x ∈ T) := by
  intro n
  induction n with
  | zero =>
      intros u v p hp_len _ hp_pos _ _ _
      omega
  | succ k ih =>
      intros u v p hp_len hp_dir hp_pos hu hv h_inter
      have hv_notS : v ∉ S := notW_of_mem_marginalize hS hv
      obtain ⟨m, head, tail, h_head_dir, h_tail_dir, h_head_pos,
              hm_notS, h_head_inter, h_lens, h_p_eq⟩ :=
        find_first_non_W_directed S p hp_dir hp_pos hv_notS
      have hm_V : m ∈ G.V :=
        Walk.target_in_GV_of_directedWalk_pos head h_head_dir h_head_pos
      have hm_marg : m ∈ G.marginalize S hS := by
        change m ∈ G.J ∪ (G.V \ S)
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hm_V, hm_notS⟩)
      have h_edge : (u, m) ∈ (G.marginalize S hS).E := by
        change (u, m) ∈ ((G.J ∪ (G.V \ S)) ×ˢ (G.V \ S)).filter
              (fun e => G.MarginalizationΦE S e.1 e.2)
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨hu, ?_⟩
          exact Finset.mem_sdiff.mpr ⟨hm_V, hm_notS⟩
        · exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩
      have hStepMarg : (G.marginalize S hS).WalkStep u (u, m) m :=
        Or.inl ⟨rfl, Or.inl h_edge⟩
      -- p.vertices = head.vertices.dropLast ++ tail.vertices.
      have h_head_drop_ne : head.vertices.dropLast ≠ [] := by
        rw [Walk.vertices_eq_head_cons_tail head]
        have h_h_t_ne : head.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos head h_head_pos
        rw [List.dropLast_cons_of_ne_nil h_h_t_ne]
        simp
      have h_tail_vs_ne : tail.vertices ≠ [] := Walk.vertices_ne_nil tail
      have h_u_in_head_drop : u ∈ head.vertices.dropLast := by
        rw [Walk.vertices_eq_head_cons_tail head,
            List.dropLast_cons_of_ne_nil
              (Walk.tail_vertices_ne_nil_of_pos head h_head_pos)]
        exact List.mem_cons_self
      have h_m_in_tail : m ∈ tail.vertices := Walk.head_mem_vertices tail
      by_cases h_tail_pos : tail.length ≥ 1
      · have h_tail_t_ne : tail.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos tail h_tail_pos
        have h_tail_vs : tail.vertices = m :: tail.vertices.tail :=
          Walk.vertices_eq_head_cons_tail tail
        have hm_in_p_int : m ∈ p.vertices.tail.dropLast := by
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne,
              List.dropLast_append_of_ne_nil h_tail_vs_ne]
          apply List.mem_append.mpr
          right
          rw [h_tail_vs, List.dropLast_cons_of_ne_nil h_tail_t_ne]
          exact List.mem_cons_self
        have hm_in_T : m ∈ T := by
          rcases h_inter m hm_in_p_int with h_S | h_T
          · exact absurd h_S hm_notS
          · exact h_T
        have h_tail_inter :
            ∀ x ∈ tail.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
          intro x hx
          apply h_inter
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne,
              List.dropLast_append_of_ne_nil h_tail_vs_ne]
          apply List.mem_append.mpr
          right
          rw [h_tail_vs, List.dropLast_cons_of_ne_nil h_tail_t_ne]
          exact List.mem_cons_of_mem _ hx
        have h_tail_len : tail.length ≤ k := by omega
        obtain ⟨q_tail, hq_tail_dir, hq_tail_pos,
                hq_tail_sub, hq_tail_drop_sub, hq_tail_tail_sub, hq_tail_inter⟩ :=
          ih tail h_tail_len h_tail_dir h_tail_pos hm_marg hv h_tail_inter
        refine ⟨Walk.cons m (u, m) hStepMarg q_tail,
                ⟨rfl, h_edge, hq_tail_dir⟩, ?_, ?_, ?_, ?_, ?_⟩
        · change q_tail.length + 1 ≥ 1; omega
        · -- q.vertices ⊆ p.vertices.
          intro x hx
          change x ∈ u :: q_tail.vertices at hx
          rw [h_p_eq]
          rcases List.mem_cons.mp hx with rfl | hx_in
          · exact List.mem_append.mpr (Or.inl h_u_in_head_drop)
          · exact List.mem_append.mpr (Or.inr (hq_tail_sub x hx_in))
        · -- q.vertices.dropLast ⊆ p.vertices.dropLast.
          intro x hx
          have h_qt_vs_ne : q_tail.vertices ≠ [] := Walk.vertices_ne_nil q_tail
          change x ∈ (u :: q_tail.vertices).dropLast at hx
          rw [List.dropLast_cons_of_ne_nil h_qt_vs_ne] at hx
          rw [h_p_eq, List.dropLast_append_of_ne_nil h_tail_vs_ne]
          rcases List.mem_cons.mp hx with rfl | hx_in
          · exact List.mem_append.mpr (Or.inl h_u_in_head_drop)
          · exact List.mem_append.mpr (Or.inr (hq_tail_drop_sub x hx_in))
        · -- q.vertices.tail ⊆ p.vertices.tail.
          intro x hx
          change x ∈ q_tail.vertices at hx
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne]
          -- head.vertices.dropLast.tail = head.vertices.tail.dropLast.
          -- We just need x ∈ p.vertices.tail.
          exact List.mem_append.mpr (Or.inr (hq_tail_sub x hx))
        · -- q.vertices.tail.dropLast ⊆ T.
          intro x hx
          change x ∈ (u :: q_tail.vertices).tail.dropLast at hx
          rw [List.tail_cons] at hx
          have h_qtv : q_tail.vertices = m :: q_tail.vertices.tail :=
            Walk.vertices_eq_head_cons_tail q_tail
          rw [h_qtv] at hx
          have h_qtt_ne : q_tail.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos q_tail hq_tail_pos
          rw [List.dropLast_cons_of_ne_nil h_qtt_ne] at hx
          rcases List.mem_cons.mp hx with rfl | hx_inner
          · exact hm_in_T
          · exact hq_tail_inter x hx_inner
      · have h_tail_zero : tail.length = 0 := by omega
        have hmv_eq : m = v := by
          generalize htail_eq : tail.length = ℓ at h_tail_zero
          subst h_tail_zero
          match tail, htail_eq with
          | .nil _ _, _ => rfl
        subst hmv_eq
        refine ⟨Walk.cons m (u, m) hStepMarg
                  (Walk.nil m hv),
                ⟨rfl, h_edge, trivial⟩, ?_, ?_, ?_, ?_, ?_⟩
        · change 1 ≥ 1; omega
        · intro x hx
          change x ∈ ([u, m] : List Node) at hx
          rw [h_p_eq]
          rcases List.mem_cons.mp hx with rfl | hx_rest
          · exact List.mem_append.mpr (Or.inl h_u_in_head_drop)
          · rw [List.mem_singleton] at hx_rest
            subst hx_rest
            exact List.mem_append.mpr (Or.inr (Walk.head_mem_vertices _))
        · intro x hx
          change x ∈ ([u, m] : List Node).dropLast at hx
          simp [List.dropLast] at hx
          subst hx
          rw [h_p_eq, List.dropLast_append_of_ne_nil h_tail_vs_ne]
          exact List.mem_append.mpr (Or.inl h_u_in_head_drop)
        · intro x hx
          change x ∈ ([u, m] : List Node).tail at hx
          simp [List.tail] at hx
          subst hx
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne]
          apply List.mem_append.mpr
          right
          exact Walk.head_mem_vertices _
        · intro x hx
          change x ∈ (u :: [m] : List Node).tail.dropLast at hx
          simp at hx

private lemma project_walk_marg_full {G : CDMG Node}
    {S T : Finset Node} {hS : S ⊆ G.V}
    {u v : Node} (p : Walk G u v)
    (hp_dir : p.IsDirectedWalk) (hp_pos : p.length ≥ 1)
    (hu : u ∈ G.marginalize S hS) (hv : v ∈ G.marginalize S hS)
    (h_inter : ∀ x ∈ p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T) :
    ∃ (q : Walk (G.marginalize S hS) u v),
      q.IsDirectedWalk ∧ q.length ≥ 1 ∧
      (∀ x ∈ q.vertices, x ∈ p.vertices) ∧
      (∀ x ∈ q.vertices.dropLast, x ∈ p.vertices.dropLast) ∧
      (∀ x ∈ q.vertices.tail, x ∈ p.vertices.tail) ∧
      (∀ x ∈ q.vertices.tail.dropLast, x ∈ T) :=
  project_walk_marg_full_aux (S := S) (T := T) (hS := hS)
    p.length p le_rfl hp_dir hp_pos hu hv h_inter

private lemma mem_marg_of_notin_union_V {G : CDMG Node}
    (S T : Finset Node) (hS : S ⊆ G.V) {u : Node}
    (hu : u ∈ G.J ∪ (G.V \ (S ∪ T))) :
    u ∈ G.marginalize S hS := by
  change u ∈ G.J ∪ (G.V \ S)
  rcases Finset.mem_union.mp hu with hJ | hVW
  · exact Finset.mem_union_left _ hJ
  · refine Finset.mem_union_right _ ?_
    rw [Finset.mem_sdiff] at hVW ⊢
    refine ⟨hVW.1, ?_⟩
    intro hu_in_S
    exact hVW.2 (Finset.mem_union_left _ hu_in_S)

private lemma mem_marg_of_notin_union_VnoJ {G : CDMG Node}
    (S T : Finset Node) (hS : S ⊆ G.V) {v : Node}
    (hv : v ∈ G.V \ (S ∪ T)) :
    v ∈ G.marginalize S hS := by
  change v ∈ G.J ∪ (G.V \ S)
  refine Finset.mem_union_right _ ?_
  rw [Finset.mem_sdiff] at hv ⊢
  refine ⟨hv.1, ?_⟩
  intro hv_in_S
  exact hv.2 (Finset.mem_union_left _ hv_in_S)

-- ## E-membership iff (parametric in `S, T`).
private lemma marg_PhiE_iff {G : CDMG Node} (S T : Finset Node)
    (hS : S ⊆ G.V) (_hT : T ⊆ G.V) (_hDisj : Disjoint S T)
    {u v : Node}
    (hu : u ∈ G.J ∪ (G.V \ (S ∪ T))) (hv : v ∈ G.V \ (S ∪ T)) :
    (G.marginalize S hS).MarginalizationΦE T u v ↔
      G.MarginalizationΦE (S ∪ T) u v := by
  constructor
  · rintro ⟨p, hp_dir, hp_pos, hp_inter⟩
    obtain ⟨q, hq_dir, hq_len, _, _, _, hq_inter⟩ :=
      expand_directed_walk_marginalize p hp_dir
    refine ⟨q, hq_dir, ?_, ?_⟩
    · omega
    · intro x hx
      rcases hq_inter x hx with hxp | hxS
      · exact Finset.mem_union_right _ (hp_inter x hxp)
      · exact Finset.mem_union_left _ hxS
  · rintro ⟨q, hq_dir, hq_pos, hq_inter⟩
    have hu_marg : u ∈ G.marginalize S hS :=
      mem_marg_of_notin_union_V S T hS hu
    have hv_marg : v ∈ G.marginalize S hS :=
      mem_marg_of_notin_union_VnoJ S T hS hv
    have h_inter : ∀ x ∈ q.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
      intro x hx
      have hin := hq_inter x hx
      rcases Finset.mem_union.mp hin with hS_in | hT_in
      · exact Or.inl hS_in
      · exact Or.inr hT_in
    obtain ⟨p, hp_dir, hp_pos, hp_inter⟩ :=
      project_walk_marg_with_interior (S := S) (T := T) (hS := hS)
        q hq_dir hq_pos hu_marg hv_marg h_inter
    exact ⟨p, hp_dir, hp_pos, hp_inter⟩

-- ## E-field equality (parametric in `S, T`).
private lemma marg_E_field_eq {G : CDMG Node} (S T : Finset Node)
    (hS : S ⊆ G.V) (hT : T ⊆ G.V) (hDisj : Disjoint S T) :
    ((G.marginalize S hS).marginalize T
        (subset_sdiff_of_disjoint hT hDisj.symm)).E
      = (G.marginalize (S ∪ T) (Finset.union_subset hS hT)).E := by
  change ((G.J ∪ ((G.V \ S) \ T)) ×ˢ ((G.V \ S) \ T)).filter
          (fun e => (G.marginalize S hS).MarginalizationΦE T e.1 e.2)
        = ((G.J ∪ (G.V \ (S ∪ T))) ×ˢ (G.V \ (S ∪ T))).filter
          (fun e => G.MarginalizationΦE (S ∪ T) e.1 e.2)
  have h_sd : (G.V \ S) \ T = G.V \ (S ∪ T) := sdiff_sdiff_left
  rw [h_sd]
  apply Finset.filter_congr
  intro e he
  rw [Finset.mem_product] at he
  exact marg_PhiE_iff S T hS hT hDisj he.1 he.2

-- ## L-field equality (parametric in `S, T`).
--
-- The L-field equality requires translating bifurcations between
-- `(G.marginalize S hS)` and `G` while tracking the interior set.

-- ## Helper: source uniqueness of bif `p` upgrades "c ∈ p.tail and
-- c ∈ p.dropLast" to "c ∈ p.tail.dropLast".
private lemma mem_interior_of_arm_source
    {G : CDMG Node} {u v : Node}
    {p : Walk G u v} (hu_p_tail : u ∉ p.vertices.tail)
    (hp_pos : p.length ≥ 1)
    {c : Node}
    (hc_p_tail : c ∈ p.vertices.tail) (hc_p_drop : c ∈ p.vertices.dropLast) :
    c ∈ p.vertices.tail.dropLast := by
  have h_p_tail_ne : p.vertices.tail ≠ [] :=
    Walk.tail_vertices_ne_nil_of_pos p hp_pos
  have h_p_vs_eq : p.vertices = u :: p.vertices.tail :=
    Walk.vertices_eq_head_cons_tail p
  have h_p_drop_eq : p.vertices.dropLast = u :: p.vertices.tail.dropLast := by
    conv_lhs => rw [h_p_vs_eq]
    exact List.dropLast_cons_of_ne_nil h_p_tail_ne
  rw [h_p_drop_eq] at hc_p_drop
  rcases List.mem_cons.mp hc_p_drop with h_c_eq_u | h_in
  · exact absurd (h_c_eq_u ▸ hc_p_tail) hu_p_tail
  · exact h_in

-- ## Helper: vertices_tail_dropLast for mkBifurcation with both arms positive.
private lemma vertices_tail_dropLast_mkBifurcation
    {G : CDMG Node} {c v w : Node}
    (qv : Walk G c v) (hqv_dir : qv.IsDirectedWalk)
    (hqv_pos : qv.length ≥ 1)
    (qw : Walk G c w) (hqw_pos : qw.length ≥ 1) :
    (Walk.mkBifurcation qv hqv_dir hqv_pos qw).vertices.tail.dropLast
      = qv.vertices.tail.dropLast.reverse ++ qw.vertices.dropLast := by
  have h_vs := Walk.vertices_mkBifurcation qv hqv_dir hqv_pos qw
  have h_rev_drop : qv.vertices.reverse.dropLast = qv.vertices.tail.reverse :=
    Walk.vertices_reverse_dropLast qv
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
  have h_qv_tail_ne : qv.vertices.tail ≠ [] :=
    Walk.tail_vertices_ne_nil_of_pos qv hqv_pos
  have h_qv_rev_drop_ne : qv.vertices.reverse.dropLast ≠ [] := by
    rw [h_rev_drop]
    intro hempty
    apply h_qv_tail_ne
    have : qv.vertices.tail = qv.vertices.tail.reverse.reverse := by
      rw [List.reverse_reverse]
    rw [this, hempty]; rfl
  have h_qw_vs_ne : qw.vertices ≠ [] := Walk.vertices_ne_nil qw
  rw [h_vs]
  rw [List.tail_append_of_ne_nil h_qv_rev_drop_ne]
  rw [List.dropLast_append_of_ne_nil h_qw_vs_ne]
  rw [h_rev_drop, h_aux]

-- ## Helper: vertices_tail_dropLast for mkBifurcationBidir with L positive.
private lemma vertices_tail_dropLast_mkBifurcationBidir_Lpos
    {G : CDMG Node} {vL vR v1 v2 : Node}
    (L : Walk G vL v1) (hL_dir : L.IsDirectedWalk)
    (R : Walk G vR v2) (hLR : (vL, vR) ∈ G.L) (hL_pos : L.length ≥ 1) :
    (Walk.mkBifurcationBidir L hL_dir R hLR).vertices.tail.dropLast
      = L.vertices.tail.dropLast.reverse ++ (vL :: R.vertices).dropLast := by
  have h_vs := Walk.vertices_mkBifurcationBidir L hL_dir R hLR
  have h_rev_drop : L.vertices.reverse.dropLast = L.vertices.tail.reverse :=
    Walk.vertices_reverse_dropLast L
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
  have h_L_tail_ne : L.vertices.tail ≠ [] :=
    Walk.tail_vertices_ne_nil_of_pos L hL_pos
  have h_L_rev_drop_ne : L.vertices.reverse.dropLast ≠ [] := by
    rw [h_rev_drop]
    intro hempty
    apply h_L_tail_ne
    have : L.vertices.tail = L.vertices.tail.reverse.reverse := by
      rw [List.reverse_reverse]
    rw [this, hempty]; rfl
  have h_cons_ne : (vL :: R.vertices) ≠ [] := by simp
  rw [h_vs]
  rw [List.tail_append_of_ne_nil h_L_rev_drop_ne]
  rw [List.dropLast_append_of_ne_nil h_cons_ne]
  rw [h_rev_drop, h_aux]

-- ## Helper: inclusive variant of `find_first_non_W_directed`.
--
-- Unlike `find_first_non_W_directed` (which always returns a non-trivial
-- head, skipping the source `u`), this variant lets the source `u` itself
-- be the "first non-W" vertex: if `u ∉ W`, then `m := u`, `head := nil`,
-- `tail := p`.  Used by the backward bidirected-hinge case where the
-- bidirected hinge endpoints `(vL, vR) ∈ G.L` might or might not lie in
-- `S`, so the "first non-S vertex starting from vL inclusive" search needs
-- to handle both possibilities uniformly.  The post-condition
-- `∀ x ∈ head.vertices.dropLast, x ∈ W` is *inclusive* of the source
-- (all of head's vertices except the target are in `W`); when `head` is
-- trivial this is vacuous.
private lemma find_first_non_W_directed_inclusive
    {G : CDMG Node} (W : Finset Node)
    {u v : Node} (p : Walk G u v)
    (hp_dir : p.IsDirectedWalk) (hv_notW : v ∉ W) :
    ∃ (m : Node) (head : Walk G u m) (tail : Walk G m v),
      head.IsDirectedWalk ∧ tail.IsDirectedWalk ∧
      m ∉ W ∧
      (∀ x ∈ head.vertices.dropLast, x ∈ W) ∧
      head.length + tail.length = p.length ∧
      p.vertices = head.vertices.dropLast ++ tail.vertices := by
  by_cases hu_W : u ∈ W
  · have hu_ne_v : u ≠ v := fun heq => hv_notW (heq ▸ hu_W)
    have hp_pos : p.length ≥ 1 := Walk.length_pos_of_ne p hu_ne_v
    obtain ⟨m, head, tail, h_head_dir, h_tail_dir, h_head_pos, hm_notW,
            h_head_inter, h_lens, h_p_eq⟩ :=
      find_first_non_W_directed W p hp_dir hp_pos hv_notW
    refine ⟨m, head, tail, h_head_dir, h_tail_dir, hm_notW, ?_, h_lens, h_p_eq⟩
    intro x hx
    have h_head_t_ne : head.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos head h_head_pos
    have h_head_drop_eq :
        head.vertices.dropLast = u :: head.vertices.tail.dropLast := by
      conv_lhs => rw [Walk.vertices_eq_head_cons_tail head]
      exact List.dropLast_cons_of_ne_nil h_head_t_ne
    rw [h_head_drop_eq] at hx
    rcases List.mem_cons.mp hx with rfl | hx_rest
    · exact hu_W
    · exact h_head_inter x hx_rest
  · have hu_in_G : u ∈ G :=
      Walk.mem_of_mem_vertices p (Walk.head_mem_vertices p)
    refine ⟨u, Walk.nil u hu_in_G, p, trivial, hp_dir, hu_W, ?_, ?_, ?_⟩
    · intro x hx
      change x ∈ ([u] : List Node).dropLast at hx
      simp at hx
    · change 0 + p.length = p.length; omega
    · change p.vertices = ([u] : List Node).dropLast ++ p.vertices
      simp

-- ## Helper: forward direction (marg-bif → G-bif) for a single orientation.
--
-- Extracted as a top-level private lemma to keep `marg_PhiL_iff`'s body
-- readable.  The proof case-splits on p's hinge type (directed vs
-- bidirected).  For each arm/hinge in `p`, we use
-- `expand_directed_walk_marginalize` (for directed steps/arms) and
-- unfold `MarginalizationΦL` (for the bidirected hinge L-edge) to
-- obtain G-walks, then reassemble via `Walk.mkBifurcation` or
-- `Walk.mkBifurcationBidir`.  Interior tracking: each expansion can
-- introduce S-vertices, and the original marg interior is in T, so
-- the assembled G-bif's interior is ⊆ S ∪ T.
private lemma forward_marg_to_g_bif_one_orientation
    {G : CDMG Node} (S T : Finset Node)
    (hS : S ⊆ G.V) {a b : Node}
    (ha_VST : a ∈ G.V \ (S ∪ T)) (hb_VST : b ∈ G.V \ (S ∪ T))
    (ha_marg : a ∈ G.marginalize S hS) (hb_marg : b ∈ G.marginalize S hS)
    (p : Walk (G.marginalize S hS) a b)
    (hp_bif : p.IsBifurcation)
    (hp_inter : ∀ x ∈ p.vertices.tail.dropLast, x ∈ T) :
    ∃ q : Walk G a b, q.IsBifurcation ∧
      ∀ x ∈ q.vertices.tail.dropLast, x ∈ S ∪ T := by
  have ha_notSuT : a ∉ S ∪ T := (Finset.mem_sdiff.mp ha_VST).2
  have hb_notSuT : b ∉ S ∪ T := (Finset.mem_sdiff.mp hb_VST).2
  have ha_notS : a ∉ S := fun h => ha_notSuT (Finset.mem_union_left _ h)
  have hb_notS : b ∉ S := fun h => hb_notSuT (Finset.mem_union_left _ h)
  have hp_pos : p.length ≥ 1 := Walk.length_pos_of_isBifurcation hp_bif
  obtain ⟨hab_ne, ha_p_tail, hb_p_drop, i, hp_split⟩ := hp_bif
  by_cases h_dir : p.IsBifurcationDirectedHingeWithSplit i
  · -- DIRECTED HINGE CASE: source `c` in marg.
    obtain ⟨c, L_p, R_p, hL_p_dir, hR_p_dir, hL_p_pos, hR_p_pos, _,
            hL_p_sub, hR_p_sub, hL_p_drop_sub, hR_p_drop_sub⟩ :=
      Walk.exists_arms_of_bifurcation_directed_hinge_strong p i h_dir
    -- c is the bifurcation source; trace c ∈ p.tail.dropLast → c ∈ T.
    have hc_in_L_p : c ∈ L_p.vertices := Walk.head_mem_vertices L_p
    have hc_in_R_p : c ∈ R_p.vertices := Walk.head_mem_vertices R_p
    have hc_in_p_drop : c ∈ p.vertices.dropLast := hL_p_sub _ hc_in_L_p
    have hc_in_p_tail : c ∈ p.vertices.tail := hR_p_sub _ hc_in_R_p
    have hc_in_p_inter : c ∈ p.vertices.tail.dropLast :=
      mem_interior_of_arm_source ha_p_tail hp_pos hc_in_p_tail hc_in_p_drop
    have hc_T : c ∈ T := hp_inter c hc_in_p_inter
    -- Expand each arm into G.
    obtain ⟨L_g, hL_g_dir, hL_g_len, hL_g_sub_S, hL_g_drop_sub_S,
            _, hL_g_tdL_sub_S⟩ :=
      expand_directed_walk_marginalize L_p hL_p_dir
    obtain ⟨R_g, hR_g_dir, hR_g_len, hR_g_sub_S, hR_g_drop_sub_S,
            _, hR_g_tdL_sub_S⟩ :=
      expand_directed_walk_marginalize R_p hR_p_dir
    have hL_g_pos : L_g.length ≥ 1 := by omega
    have hR_g_pos : R_g.length ≥ 1 := by omega
    -- Trace L_p's interior to T (similarly for R_p).
    have hL_p_inter_T : ∀ x ∈ L_p.vertices.tail.dropLast, x ∈ T := by
      intro x hx
      have h_t_ne : L_p.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L_p hL_p_pos
      have h_drop_eq : L_p.vertices.dropLast = c :: L_p.vertices.tail.dropLast := by
        conv_lhs => rw [Walk.vertices_eq_head_cons_tail L_p]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have hx_L_p_drop : x ∈ L_p.vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have hx_p_tail : x ∈ p.vertices.tail := hL_p_drop_sub _ hx_L_p_drop
      have hx_L_p : x ∈ L_p.vertices := List.mem_of_mem_dropLast hx_L_p_drop
      have hx_p_drop : x ∈ p.vertices.dropLast := hL_p_sub _ hx_L_p
      have hx_p_inter : x ∈ p.vertices.tail.dropLast :=
        mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
      exact hp_inter _ hx_p_inter
    have hR_p_inter_T : ∀ x ∈ R_p.vertices.tail.dropLast, x ∈ T := by
      intro x hx
      have h_t_ne : R_p.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R_p hR_p_pos
      have h_drop_eq : R_p.vertices.dropLast = c :: R_p.vertices.tail.dropLast := by
        conv_lhs => rw [Walk.vertices_eq_head_cons_tail R_p]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have hx_R_p_drop : x ∈ R_p.vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have hx_p_drop : x ∈ p.vertices.dropLast := hR_p_drop_sub _ hx_R_p_drop
      have hx_R_p : x ∈ R_p.vertices := List.mem_of_mem_dropLast hx_R_p_drop
      have hx_p_tail : x ∈ p.vertices.tail := hR_p_sub _ hx_R_p
      have hx_p_inter : x ∈ p.vertices.tail.dropLast :=
        mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
      exact hp_inter _ hx_p_inter
    -- Vertex bounds for L_g, R_g (a/b in correct positions).
    have ha_notin_L_g_drop : a ∉ L_g.vertices.dropLast := by
      intro h_in
      rcases hL_g_drop_sub_S a h_in with h_in_L_p | h_in_S
      · exact ha_p_tail (hL_p_drop_sub a h_in_L_p)
      · exact ha_notS h_in_S
    have ha_notin_R_g : a ∉ R_g.vertices := by
      intro h_in
      rcases hR_g_sub_S a h_in with h_in_R_p | h_in_S
      · exact ha_p_tail (hR_p_sub a h_in_R_p)
      · exact ha_notS h_in_S
    have hb_notin_L_g : b ∉ L_g.vertices := by
      intro h_in
      rcases hL_g_sub_S b h_in with h_in_L_p | h_in_S
      · exact hb_p_drop (hL_p_sub b h_in_L_p)
      · exact hb_notS h_in_S
    have hb_notin_R_g_drop : b ∉ R_g.vertices.dropLast := by
      intro h_in
      rcases hR_g_drop_sub_S b h_in with h_in_R_p | h_in_S
      · exact hb_p_drop (hR_p_drop_sub b h_in_R_p)
      · exact hb_notS h_in_S
    -- Build the bifurcation in G.
    refine ⟨Walk.mkBifurcation L_g hL_g_dir hL_g_pos R_g, ?_, ?_⟩
    · have h_src := Walk.mkBifurcation_isBifurcationSource L_g hL_g_dir hL_g_pos
                      R_g hR_g_dir hR_g_pos
                      hab_ne ha_notin_L_g_drop ha_notin_R_g hb_notin_L_g
                      hb_notin_R_g_drop
      exact Walk.isBifurcationSource_to_isBifurcation _ c h_src
    · intro x hx
      rw [vertices_tail_dropLast_mkBifurcation L_g hL_g_dir hL_g_pos R_g
            hR_g_pos] at hx
      rcases List.mem_append.mp hx with hx_L | hx_R
      · rw [List.mem_reverse] at hx_L
        rcases hL_g_tdL_sub_S x hx_L with hx_L_p_inter | hx_S
        · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p_inter)
        · exact Finset.mem_union_left _ hx_S
      · have h_R_t_ne : R_g.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos R_g hR_g_pos
        rw [Walk.vertices_eq_head_cons_tail R_g,
            List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R
        rcases List.mem_cons.mp hx_R with rfl | hx_inner
        · exact Finset.mem_union_right _ hc_T
        · rcases hR_g_tdL_sub_S x hx_inner with hx_R_p_inter | hx_S
          · exact Finset.mem_union_right _ (hR_p_inter_T x hx_R_p_inter)
          · exact Finset.mem_union_left _ hx_S
  · -- BIDIRECTED HINGE CASE.
    obtain ⟨vL_p, vR_p, L_p, R_p, hL_p_dir, hR_p_dir, hLR_p_marg, _,
            hL_p_sub, hR_p_sub, hL_p_drop_sub, hR_p_drop_sub⟩ :=
      Walk.exists_arms_of_bifurcation_bidir_hinge_strong p i hp_split h_dir
    -- Unfold marg.L's filter to get Φ_L witness.
    have hLR_filter : (vL_p, vR_p) ∈ ((G.V \ S) ×ˢ (G.V \ S)).filter
                            (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL S e.1 e.2) :=
      hLR_p_marg
    rw [Finset.mem_filter, Finset.mem_product] at hLR_filter
    obtain ⟨⟨hvL_VS, hvR_VS⟩, _, h_phi_L⟩ := hLR_filter
    have hvL_notS : vL_p ∉ S := (Finset.mem_sdiff.mp hvL_VS).2
    have hvR_notS : vR_p ∉ S := (Finset.mem_sdiff.mp hvR_VS).2
    have hvL_in_L_p : vL_p ∈ L_p.vertices := Walk.head_mem_vertices L_p
    have hvL_in_p_drop : vL_p ∈ p.vertices.dropLast := hL_p_sub _ hvL_in_L_p
    have hvR_in_R_p : vR_p ∈ R_p.vertices := Walk.head_mem_vertices R_p
    have hvR_in_p_tail : vR_p ∈ p.vertices.tail := hR_p_sub _ hvR_in_R_p
    -- Expand each arm into G (may have length 0 in the bid case).
    obtain ⟨L_g, hL_g_dir, hL_g_len, hL_g_sub_S, hL_g_drop_sub_S,
            _, hL_g_tdL_sub_S⟩ :=
      expand_directed_walk_marginalize L_p hL_p_dir
    obtain ⟨R_g, hR_g_dir, hR_g_len, hR_g_sub_S, hR_g_drop_sub_S,
            _, hR_g_tdL_sub_S⟩ :=
      expand_directed_walk_marginalize R_p hR_p_dir
    -- Helper: trace L_p's interior to T.
    have hL_p_inter_T : ∀ x ∈ L_p.vertices.tail.dropLast, x ∈ T := by
      intro x hx
      by_cases h_L_p_pos : L_p.length ≥ 1
      · have h_t_ne : L_p.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos L_p h_L_p_pos
        have h_drop_eq :
            L_p.vertices.dropLast = vL_p :: L_p.vertices.tail.dropLast := by
          conv_lhs => rw [Walk.vertices_eq_head_cons_tail L_p]
          exact List.dropLast_cons_of_ne_nil h_t_ne
        have hx_L_p_drop : x ∈ L_p.vertices.dropLast := by
          rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
        have hx_p_tail : x ∈ p.vertices.tail := hL_p_drop_sub _ hx_L_p_drop
        have hx_L_p : x ∈ L_p.vertices := List.mem_of_mem_dropLast hx_L_p_drop
        have hx_p_drop : x ∈ p.vertices.dropLast := hL_p_sub _ hx_L_p
        have hx_p_inter : x ∈ p.vertices.tail.dropLast :=
          mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
        exact hp_inter _ hx_p_inter
      · have h_zero : L_p.length = 0 := by omega
        match L_p, h_zero with
        | .nil _ _, _ => simp [Walk.vertices, List.tail, List.dropLast] at hx
    have hR_p_inter_T : ∀ x ∈ R_p.vertices.tail.dropLast, x ∈ T := by
      intro x hx
      by_cases h_R_p_pos : R_p.length ≥ 1
      · have h_t_ne : R_p.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos R_p h_R_p_pos
        have h_drop_eq :
            R_p.vertices.dropLast = vR_p :: R_p.vertices.tail.dropLast := by
          conv_lhs => rw [Walk.vertices_eq_head_cons_tail R_p]
          exact List.dropLast_cons_of_ne_nil h_t_ne
        have hx_R_p_drop : x ∈ R_p.vertices.dropLast := by
          rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
        have hx_p_drop : x ∈ p.vertices.dropLast := hR_p_drop_sub _ hx_R_p_drop
        have hx_R_p : x ∈ R_p.vertices := List.mem_of_mem_dropLast hx_R_p_drop
        have hx_p_tail : x ∈ p.vertices.tail := hR_p_sub _ hx_R_p
        have hx_p_inter : x ∈ p.vertices.tail.dropLast :=
          mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
        exact hp_inter _ hx_p_inter
      · have h_zero : R_p.length = 0 := by omega
        match R_p, h_zero with
        | .nil _ _, _ => simp [Walk.vertices, List.tail, List.dropLast] at hx
    -- vL_p ∈ T (when L_p.length ≥ 1, i.e., vL_p ≠ a).
    have hvL_T_if_L_p_pos : L_p.length ≥ 1 → vL_p ∈ T := by
      intro h_L_p_pos
      have h_t_ne : L_p.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L_p h_L_p_pos
      have hvL_in_L_p_drop : vL_p ∈ L_p.vertices.dropLast := by
        rw [Walk.vertices_eq_head_cons_tail L_p,
            List.dropLast_cons_of_ne_nil h_t_ne]
        exact List.mem_cons_self
      have hvL_p_tail : vL_p ∈ p.vertices.tail :=
        hL_p_drop_sub _ hvL_in_L_p_drop
      have hvL_p_inter : vL_p ∈ p.vertices.tail.dropLast :=
        mem_interior_of_arm_source ha_p_tail hp_pos hvL_p_tail hvL_in_p_drop
      exact hp_inter _ hvL_p_inter
    -- vR_p ∈ T (when R_p.length ≥ 1, i.e., vR_p ≠ b).
    have hvR_T_if_R_p_pos : R_p.length ≥ 1 → vR_p ∈ T := by
      intro h_R_p_pos
      have h_t_ne : R_p.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R_p h_R_p_pos
      have hvR_in_R_p_drop : vR_p ∈ R_p.vertices.dropLast := by
        rw [Walk.vertices_eq_head_cons_tail R_p,
            List.dropLast_cons_of_ne_nil h_t_ne]
        exact List.mem_cons_self
      have hvR_p_drop : vR_p ∈ p.vertices.dropLast :=
        hR_p_drop_sub _ hvR_in_R_p_drop
      have hvR_p_inter : vR_p ∈ p.vertices.tail.dropLast :=
        mem_interior_of_arm_source ha_p_tail hp_pos hvR_in_p_tail hvR_p_drop
      exact hp_inter _ hvR_p_inter
    -- Vertex bounds for L_g, R_g (a/b in correct positions).
    have ha_notin_L_g_drop : a ∉ L_g.vertices.dropLast := by
      intro h_in
      rcases hL_g_drop_sub_S a h_in with h_in_L_p | h_in_S
      · exact ha_p_tail (hL_p_drop_sub a h_in_L_p)
      · exact ha_notS h_in_S
    have ha_notin_R_g : a ∉ R_g.vertices := by
      intro h_in
      rcases hR_g_sub_S a h_in with h_in_R_p | h_in_S
      · exact ha_p_tail (hR_p_sub a h_in_R_p)
      · exact ha_notS h_in_S
    have hb_notin_L_g : b ∉ L_g.vertices := by
      intro h_in
      rcases hL_g_sub_S b h_in with h_in_L_p | h_in_S
      · exact hb_p_drop (hL_p_sub b h_in_L_p)
      · exact hb_notS h_in_S
    have hb_notin_R_g_drop : b ∉ R_g.vertices.dropLast := by
      intro h_in
      rcases hR_g_drop_sub_S b h_in with h_in_R_p | h_in_S
      · exact hb_p_drop (hR_p_drop_sub b h_in_R_p)
      · exact hb_notS h_in_S
    -- Case split on Φ_L S vL_p vR_p (Or).
    rcases h_phi_L with ⟨M, hM_bif, hM_W⟩ | ⟨M, hM_bif, hM_W⟩
    · -- Inl case: M : Walk G vL_p vR_p.
      have hM_split_ex : ∃ k, M.IsBifurcationWithSplit k := hM_bif.2.2.2
      obtain ⟨k_M, hM_split⟩ := hM_split_ex
      have hM_pos : M.length ≥ 1 := Walk.length_pos_of_isBifurcation hM_bif
      have hvL_M_tail : vL_p ∉ M.vertices.tail := hM_bif.2.1
      have hvR_M_drop : vR_p ∉ M.vertices.dropLast := hM_bif.2.2.1
      by_cases h_M_dir : M.IsBifurcationDirectedHingeWithSplit k_M
      · -- Inl + directed M-hinge.
        obtain ⟨c_M, M_L, M_R, hM_L_dir, hM_R_dir, hM_L_pos, hM_R_pos, hidx_M,
                hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
          Walk.exists_arms_of_bifurcation_directed_hinge_strong M k_M h_M_dir
        -- Combined L: M_L.comp L_g : c_M → a.
        -- Combined R: M_R.comp R_g : c_M → b.
        have hLc_dir : (M_L.comp L_g).IsDirectedWalk :=
          Walk.isDirectedWalk_comp M_L L_g hM_L_dir hL_g_dir
        have hRc_dir : (M_R.comp R_g).IsDirectedWalk :=
          Walk.isDirectedWalk_comp M_R R_g hM_R_dir hR_g_dir
        have hLc_pos : (M_L.comp L_g).length ≥ 1 := by
          rw [Walk.length_comp]; omega
        have hRc_pos : (M_R.comp R_g).length ≥ 1 := by
          rw [Walk.length_comp]; omega
        -- M_L.dropLast ⊆ S (via M's interior).
        have hM_L_drop_S : ∀ x ∈ M_L.vertices.dropLast, x ∈ S :=
          Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx))
        have hM_R_drop_S : ∀ x ∈ M_R.vertices.dropLast, x ∈ S :=
          Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub
        -- a ∉ M_L.dropLast (since a ∉ S).
        have ha_notin_M_L_drop : a ∉ M_L.vertices.dropLast := fun h_in =>
          ha_notS (hM_L_drop_S a h_in)
        have ha_notin_M_R_drop : a ∉ M_R.vertices.dropLast := fun h_in =>
          ha_notS (hM_R_drop_S a h_in)
        have hb_notin_M_L_drop : b ∉ M_L.vertices.dropLast := fun h_in =>
          hb_notS (hM_L_drop_S b h_in)
        have hb_notin_M_R_drop : b ∉ M_R.vertices.dropLast := fun h_in =>
          hb_notS (hM_R_drop_S b h_in)
        -- Vertex bounds for combined walks via vertices_comp.
        have h_Lc_vs :
            (M_L.comp L_g).vertices = M_L.vertices.dropLast ++ L_g.vertices :=
          Walk.vertices_comp M_L L_g
        have h_Rc_vs :
            (M_R.comp R_g).vertices = M_R.vertices.dropLast ++ R_g.vertices :=
          Walk.vertices_comp M_R R_g
        have h_L_g_ne : L_g.vertices ≠ [] := Walk.vertices_ne_nil L_g
        have h_R_g_ne : R_g.vertices ≠ [] := Walk.vertices_ne_nil R_g
        have h_Lc_drop : (M_L.comp L_g).vertices.dropLast
            = M_L.vertices.dropLast ++ L_g.vertices.dropLast := by
          rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
        have h_Rc_drop : (M_R.comp R_g).vertices.dropLast
            = M_R.vertices.dropLast ++ R_g.vertices.dropLast := by
          rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
        have ha_notin_Lc_drop : a ∉ (M_L.comp L_g).vertices.dropLast := by
          rw [h_Lc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact ha_notin_M_L_drop h_M
          · exact ha_notin_L_g_drop h_L
        have ha_notin_Rc : a ∉ (M_R.comp R_g).vertices := by
          rw [h_Rc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact ha_notin_M_R_drop h_M
          · exact ha_notin_R_g h_R
        have hb_notin_Lc : b ∉ (M_L.comp L_g).vertices := by
          rw [h_Lc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact hb_notin_M_L_drop h_M
          · exact hb_notin_L_g h_L
        have hb_notin_Rc_drop : b ∉ (M_R.comp R_g).vertices.dropLast := by
          rw [h_Rc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact hb_notin_M_R_drop h_M
          · exact hb_notin_R_g_drop h_R
        refine ⟨Walk.mkBifurcation (M_L.comp L_g) hLc_dir hLc_pos
                  (M_R.comp R_g), ?_, ?_⟩
        · have h_src := Walk.mkBifurcation_isBifurcationSource
              (M_L.comp L_g) hLc_dir hLc_pos (M_R.comp R_g) hRc_dir hRc_pos
              hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
          exact Walk.isBifurcationSource_to_isBifurcation _ c_M h_src
        · -- Interior bound: ∀ x ∈ (mkBifurcation Lc Rc).tail.dropLast, x ∈ S ∪ T.
          intro x hx
          rw [vertices_tail_dropLast_mkBifurcation (M_L.comp L_g) hLc_dir hLc_pos
                (M_R.comp R_g) hRc_pos] at hx
          rcases List.mem_append.mp hx with hx_L | hx_R
          · -- x ∈ (M_L.comp L_g).vertices.tail.dropLast.reverse.
            rw [List.mem_reverse] at hx_L
            -- x ∈ Lc.tail.dropLast → x ∈ Lc.tail ⊆ Lc.vertices.
            have hx_Lc : x ∈ (M_L.comp L_g).vertices :=
              List.mem_of_mem_tail (List.mem_of_mem_dropLast hx_L)
            rw [h_Lc_vs] at hx_Lc
            rcases List.mem_append.mp hx_Lc with hxM | hxL
            · -- x ∈ M_L.vertices.dropLast → x ∈ S.
              exact Finset.mem_union_left _ (hM_L_drop_S x hxM)
            · -- x ∈ L_g.vertices.
              -- Need: x ∈ S ∪ T.  Split based on x ∈ L_g.tail.dropLast or boundary.
              have hLg_vs_eq : L_g.vertices = vL_p :: L_g.vertices.tail :=
                Walk.vertices_eq_head_cons_tail L_g
              rw [hLg_vs_eq] at hxL
              rcases List.mem_cons.mp hxL with hxL_eq | hxL_tail
              · -- hxL_eq : x = vL_p.  Need x ∈ S ∪ T.
                by_cases h_L_p_pos : L_p.length ≥ 1
                · rw [hxL_eq]
                  exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                · -- L_p.length = 0 → vL_p = a → x = a → contradiction.
                  have h_L_p_zero : L_p.length = 0 := by omega
                  have hvL_eq_a : vL_p = a := by
                    by_contra h_ne
                    have := Walk.length_pos_of_ne L_p h_ne
                    omega
                  have hx_eq_a : x = a := hxL_eq.trans hvL_eq_a
                  rw [hx_eq_a] at hx_L
                  -- a ∈ Lc.tail.dropLast → a ∈ Lc.dropLast (via Lc.dropLast = c_M :: Lc.tail.dropLast).
                  have h_Lc_t_ne : (M_L.comp L_g).vertices.tail ≠ [] :=
                    Walk.tail_vertices_ne_nil_of_pos _ hLc_pos
                  have h_Lc_drop_eq :
                      (M_L.comp L_g).vertices.dropLast
                        = c_M :: (M_L.comp L_g).vertices.tail.dropLast := by
                    conv_lhs => rw [Walk.vertices_eq_head_cons_tail (M_L.comp L_g)]
                    exact List.dropLast_cons_of_ne_nil h_Lc_t_ne
                  have hx_Lc_drop : a ∈ (M_L.comp L_g).vertices.dropLast := by
                    rw [h_Lc_drop_eq]; exact List.mem_cons_of_mem _ hx_L
                  exact absurd hx_Lc_drop ha_notin_Lc_drop
              · -- x ∈ L_g.vertices.tail.
                by_cases h_L_g_pos : L_g.length ≥ 1
                · have h_Lg_t_ne : L_g.vertices.tail ≠ [] :=
                    Walk.tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                  have h_Lg_t_last :=
                    Walk.tail_getLast_of_pos L_g h_L_g_pos
                  have h_Lg_decomp :
                      L_g.vertices.tail = L_g.vertices.tail.dropLast ++ [a] := by
                    have := List.dropLast_append_getLast h_Lg_t_ne
                    rw [h_Lg_t_last] at this
                    exact this.symm
                  rw [h_Lg_decomp] at hxL_tail
                  rcases List.mem_append.mp hxL_tail with hxL_int | hxL_a
                  · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                    · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                    · exact Finset.mem_union_left _ hx_S
                  · rw [List.mem_singleton] at hxL_a
                    rw [hxL_a] at hx_L
                    have h_Lc_t_ne : (M_L.comp L_g).vertices.tail ≠ [] :=
                      Walk.tail_vertices_ne_nil_of_pos _ hLc_pos
                    have h_Lc_drop_eq :
                        (M_L.comp L_g).vertices.dropLast
                          = c_M :: (M_L.comp L_g).vertices.tail.dropLast := by
                      conv_lhs => rw [Walk.vertices_eq_head_cons_tail (M_L.comp L_g)]
                      exact List.dropLast_cons_of_ne_nil h_Lc_t_ne
                    have hx_Lc_drop : a ∈ (M_L.comp L_g).vertices.dropLast := by
                      rw [h_Lc_drop_eq]; exact List.mem_cons_of_mem _ hx_L
                    exact absurd hx_Lc_drop ha_notin_Lc_drop
                · -- L_g.length = 0 → L_g.tail = []. Contradiction with hxL_tail.
                  have h_L_g_zero : L_g.length = 0 := by omega
                  match L_g, h_L_g_zero with
                  | .nil _ _, _ => simp [Walk.vertices, List.tail] at hxL_tail
          · -- x ∈ (M_R.comp R_g).vertices.dropLast.
            rw [h_Rc_drop] at hx_R
            rcases List.mem_append.mp hx_R with hxM | hxR
            · exact Finset.mem_union_left _ (hM_R_drop_S x hxM)
            · -- x ∈ R_g.vertices.dropLast.
              by_cases h_R_g_pos : R_g.length ≥ 1
              · have h_Rg_t_ne : R_g.vertices.tail ≠ [] :=
                  Walk.tail_vertices_ne_nil_of_pos R_g h_R_g_pos
                have h_Rg_drop_eq :
                    R_g.vertices.dropLast = vR_p :: R_g.vertices.tail.dropLast := by
                  conv_lhs => rw [Walk.vertices_eq_head_cons_tail R_g]
                  exact List.dropLast_cons_of_ne_nil h_Rg_t_ne
                rw [h_Rg_drop_eq] at hxR
                rcases List.mem_cons.mp hxR with hxR_eq | hxR_int
                · -- hxR_eq : x = vR_p.  Need x ∈ S ∪ T (vR_p ∉ S, so need ∈ T).
                  by_cases h_R_p_pos : R_p.length ≥ 1
                  · rw [hxR_eq]
                    exact Finset.mem_union_right _ (hvR_T_if_R_p_pos h_R_p_pos)
                  · -- R_p.length = 0 → vR_p = b → x = b → contradiction.
                    have h_R_p_zero : R_p.length = 0 := by omega
                    have hvR_eq_b : vR_p = b := by
                      by_contra h_ne
                      have := Walk.length_pos_of_ne R_p h_ne
                      omega
                    have hx_eq_b : x = b := hxR_eq.trans hvR_eq_b
                    rw [hx_eq_b] at hx_R
                    exact absurd hx_R (h_Rc_drop ▸ hb_notin_Rc_drop)
                · rcases hR_g_tdL_sub_S x hxR_int with hx_R_p | hx_S
                  · exact Finset.mem_union_right _ (hR_p_inter_T x hx_R_p)
                  · exact Finset.mem_union_left _ hx_S
              · -- R_g.length = 0 → R_g.dropLast = []. Contradiction with hxR.
                have h_R_g_zero : R_g.length = 0 := by omega
                match R_g, h_R_g_zero with
                | .nil _ _, _ => simp [Walk.vertices, List.dropLast] at hxR
      · -- Inl + bid M-hinge.
        obtain ⟨vML, vMR, M_L, M_R, hM_L_dir, hM_R_dir, hMLR_G, _,
                hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
          Walk.exists_arms_of_bifurcation_bidir_hinge_strong M k_M hM_split h_M_dir
        -- M_L : Walk G vML vL_p. M_R : Walk G vMR vR_p. (vML, vMR) ∈ G.L.
        have hLc_dir : (M_L.comp L_g).IsDirectedWalk :=
          Walk.isDirectedWalk_comp M_L L_g hM_L_dir hL_g_dir
        have hRc_dir : (M_R.comp R_g).IsDirectedWalk :=
          Walk.isDirectedWalk_comp M_R R_g hM_R_dir hR_g_dir
        have hM_L_drop_S : ∀ x ∈ M_L.vertices.dropLast, x ∈ S :=
          Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx))
        have hM_R_drop_S : ∀ x ∈ M_R.vertices.dropLast, x ∈ S :=
          Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub
        have ha_notin_M_L_drop : a ∉ M_L.vertices.dropLast := fun h_in =>
          ha_notS (hM_L_drop_S a h_in)
        have ha_notin_M_R_drop : a ∉ M_R.vertices.dropLast := fun h_in =>
          ha_notS (hM_R_drop_S a h_in)
        have hb_notin_M_L_drop : b ∉ M_L.vertices.dropLast := fun h_in =>
          hb_notS (hM_L_drop_S b h_in)
        have hb_notin_M_R_drop : b ∉ M_R.vertices.dropLast := fun h_in =>
          hb_notS (hM_R_drop_S b h_in)
        have h_Lc_vs :
            (M_L.comp L_g).vertices = M_L.vertices.dropLast ++ L_g.vertices :=
          Walk.vertices_comp M_L L_g
        have h_Rc_vs :
            (M_R.comp R_g).vertices = M_R.vertices.dropLast ++ R_g.vertices :=
          Walk.vertices_comp M_R R_g
        have h_L_g_ne : L_g.vertices ≠ [] := Walk.vertices_ne_nil L_g
        have h_R_g_ne : R_g.vertices ≠ [] := Walk.vertices_ne_nil R_g
        have h_Lc_drop : (M_L.comp L_g).vertices.dropLast
            = M_L.vertices.dropLast ++ L_g.vertices.dropLast := by
          rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
        have h_Rc_drop : (M_R.comp R_g).vertices.dropLast
            = M_R.vertices.dropLast ++ R_g.vertices.dropLast := by
          rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
        have ha_notin_Lc_drop : a ∉ (M_L.comp L_g).vertices.dropLast := by
          rw [h_Lc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact ha_notin_M_L_drop h_M
          · exact ha_notin_L_g_drop h_L
        have ha_notin_Rc : a ∉ (M_R.comp R_g).vertices := by
          rw [h_Rc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact ha_notin_M_R_drop h_M
          · exact ha_notin_R_g h_R
        have hb_notin_Lc : b ∉ (M_L.comp L_g).vertices := by
          rw [h_Lc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact hb_notin_M_L_drop h_M
          · exact hb_notin_L_g h_L
        have hb_notin_Rc_drop : b ∉ (M_R.comp R_g).vertices.dropLast := by
          rw [h_Rc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact hb_notin_M_R_drop h_M
          · exact hb_notin_R_g_drop h_R
        refine ⟨Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir
                  (M_R.comp R_g) hMLR_G, ?_, ?_⟩
        · exact Walk.mkBifurcationBidir_isBifurcation (M_L.comp L_g) hLc_dir
            (M_R.comp R_g) hRc_dir hMLR_G hab_ne ha_notin_Lc_drop ha_notin_Rc
            hb_notin_Lc hb_notin_Rc_drop
        · -- Interior bound.
          intro x hx
          -- bif vertices = Lc.vertices.reverse.dropLast ++ (vML :: Rc.vertices).
          -- Need: x ∈ bif.vertices.tail.dropLast → x ∈ S ∪ T.
          -- We argue from x ∈ bif.vertices.
          have hx_bif_vs : x ∈
              (Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir
                (M_R.comp R_g) hMLR_G).vertices :=
            List.mem_of_mem_tail (List.mem_of_mem_dropLast hx)
          rw [Walk.vertices_mkBifurcationBidir
                (M_L.comp L_g) hLc_dir (M_R.comp R_g) hMLR_G] at hx_bif_vs
          rcases List.mem_append.mp hx_bif_vs with hx_Lc_rev | hx_Rc
          · -- x ∈ Lc.vertices.reverse.dropLast → x ∈ Lc.vertices and x ≠ a (Lc's target).
            have hx_Lc_vs : x ∈ (M_L.comp L_g).vertices := by
              have := List.mem_of_mem_dropLast hx_Lc_rev
              rwa [List.mem_reverse] at this
            -- x ≠ a, since otherwise hx_bif (tail.dropLast) would contradict by giving
            -- a in tail.dropLast.  Actually we need a stronger argument.
            -- We'll show x ∈ Lc.dropLast (excluding the target a).
            -- x ∈ Lc.reverse.dropLast → x is in Lc.reverse but not the last (= a).
            -- Equivalently, x ∈ Lc.tail (= Lc.reverse.dropLast.reverse).
            -- We have hx_Lc_rev : x ∈ Lc.reverse.dropLast.
            -- Lc.reverse = a :: ... (since Lc ends at a). Lc.reverse.dropLast drops the last.
            -- Hmm, this is getting complicated. Let me use a direct approach:
            -- Lc.reverse.dropLast = Lc.tail.reverse (Walk.vertices_reverse_dropLast).
            rw [Walk.vertices_reverse_dropLast (M_L.comp L_g)] at hx_Lc_rev
            -- hx_Lc_rev : x ∈ Lc.vertices.tail.reverse.
            rw [List.mem_reverse] at hx_Lc_rev
            -- hx_Lc_rev : x ∈ Lc.vertices.tail.
            -- x ∈ Lc.vertices.tail = (M_L.dropLast ++ L_g.vertices).tail.
            -- Case-split on M_L.length.
            by_cases h_M_L_pos : M_L.length ≥ 1
            · -- M_L.dropLast ≠ [].  Lc.tail = M_L.dropLast.tail ++ L_g.vertices.
              have h_M_L_drop_ne : M_L.vertices.dropLast ≠ [] := by
                have h_M_L_t_ne : M_L.vertices.tail ≠ [] :=
                  Walk.tail_vertices_ne_nil_of_pos M_L h_M_L_pos
                rw [Walk.vertices_eq_head_cons_tail M_L,
                    List.dropLast_cons_of_ne_nil h_M_L_t_ne]
                exact List.cons_ne_nil _ _
              rw [h_Lc_vs, List.tail_append_of_ne_nil h_M_L_drop_ne] at hx_Lc_rev
              rcases List.mem_append.mp hx_Lc_rev with hxM | hxL
              · -- x ∈ M_L.vertices.dropLast.tail.
                have hxM_in_drop : x ∈ M_L.vertices.dropLast :=
                  List.mem_of_mem_tail hxM
                exact Finset.mem_union_left _ (hM_L_drop_S x hxM_in_drop)
              · -- x ∈ L_g.vertices.  Same analysis as before (with vL_p, L_p.length cases).
                have hLg_vs_eq : L_g.vertices = vL_p :: L_g.vertices.tail :=
                  Walk.vertices_eq_head_cons_tail L_g
                rw [hLg_vs_eq] at hxL
                rcases List.mem_cons.mp hxL with hx_eq_vL | hxL_tail
                · -- x = vL_p.
                  by_cases h_L_p_pos : L_p.length ≥ 1
                  · rw [hx_eq_vL]
                    exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                  · -- L_p.length = 0 → vL_p = a → x = a, contradicting hx in bif.tail.dropLast.
                    have h_L_p_zero : L_p.length = 0 := by omega
                    have hvL_eq_a : vL_p = a := by
                      by_contra h_ne
                      have := Walk.length_pos_of_ne L_p h_ne
                      omega
                    -- x = vL_p = a. But hx_bif_vs derived from hx in bif.tail.dropLast.
                    -- a ∉ bif.tail.dropLast (a is the bif walk's head).
                    -- More concretely, we need a contradiction via hx.
                    have hx_a : x = a := hx_eq_vL.trans hvL_eq_a
                    rw [hx_a] at hx
                    -- hx : a ∈ bif.tail.dropLast → a ∈ bif.tail → false (a is bif's head).
                    -- Use the bif's IsBifurcation: head ∉ tail.
                    have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                      (M_L.comp L_g) hLc_dir (M_R.comp R_g) hRc_dir hMLR_G
                      hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                    have h_head_notin_tail := hbif_bif.2.1
                    -- h_head_notin_tail : a ∉ bif.vertices.tail.
                    have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                    exact absurd hx_bif_tail h_head_notin_tail
                · -- x ∈ L_g.vertices.tail.  Case-split on L_g.length.
                  by_cases h_L_g_pos : L_g.length ≥ 1
                  · have h_Lg_t_ne : L_g.vertices.tail ≠ [] :=
                      Walk.tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                    have h_Lg_t_last :=
                      Walk.tail_getLast_of_pos L_g h_L_g_pos
                    have h_Lg_decomp :
                        L_g.vertices.tail = L_g.vertices.tail.dropLast ++ [a] := by
                      have := List.dropLast_append_getLast h_Lg_t_ne
                      rw [h_Lg_t_last] at this
                      exact this.symm
                    rw [h_Lg_decomp] at hxL_tail
                    rcases List.mem_append.mp hxL_tail with hxL_int | hxL_a
                    · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                      · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                      · exact Finset.mem_union_left _ hx_S
                    · rw [List.mem_singleton] at hxL_a
                      rw [hxL_a] at hx
                      have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                        (M_L.comp L_g) hLc_dir (M_R.comp R_g) hRc_dir hMLR_G
                        hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                      have h_head_notin_tail := hbif_bif.2.1
                      have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                      exact absurd hx_bif_tail h_head_notin_tail
                  · -- L_g.length = 0 → L_g.tail = []. hxL_tail vacuous.
                    have h_L_g_zero : L_g.length = 0 := by omega
                    match L_g, h_L_g_zero with
                    | .nil _ _, _ => simp [Walk.vertices, List.tail] at hxL_tail
            · -- M_L.length = 0 → M_L = nil, vML = vL_p.
              -- M_L.dropLast = []. Lc.vertices = [] ++ L_g.vertices = L_g.vertices.
              -- Lc.vertices.tail = L_g.vertices.tail.
              have h_M_L_zero : M_L.length = 0 := by omega
              have hM_L_drop_empty : M_L.vertices.dropLast = [] := by
                match M_L, h_M_L_zero with
                | .nil _ _, _ => simp [Walk.vertices, List.dropLast]
              rw [h_Lc_vs, hM_L_drop_empty, List.nil_append] at hx_Lc_rev
              -- hx_Lc_rev : x ∈ L_g.vertices.tail.
              by_cases h_L_g_pos : L_g.length ≥ 1
              · have h_Lg_t_ne : L_g.vertices.tail ≠ [] :=
                  Walk.tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                have h_Lg_t_last :=
                  Walk.tail_getLast_of_pos L_g h_L_g_pos
                have h_Lg_decomp :
                    L_g.vertices.tail = L_g.vertices.tail.dropLast ++ [a] := by
                  have := List.dropLast_append_getLast h_Lg_t_ne
                  rw [h_Lg_t_last] at this
                  exact this.symm
                rw [h_Lg_decomp] at hx_Lc_rev
                rcases List.mem_append.mp hx_Lc_rev with hxL_int | hxL_a
                · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                  · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                  · exact Finset.mem_union_left _ hx_S
                · rw [List.mem_singleton] at hxL_a
                  rw [hxL_a] at hx
                  have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                    (M_L.comp L_g) hLc_dir (M_R.comp R_g) hRc_dir hMLR_G
                    hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                  have h_head_notin_tail := hbif_bif.2.1
                  have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                  exact absurd hx_bif_tail h_head_notin_tail
              · -- L_g.length = 0 → L_g.tail = []. Contradiction.
                have h_L_g_zero : L_g.length = 0 := by omega
                match L_g, h_L_g_zero with
                | .nil _ _, _ => simp [Walk.vertices, List.tail] at hx_Lc_rev
          · -- x ∈ vML :: Rc.vertices.
            rcases List.mem_cons.mp hx_Rc with hx_eq_vML | hx_Rc_vs
            · -- x = vML.
              -- vML's status: either vML ∈ S (if M_L.length ≥ 1) or vML = vL_p
              -- (if M_L = nil), in which case the vL_p analysis applies.
              by_cases h_M_L_pos : M_L.length ≥ 1
              · -- vML ∈ M_L.dropLast (head). M_L.dropLast ⊆ S. So vML ∈ S.
                have h_M_L_t_ne : M_L.vertices.tail ≠ [] :=
                  Walk.tail_vertices_ne_nil_of_pos M_L h_M_L_pos
                have hvML_in_M_L_drop : vML ∈ M_L.vertices.dropLast := by
                  rw [Walk.vertices_eq_head_cons_tail M_L,
                      List.dropLast_cons_of_ne_nil h_M_L_t_ne]
                  exact List.mem_cons_self
                rw [hx_eq_vML]
                exact Finset.mem_union_left _ (hM_L_drop_S vML hvML_in_M_L_drop)
              · -- M_L.length = 0 → vML = vL_p. Then either vL_p ∈ T (L_p.length ≥ 1)
                -- or vL_p = a (then x = a contradicts hx).
                have h_M_L_zero : M_L.length = 0 := by omega
                have hvML_eq_vL : vML = vL_p := by
                  by_contra h_ne
                  have := Walk.length_pos_of_ne M_L h_ne
                  omega
                by_cases h_L_p_pos : L_p.length ≥ 1
                · rw [hx_eq_vML, hvML_eq_vL]
                  exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                · -- L_p.length = 0 → vL_p = a → vML = a → x = a → contradiction.
                  have h_L_p_zero : L_p.length = 0 := by omega
                  have hvL_eq_a : vL_p = a := by
                    by_contra h_ne
                    have := Walk.length_pos_of_ne L_p h_ne
                    omega
                  have hx_a : x = a := hx_eq_vML.trans (hvML_eq_vL.trans hvL_eq_a)
                  rw [hx_a] at hx
                  have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                    (M_L.comp L_g) hLc_dir (M_R.comp R_g) hRc_dir hMLR_G
                    hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                  have h_head_notin_tail := hbif_bif.2.1
                  have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                  exact absurd hx_bif_tail h_head_notin_tail
            · -- x ∈ Rc.vertices = M_R.dropLast ++ R_g.vertices.
              rw [h_Rc_vs] at hx_Rc_vs
              rcases List.mem_append.mp hx_Rc_vs with hxM | hxR
              · exact Finset.mem_union_left _ (hM_R_drop_S x hxM)
              · -- x ∈ R_g.vertices.
                have hRg_vs_eq : R_g.vertices = vR_p :: R_g.vertices.tail :=
                  Walk.vertices_eq_head_cons_tail R_g
                rw [hRg_vs_eq] at hxR
                rcases List.mem_cons.mp hxR with hx_eq_vR | hxR_tail
                · -- x = vR_p.
                  by_cases h_R_p_pos : R_p.length ≥ 1
                  · rw [hx_eq_vR]
                    exact Finset.mem_union_right _ (hvR_T_if_R_p_pos h_R_p_pos)
                  · -- R_p.length = 0 → vR_p = b → x = b → contradiction (b is bif's last).
                    have h_R_p_zero : R_p.length = 0 := by omega
                    have hvR_eq_b : vR_p = b := by
                      by_contra h_ne
                      have := Walk.length_pos_of_ne R_p h_ne
                      omega
                    have hx_b : x = b := hx_eq_vR.trans hvR_eq_b
                    rw [hx_b] at hx
                    -- hx : b ∈ bif.tail.dropLast.  b is bif's last.
                    have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                      (M_L.comp L_g) hLc_dir (M_R.comp R_g) hRc_dir hMLR_G
                      hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                    have h_last_notin_drop := hbif_bif.2.2.1
                    -- h_last_notin_drop : b ∉ bif.vertices.dropLast.
                    -- hx : b ∈ bif.vertices.tail.dropLast → b ∈ bif.vertices.dropLast.
                    -- (Because tail.dropLast ⊆ dropLast for non-trivial walks.)
                    have h_bif_t_ne : (Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir
                                         (M_R.comp R_g) hMLR_G).vertices.tail ≠ [] := by
                      have h_bif_pos := Walk.length_pos_of_isBifurcation hbif_bif
                      exact Walk.tail_vertices_ne_nil_of_pos _ h_bif_pos
                    have h_bif_drop_eq :
                        (Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir
                          (M_R.comp R_g) hMLR_G).vertices.dropLast
                        = a :: (Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir
                                  (M_R.comp R_g) hMLR_G).vertices.tail.dropLast := by
                      conv_lhs => rw [Walk.vertices_eq_head_cons_tail _]
                      exact List.dropLast_cons_of_ne_nil h_bif_t_ne
                    have hx_bif_drop : b ∈ (Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir
                                              (M_R.comp R_g) hMLR_G).vertices.dropLast := by
                      rw [h_bif_drop_eq]; exact List.mem_cons_of_mem _ hx
                    exact absurd hx_bif_drop h_last_notin_drop
                · -- x ∈ R_g.vertices.tail.  Case-split on R_g.length.
                  by_cases h_R_g_pos : R_g.length ≥ 1
                  · have h_Rg_t_ne : R_g.vertices.tail ≠ [] :=
                      Walk.tail_vertices_ne_nil_of_pos R_g h_R_g_pos
                    have h_Rg_t_last :=
                      Walk.tail_getLast_of_pos R_g h_R_g_pos
                    have h_Rg_decomp :
                        R_g.vertices.tail = R_g.vertices.tail.dropLast ++ [b] := by
                      have := List.dropLast_append_getLast h_Rg_t_ne
                      rw [h_Rg_t_last] at this
                      exact this.symm
                    rw [h_Rg_decomp] at hxR_tail
                    rcases List.mem_append.mp hxR_tail with hxR_int | hxR_b
                    · rcases hR_g_tdL_sub_S x hxR_int with hx_R_p | hx_S
                      · exact Finset.mem_union_right _ (hR_p_inter_T x hx_R_p)
                      · exact Finset.mem_union_left _ hx_S
                    · rw [List.mem_singleton] at hxR_b
                      rw [hxR_b] at hx
                      have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                        (M_L.comp L_g) hLc_dir (M_R.comp R_g) hRc_dir hMLR_G
                        hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                      have h_last_notin_drop := hbif_bif.2.2.1
                      have h_bif_t_ne : (Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir
                                           (M_R.comp R_g) hMLR_G).vertices.tail ≠ [] := by
                        have h_bif_pos := Walk.length_pos_of_isBifurcation hbif_bif
                        exact Walk.tail_vertices_ne_nil_of_pos _ h_bif_pos
                      have h_bif_drop_eq :
                          (Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir
                            (M_R.comp R_g) hMLR_G).vertices.dropLast
                          = a :: (Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir
                                    (M_R.comp R_g) hMLR_G).vertices.tail.dropLast := by
                        conv_lhs => rw [Walk.vertices_eq_head_cons_tail _]
                        exact List.dropLast_cons_of_ne_nil h_bif_t_ne
                      have hx_bif_drop : b ∈ (Walk.mkBifurcationBidir (M_L.comp L_g) hLc_dir
                                                (M_R.comp R_g) hMLR_G).vertices.dropLast := by
                        rw [h_bif_drop_eq]; exact List.mem_cons_of_mem _ hx
                      exact absurd hx_bif_drop h_last_notin_drop
                  · -- R_g.length = 0 → R_g.tail = []. Contradiction.
                    have h_R_g_zero : R_g.length = 0 := by omega
                    match R_g, h_R_g_zero with
                    | .nil _ _, _ => simp [Walk.vertices, List.tail] at hxR_tail
    · -- Inr case: M : Walk G vR_p vL_p.
      have hM_split_ex : ∃ k, M.IsBifurcationWithSplit k := hM_bif.2.2.2
      obtain ⟨k_M, hM_split⟩ := hM_split_ex
      have hM_pos : M.length ≥ 1 := Walk.length_pos_of_isBifurcation hM_bif
      -- For inr orientation: M.head = vR_p, M.tail's last = vL_p.
      have hvR_M_tail : vR_p ∉ M.vertices.tail := hM_bif.2.1
      have hvL_M_drop : vL_p ∉ M.vertices.dropLast := hM_bif.2.2.1
      by_cases h_M_dir : M.IsBifurcationDirectedHingeWithSplit k_M
      · -- Inr + directed M-hinge.
        obtain ⟨c_M, M_L, M_R, hM_L_dir, hM_R_dir, hM_L_pos, hM_R_pos, _,
                hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
          Walk.exists_arms_of_bifurcation_directed_hinge_strong M k_M h_M_dir
        -- M_L : Walk G c_M vR_p, M_R : Walk G c_M vL_p.
        -- Combined L (to a via vL_p): M_R.comp L_g : Walk G c_M a.
        -- Combined R (to b via vR_p): M_L.comp R_g : Walk G c_M b.
        have hLc_dir : (M_R.comp L_g).IsDirectedWalk :=
          Walk.isDirectedWalk_comp M_R L_g hM_R_dir hL_g_dir
        have hRc_dir : (M_L.comp R_g).IsDirectedWalk :=
          Walk.isDirectedWalk_comp M_L R_g hM_L_dir hR_g_dir
        have hLc_pos : (M_R.comp L_g).length ≥ 1 := by
          rw [Walk.length_comp]; omega
        have hRc_pos : (M_L.comp R_g).length ≥ 1 := by
          rw [Walk.length_comp]; omega
        -- M_L.dropLast ⊆ S, M_R.dropLast ⊆ S via M's interior.
        have hM_L_drop_S : ∀ x ∈ M_L.vertices.dropLast, x ∈ S :=
          Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx))
        have hM_R_drop_S : ∀ x ∈ M_R.vertices.dropLast, x ∈ S :=
          Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub
        have ha_notin_M_L_drop : a ∉ M_L.vertices.dropLast := fun h_in =>
          ha_notS (hM_L_drop_S a h_in)
        have ha_notin_M_R_drop : a ∉ M_R.vertices.dropLast := fun h_in =>
          ha_notS (hM_R_drop_S a h_in)
        have hb_notin_M_L_drop : b ∉ M_L.vertices.dropLast := fun h_in =>
          hb_notS (hM_L_drop_S b h_in)
        have hb_notin_M_R_drop : b ∉ M_R.vertices.dropLast := fun h_in =>
          hb_notS (hM_R_drop_S b h_in)
        have h_Lc_vs :
            (M_R.comp L_g).vertices = M_R.vertices.dropLast ++ L_g.vertices :=
          Walk.vertices_comp M_R L_g
        have h_Rc_vs :
            (M_L.comp R_g).vertices = M_L.vertices.dropLast ++ R_g.vertices :=
          Walk.vertices_comp M_L R_g
        have h_L_g_ne : L_g.vertices ≠ [] := Walk.vertices_ne_nil L_g
        have h_R_g_ne : R_g.vertices ≠ [] := Walk.vertices_ne_nil R_g
        have h_Lc_drop : (M_R.comp L_g).vertices.dropLast
            = M_R.vertices.dropLast ++ L_g.vertices.dropLast := by
          rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
        have h_Rc_drop : (M_L.comp R_g).vertices.dropLast
            = M_L.vertices.dropLast ++ R_g.vertices.dropLast := by
          rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
        have ha_notin_Lc_drop : a ∉ (M_R.comp L_g).vertices.dropLast := by
          rw [h_Lc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact ha_notin_M_R_drop h_M
          · exact ha_notin_L_g_drop h_L
        have ha_notin_Rc : a ∉ (M_L.comp R_g).vertices := by
          rw [h_Rc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact ha_notin_M_L_drop h_M
          · exact ha_notin_R_g h_R
        have hb_notin_Lc : b ∉ (M_R.comp L_g).vertices := by
          rw [h_Lc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact hb_notin_M_R_drop h_M
          · exact hb_notin_L_g h_L
        have hb_notin_Rc_drop : b ∉ (M_L.comp R_g).vertices.dropLast := by
          rw [h_Rc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact hb_notin_M_L_drop h_M
          · exact hb_notin_R_g_drop h_R
        refine ⟨Walk.mkBifurcation (M_R.comp L_g) hLc_dir hLc_pos
                  (M_L.comp R_g), ?_, ?_⟩
        · have h_src := Walk.mkBifurcation_isBifurcationSource
              (M_R.comp L_g) hLc_dir hLc_pos (M_L.comp R_g) hRc_dir hRc_pos
              hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
          exact Walk.isBifurcationSource_to_isBifurcation _ c_M h_src
        · intro x hx
          rw [vertices_tail_dropLast_mkBifurcation (M_R.comp L_g) hLc_dir hLc_pos
                (M_L.comp R_g) hRc_pos] at hx
          rcases List.mem_append.mp hx with hx_L | hx_R
          · rw [List.mem_reverse] at hx_L
            have hx_Lc : x ∈ (M_R.comp L_g).vertices :=
              List.mem_of_mem_tail (List.mem_of_mem_dropLast hx_L)
            rw [h_Lc_vs] at hx_Lc
            rcases List.mem_append.mp hx_Lc with hxM | hxL
            · exact Finset.mem_union_left _ (hM_R_drop_S x hxM)
            · have hLg_vs_eq : L_g.vertices = vL_p :: L_g.vertices.tail :=
                Walk.vertices_eq_head_cons_tail L_g
              rw [hLg_vs_eq] at hxL
              rcases List.mem_cons.mp hxL with hx_eq_vL | hxL_tail
              · by_cases h_L_p_pos : L_p.length ≥ 1
                · rw [hx_eq_vL]
                  exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                · have h_L_p_zero : L_p.length = 0 := by omega
                  have hvL_eq_a : vL_p = a := by
                    by_contra h_ne
                    have := Walk.length_pos_of_ne L_p h_ne
                    omega
                  have hx_eq_a : x = a := hx_eq_vL.trans hvL_eq_a
                  rw [hx_eq_a] at hx_L
                  have h_Lc_t_ne : (M_R.comp L_g).vertices.tail ≠ [] :=
                    Walk.tail_vertices_ne_nil_of_pos _ hLc_pos
                  have h_Lc_drop_eq :
                      (M_R.comp L_g).vertices.dropLast
                        = c_M :: (M_R.comp L_g).vertices.tail.dropLast := by
                    conv_lhs => rw [Walk.vertices_eq_head_cons_tail (M_R.comp L_g)]
                    exact List.dropLast_cons_of_ne_nil h_Lc_t_ne
                  have hx_Lc_drop : a ∈ (M_R.comp L_g).vertices.dropLast := by
                    rw [h_Lc_drop_eq]; exact List.mem_cons_of_mem _ hx_L
                  exact absurd hx_Lc_drop ha_notin_Lc_drop
              · by_cases h_L_g_pos : L_g.length ≥ 1
                · have h_Lg_t_ne : L_g.vertices.tail ≠ [] :=
                    Walk.tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                  have h_Lg_t_last :=
                    Walk.tail_getLast_of_pos L_g h_L_g_pos
                  have h_Lg_decomp :
                      L_g.vertices.tail = L_g.vertices.tail.dropLast ++ [a] := by
                    have := List.dropLast_append_getLast h_Lg_t_ne
                    rw [h_Lg_t_last] at this
                    exact this.symm
                  rw [h_Lg_decomp] at hxL_tail
                  rcases List.mem_append.mp hxL_tail with hxL_int | hxL_a
                  · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                    · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                    · exact Finset.mem_union_left _ hx_S
                  · rw [List.mem_singleton] at hxL_a
                    rw [hxL_a] at hx_L
                    have h_Lc_t_ne : (M_R.comp L_g).vertices.tail ≠ [] :=
                      Walk.tail_vertices_ne_nil_of_pos _ hLc_pos
                    have h_Lc_drop_eq :
                        (M_R.comp L_g).vertices.dropLast
                          = c_M :: (M_R.comp L_g).vertices.tail.dropLast := by
                      conv_lhs => rw [Walk.vertices_eq_head_cons_tail (M_R.comp L_g)]
                      exact List.dropLast_cons_of_ne_nil h_Lc_t_ne
                    have hx_Lc_drop : a ∈ (M_R.comp L_g).vertices.dropLast := by
                      rw [h_Lc_drop_eq]; exact List.mem_cons_of_mem _ hx_L
                    exact absurd hx_Lc_drop ha_notin_Lc_drop
                · have h_L_g_zero : L_g.length = 0 := by omega
                  match L_g, h_L_g_zero with
                  | .nil _ _, _ => simp [Walk.vertices, List.tail] at hxL_tail
          · rw [h_Rc_drop] at hx_R
            rcases List.mem_append.mp hx_R with hxM | hxR
            · exact Finset.mem_union_left _ (hM_L_drop_S x hxM)
            · by_cases h_R_g_pos : R_g.length ≥ 1
              · have h_Rg_t_ne : R_g.vertices.tail ≠ [] :=
                  Walk.tail_vertices_ne_nil_of_pos R_g h_R_g_pos
                have h_Rg_drop_eq :
                    R_g.vertices.dropLast = vR_p :: R_g.vertices.tail.dropLast := by
                  conv_lhs => rw [Walk.vertices_eq_head_cons_tail R_g]
                  exact List.dropLast_cons_of_ne_nil h_Rg_t_ne
                rw [h_Rg_drop_eq] at hxR
                rcases List.mem_cons.mp hxR with hxR_eq | hxR_int
                · by_cases h_R_p_pos : R_p.length ≥ 1
                  · rw [hxR_eq]
                    exact Finset.mem_union_right _ (hvR_T_if_R_p_pos h_R_p_pos)
                  · have h_R_p_zero : R_p.length = 0 := by omega
                    have hvR_eq_b : vR_p = b := by
                      by_contra h_ne
                      have := Walk.length_pos_of_ne R_p h_ne
                      omega
                    have hx_eq_b : x = b := hxR_eq.trans hvR_eq_b
                    rw [hx_eq_b] at hx_R
                    exact absurd hx_R (h_Rc_drop ▸ hb_notin_Rc_drop)
                · rcases hR_g_tdL_sub_S x hxR_int with hx_R_p | hx_S
                  · exact Finset.mem_union_right _ (hR_p_inter_T x hx_R_p)
                  · exact Finset.mem_union_left _ hx_S
              · have h_R_g_zero : R_g.length = 0 := by omega
                match R_g, h_R_g_zero with
                | .nil _ _, _ => simp [Walk.vertices, List.dropLast] at hxR
      · -- Inr + bid M-hinge.
        obtain ⟨vML, vMR, M_L, M_R, hM_L_dir, hM_R_dir, hMLR_G, _,
                hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
          Walk.exists_arms_of_bifurcation_bidir_hinge_strong M k_M hM_split h_M_dir
        -- M_L : Walk G vML vR_p. M_R : Walk G vMR vL_p. (vML, vMR) ∈ G.L.
        -- Combined L (to a via vL_p): M_R.comp L_g : Walk G vMR a.
        -- Combined R (to b via vR_p): M_L.comp R_g : Walk G vML b.
        -- Hinge: (vMR, vML) ∈ G.L via hL_symm.
        have hMLR_sym : (vMR, vML) ∈ G.L := G.hL_symm hMLR_G
        have hLc_dir : (M_R.comp L_g).IsDirectedWalk :=
          Walk.isDirectedWalk_comp M_R L_g hM_R_dir hL_g_dir
        have hRc_dir : (M_L.comp R_g).IsDirectedWalk :=
          Walk.isDirectedWalk_comp M_L R_g hM_L_dir hR_g_dir
        have hM_L_drop_S : ∀ x ∈ M_L.vertices.dropLast, x ∈ S :=
          Walk.arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx))
        have hM_R_drop_S : ∀ x ∈ M_R.vertices.dropLast, x ∈ S :=
          Walk.arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub
        have ha_notin_M_L_drop : a ∉ M_L.vertices.dropLast := fun h_in =>
          ha_notS (hM_L_drop_S a h_in)
        have ha_notin_M_R_drop : a ∉ M_R.vertices.dropLast := fun h_in =>
          ha_notS (hM_R_drop_S a h_in)
        have hb_notin_M_L_drop : b ∉ M_L.vertices.dropLast := fun h_in =>
          hb_notS (hM_L_drop_S b h_in)
        have hb_notin_M_R_drop : b ∉ M_R.vertices.dropLast := fun h_in =>
          hb_notS (hM_R_drop_S b h_in)
        have h_Lc_vs :
            (M_R.comp L_g).vertices = M_R.vertices.dropLast ++ L_g.vertices :=
          Walk.vertices_comp M_R L_g
        have h_Rc_vs :
            (M_L.comp R_g).vertices = M_L.vertices.dropLast ++ R_g.vertices :=
          Walk.vertices_comp M_L R_g
        have h_L_g_ne : L_g.vertices ≠ [] := Walk.vertices_ne_nil L_g
        have h_R_g_ne : R_g.vertices ≠ [] := Walk.vertices_ne_nil R_g
        have h_Lc_drop : (M_R.comp L_g).vertices.dropLast
            = M_R.vertices.dropLast ++ L_g.vertices.dropLast := by
          rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
        have h_Rc_drop : (M_L.comp R_g).vertices.dropLast
            = M_L.vertices.dropLast ++ R_g.vertices.dropLast := by
          rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
        have ha_notin_Lc_drop : a ∉ (M_R.comp L_g).vertices.dropLast := by
          rw [h_Lc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact ha_notin_M_R_drop h_M
          · exact ha_notin_L_g_drop h_L
        have ha_notin_Rc : a ∉ (M_L.comp R_g).vertices := by
          rw [h_Rc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact ha_notin_M_L_drop h_M
          · exact ha_notin_R_g h_R
        have hb_notin_Lc : b ∉ (M_R.comp L_g).vertices := by
          rw [h_Lc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact hb_notin_M_R_drop h_M
          · exact hb_notin_L_g h_L
        have hb_notin_Rc_drop : b ∉ (M_L.comp R_g).vertices.dropLast := by
          rw [h_Rc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact hb_notin_M_L_drop h_M
          · exact hb_notin_R_g_drop h_R
        refine ⟨Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir
                  (M_L.comp R_g) hMLR_sym, ?_, ?_⟩
        · exact Walk.mkBifurcationBidir_isBifurcation (M_R.comp L_g) hLc_dir
            (M_L.comp R_g) hRc_dir hMLR_sym hab_ne ha_notin_Lc_drop ha_notin_Rc
            hb_notin_Lc hb_notin_Rc_drop
        · -- Interior bound.
          intro x hx
          have hx_bif_vs : x ∈
              (Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir
                (M_L.comp R_g) hMLR_sym).vertices :=
            List.mem_of_mem_tail (List.mem_of_mem_dropLast hx)
          rw [Walk.vertices_mkBifurcationBidir
                (M_R.comp L_g) hLc_dir (M_L.comp R_g) hMLR_sym] at hx_bif_vs
          rcases List.mem_append.mp hx_bif_vs with hx_Lc_rev | hx_Rc
          · rw [Walk.vertices_reverse_dropLast (M_R.comp L_g)] at hx_Lc_rev
            rw [List.mem_reverse] at hx_Lc_rev
            by_cases h_M_R_pos : M_R.length ≥ 1
            · have h_M_R_drop_ne : M_R.vertices.dropLast ≠ [] := by
                have h_M_R_t_ne : M_R.vertices.tail ≠ [] :=
                  Walk.tail_vertices_ne_nil_of_pos M_R h_M_R_pos
                rw [Walk.vertices_eq_head_cons_tail M_R,
                    List.dropLast_cons_of_ne_nil h_M_R_t_ne]
                exact List.cons_ne_nil _ _
              rw [h_Lc_vs, List.tail_append_of_ne_nil h_M_R_drop_ne] at hx_Lc_rev
              rcases List.mem_append.mp hx_Lc_rev with hxM | hxL
              · have hxM_in_drop : x ∈ M_R.vertices.dropLast :=
                  List.mem_of_mem_tail hxM
                exact Finset.mem_union_left _ (hM_R_drop_S x hxM_in_drop)
              · have hLg_vs_eq : L_g.vertices = vL_p :: L_g.vertices.tail :=
                  Walk.vertices_eq_head_cons_tail L_g
                rw [hLg_vs_eq] at hxL
                rcases List.mem_cons.mp hxL with hx_eq_vL | hxL_tail
                · by_cases h_L_p_pos : L_p.length ≥ 1
                  · rw [hx_eq_vL]
                    exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                  · have h_L_p_zero : L_p.length = 0 := by omega
                    have hvL_eq_a : vL_p = a := by
                      by_contra h_ne
                      have := Walk.length_pos_of_ne L_p h_ne
                      omega
                    have hx_a : x = a := hx_eq_vL.trans hvL_eq_a
                    rw [hx_a] at hx
                    have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                      (M_R.comp L_g) hLc_dir (M_L.comp R_g) hRc_dir hMLR_sym
                      hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                    have h_head_notin_tail := hbif_bif.2.1
                    have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                    exact absurd hx_bif_tail h_head_notin_tail
                · by_cases h_L_g_pos : L_g.length ≥ 1
                  · have h_Lg_t_ne : L_g.vertices.tail ≠ [] :=
                      Walk.tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                    have h_Lg_t_last :=
                      Walk.tail_getLast_of_pos L_g h_L_g_pos
                    have h_Lg_decomp :
                        L_g.vertices.tail = L_g.vertices.tail.dropLast ++ [a] := by
                      have := List.dropLast_append_getLast h_Lg_t_ne
                      rw [h_Lg_t_last] at this
                      exact this.symm
                    rw [h_Lg_decomp] at hxL_tail
                    rcases List.mem_append.mp hxL_tail with hxL_int | hxL_a
                    · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                      · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                      · exact Finset.mem_union_left _ hx_S
                    · rw [List.mem_singleton] at hxL_a
                      rw [hxL_a] at hx
                      have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                        (M_R.comp L_g) hLc_dir (M_L.comp R_g) hRc_dir hMLR_sym
                        hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                      have h_head_notin_tail := hbif_bif.2.1
                      have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                      exact absurd hx_bif_tail h_head_notin_tail
                  · have h_L_g_zero : L_g.length = 0 := by omega
                    match L_g, h_L_g_zero with
                    | .nil _ _, _ => simp [Walk.vertices, List.tail] at hxL_tail
            · have h_M_R_zero : M_R.length = 0 := by omega
              have hM_R_drop_empty : M_R.vertices.dropLast = [] := by
                match M_R, h_M_R_zero with
                | .nil _ _, _ => simp [Walk.vertices, List.dropLast]
              rw [h_Lc_vs, hM_R_drop_empty, List.nil_append] at hx_Lc_rev
              by_cases h_L_g_pos : L_g.length ≥ 1
              · have h_Lg_t_ne : L_g.vertices.tail ≠ [] :=
                  Walk.tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                have h_Lg_t_last :=
                  Walk.tail_getLast_of_pos L_g h_L_g_pos
                have h_Lg_decomp :
                    L_g.vertices.tail = L_g.vertices.tail.dropLast ++ [a] := by
                  have := List.dropLast_append_getLast h_Lg_t_ne
                  rw [h_Lg_t_last] at this
                  exact this.symm
                rw [h_Lg_decomp] at hx_Lc_rev
                rcases List.mem_append.mp hx_Lc_rev with hxL_int | hxL_a
                · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                  · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                  · exact Finset.mem_union_left _ hx_S
                · rw [List.mem_singleton] at hxL_a
                  rw [hxL_a] at hx
                  have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                    (M_R.comp L_g) hLc_dir (M_L.comp R_g) hRc_dir hMLR_sym
                    hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                  have h_head_notin_tail := hbif_bif.2.1
                  have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                  exact absurd hx_bif_tail h_head_notin_tail
              · have h_L_g_zero : L_g.length = 0 := by omega
                match L_g, h_L_g_zero with
                | .nil _ _, _ => simp [Walk.vertices, List.tail] at hx_Lc_rev
          · -- x ∈ vMR :: Rc.vertices.
            rcases List.mem_cons.mp hx_Rc with hx_eq_vMR | hx_Rc_vs
            · -- x = vMR.
              by_cases h_M_R_pos : M_R.length ≥ 1
              · have h_M_R_t_ne : M_R.vertices.tail ≠ [] :=
                  Walk.tail_vertices_ne_nil_of_pos M_R h_M_R_pos
                have hvMR_in_M_R_drop : vMR ∈ M_R.vertices.dropLast := by
                  rw [Walk.vertices_eq_head_cons_tail M_R,
                      List.dropLast_cons_of_ne_nil h_M_R_t_ne]
                  exact List.mem_cons_self
                rw [hx_eq_vMR]
                exact Finset.mem_union_left _ (hM_R_drop_S vMR hvMR_in_M_R_drop)
              · -- M_R.length = 0 → vMR = vL_p.
                have h_M_R_zero : M_R.length = 0 := by omega
                have hvMR_eq_vL : vMR = vL_p := by
                  by_contra h_ne
                  have := Walk.length_pos_of_ne M_R h_ne
                  omega
                by_cases h_L_p_pos : L_p.length ≥ 1
                · rw [hx_eq_vMR, hvMR_eq_vL]
                  exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                · have h_L_p_zero : L_p.length = 0 := by omega
                  have hvL_eq_a : vL_p = a := by
                    by_contra h_ne
                    have := Walk.length_pos_of_ne L_p h_ne
                    omega
                  have hx_a : x = a := hx_eq_vMR.trans (hvMR_eq_vL.trans hvL_eq_a)
                  rw [hx_a] at hx
                  have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                    (M_R.comp L_g) hLc_dir (M_L.comp R_g) hRc_dir hMLR_sym
                    hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                  have h_head_notin_tail := hbif_bif.2.1
                  have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                  exact absurd hx_bif_tail h_head_notin_tail
            · rw [h_Rc_vs] at hx_Rc_vs
              rcases List.mem_append.mp hx_Rc_vs with hxM | hxR
              · exact Finset.mem_union_left _ (hM_L_drop_S x hxM)
              · have hRg_vs_eq : R_g.vertices = vR_p :: R_g.vertices.tail :=
                  Walk.vertices_eq_head_cons_tail R_g
                rw [hRg_vs_eq] at hxR
                rcases List.mem_cons.mp hxR with hx_eq_vR | hxR_tail
                · by_cases h_R_p_pos : R_p.length ≥ 1
                  · rw [hx_eq_vR]
                    exact Finset.mem_union_right _ (hvR_T_if_R_p_pos h_R_p_pos)
                  · have h_R_p_zero : R_p.length = 0 := by omega
                    have hvR_eq_b : vR_p = b := by
                      by_contra h_ne
                      have := Walk.length_pos_of_ne R_p h_ne
                      omega
                    have hx_b : x = b := hx_eq_vR.trans hvR_eq_b
                    rw [hx_b] at hx
                    have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                      (M_R.comp L_g) hLc_dir (M_L.comp R_g) hRc_dir hMLR_sym
                      hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                    have h_last_notin_drop := hbif_bif.2.2.1
                    have h_bif_t_ne :
                        (Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir
                            (M_L.comp R_g) hMLR_sym).vertices.tail ≠ [] := by
                      have h_bif_pos := Walk.length_pos_of_isBifurcation hbif_bif
                      exact Walk.tail_vertices_ne_nil_of_pos _ h_bif_pos
                    have h_bif_drop_eq :
                        (Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir
                            (M_L.comp R_g) hMLR_sym).vertices.dropLast
                        = a :: (Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir
                                    (M_L.comp R_g) hMLR_sym).vertices.tail.dropLast := by
                      conv_lhs => rw [Walk.vertices_eq_head_cons_tail _]
                      exact List.dropLast_cons_of_ne_nil h_bif_t_ne
                    have hx_bif_drop : b ∈
                        (Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir
                            (M_L.comp R_g) hMLR_sym).vertices.dropLast := by
                      rw [h_bif_drop_eq]; exact List.mem_cons_of_mem _ hx
                    exact absurd hx_bif_drop h_last_notin_drop
                · by_cases h_R_g_pos : R_g.length ≥ 1
                  · have h_Rg_t_ne : R_g.vertices.tail ≠ [] :=
                      Walk.tail_vertices_ne_nil_of_pos R_g h_R_g_pos
                    have h_Rg_t_last :=
                      Walk.tail_getLast_of_pos R_g h_R_g_pos
                    have h_Rg_decomp :
                        R_g.vertices.tail = R_g.vertices.tail.dropLast ++ [b] := by
                      have := List.dropLast_append_getLast h_Rg_t_ne
                      rw [h_Rg_t_last] at this
                      exact this.symm
                    rw [h_Rg_decomp] at hxR_tail
                    rcases List.mem_append.mp hxR_tail with hxR_int | hxR_b
                    · rcases hR_g_tdL_sub_S x hxR_int with hx_R_p | hx_S
                      · exact Finset.mem_union_right _ (hR_p_inter_T x hx_R_p)
                      · exact Finset.mem_union_left _ hx_S
                    · rw [List.mem_singleton] at hxR_b
                      rw [hxR_b] at hx
                      have hbif_bif := Walk.mkBifurcationBidir_isBifurcation
                        (M_R.comp L_g) hLc_dir (M_L.comp R_g) hRc_dir hMLR_sym
                        hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                      have h_last_notin_drop := hbif_bif.2.2.1
                      have h_bif_t_ne :
                          (Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir
                              (M_L.comp R_g) hMLR_sym).vertices.tail ≠ [] := by
                        have h_bif_pos := Walk.length_pos_of_isBifurcation hbif_bif
                        exact Walk.tail_vertices_ne_nil_of_pos _ h_bif_pos
                      have h_bif_drop_eq :
                          (Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir
                              (M_L.comp R_g) hMLR_sym).vertices.dropLast
                          = a :: (Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir
                                      (M_L.comp R_g) hMLR_sym).vertices.tail.dropLast := by
                        conv_lhs => rw [Walk.vertices_eq_head_cons_tail _]
                        exact List.dropLast_cons_of_ne_nil h_bif_t_ne
                      have hx_bif_drop : b ∈
                          (Walk.mkBifurcationBidir (M_R.comp L_g) hLc_dir
                              (M_L.comp R_g) hMLR_sym).vertices.dropLast := by
                        rw [h_bif_drop_eq]; exact List.mem_cons_of_mem _ hx
                      exact absurd hx_bif_drop h_last_notin_drop
                  · have h_R_g_zero : R_g.length = 0 := by omega
                    match R_g, h_R_g_zero with
                    | .nil _ _, _ => simp [Walk.vertices, List.tail] at hxR_tail

-- ## Helper: backward direction (G-bif → marg-bif) for the
-- bidirected-hinge case, single orientation.
--
-- Mirrors the structure of `forward_marg_to_g_bif_one_orientation`'s
-- bidirected branch but in the opposite direction.  Input: a G-bifurcation
-- `p` between `a, b ∉ S ∪ T` with interior ⊆ S ∪ T, plus a split index
-- `i` whose hinge step is *not* directed (so it's bidirected).  Output:
-- a marg-bifurcation between `a, b` with interior ⊆ T.
--
-- Algorithm (mirrors the LN tex proof):
-- 1. Extract the bidirected hinge `(vL_h, vR_h) ∈ G.L` and the two
--    directed arms `L_p : Walk G vL_h a`, `R_p : Walk G vR_h b` via
--    `exists_arms_of_bifurcation_bidir_hinge_strong`.
-- 2. Apply `find_first_non_W_directed_inclusive S` to each arm to find
--    β := first non-`S` vertex on `L_p` (starting at `vL_h` inclusive),
--    γ := first non-`S` vertex on `R_p` (starting at `vR_h` inclusive).
-- 3. Case-split on β = γ:
--    - β = γ: both `L_tail : Walk G β a`, `R_tail : Walk G β b` have
--      length ≥ 1 (since β ∈ p.vertices.tail ∧ p.vertices.dropLast,
--      hence β ≠ a ∧ β ≠ b).  Project both via `project_walk_marg_full`
--      and assemble with `mkBifurcation` (source β).
--    - β ≠ γ: build `(β, γ) ∈ marg.L` via `Φ_L S β γ` (witness =
--      G-bif `mkBifurcationBidir L_head ... R_head ...` between β and γ
--      with interior ⊆ S).  Project tail walks (handling potentially
--      nil tails); assemble with `mkBifurcationBidir`.
private lemma backward_marg_to_g_bif_bidir_hinge_one_orientation
    {G : CDMG Node} (S T : Finset Node)
    (hS : S ⊆ G.V) {a b : Node}
    (ha_VST : a ∈ G.V \ (S ∪ T)) (hb_VST : b ∈ G.V \ (S ∪ T))
    (ha_marg : a ∈ G.marginalize S hS) (hb_marg : b ∈ G.marginalize S hS)
    (p : Walk G a b)
    (hp_bif : p.IsBifurcation)
    (hp_inter : ∀ x ∈ p.vertices.tail.dropLast, x ∈ S ∪ T)
    (i : ℕ) (hp_split : p.IsBifurcationWithSplit i)
    (h_not_dir : ¬ p.IsBifurcationDirectedHingeWithSplit i) :
    ∃ q : Walk (G.marginalize S hS) a b, q.IsBifurcation ∧
      ∀ x ∈ q.vertices.tail.dropLast, x ∈ T := by
  have ha_notSuT : a ∉ S ∪ T := (Finset.mem_sdiff.mp ha_VST).2
  have hb_notSuT : b ∉ S ∪ T := (Finset.mem_sdiff.mp hb_VST).2
  have ha_notS : a ∉ S := fun h => ha_notSuT (Finset.mem_union_left _ h)
  have hb_notS : b ∉ S := fun h => hb_notSuT (Finset.mem_union_left _ h)
  have hp_pos : p.length ≥ 1 := Walk.length_pos_of_isBifurcation hp_bif
  obtain ⟨hab_ne, ha_p_tail, hb_p_drop, _⟩ := hp_bif
  have hp_inter_ST : ∀ x ∈ p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T :=
    fun x hx => Finset.mem_union.mp (hp_inter x hx)
  -- Extract bidirected hinge arms.
  obtain ⟨vL_h, vR_h, L_p, R_p, hL_p_dir, hR_p_dir, hLR_G, _hidx,
          hL_p_sub, hR_p_sub, hL_p_drop_sub, hR_p_drop_sub⟩ :=
    Walk.exists_arms_of_bifurcation_bidir_hinge_strong p i hp_split h_not_dir
  have hvL_h_V : vL_h ∈ G.V := (G.hL_subset hLR_G).1
  have hvR_h_V : vR_h ∈ G.V := (G.hL_subset hLR_G).2
  have hvL_h_g : vL_h ∈ G := Finset.mem_union_right _ hvL_h_V
  have hvR_h_g : vR_h ∈ G := Finset.mem_union_right _ hvR_h_V
  have hvLR_h_ne : vL_h ≠ vR_h := fun heq =>
    G.hL_irrefl hLR_G heq
  -- L_p, R_p vertex bounds.
  have ha_notin_L_p_drop : a ∉ L_p.vertices.dropLast := fun h_in =>
    ha_p_tail (hL_p_drop_sub a h_in)
  have ha_notin_R_p : a ∉ R_p.vertices := fun h_in =>
    ha_p_tail (hR_p_sub a h_in)
  have hb_notin_L_p : b ∉ L_p.vertices := fun h_in =>
    hb_p_drop (hL_p_sub b h_in)
  have hb_notin_R_p_drop : b ∉ R_p.vertices.dropLast := fun h_in =>
    hb_p_drop (hR_p_drop_sub b h_in)
  -- L_p, R_p interior ⊆ S ∨ T.
  have hL_p_inter_ST : ∀ x ∈ L_p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
    intro x hx
    by_cases h_L_p_pos : L_p.length ≥ 1
    · have h_t_ne : L_p.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L_p h_L_p_pos
      have h_drop_eq :
          L_p.vertices.dropLast = vL_h :: L_p.vertices.tail.dropLast := by
        conv_lhs => rw [Walk.vertices_eq_head_cons_tail L_p]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have hx_L_p_drop : x ∈ L_p.vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have hx_p_tail : x ∈ p.vertices.tail := hL_p_drop_sub _ hx_L_p_drop
      have hx_L_p : x ∈ L_p.vertices := List.mem_of_mem_dropLast hx_L_p_drop
      have hx_p_drop : x ∈ p.vertices.dropLast := hL_p_sub _ hx_L_p
      have hx_p_inter : x ∈ p.vertices.tail.dropLast :=
        mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
      exact hp_inter_ST _ hx_p_inter
    · have h_zero : L_p.length = 0 := by omega
      match L_p, h_zero with
      | .nil _ _, _ => simp [Walk.vertices, List.tail] at hx
  have hR_p_inter_ST : ∀ x ∈ R_p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
    intro x hx
    by_cases h_R_p_pos : R_p.length ≥ 1
    · have h_t_ne : R_p.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R_p h_R_p_pos
      have h_drop_eq :
          R_p.vertices.dropLast = vR_h :: R_p.vertices.tail.dropLast := by
        conv_lhs => rw [Walk.vertices_eq_head_cons_tail R_p]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have hx_R_p_drop : x ∈ R_p.vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have hx_p_drop : x ∈ p.vertices.dropLast := hR_p_drop_sub _ hx_R_p_drop
      have hx_R_p : x ∈ R_p.vertices := List.mem_of_mem_dropLast hx_R_p_drop
      have hx_p_tail : x ∈ p.vertices.tail := hR_p_sub _ hx_R_p
      have hx_p_inter : x ∈ p.vertices.tail.dropLast :=
        mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
      exact hp_inter_ST _ hx_p_inter
    · have h_zero : R_p.length = 0 := by omega
      match R_p, h_zero with
      | .nil _ _, _ => simp [Walk.vertices, List.tail] at hx
  -- Apply inclusive find_first_non_W on each arm.
  obtain ⟨β, L_head, L_tail, hL_head_dir, hL_tail_dir, hβ_notS,
          hL_head_dL_S, _hL_lens, hL_p_vs_eq⟩ :=
    find_first_non_W_directed_inclusive S L_p hL_p_dir ha_notS
  obtain ⟨γ, R_head, R_tail, hR_head_dir, hR_tail_dir, hγ_notS,
          hR_head_dL_S, _hR_lens, hR_p_vs_eq⟩ :=
    find_first_non_W_directed_inclusive S R_p hR_p_dir hb_notS
  -- β, γ ∈ G.V (target of L_head / R_head, or vL_h / vR_h if head is nil).
  have hβ_V : β ∈ G.V := by
    by_cases h_pos : L_head.length ≥ 1
    · exact Walk.target_in_GV_of_directedWalk_pos L_head hL_head_dir h_pos
    · have h_zero : L_head.length = 0 := by omega
      have h_vL_eq_β : vL_h = β := by
        match L_head, h_zero with
        | .nil _ _, _ => rfl
      rw [← h_vL_eq_β]; exact hvL_h_V
  have hγ_V : γ ∈ G.V := by
    by_cases h_pos : R_head.length ≥ 1
    · exact Walk.target_in_GV_of_directedWalk_pos R_head hR_head_dir h_pos
    · have h_zero : R_head.length = 0 := by omega
      have h_vR_eq_γ : vR_h = γ := by
        match R_head, h_zero with
        | .nil _ _, _ => rfl
      rw [← h_vR_eq_γ]; exact hvR_h_V
  -- β, γ ∈ G.V \ S → β, γ ∈ G.marginalize S hS.
  have hβ_VS : β ∈ G.V \ S := Finset.mem_sdiff.mpr ⟨hβ_V, hβ_notS⟩
  have hγ_VS : γ ∈ G.V \ S := Finset.mem_sdiff.mpr ⟨hγ_V, hγ_notS⟩
  have hβ_marg : β ∈ G.marginalize S hS := by
    change β ∈ G.J ∪ (G.V \ S); exact Finset.mem_union_right _ hβ_VS
  have hγ_marg : γ ∈ G.marginalize S hS := by
    change γ ∈ G.J ∪ (G.V \ S); exact Finset.mem_union_right _ hγ_VS
  -- Vertex memberships of L_head, R_head, L_tail, R_tail back into L_p / R_p / p.
  -- These follow from `hL_p_vs_eq : L_p.vertices = L_head.vertices.dropLast ++ L_tail.vertices`.
  have hL_head_dL_sub_L_p : ∀ x ∈ L_head.vertices.dropLast, x ∈ L_p.vertices := by
    intro x hx; rw [hL_p_vs_eq]; exact List.mem_append.mpr (Or.inl hx)
  have hL_tail_sub_L_p : ∀ x ∈ L_tail.vertices, x ∈ L_p.vertices := by
    intro x hx; rw [hL_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
  have hR_head_dL_sub_R_p : ∀ x ∈ R_head.vertices.dropLast, x ∈ R_p.vertices := by
    intro x hx; rw [hR_p_vs_eq]; exact List.mem_append.mpr (Or.inl hx)
  have hR_tail_sub_R_p : ∀ x ∈ R_tail.vertices, x ∈ R_p.vertices := by
    intro x hx; rw [hR_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
  -- DropLast bounds for L_tail, R_tail (via L_p / R_p).
  have hL_tail_ne : L_tail.vertices ≠ [] := Walk.vertices_ne_nil L_tail
  have hR_tail_ne : R_tail.vertices ≠ [] := Walk.vertices_ne_nil R_tail
  have hL_tail_dL_sub_L_p_dL :
      ∀ x ∈ L_tail.vertices.dropLast, x ∈ L_p.vertices.dropLast := by
    intro x hx
    rw [hL_p_vs_eq, List.dropLast_append_of_ne_nil hL_tail_ne]
    exact List.mem_append.mpr (Or.inr hx)
  have hR_tail_dL_sub_R_p_dL :
      ∀ x ∈ R_tail.vertices.dropLast, x ∈ R_p.vertices.dropLast := by
    intro x hx
    rw [hR_p_vs_eq, List.dropLast_append_of_ne_nil hR_tail_ne]
    exact List.mem_append.mpr (Or.inr hx)
  -- L_tail's interior ⊆ S ∪ T.
  have hL_tail_inter_ST : ∀ x ∈ L_tail.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
    intro x hx
    have h_t : x ∈ L_tail.vertices.tail := List.mem_of_mem_dropLast hx
    have h_v : x ∈ L_tail.vertices := List.mem_of_mem_tail h_t
    have h_L_p : x ∈ L_p.vertices := hL_tail_sub_L_p _ h_v
    have h_x_p_drop : x ∈ p.vertices.dropLast := hL_p_sub _ h_L_p
    by_cases h_pos : L_tail.length ≥ 1
    · have h_t_ne : L_tail.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L_tail h_pos
      have h_drop_eq :
          L_tail.vertices.dropLast = β :: L_tail.vertices.tail.dropLast := by
        conv_lhs => rw [Walk.vertices_eq_head_cons_tail L_tail]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have h_drop : x ∈ L_tail.vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have h_L_p_drop : x ∈ L_p.vertices.dropLast := hL_tail_dL_sub_L_p_dL _ h_drop
      have h_x_p_tail : x ∈ p.vertices.tail := hL_p_drop_sub _ h_L_p_drop
      have h_x_p_inter : x ∈ p.vertices.tail.dropLast :=
        mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
      exact hp_inter_ST _ h_x_p_inter
    · have h_zero : L_tail.length = 0 := by omega
      match L_tail, h_zero with
      | .nil _ _, _ => simp [Walk.vertices, List.tail] at hx
  have hR_tail_inter_ST : ∀ x ∈ R_tail.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
    intro x hx
    have h_t : x ∈ R_tail.vertices.tail := List.mem_of_mem_dropLast hx
    have h_v : x ∈ R_tail.vertices := List.mem_of_mem_tail h_t
    have h_R_p : x ∈ R_p.vertices := hR_tail_sub_R_p _ h_v
    have h_x_p_tail : x ∈ p.vertices.tail := hR_p_sub _ h_R_p
    by_cases h_pos : R_tail.length ≥ 1
    · have h_t_ne : R_tail.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R_tail h_pos
      have h_drop_eq :
          R_tail.vertices.dropLast = γ :: R_tail.vertices.tail.dropLast := by
        conv_lhs => rw [Walk.vertices_eq_head_cons_tail R_tail]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have h_drop : x ∈ R_tail.vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have h_R_p_drop : x ∈ R_p.vertices.dropLast := hR_tail_dL_sub_R_p_dL _ h_drop
      have h_x_p_drop : x ∈ p.vertices.dropLast := hR_p_drop_sub _ h_R_p_drop
      have h_x_p_inter : x ∈ p.vertices.tail.dropLast :=
        mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
      exact hp_inter_ST _ h_x_p_inter
    · have h_zero : R_tail.length = 0 := by omega
      match R_tail, h_zero with
      | .nil _ _, _ => simp [Walk.vertices, List.tail] at hx
  -- Vertex bounds: a, b vs L_tail, R_tail.
  have ha_notin_L_tail_dL : a ∉ L_tail.vertices.dropLast := fun h_in =>
    ha_notin_L_p_drop (hL_tail_dL_sub_L_p_dL a h_in)
  have ha_notin_R_tail : a ∉ R_tail.vertices := fun h_in =>
    ha_notin_R_p (hR_tail_sub_R_p a h_in)
  have hb_notin_L_tail : b ∉ L_tail.vertices := fun h_in =>
    hb_notin_L_p (hL_tail_sub_L_p b h_in)
  have hb_notin_R_tail_dL : b ∉ R_tail.vertices.dropLast := fun h_in =>
    hb_notin_R_p_drop (hR_tail_dL_sub_R_p_dL b h_in)
  -- Case-split on β = γ.
  by_cases hβγ_eq : β = γ
  · -- β = γ.  Build mkBifurcation with source β.
    subst hβγ_eq
    -- β ≠ a (since β ∈ R_tail.vertices ⊆ R_p.vertices ⊆ p.vertices.tail, ha_p_tail).
    have hβ_ne_a : β ≠ a := by
      intro heq
      have h_in_R_tail : β ∈ R_tail.vertices := Walk.head_mem_vertices R_tail
      have h_in_R_p : β ∈ R_p.vertices := hR_tail_sub_R_p _ h_in_R_tail
      have h_p_tail : β ∈ p.vertices.tail := hR_p_sub _ h_in_R_p
      exact ha_p_tail (heq ▸ h_p_tail)
    have hβ_ne_b : β ≠ b := by
      intro heq
      have h_in_L_tail : β ∈ L_tail.vertices := Walk.head_mem_vertices L_tail
      have h_in_L_p : β ∈ L_p.vertices := hL_tail_sub_L_p _ h_in_L_tail
      have h_p_drop : β ∈ p.vertices.dropLast := hL_p_sub _ h_in_L_p
      exact hb_p_drop (heq ▸ h_p_drop)
    have hL_tail_pos : L_tail.length ≥ 1 := Walk.length_pos_of_ne L_tail hβ_ne_a
    have hR_tail_pos : R_tail.length ≥ 1 := Walk.length_pos_of_ne R_tail hβ_ne_b
    -- Project L_tail, R_tail to marg.
    obtain ⟨L_marg, hL_marg_dir, hL_marg_pos, hL_marg_vs_sub, hL_marg_dL_sub,
            _, hL_marg_inter_T⟩ :=
      project_walk_marg_full (S := S) (T := T) (hS := hS)
        L_tail hL_tail_dir hL_tail_pos hβ_marg ha_marg hL_tail_inter_ST
    obtain ⟨R_marg, hR_marg_dir, hR_marg_pos, hR_marg_vs_sub, hR_marg_dL_sub,
            _, hR_marg_inter_T⟩ :=
      project_walk_marg_full (S := S) (T := T) (hS := hS)
        R_tail hR_tail_dir hR_tail_pos hβ_marg hb_marg hR_tail_inter_ST
    -- Vertex bounds in marg.
    have ha_notin_L_marg_dL : a ∉ L_marg.vertices.dropLast := fun h_in =>
      ha_notin_L_tail_dL (hL_marg_dL_sub a h_in)
    have ha_notin_R_marg : a ∉ R_marg.vertices := fun h_in =>
      ha_notin_R_tail (hR_marg_vs_sub a h_in)
    have hb_notin_L_marg : b ∉ L_marg.vertices := fun h_in =>
      hb_notin_L_tail (hL_marg_vs_sub b h_in)
    have hb_notin_R_marg_dL : b ∉ R_marg.vertices.dropLast := fun h_in =>
      hb_notin_R_tail_dL (hR_marg_dL_sub b h_in)
    -- Build the bifurcation.
    refine ⟨Walk.mkBifurcation L_marg hL_marg_dir hL_marg_pos R_marg, ?_, ?_⟩
    · have h_src := Walk.mkBifurcation_isBifurcationSource
        L_marg hL_marg_dir hL_marg_pos R_marg hR_marg_dir hR_marg_pos
        hab_ne ha_notin_L_marg_dL ha_notin_R_marg hb_notin_L_marg hb_notin_R_marg_dL
      exact Walk.isBifurcationSource_to_isBifurcation _ β h_src
    · intro x hx
      rw [vertices_tail_dropLast_mkBifurcation
            L_marg hL_marg_dir hL_marg_pos R_marg hR_marg_pos] at hx
      rcases List.mem_append.mp hx with hx_L | hx_R
      · rw [List.mem_reverse] at hx_L
        exact hL_marg_inter_T x hx_L
      · -- x ∈ R_marg.vertices.dropLast.  R_marg starts at β (the source).
        have h_R_t_ne : R_marg.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos R_marg hR_marg_pos
        rw [Walk.vertices_eq_head_cons_tail R_marg,
            List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R
        rcases List.mem_cons.mp hx_R with rfl | hx_inner
        · -- x = β.  β is on both L_p (target of L_tail's source) and R_p (similar).
          -- We argue β ∈ p.vertices.tail.dropLast via mem_interior_of_arm_source.
          have h_x_in_L_p : x ∈ L_p.vertices :=
            hL_tail_sub_L_p _ (Walk.head_mem_vertices L_tail)
          have h_x_in_p_drop : x ∈ p.vertices.dropLast :=
            hL_p_sub _ h_x_in_L_p
          have h_x_in_R_p : x ∈ R_p.vertices :=
            hR_tail_sub_R_p _ (Walk.head_mem_vertices R_tail)
          have h_x_in_p_tail : x ∈ p.vertices.tail :=
            hR_p_sub _ h_x_in_R_p
          have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
            mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
          rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
          · exact absurd h_S hβ_notS
          · exact h_T
        · exact hR_marg_inter_T x hx_inner
  · -- β ≠ γ.  Build L-edge (β, γ) ∈ marg.L via Φ_L S.
    -- First, construct the G-bif witness using mkBifurcationBidir.
    -- G-bif : Walk G β γ with bidirected hinge at (vL_h, vR_h).
    -- Vertex bounds (since β ∉ S, γ ∉ S, and L_head/R_head interiors ⊆ S):
    have hβ_notin_L_head_dL : β ∉ L_head.vertices.dropLast := fun h_in =>
      hβ_notS (hL_head_dL_S β h_in)
    have hγ_notin_R_head_dL : γ ∉ R_head.vertices.dropLast := fun h_in =>
      hγ_notS (hR_head_dL_S γ h_in)
    -- R_head.vertices = R_head.vertices.dropLast ++ [γ] (via getLast).
    have hR_head_decomp : R_head.vertices = R_head.vertices.dropLast ++ [γ] := by
      have h_ne : R_head.vertices ≠ [] := Walk.vertices_ne_nil R_head
      have h_last : R_head.vertices.getLast h_ne = γ := Walk.vertices_getLast R_head
      have := List.dropLast_append_getLast h_ne
      rw [h_last] at this
      exact this.symm
    have hL_head_decomp : L_head.vertices = L_head.vertices.dropLast ++ [β] := by
      have h_ne : L_head.vertices ≠ [] := Walk.vertices_ne_nil L_head
      have h_last : L_head.vertices.getLast h_ne = β := Walk.vertices_getLast L_head
      have := List.dropLast_append_getLast h_ne
      rw [h_last] at this
      exact this.symm
    have hβ_notin_R_head : β ∉ R_head.vertices := by
      intro h_in
      rw [hR_head_decomp] at h_in
      rcases List.mem_append.mp h_in with h_dL | h_last
      · exact hβ_notS (hR_head_dL_S β h_dL)
      · rw [List.mem_singleton] at h_last; exact hβγ_eq h_last
    have hγ_notin_L_head : γ ∉ L_head.vertices := by
      intro h_in
      rw [hL_head_decomp] at h_in
      rcases List.mem_append.mp h_in with h_dL | h_last
      · exact hγ_notS (hL_head_dL_S γ h_dL)
      · rw [List.mem_singleton] at h_last; exact hβγ_eq h_last.symm
    -- G-bif IsBifurcation.
    have h_G_bif_is_bif : (Walk.mkBifurcationBidir L_head hL_head_dir
                            R_head hLR_G).IsBifurcation :=
      Walk.mkBifurcationBidir_isBifurcation
        L_head hL_head_dir R_head hR_head_dir hLR_G
        hβγ_eq hβ_notin_L_head_dL hβ_notin_R_head hγ_notin_L_head hγ_notin_R_head_dL
    -- G-bif's interior ⊆ S.
    have h_G_bif_inter_S :
        ∀ x ∈ (Walk.mkBifurcationBidir L_head hL_head_dir
                R_head hLR_G).vertices.tail.dropLast, x ∈ S := by
      intro x hx
      have h_bif_vs := Walk.vertices_mkBifurcationBidir L_head hL_head_dir
                         R_head hLR_G
      -- The bif walk's vertices = L_head.vertices.reverse.dropLast ++ (vL_h :: R_head.vertices).
      -- We split based on L_head.length.
      by_cases hL_head_pos : L_head.length ≥ 1
      · -- Use vertices_tail_dropLast_mkBifurcationBidir_Lpos.
        rw [vertices_tail_dropLast_mkBifurcationBidir_Lpos
              L_head hL_head_dir R_head hLR_G hL_head_pos] at hx
        rcases List.mem_append.mp hx with hx_L | hx_R
        · -- x ∈ L_head.vertices.tail.dropLast.reverse → x ∈ L_head.tail.dropLast.
          rw [List.mem_reverse] at hx_L
          have h_x_in_L_head_dL : x ∈ L_head.vertices.dropLast := by
            -- tail.dropLast ⊆ dropLast (via tail).
            have h_t : x ∈ L_head.vertices.tail :=
              List.mem_of_mem_dropLast hx_L
            -- dropLast = vL_h :: tail.dropLast when tail.length pos.
            have h_t_ne : L_head.vertices.tail ≠ [] :=
              Walk.tail_vertices_ne_nil_of_pos L_head hL_head_pos
            have h_drop_eq :
                L_head.vertices.dropLast = vL_h :: L_head.vertices.tail.dropLast := by
              conv_lhs => rw [Walk.vertices_eq_head_cons_tail L_head]
              exact List.dropLast_cons_of_ne_nil h_t_ne
            rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx_L
          exact hL_head_dL_S x h_x_in_L_head_dL
        · -- x ∈ (vL_h :: R_head.vertices).dropLast.
          -- = vL_h :: R_head.vertices.dropLast when R_head.vertices ≠ [].
          have h_R_head_ne : R_head.vertices ≠ [] :=
            Walk.vertices_ne_nil R_head
          rw [List.dropLast_cons_of_ne_nil h_R_head_ne] at hx_R
          rcases List.mem_cons.mp hx_R with rfl | hx_R_dL
          · -- After rcases rfl, vL_h is substituted to x.  Use x.
            -- L_head.length ≥ 1 ∧ L_head.vertices.dropLast ⊆ S ∧ x ∈ L_head.dropLast → x ∈ S.
            have h_t_ne : L_head.vertices.tail ≠ [] :=
              Walk.tail_vertices_ne_nil_of_pos L_head hL_head_pos
            have hx_in_dL : x ∈ L_head.vertices.dropLast := by
              rw [Walk.vertices_eq_head_cons_tail L_head,
                  List.dropLast_cons_of_ne_nil h_t_ne]
              exact List.mem_cons_self
            exact hL_head_dL_S _ hx_in_dL
          · exact hR_head_dL_S x hx_R_dL
      · -- L_head.length = 0 → vL_h = β → L_head = nil.
        have h_zero : L_head.length = 0 := by omega
        have hvL_eq_β : vL_h = β := by
          match L_head, h_zero with
          | .nil _ _, _ => rfl
        have h_L_head_vs : L_head.vertices = [vL_h] := by
          match L_head, h_zero with
          | .nil _ _, _ => simp [Walk.vertices]
        -- bif.vertices = L_head.vertices.reverse.dropLast ++ (vL_h :: R_head.vertices)
        --              = [vL_h].reverse.dropLast ++ (vL_h :: R_head.vertices)
        --              = [] ++ (vL_h :: R_head.vertices)
        --              = vL_h :: R_head.vertices
        rw [h_bif_vs, h_L_head_vs] at hx
        change x ∈ ((vL_h :: R_head.vertices) : List Node).tail.dropLast at hx
        change x ∈ R_head.vertices.dropLast at hx
        exact hR_head_dL_S x hx
    -- L-edge: (β, γ) ∈ marg.L via Φ_L S.
    have hβ_ne_γ : β ≠ γ := hβγ_eq
    have hβγ_in_margL : (β, γ) ∈ (G.marginalize S hS).L := by
      change (β, γ) ∈ ((G.V \ S) ×ˢ (G.V \ S)).filter
                       (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL S e.1 e.2)
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hβ_VS, hγ_VS⟩,
                                     hβ_ne_γ, ?_⟩
      -- Φ_L S β γ via the G-bif we just constructed.
      exact Or.inl ⟨Walk.mkBifurcationBidir L_head hL_head_dir R_head hLR_G,
                    h_G_bif_is_bif, h_G_bif_inter_S⟩
    -- Construct marg arms via inline case-splits on L_tail.length and
    -- R_tail.length to avoid type-cast issues with nil walks (β = a or
    -- γ = b would require casting `Walk marg β β` to `Walk marg β a`,
    -- which trips up Lean's defeq for `IsDirectedWalk`).  Instead, use
    -- `subst` at each branch to eliminate β (resp. γ) and provide a
    -- well-typed nil walk directly.
    -- Inline case-splits on L_tail.length and R_tail.length.  Note: in Lean
    -- 4, `subst hβa_eq` (where hβa_eq : β = a) eliminates `a` (keeping β),
    -- so after the L_tail nil subst we use β where we'd otherwise use a.
    -- Similarly for hγb_eq : γ = b (eliminates b, keeps γ).
    by_cases hL_tail_pos : L_tail.length ≥ 1
    · -- L_tail.length ≥ 1.  Project L_tail to marg.
      obtain ⟨L_marg, hL_marg_dir, hL_marg_pos, hL_marg_vs, hL_marg_dL,
              _, hL_marg_inter⟩ :=
        project_walk_marg_full (S := S) (T := T) (hS := hS)
          L_tail hL_tail_dir hL_tail_pos hβ_marg ha_marg hL_tail_inter_ST
      have ha_notin_L_marg_dL : a ∉ L_marg.vertices.dropLast := fun h_in =>
        ha_notin_L_tail_dL (hL_marg_dL a h_in)
      have hb_notin_L_marg : b ∉ L_marg.vertices := fun h_in =>
        hb_notin_L_tail (hL_marg_vs b h_in)
      by_cases hR_tail_pos : R_tail.length ≥ 1
      · -- L_tail pos, R_tail pos.
        obtain ⟨R_marg, hR_marg_dir, hR_marg_pos, hR_marg_vs, hR_marg_dL,
                _, hR_marg_inter⟩ :=
          project_walk_marg_full (S := S) (T := T) (hS := hS)
            R_tail hR_tail_dir hR_tail_pos hγ_marg hb_marg hR_tail_inter_ST
        have ha_notin_R_marg : a ∉ R_marg.vertices := fun h_in =>
          ha_notin_R_tail (hR_marg_vs a h_in)
        have hb_notin_R_marg_dL : b ∉ R_marg.vertices.dropLast := fun h_in =>
          hb_notin_R_tail_dL (hR_marg_dL b h_in)
        refine ⟨Walk.mkBifurcationBidir L_marg hL_marg_dir R_marg hβγ_in_margL,
                ?_, ?_⟩
        · exact Walk.mkBifurcationBidir_isBifurcation L_marg hL_marg_dir
            R_marg hR_marg_dir hβγ_in_margL hab_ne ha_notin_L_marg_dL ha_notin_R_marg
            hb_notin_L_marg hb_notin_R_marg_dL
        · intro x hx
          rw [vertices_tail_dropLast_mkBifurcationBidir_Lpos
                L_marg hL_marg_dir R_marg hβγ_in_margL hL_marg_pos] at hx
          rcases List.mem_append.mp hx with hx_L | hx_R
          · rw [List.mem_reverse] at hx_L
            exact hL_marg_inter x hx_L
          · have h_R_marg_ne : R_marg.vertices ≠ [] :=
              Walk.vertices_ne_nil R_marg
            rw [List.dropLast_cons_of_ne_nil h_R_marg_ne] at hx_R
            rcases List.mem_cons.mp hx_R with rfl | hx_R_dL
            · -- x = β.
              have h_x_in_L_p : x ∈ L_p.vertices :=
                hL_tail_sub_L_p _ (Walk.head_mem_vertices L_tail)
              have h_x_in_p_drop : x ∈ p.vertices.dropLast :=
                hL_p_sub _ h_x_in_L_p
              have h_L_marg_t_ne : L_marg.vertices.tail ≠ [] :=
                Walk.tail_vertices_ne_nil_of_pos L_marg hL_marg_pos
              have hβ_in_L_marg_dL : x ∈ L_marg.vertices.dropLast := by
                rw [Walk.vertices_eq_head_cons_tail L_marg,
                    List.dropLast_cons_of_ne_nil h_L_marg_t_ne]
                exact List.mem_cons_self
              have hβ_in_L_tail_dL : x ∈ L_tail.vertices.dropLast :=
                hL_marg_dL _ hβ_in_L_marg_dL
              have hβ_in_L_p_dL : x ∈ L_p.vertices.dropLast :=
                hL_tail_dL_sub_L_p_dL _ hβ_in_L_tail_dL
              have h_x_in_p_tail : x ∈ p.vertices.tail :=
                hL_p_drop_sub _ hβ_in_L_p_dL
              have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
                mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
              rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
              · exact absurd h_S hβ_notS
              · exact h_T
            · -- x ∈ R_marg.vertices.dropLast.
              have h_R_t_ne : R_marg.vertices.tail ≠ [] :=
                Walk.tail_vertices_ne_nil_of_pos R_marg hR_marg_pos
              rw [Walk.vertices_eq_head_cons_tail R_marg,
                  List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R_dL
              rcases List.mem_cons.mp hx_R_dL with rfl | hx_R_inner
              · -- x = γ.
                have h_x_in_R_p : x ∈ R_p.vertices :=
                  hR_tail_sub_R_p _ (Walk.head_mem_vertices R_tail)
                have h_x_in_p_tail : x ∈ p.vertices.tail :=
                  hR_p_sub _ h_x_in_R_p
                have hγ_in_R_marg_dL : x ∈ R_marg.vertices.dropLast := by
                  rw [Walk.vertices_eq_head_cons_tail R_marg,
                      List.dropLast_cons_of_ne_nil h_R_t_ne]
                  exact List.mem_cons_self
                have hγ_in_R_tail_dL : x ∈ R_tail.vertices.dropLast :=
                  hR_marg_dL _ hγ_in_R_marg_dL
                have hγ_in_R_p_dL : x ∈ R_p.vertices.dropLast :=
                  hR_tail_dL_sub_R_p_dL _ hγ_in_R_tail_dL
                have h_x_in_p_drop : x ∈ p.vertices.dropLast :=
                  hR_p_drop_sub _ hγ_in_R_p_dL
                have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
                  mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
                rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
                · exact absurd h_S hγ_notS
                · exact h_T
              · exact hR_marg_inter x hx_R_inner
      · -- L_tail pos, R_tail = 0 → γ = b (after subst, b is eliminated).
        have h_R_zero : R_tail.length = 0 := by omega
        have hγb_eq : γ = b := by
          match R_tail, h_R_zero with
          | .nil _ _, _ => rfl
        subst hγb_eq
        -- After subst, b is gone, γ remains.  R_marg = Walk.nil γ hγ_marg.
        refine ⟨Walk.mkBifurcationBidir L_marg hL_marg_dir (Walk.nil γ hγ_marg)
                  hβγ_in_margL, ?_, ?_⟩
        · refine Walk.mkBifurcationBidir_isBifurcation L_marg hL_marg_dir
            (Walk.nil γ hγ_marg) trivial hβγ_in_margL hab_ne ha_notin_L_marg_dL
            ?_ hb_notin_L_marg ?_
          · intro h_in
            change a ∈ ([γ] : List Node) at h_in
            rw [List.mem_singleton] at h_in
            -- After subst hγb_eq, ha_notin_R_tail : a ∉ R_tail.vertices = [γ].
            exact ha_notin_R_tail (by rw [h_in]; exact Walk.head_mem_vertices R_tail)
          · intro h_in
            change γ ∈ ([γ] : List Node).dropLast at h_in
            simp at h_in
        · intro x hx
          rw [vertices_tail_dropLast_mkBifurcationBidir_Lpos
                L_marg hL_marg_dir (Walk.nil γ hγ_marg) hβγ_in_margL
                hL_marg_pos] at hx
          rcases List.mem_append.mp hx with hx_L | hx_R
          · rw [List.mem_reverse] at hx_L
            exact hL_marg_inter x hx_L
          · -- x ∈ (β :: [γ]).dropLast = [β].
            change x ∈ ((β :: [γ]) : List Node).dropLast at hx_R
            change x ∈ ([β, γ] : List Node).dropLast at hx_R
            simp [List.dropLast] at hx_R
            -- hx_R : x = β.  Rewrite goal to β ∈ T.
            rw [hx_R]
            have h_β_in_L_p : β ∈ L_p.vertices :=
              hL_tail_sub_L_p _ (Walk.head_mem_vertices L_tail)
            have h_β_in_p_drop : β ∈ p.vertices.dropLast :=
              hL_p_sub _ h_β_in_L_p
            have h_L_marg_t_ne : L_marg.vertices.tail ≠ [] :=
              Walk.tail_vertices_ne_nil_of_pos L_marg hL_marg_pos
            have hβ_in_L_marg_dL : β ∈ L_marg.vertices.dropLast := by
              rw [Walk.vertices_eq_head_cons_tail L_marg,
                  List.dropLast_cons_of_ne_nil h_L_marg_t_ne]
              exact List.mem_cons_self
            have hβ_in_L_tail_dL : β ∈ L_tail.vertices.dropLast :=
              hL_marg_dL _ hβ_in_L_marg_dL
            have hβ_in_L_p_dL : β ∈ L_p.vertices.dropLast :=
              hL_tail_dL_sub_L_p_dL _ hβ_in_L_tail_dL
            have h_β_in_p_tail : β ∈ p.vertices.tail :=
              hL_p_drop_sub _ hβ_in_L_p_dL
            have h_β_in_p_inter : β ∈ p.vertices.tail.dropLast :=
              mem_interior_of_arm_source ha_p_tail hp_pos h_β_in_p_tail h_β_in_p_drop
            rcases hp_inter_ST β h_β_in_p_inter with h_S | h_T
            · exact absurd h_S hβ_notS
            · exact h_T
    · -- L_tail.length = 0 → β = a (after subst, a is eliminated, β remains).
      have h_L_zero : L_tail.length = 0 := by omega
      have hβa_eq : β = a := by
        match L_tail, h_L_zero with
        | .nil _ _, _ => rfl
      subst hβa_eq
      by_cases hR_tail_pos : R_tail.length ≥ 1
      · -- L nil, R pos.  L_marg = nil β.  R_marg = projected R_tail.
        obtain ⟨R_marg, hR_marg_dir, hR_marg_pos, hR_marg_vs, hR_marg_dL,
                _, hR_marg_inter⟩ :=
          project_walk_marg_full (S := S) (T := T) (hS := hS)
            R_tail hR_tail_dir hR_tail_pos hγ_marg hb_marg hR_tail_inter_ST
        -- Note: after subst hβa_eq, references to `a` become `β`.
        -- ha_notin_R_tail : β ∉ R_tail.vertices  (rewritten).
        have hβ_notin_R_marg : β ∉ R_marg.vertices := fun h_in =>
          ha_notin_R_tail (hR_marg_vs β h_in)
        have hb_notin_R_marg_dL : b ∉ R_marg.vertices.dropLast := fun h_in =>
          hb_notin_R_tail_dL (hR_marg_dL b h_in)
        refine ⟨Walk.mkBifurcationBidir (Walk.nil β hβ_marg) trivial R_marg
                  hβγ_in_margL, ?_, ?_⟩
        · refine Walk.mkBifurcationBidir_isBifurcation (Walk.nil β hβ_marg)
            trivial R_marg hR_marg_dir hβγ_in_margL hab_ne ?_ hβ_notin_R_marg
            ?_ hb_notin_R_marg_dL
          · intro h_in
            change β ∈ ([β] : List Node).dropLast at h_in
            simp at h_in
          · intro h_in
            change b ∈ ([β] : List Node) at h_in
            rw [List.mem_singleton] at h_in
            exact hab_ne h_in.symm
        · intro x hx
          have h_bif_vs : (Walk.mkBifurcationBidir (Walk.nil β hβ_marg) trivial
                            R_marg hβγ_in_margL).vertices = β :: R_marg.vertices := by
            rw [Walk.vertices_mkBifurcationBidir]
            change ([β] : List Node).reverse.dropLast ++ (β :: R_marg.vertices)
                  = β :: R_marg.vertices
            simp
          rw [h_bif_vs] at hx
          -- bif.vertices.tail = R_marg.vertices.
          -- bif.vertices.tail.dropLast = R_marg.vertices.dropLast.
          change x ∈ R_marg.vertices.dropLast at hx
          -- Case-split: x = γ (R_marg's source) or x ∈ R_marg.vertices.tail.dropLast.
          have h_R_t_ne : R_marg.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos R_marg hR_marg_pos
          rw [Walk.vertices_eq_head_cons_tail R_marg,
              List.dropLast_cons_of_ne_nil h_R_t_ne] at hx
          rcases List.mem_cons.mp hx with rfl | hx_inner
          · -- x = γ.  Show x ∈ T via mem_interior_of_arm_source.
            have h_x_in_R_p : x ∈ R_p.vertices :=
              hR_tail_sub_R_p _ (Walk.head_mem_vertices R_tail)
            have h_x_in_p_tail : x ∈ p.vertices.tail :=
              hR_p_sub _ h_x_in_R_p
            have hγ_in_R_marg_dL : x ∈ R_marg.vertices.dropLast := by
              rw [Walk.vertices_eq_head_cons_tail R_marg,
                  List.dropLast_cons_of_ne_nil h_R_t_ne]
              exact List.mem_cons_self
            have hγ_in_R_tail_dL : x ∈ R_tail.vertices.dropLast :=
              hR_marg_dL _ hγ_in_R_marg_dL
            have hγ_in_R_p_dL : x ∈ R_p.vertices.dropLast :=
              hR_tail_dL_sub_R_p_dL _ hγ_in_R_tail_dL
            have h_x_in_p_drop : x ∈ p.vertices.dropLast :=
              hR_p_drop_sub _ hγ_in_R_p_dL
            have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
              mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
            rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
            · exact absurd h_S hγ_notS
            · exact h_T
          · exact hR_marg_inter x hx_inner
      · -- L nil, R nil → γ = b too.
        have h_R_zero : R_tail.length = 0 := by omega
        have hγb_eq : γ = b := by
          match R_tail, h_R_zero with
          | .nil _ _, _ => rfl
        subst hγb_eq
        -- Both arms nil. Bif is the L-edge (β, γ) alone.
        refine ⟨Walk.mkBifurcationBidir (Walk.nil β hβ_marg) trivial
                  (Walk.nil γ hγ_marg) hβγ_in_margL, ?_, ?_⟩
        · refine Walk.mkBifurcationBidir_isBifurcation (Walk.nil β hβ_marg)
            trivial (Walk.nil γ hγ_marg) trivial hβγ_in_margL hab_ne ?_ ?_ ?_ ?_
          · intro h_in
            change β ∈ ([β] : List Node).dropLast at h_in
            simp at h_in
          · intro h_in
            change β ∈ ([γ] : List Node) at h_in
            rw [List.mem_singleton] at h_in
            exact hβγ_eq h_in
          · intro h_in
            change γ ∈ ([β] : List Node) at h_in
            rw [List.mem_singleton] at h_in
            exact hβγ_eq h_in.symm
          · intro h_in
            change γ ∈ ([γ] : List Node).dropLast at h_in
            simp at h_in
        · intro x hx
          have h_bif_vs : (Walk.mkBifurcationBidir (Walk.nil β hβ_marg) trivial
                            (Walk.nil γ hγ_marg) hβγ_in_margL).vertices = [β, γ] := by
            rw [Walk.vertices_mkBifurcationBidir]
            change ([β] : List Node).reverse.dropLast ++ (β :: [γ]) = [β, γ]
            simp
          rw [h_bif_vs] at hx
          change x ∈ ([β, γ] : List Node).tail.dropLast at hx
          simp at hx

-- ## Helper: backward, directed-hinge, c ∈ S, β ≠ γ non-degenerate case.
--
-- Lifted as a top-level private lemma (same shape as
-- `backward_marg_to_g_bif_bidir_hinge_one_orientation` above): given a
-- directed-hinge bifurcation `p : Walk G a b` with source `c ∈ S`, plus
-- the `find_first_non_W_directed S` decomposition on each arm, in the
-- branch `vL_exit ≠ vR_exit`, build a bidirected-hinge bifurcation in
-- `G.marginalize S hS` with the same endpoints `a, b` and interior ⊆ T.
--
-- The construction:
--   (1) Build a `marg.L` edge `(vL_exit, vR_exit)` via the G-bifurcation
--       `Walk.mkBifurcation L_W_seg R_W_seg` with directed-hinge source
--       `c`; its interior lies in `S` (via `hL_W_inter`, `hR_W_inter`,
--       `hc_S`).
--   (2-4) Case-split on `L_marg_seg.length`, `R_marg_seg.length` for
--       four sub-sub-cases (positive/nil × positive/nil).  In each,
--       project the positive arms via `project_walk_marg_full` and use
--       `Walk.nil` for the nil arms; assemble via
--       `Walk.mkBifurcationBidir` with the freshly-built `marg.L` edge.
private lemma backward_marg_to_g_bif_dir_hinge_cInS_betaNeGamma_one_orientation
    {G : CDMG Node} (S T : Finset Node) (hS : S ⊆ G.V)
    {a b : Node}
    (ha_VST : a ∈ G.V \ (S ∪ T)) (hb_VST : b ∈ G.V \ (S ∪ T))
    (ha_marg : a ∈ G.marginalize S hS) (hb_marg : b ∈ G.marginalize S hS)
    {p : Walk G a b}
    (hp_bif : p.IsBifurcation)
    (hp_inter : ∀ x ∈ p.vertices.tail.dropLast, x ∈ S ∪ T)
    {c : Node} (hc_S : c ∈ S)
    {L_p : Walk G c a} {R_p : Walk G c b}
    (hL_p_dir : L_p.IsDirectedWalk) (hR_p_dir : R_p.IsDirectedWalk)
    (hL_p_pos : L_p.length ≥ 1) (hR_p_pos : R_p.length ≥ 1)
    (hL_p_sub : ∀ x ∈ L_p.vertices, x ∈ p.vertices.dropLast)
    (hR_p_sub : ∀ x ∈ R_p.vertices, x ∈ p.vertices.tail)
    (hL_p_drop_sub : ∀ x ∈ L_p.vertices.dropLast, x ∈ p.vertices.tail)
    (hR_p_drop_sub : ∀ x ∈ R_p.vertices.dropLast, x ∈ p.vertices.dropLast)
    {vL_exit vR_exit : Node}
    {L_W_seg : Walk G c vL_exit} {L_marg_seg : Walk G vL_exit a}
    {R_W_seg : Walk G c vR_exit} {R_marg_seg : Walk G vR_exit b}
    (hL_W_dir : L_W_seg.IsDirectedWalk)
    (hL_marg_dir : L_marg_seg.IsDirectedWalk)
    (hL_W_pos : L_W_seg.length ≥ 1) (hvL_exit_notS : vL_exit ∉ S)
    (hL_W_inter : ∀ x ∈ L_W_seg.vertices.tail.dropLast, x ∈ S)
    (hL_p_vs_eq :
      L_p.vertices = L_W_seg.vertices.dropLast ++ L_marg_seg.vertices)
    (hR_W_dir : R_W_seg.IsDirectedWalk)
    (hR_marg_dir : R_marg_seg.IsDirectedWalk)
    (hR_W_pos : R_W_seg.length ≥ 1) (hvR_exit_notS : vR_exit ∉ S)
    (hR_W_inter : ∀ x ∈ R_W_seg.vertices.tail.dropLast, x ∈ S)
    (hR_p_vs_eq :
      R_p.vertices = R_W_seg.vertices.dropLast ++ R_marg_seg.vertices)
    (hvL_vR_exit_ne : vL_exit ≠ vR_exit) :
    ∃ q : Walk (G.marginalize S hS) a b, q.IsBifurcation ∧
      ∀ x ∈ q.vertices.tail.dropLast, x ∈ T := by
  -- Unpack hp_bif and derive ancillary facts.
  have hp_pos : p.length ≥ 1 := Walk.length_pos_of_isBifurcation hp_bif
  obtain ⟨hab_ne, ha_p_tail, hb_p_drop, _⟩ := hp_bif
  have hp_inter_ST : ∀ x ∈ p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T :=
    fun x hx => Finset.mem_union.mp (hp_inter x hx)
  -- L_p, R_p vertex bounds.
  have ha_notin_L_p_drop : a ∉ L_p.vertices.dropLast := fun h_in =>
    ha_p_tail (hL_p_drop_sub a h_in)
  have ha_notin_R_p : a ∉ R_p.vertices := fun h_in =>
    ha_p_tail (hR_p_sub a h_in)
  have hb_notin_L_p : b ∉ L_p.vertices := fun h_in =>
    hb_p_drop (hL_p_sub b h_in)
  have hb_notin_R_p_drop : b ∉ R_p.vertices.dropLast := fun h_in =>
    hb_p_drop (hR_p_drop_sub b h_in)
  -- vL_exit, vR_exit ∈ G.V, ∈ G.V \ S, ∈ marg.
  have hvL_exit_GV : vL_exit ∈ G.V :=
    Walk.target_in_GV_of_directedWalk_pos L_W_seg hL_W_dir hL_W_pos
  have hvR_exit_GV : vR_exit ∈ G.V :=
    Walk.target_in_GV_of_directedWalk_pos R_W_seg hR_W_dir hR_W_pos
  have hvL_exit_VS : vL_exit ∈ G.V \ S :=
    Finset.mem_sdiff.mpr ⟨hvL_exit_GV, hvL_exit_notS⟩
  have hvR_exit_VS : vR_exit ∈ G.V \ S :=
    Finset.mem_sdiff.mpr ⟨hvR_exit_GV, hvR_exit_notS⟩
  have hvL_exit_marg : vL_exit ∈ G.marginalize S hS := by
    change vL_exit ∈ G.J ∪ (G.V \ S)
    exact Finset.mem_union_right _ hvL_exit_VS
  have hvR_exit_marg : vR_exit ∈ G.marginalize S hS := by
    change vR_exit ∈ G.J ∪ (G.V \ S)
    exact Finset.mem_union_right _ hvR_exit_VS
  -- L_marg_seg, R_marg_seg vertex subsets back into L_p, R_p.
  have hL_marg_ne : L_marg_seg.vertices ≠ [] := Walk.vertices_ne_nil L_marg_seg
  have hR_marg_ne : R_marg_seg.vertices ≠ [] := Walk.vertices_ne_nil R_marg_seg
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
  -- L_marg_seg, R_marg_seg interior ⊆ S ∨ T.
  have hL_marg_inter_ST :
      ∀ x ∈ L_marg_seg.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
    intro x hx
    by_cases h_L_marg_pos : L_marg_seg.length ≥ 1
    · have h_t_ne : L_marg_seg.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos L_marg_seg h_L_marg_pos
      have h_drop_eq : L_marg_seg.vertices.dropLast
          = vL_exit :: L_marg_seg.vertices.tail.dropLast := by
        conv_lhs => rw [Walk.vertices_eq_head_cons_tail L_marg_seg]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have h_drop : x ∈ L_marg_seg.vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have h_L_p_drop : x ∈ L_p.vertices.dropLast :=
        hL_marg_drop_sub_L_p_drop x h_drop
      have h_x_p_tail : x ∈ p.vertices.tail := hL_p_drop_sub x h_L_p_drop
      have h_v : x ∈ L_marg_seg.vertices := List.mem_of_mem_dropLast h_drop
      have h_L_p : x ∈ L_p.vertices := hL_marg_sub_L_p x h_v
      have h_x_p_drop : x ∈ p.vertices.dropLast := hL_p_sub x h_L_p
      have h_x_p_inter : x ∈ p.vertices.tail.dropLast :=
        mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
      exact hp_inter_ST x h_x_p_inter
    · have h_L_marg_zero : L_marg_seg.length = 0 := by omega
      match L_marg_seg, h_L_marg_zero with
      | .nil _ _, _ => simp [Walk.vertices, List.tail] at hx
  have hR_marg_inter_ST :
      ∀ x ∈ R_marg_seg.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
    intro x hx
    by_cases h_R_marg_pos : R_marg_seg.length ≥ 1
    · have h_t_ne : R_marg_seg.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos R_marg_seg h_R_marg_pos
      have h_drop_eq : R_marg_seg.vertices.dropLast
          = vR_exit :: R_marg_seg.vertices.tail.dropLast := by
        conv_lhs => rw [Walk.vertices_eq_head_cons_tail R_marg_seg]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have h_drop : x ∈ R_marg_seg.vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have h_R_p_drop : x ∈ R_p.vertices.dropLast :=
        hR_marg_drop_sub_R_p_drop x h_drop
      have h_x_p_drop : x ∈ p.vertices.dropLast := hR_p_drop_sub x h_R_p_drop
      have h_v : x ∈ R_marg_seg.vertices := List.mem_of_mem_dropLast h_drop
      have h_R_p : x ∈ R_p.vertices := hR_marg_sub_R_p x h_v
      have h_x_p_tail : x ∈ p.vertices.tail := hR_p_sub x h_R_p
      have h_x_p_inter : x ∈ p.vertices.tail.dropLast :=
        mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
      exact hp_inter_ST x h_x_p_inter
    · have h_R_marg_zero : R_marg_seg.length = 0 := by omega
      match R_marg_seg, h_R_marg_zero with
      | .nil _ _, _ => simp [Walk.vertices, List.tail] at hx
  -- L_marg_seg, R_marg_seg vertex bounds for a, b.
  have ha_notin_L_marg_drop : a ∉ L_marg_seg.vertices.dropLast := fun h_in =>
    ha_notin_L_p_drop (hL_marg_drop_sub_L_p_drop a h_in)
  have ha_notin_R_marg : a ∉ R_marg_seg.vertices := fun h_in =>
    ha_notin_R_p (hR_marg_sub_R_p a h_in)
  have hb_notin_L_marg : b ∉ L_marg_seg.vertices := fun h_in =>
    hb_notin_L_p (hL_marg_sub_L_p b h_in)
  have hb_notin_R_marg_drop : b ∉ R_marg_seg.vertices.dropLast := fun h_in =>
    hb_notin_R_p_drop (hR_marg_drop_sub_R_p_drop b h_in)
  -- Step 1: Build the marg.L edge (vL_exit, vR_exit) ∈ marg.L via a
  -- G-bifurcation `mkBifurcation L_W_seg R_W_seg` with directed-hinge
  -- source `c`.
  -- L_W_seg.vertices.dropLast ⊆ S (source c ∈ S + interior ⊆ S).
  have hL_W_drop_S : ∀ x ∈ L_W_seg.vertices.dropLast, x ∈ S := by
    intro x hx
    have h_tail_ne : L_W_seg.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos L_W_seg hL_W_pos
    have h_drop_eq : L_W_seg.vertices.dropLast
        = c :: L_W_seg.vertices.tail.dropLast := by
      conv_lhs => rw [Walk.vertices_eq_head_cons_tail L_W_seg]
      exact List.dropLast_cons_of_ne_nil h_tail_ne
    rw [h_drop_eq] at hx
    rcases List.mem_cons.mp hx with rfl | hx_rest
    · exact hc_S
    · exact hL_W_inter x hx_rest
  have hR_W_drop_S : ∀ x ∈ R_W_seg.vertices.dropLast, x ∈ S := by
    intro x hx
    have h_tail_ne : R_W_seg.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos R_W_seg hR_W_pos
    have h_drop_eq : R_W_seg.vertices.dropLast
        = c :: R_W_seg.vertices.tail.dropLast := by
      conv_lhs => rw [Walk.vertices_eq_head_cons_tail R_W_seg]
      exact List.dropLast_cons_of_ne_nil h_tail_ne
    rw [h_drop_eq] at hx
    rcases List.mem_cons.mp hx with rfl | hx_rest
    · exact hc_S
    · exact hR_W_inter x hx_rest
  -- L_W_seg.vertices = L_W_seg.vertices.dropLast ++ [vL_exit].
  have hL_W_decomp : L_W_seg.vertices = L_W_seg.vertices.dropLast ++ [vL_exit] := by
    have h_ne : L_W_seg.vertices ≠ [] := Walk.vertices_ne_nil L_W_seg
    have h_last : L_W_seg.vertices.getLast h_ne = vL_exit :=
      Walk.vertices_getLast L_W_seg
    have := List.dropLast_append_getLast h_ne
    rw [h_last] at this; exact this.symm
  have hR_W_decomp : R_W_seg.vertices = R_W_seg.vertices.dropLast ++ [vR_exit] := by
    have h_ne : R_W_seg.vertices ≠ [] := Walk.vertices_ne_nil R_W_seg
    have h_last : R_W_seg.vertices.getLast h_ne = vR_exit :=
      Walk.vertices_getLast R_W_seg
    have := List.dropLast_append_getLast h_ne
    rw [h_last] at this; exact this.symm
  have hvL_exit_notin_L_W_drop : vL_exit ∉ L_W_seg.vertices.dropLast := fun h_in =>
    hvL_exit_notS (hL_W_drop_S vL_exit h_in)
  have hvR_exit_notin_R_W_drop : vR_exit ∉ R_W_seg.vertices.dropLast := fun h_in =>
    hvR_exit_notS (hR_W_drop_S vR_exit h_in)
  have hvL_exit_notin_R_W : vL_exit ∉ R_W_seg.vertices := by
    intro h_in
    rw [hR_W_decomp] at h_in
    rcases List.mem_append.mp h_in with h_dL | h_last
    · exact hvL_exit_notS (hR_W_drop_S vL_exit h_dL)
    · rw [List.mem_singleton] at h_last
      exact hvL_vR_exit_ne h_last
  have hvR_exit_notin_L_W : vR_exit ∉ L_W_seg.vertices := by
    intro h_in
    rw [hL_W_decomp] at h_in
    rcases List.mem_append.mp h_in with h_dL | h_last
    · exact hvR_exit_notS (hL_W_drop_S vR_exit h_dL)
    · rw [List.mem_singleton] at h_last
      exact hvL_vR_exit_ne h_last.symm
  -- G-bifurcation source c with hinge between vL_exit and vR_exit.
  have h_G_bif_src :
      (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos R_W_seg).IsBifurcationSource c :=
    Walk.mkBifurcation_isBifurcationSource L_W_seg hL_W_dir hL_W_pos
      R_W_seg hR_W_dir hR_W_pos
      hvL_vR_exit_ne hvL_exit_notin_L_W_drop hvL_exit_notin_R_W
      hvR_exit_notin_L_W hvR_exit_notin_R_W_drop
  have h_G_bif_is_bif :
      (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos R_W_seg).IsBifurcation :=
    Walk.isBifurcationSource_to_isBifurcation _ c h_G_bif_src
  -- G-bifurcation's interior ⊆ S.
  have h_G_bif_inter_S :
      ∀ x ∈ (Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos
              R_W_seg).vertices.tail.dropLast, x ∈ S := by
    intro x hx
    rw [vertices_tail_dropLast_mkBifurcation
          L_W_seg hL_W_dir hL_W_pos R_W_seg hR_W_pos] at hx
    rcases List.mem_append.mp hx with hx_L | hx_R
    · rw [List.mem_reverse] at hx_L
      exact hL_W_inter x hx_L
    · exact hR_W_drop_S x hx_R
  -- The marg.L edge.
  have hvLvR_in_margL : (vL_exit, vR_exit) ∈ (G.marginalize S hS).L := by
    change (vL_exit, vR_exit) ∈ ((G.V \ S) ×ˢ (G.V \ S)).filter
                     (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL S e.1 e.2)
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hvL_exit_VS, hvR_exit_VS⟩, hvL_vR_exit_ne, ?_⟩
    exact Or.inl ⟨Walk.mkBifurcation L_W_seg hL_W_dir hL_W_pos R_W_seg,
                  h_G_bif_is_bif, h_G_bif_inter_S⟩
  -- Step 2-4: Case-split on L_marg_seg.length, R_marg_seg.length and
  -- assemble via `Walk.mkBifurcationBidir` with hinge (vL_exit, vR_exit).
  by_cases hL_marg_pos : L_marg_seg.length ≥ 1
  · -- L_marg_seg positive.  Project to marg.
    obtain ⟨L_marg, hL_marg_dir', hL_marg_pos', hL_marg_vs, hL_marg_dL,
            _, hL_marg_inter⟩ :=
      project_walk_marg_full (S := S) (T := T) (hS := hS)
        L_marg_seg hL_marg_dir hL_marg_pos hvL_exit_marg ha_marg hL_marg_inter_ST
    have ha_notin_L_marg_dL : a ∉ L_marg.vertices.dropLast := fun h_in =>
      ha_notin_L_marg_drop (hL_marg_dL a h_in)
    have hb_notin_L_marg' : b ∉ L_marg.vertices := fun h_in =>
      hb_notin_L_marg (hL_marg_vs b h_in)
    by_cases hR_marg_pos : R_marg_seg.length ≥ 1
    · -- L+, R+.
      obtain ⟨R_marg, hR_marg_dir', hR_marg_pos', hR_marg_vs, hR_marg_dL,
              _, hR_marg_inter⟩ :=
        project_walk_marg_full (S := S) (T := T) (hS := hS)
          R_marg_seg hR_marg_dir hR_marg_pos hvR_exit_marg hb_marg hR_marg_inter_ST
      have ha_notin_R_marg' : a ∉ R_marg.vertices := fun h_in =>
        ha_notin_R_marg (hR_marg_vs a h_in)
      have hb_notin_R_marg_dL : b ∉ R_marg.vertices.dropLast := fun h_in =>
        hb_notin_R_marg_drop (hR_marg_dL b h_in)
      refine ⟨Walk.mkBifurcationBidir L_marg hL_marg_dir' R_marg hvLvR_in_margL,
              ?_, ?_⟩
      · exact Walk.mkBifurcationBidir_isBifurcation L_marg hL_marg_dir'
          R_marg hR_marg_dir' hvLvR_in_margL hab_ne
          ha_notin_L_marg_dL ha_notin_R_marg' hb_notin_L_marg' hb_notin_R_marg_dL
      · intro x hx
        rw [vertices_tail_dropLast_mkBifurcationBidir_Lpos
              L_marg hL_marg_dir' R_marg hvLvR_in_margL hL_marg_pos'] at hx
        rcases List.mem_append.mp hx with hx_L | hx_R
        · rw [List.mem_reverse] at hx_L
          exact hL_marg_inter x hx_L
        · have h_R_marg_ne : R_marg.vertices ≠ [] := Walk.vertices_ne_nil R_marg
          rw [List.dropLast_cons_of_ne_nil h_R_marg_ne] at hx_R
          rcases List.mem_cons.mp hx_R with rfl | hx_R_dL
          · -- x = vL_exit.
            have h_x_in_L_p : x ∈ L_p.vertices :=
              hL_marg_sub_L_p _ (Walk.head_mem_vertices L_marg_seg)
            have h_x_in_p_drop : x ∈ p.vertices.dropLast :=
              hL_p_sub _ h_x_in_L_p
            have h_L_marg_t_ne : L_marg.vertices.tail ≠ [] :=
              Walk.tail_vertices_ne_nil_of_pos L_marg hL_marg_pos'
            have hvL_in_L_marg_dL : x ∈ L_marg.vertices.dropLast := by
              rw [Walk.vertices_eq_head_cons_tail L_marg,
                  List.dropLast_cons_of_ne_nil h_L_marg_t_ne]
              exact List.mem_cons_self
            have hvL_in_L_marg_seg_dL : x ∈ L_marg_seg.vertices.dropLast :=
              hL_marg_dL _ hvL_in_L_marg_dL
            have hvL_in_L_p_dL : x ∈ L_p.vertices.dropLast :=
              hL_marg_drop_sub_L_p_drop _ hvL_in_L_marg_seg_dL
            have h_x_in_p_tail : x ∈ p.vertices.tail :=
              hL_p_drop_sub _ hvL_in_L_p_dL
            have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
              mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
            rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
            · exact absurd h_S hvL_exit_notS
            · exact h_T
          · -- x ∈ R_marg.vertices.dropLast.
            have h_R_t_ne : R_marg.vertices.tail ≠ [] :=
              Walk.tail_vertices_ne_nil_of_pos R_marg hR_marg_pos'
            rw [Walk.vertices_eq_head_cons_tail R_marg,
                List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R_dL
            rcases List.mem_cons.mp hx_R_dL with rfl | hx_R_inner
            · -- x = vR_exit.
              have h_x_in_R_p : x ∈ R_p.vertices :=
                hR_marg_sub_R_p _ (Walk.head_mem_vertices R_marg_seg)
              have h_x_in_p_tail : x ∈ p.vertices.tail :=
                hR_p_sub _ h_x_in_R_p
              have hvR_in_R_marg_dL : x ∈ R_marg.vertices.dropLast := by
                rw [Walk.vertices_eq_head_cons_tail R_marg,
                    List.dropLast_cons_of_ne_nil h_R_t_ne]
                exact List.mem_cons_self
              have hvR_in_R_marg_seg_dL : x ∈ R_marg_seg.vertices.dropLast :=
                hR_marg_dL _ hvR_in_R_marg_dL
              have hvR_in_R_p_dL : x ∈ R_p.vertices.dropLast :=
                hR_marg_drop_sub_R_p_drop _ hvR_in_R_marg_seg_dL
              have h_x_in_p_drop : x ∈ p.vertices.dropLast :=
                hR_p_drop_sub _ hvR_in_R_p_dL
              have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
                mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
              rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
              · exact absurd h_S hvR_exit_notS
              · exact h_T
            · exact hR_marg_inter x hx_R_inner
    · -- L+, R nil → vR_exit = b (after subst, b is eliminated).
      have h_R_zero : R_marg_seg.length = 0 := by omega
      have hvR_b_eq : vR_exit = b := by
        match R_marg_seg, h_R_zero with
        | .nil _ _, _ => rfl
      subst hvR_b_eq
      refine ⟨Walk.mkBifurcationBidir L_marg hL_marg_dir' (Walk.nil vR_exit hvR_exit_marg)
                hvLvR_in_margL, ?_, ?_⟩
      · refine Walk.mkBifurcationBidir_isBifurcation L_marg hL_marg_dir'
          (Walk.nil vR_exit hvR_exit_marg) trivial hvLvR_in_margL hab_ne
          ha_notin_L_marg_dL ?_ hb_notin_L_marg' ?_
        · intro h_in
          change a ∈ ([vR_exit] : List Node) at h_in
          rw [List.mem_singleton] at h_in
          exact ha_notin_R_marg (by rw [h_in]; exact Walk.head_mem_vertices R_marg_seg)
        · intro h_in
          change vR_exit ∈ ([vR_exit] : List Node).dropLast at h_in
          simp at h_in
      · intro x hx
        rw [vertices_tail_dropLast_mkBifurcationBidir_Lpos
              L_marg hL_marg_dir' (Walk.nil vR_exit hvR_exit_marg) hvLvR_in_margL
              hL_marg_pos'] at hx
        rcases List.mem_append.mp hx with hx_L | hx_R
        · rw [List.mem_reverse] at hx_L
          exact hL_marg_inter x hx_L
        · -- x ∈ (vL_exit :: [vR_exit]).dropLast = [vL_exit].
          change x ∈ ((vL_exit :: [vR_exit]) : List Node).dropLast at hx_R
          change x ∈ ([vL_exit, vR_exit] : List Node).dropLast at hx_R
          simp [List.dropLast] at hx_R
          rw [hx_R]
          have h_x_in_L_p : vL_exit ∈ L_p.vertices :=
            hL_marg_sub_L_p _ (Walk.head_mem_vertices L_marg_seg)
          have h_x_in_p_drop : vL_exit ∈ p.vertices.dropLast :=
            hL_p_sub _ h_x_in_L_p
          have h_L_marg_t_ne : L_marg.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos L_marg hL_marg_pos'
          have hvL_in_L_marg_dL : vL_exit ∈ L_marg.vertices.dropLast := by
            rw [Walk.vertices_eq_head_cons_tail L_marg,
                List.dropLast_cons_of_ne_nil h_L_marg_t_ne]
            exact List.mem_cons_self
          have hvL_in_L_marg_seg_dL : vL_exit ∈ L_marg_seg.vertices.dropLast :=
            hL_marg_dL _ hvL_in_L_marg_dL
          have hvL_in_L_p_dL : vL_exit ∈ L_p.vertices.dropLast :=
            hL_marg_drop_sub_L_p_drop _ hvL_in_L_marg_seg_dL
          have h_x_in_p_tail : vL_exit ∈ p.vertices.tail :=
            hL_p_drop_sub _ hvL_in_L_p_dL
          have h_x_in_p_inter : vL_exit ∈ p.vertices.tail.dropLast :=
            mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
          rcases hp_inter_ST vL_exit h_x_in_p_inter with h_S | h_T
          · exact absurd h_S hvL_exit_notS
          · exact h_T
  · -- L_marg_seg nil → vL_exit = a (after subst, a is eliminated).
    have h_L_zero : L_marg_seg.length = 0 := by omega
    have hvL_a_eq : vL_exit = a := by
      match L_marg_seg, h_L_zero with
      | .nil _ _, _ => rfl
    subst hvL_a_eq
    by_cases hR_marg_pos : R_marg_seg.length ≥ 1
    · -- L nil, R+.
      obtain ⟨R_marg, hR_marg_dir', hR_marg_pos', hR_marg_vs, hR_marg_dL,
              _, hR_marg_inter⟩ :=
        project_walk_marg_full (S := S) (T := T) (hS := hS)
          R_marg_seg hR_marg_dir hR_marg_pos hvR_exit_marg hb_marg hR_marg_inter_ST
      have hvL_exit_notin_R_marg : vL_exit ∉ R_marg.vertices := fun h_in =>
        ha_notin_R_marg (hR_marg_vs vL_exit h_in)
      have hb_notin_R_marg_dL : b ∉ R_marg.vertices.dropLast := fun h_in =>
        hb_notin_R_marg_drop (hR_marg_dL b h_in)
      refine ⟨Walk.mkBifurcationBidir (Walk.nil vL_exit hvL_exit_marg) trivial R_marg
                hvLvR_in_margL, ?_, ?_⟩
      · refine Walk.mkBifurcationBidir_isBifurcation (Walk.nil vL_exit hvL_exit_marg)
          trivial R_marg hR_marg_dir' hvLvR_in_margL hab_ne ?_ hvL_exit_notin_R_marg
          ?_ hb_notin_R_marg_dL
        · intro h_in
          change vL_exit ∈ ([vL_exit] : List Node).dropLast at h_in
          simp at h_in
        · intro h_in
          change b ∈ ([vL_exit] : List Node) at h_in
          rw [List.mem_singleton] at h_in
          exact hab_ne h_in.symm
      · intro x hx
        have h_bif_vs :
            (Walk.mkBifurcationBidir (Walk.nil vL_exit hvL_exit_marg) trivial R_marg
              hvLvR_in_margL).vertices = vL_exit :: R_marg.vertices := by
          rw [Walk.vertices_mkBifurcationBidir]
          change ([vL_exit] : List Node).reverse.dropLast ++ (vL_exit :: R_marg.vertices)
                = vL_exit :: R_marg.vertices
          simp
        rw [h_bif_vs] at hx
        change x ∈ R_marg.vertices.dropLast at hx
        have h_R_t_ne : R_marg.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos R_marg hR_marg_pos'
        rw [Walk.vertices_eq_head_cons_tail R_marg,
            List.dropLast_cons_of_ne_nil h_R_t_ne] at hx
        rcases List.mem_cons.mp hx with rfl | hx_inner
        · -- x = vR_exit.
          have h_x_in_R_p : x ∈ R_p.vertices :=
            hR_marg_sub_R_p _ (Walk.head_mem_vertices R_marg_seg)
          have h_x_in_p_tail : x ∈ p.vertices.tail :=
            hR_p_sub _ h_x_in_R_p
          have hvR_in_R_marg_dL : x ∈ R_marg.vertices.dropLast := by
            rw [Walk.vertices_eq_head_cons_tail R_marg,
                List.dropLast_cons_of_ne_nil h_R_t_ne]
            exact List.mem_cons_self
          have hvR_in_R_marg_seg_dL : x ∈ R_marg_seg.vertices.dropLast :=
            hR_marg_dL _ hvR_in_R_marg_dL
          have hvR_in_R_p_dL : x ∈ R_p.vertices.dropLast :=
            hR_marg_drop_sub_R_p_drop _ hvR_in_R_marg_seg_dL
          have h_x_in_p_drop : x ∈ p.vertices.dropLast :=
            hR_p_drop_sub _ hvR_in_R_p_dL
          have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
            mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
          rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
          · exact absurd h_S hvR_exit_notS
          · exact h_T
        · exact hR_marg_inter x hx_inner
    · -- L nil, R nil → vR_exit = b.
      have h_R_zero : R_marg_seg.length = 0 := by omega
      have hvR_b_eq : vR_exit = b := by
        match R_marg_seg, h_R_zero with
        | .nil _ _, _ => rfl
      subst hvR_b_eq
      refine ⟨Walk.mkBifurcationBidir (Walk.nil vL_exit hvL_exit_marg) trivial
                (Walk.nil vR_exit hvR_exit_marg) hvLvR_in_margL, ?_, ?_⟩
      · refine Walk.mkBifurcationBidir_isBifurcation (Walk.nil vL_exit hvL_exit_marg)
          trivial (Walk.nil vR_exit hvR_exit_marg) trivial hvLvR_in_margL hab_ne
          ?_ ?_ ?_ ?_
        · intro h_in
          change vL_exit ∈ ([vL_exit] : List Node).dropLast at h_in
          simp at h_in
        · intro h_in
          change vL_exit ∈ ([vR_exit] : List Node) at h_in
          rw [List.mem_singleton] at h_in
          exact hvL_vR_exit_ne h_in
        · intro h_in
          change vR_exit ∈ ([vL_exit] : List Node) at h_in
          rw [List.mem_singleton] at h_in
          exact hvL_vR_exit_ne h_in.symm
        · intro h_in
          change vR_exit ∈ ([vR_exit] : List Node).dropLast at h_in
          simp at h_in
      · intro x hx
        have h_bif_vs :
            (Walk.mkBifurcationBidir (Walk.nil vL_exit hvL_exit_marg) trivial
              (Walk.nil vR_exit hvR_exit_marg) hvLvR_in_margL).vertices
              = [vL_exit, vR_exit] := by
          rw [Walk.vertices_mkBifurcationBidir]
          change ([vL_exit] : List Node).reverse.dropLast ++ (vL_exit :: [vR_exit])
                = [vL_exit, vR_exit]
          simp
        rw [h_bif_vs] at hx
        change x ∈ ([vL_exit, vR_exit] : List Node).tail.dropLast at hx
        simp at hx

private lemma marg_PhiL_iff {G : CDMG Node} (S T : Finset Node)
    (hS : S ⊆ G.V) (_hT : T ⊆ G.V) (_hDisj : Disjoint S T)
    {u v : Node}
    (hu : u ∈ G.V \ (S ∪ T)) (hv : v ∈ G.V \ (S ∪ T)) :
    (G.marginalize S hS).MarginalizationΦL T u v ↔
      G.MarginalizationΦL (S ∪ T) u v := by
  -- Prove the helper for a single orientation; both orientations follow by swap.
  have hu_g : u ∈ G := Finset.mem_union_right _ (Finset.mem_sdiff.mp hu).1
  have hv_g : v ∈ G := Finset.mem_union_right _ (Finset.mem_sdiff.mp hv).1
  have hu_notSuT : u ∉ S ∪ T := (Finset.mem_sdiff.mp hu).2
  have hv_notSuT : v ∉ S ∪ T := (Finset.mem_sdiff.mp hv).2
  have hu_notS : u ∉ S := fun h => hu_notSuT (Finset.mem_union_left _ h)
  have hv_notS : v ∉ S := fun h => hv_notSuT (Finset.mem_union_left _ h)
  have hu_notT : u ∉ T := fun h => hu_notSuT (Finset.mem_union_right _ h)
  have hv_notT : v ∉ T := fun h => hv_notSuT (Finset.mem_union_right _ h)
  have hu_marg : u ∈ G.marginalize S hS :=
    mem_marg_of_notin_union_VnoJ S T hS hu
  have hv_marg : v ∈ G.marginalize S hS :=
    mem_marg_of_notin_union_VnoJ S T hS hv
  -- Forward direction: delegate to `forward_marg_to_g_bif_one_orientation`.
  have forward_one_orientation :
      ∀ {a b : Node},
        a ∈ G.V \ (S ∪ T) → b ∈ G.V \ (S ∪ T) →
        a ∈ G.marginalize S hS → b ∈ G.marginalize S hS →
        ∀ (p : Walk (G.marginalize S hS) a b),
          p.IsBifurcation →
          (∀ x ∈ p.vertices.tail.dropLast, x ∈ T) →
          ∃ q : Walk G a b, q.IsBifurcation ∧
            ∀ x ∈ q.vertices.tail.dropLast, x ∈ S ∪ T :=
    fun ha_VST hb_VST ha_marg hb_marg p hp_bif hp_inter =>
      forward_marg_to_g_bif_one_orientation S T hS ha_VST hb_VST ha_marg hb_marg
        p hp_bif hp_inter
  -- Backward direction helper, analogous.
  have backward_one_orientation :
      ∀ {a b : Node},
        a ∈ G.V \ (S ∪ T) → b ∈ G.V \ (S ∪ T) →
        a ∈ G.marginalize S hS → b ∈ G.marginalize S hS →
        ∀ (p : Walk G a b),
          p.IsBifurcation →
          (∀ x ∈ p.vertices.tail.dropLast, x ∈ S ∪ T) →
          ∃ q : Walk (G.marginalize S hS) a b, q.IsBifurcation ∧
            ∀ x ∈ q.vertices.tail.dropLast, x ∈ T := by
    intro a b ha_VST hb_VST ha_marg hb_marg p hp_bif hp_inter
    have ha_notSuT : a ∉ S ∪ T := (Finset.mem_sdiff.mp ha_VST).2
    have hb_notSuT : b ∉ S ∪ T := (Finset.mem_sdiff.mp hb_VST).2
    have ha_notS : a ∉ S := fun h => ha_notSuT (Finset.mem_union_left _ h)
    have hb_notS : b ∉ S := fun h => hb_notSuT (Finset.mem_union_left _ h)
    have ha_notT : a ∉ T := fun h => ha_notSuT (Finset.mem_union_right _ h)
    have hb_notT : b ∉ T := fun h => hb_notSuT (Finset.mem_union_right _ h)
    have hp_pos : p.length ≥ 1 := Walk.length_pos_of_isBifurcation hp_bif
    obtain ⟨hab_ne, ha_p_tail, hb_p_drop, i, hp_split⟩ := hp_bif
    have hp_inter_ST : ∀ x ∈ p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T :=
      fun x hx => Finset.mem_union.mp (hp_inter x hx)
    -- Get a marg bif walk via the existing marg_preserves_bif_forward.
    -- This walk's interior is the issue: we need it in T.
    -- The existing helper doesn't give interior info, so we directly construct.
    --
    -- Direct construction via case-split.
    by_cases h_dir : p.IsBifurcationDirectedHingeWithSplit i
    · -- Directed hinge in p.  Source c.
      obtain ⟨c, L_p, R_p, hL_p_dir, hR_p_dir, hL_p_pos, hR_p_pos, hidx,
              hL_p_sub, hR_p_sub, hL_p_drop_sub, hR_p_drop_sub⟩ :=
        Walk.exists_arms_of_bifurcation_directed_hinge_strong p i h_dir
      -- a ∉ L_p.vertices.dropLast etc.
      have ha_notin_L_p_drop : a ∉ L_p.vertices.dropLast := fun h_in =>
        ha_p_tail (hL_p_drop_sub a h_in)
      have ha_notin_R_p : a ∉ R_p.vertices := fun h_in =>
        ha_p_tail (hR_p_sub a h_in)
      have hb_notin_L_p : b ∉ L_p.vertices := fun h_in =>
        hb_p_drop (hL_p_sub b h_in)
      have hb_notin_R_p_drop : b ∉ R_p.vertices.dropLast := fun h_in =>
        hb_p_drop (hR_p_drop_sub b h_in)
      -- The interior of L_p (everything in L_p.vertices.dropLast except possibly c) is in p.tail.dropLast.
      -- Similarly R_p.
      -- More precisely: for x in L_p.vertices.dropLast (which includes c), x is in p.vertices.tail.
      -- For x in L_p.vertices (including target a... no, a may not be there since ha_notin_L_p_drop)...
      -- Let me think: L_p is a walk from c to a. L_p.vertices.dropLast includes c, c→a's intermediates.
      -- L_p.vertices.dropLast ⊆ p.vertices.tail (from hL_p_drop_sub).
      -- For x ∈ L_p.vertices.tail.dropLast (the "interior" of L_p strictly between c and a):
      -- this is a subset of L_p.vertices.dropLast (just c and a's path; but L_p has length ≥ 1
      -- so dropLast excludes only the last = a; tail.dropLast excludes the first = c too).
      -- Yes, L_p.vertices.tail.dropLast ⊆ L_p.vertices.dropLast.
      -- Also L_p.vertices.tail.dropLast ⊆ p.vertices.tail.dropLast (by mem_interior_of_arm_source).
      -- So interior of L_p is in S ∪ T.
      have hL_p_inter_ST : ∀ x ∈ L_p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
        intro x hx
        -- x ∈ L_p.tail.dropLast → x ∈ L_p.tail (mem_of_mem_dropLast) → x ∈ L_p.vertices.
        have h_x_in_L_p_tail : x ∈ L_p.vertices.tail := List.mem_of_mem_dropLast hx
        have h_x_in_L_p : x ∈ L_p.vertices := List.mem_of_mem_tail h_x_in_L_p_tail
        -- x ∈ L_p.tail.dropLast → x ∈ L_p.dropLast (use the lemma that tail.dropLast ⊆ dropLast).
        -- For L_p.length ≥ 1: L_p.dropLast = source :: L_p.tail.dropLast (when L_p.tail nonempty).
        -- So x ∈ L_p.tail.dropLast → x ∈ L_p.dropLast.
        have h_L_p_t_ne : L_p.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos L_p hL_p_pos
        have h_L_p_drop_eq : L_p.vertices.dropLast = c :: L_p.vertices.tail.dropLast := by
          conv_lhs => rw [Walk.vertices_eq_head_cons_tail L_p]
          exact List.dropLast_cons_of_ne_nil h_L_p_t_ne
        have h_x_in_L_p_drop : x ∈ L_p.vertices.dropLast := by
          rw [h_L_p_drop_eq]; exact List.mem_cons_of_mem _ hx
        have h_x_in_p_tail : x ∈ p.vertices.tail := hL_p_drop_sub x h_x_in_L_p_drop
        have h_x_in_p_drop : x ∈ p.vertices.dropLast := hL_p_sub x h_x_in_L_p
        have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
          mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
        exact hp_inter_ST x h_x_in_p_inter
      have hR_p_inter_ST : ∀ x ∈ R_p.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
        intro x hx
        have h_x_in_R_p_tail : x ∈ R_p.vertices.tail := List.mem_of_mem_dropLast hx
        have h_x_in_R_p : x ∈ R_p.vertices := List.mem_of_mem_tail h_x_in_R_p_tail
        have h_R_p_t_ne : R_p.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos R_p hR_p_pos
        have h_R_p_drop_eq : R_p.vertices.dropLast = c :: R_p.vertices.tail.dropLast := by
          conv_lhs => rw [Walk.vertices_eq_head_cons_tail R_p]
          exact List.dropLast_cons_of_ne_nil h_R_p_t_ne
        have h_x_in_R_p_drop : x ∈ R_p.vertices.dropLast := by
          rw [h_R_p_drop_eq]; exact List.mem_cons_of_mem _ hx
        have h_x_in_p_drop : x ∈ p.vertices.dropLast := hR_p_drop_sub x h_x_in_R_p_drop
        have h_x_in_p_tail : x ∈ p.vertices.tail := hR_p_sub x h_x_in_R_p
        have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
          mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
        exact hp_inter_ST x h_x_in_p_inter
      -- Case-split on c ∈ S or not.
      by_cases hc_S : c ∈ S
      · -- c ∈ S.  Apply find_first_non_W_directed S on L_p and R_p.
        obtain ⟨vL_exit, L_W_seg, L_marg_seg, hL_W_dir, hL_marg_dir, hL_W_pos,
                hvL_exit_notS, hL_W_inter, _, hL_p_vs_eq⟩ :=
          find_first_non_W_directed S L_p hL_p_dir hL_p_pos ha_notS
        obtain ⟨vR_exit, R_W_seg, R_marg_seg, hR_W_dir, hR_marg_dir, hR_W_pos,
                hvR_exit_notS, hR_W_inter, _, hR_p_vs_eq⟩ :=
          find_first_non_W_directed S R_p hR_p_dir hR_p_pos hb_notS
        have hvL_exit_GV : vL_exit ∈ G.V :=
          Walk.target_in_GV_of_directedWalk_pos L_W_seg hL_W_dir hL_W_pos
        have hvR_exit_GV : vR_exit ∈ G.V :=
          Walk.target_in_GV_of_directedWalk_pos R_W_seg hR_W_dir hR_W_pos
        have hvL_exit_VS : vL_exit ∈ G.V \ S :=
          Finset.mem_sdiff.mpr ⟨hvL_exit_GV, hvL_exit_notS⟩
        have hvR_exit_VS : vR_exit ∈ G.V \ S :=
          Finset.mem_sdiff.mpr ⟨hvR_exit_GV, hvR_exit_notS⟩
        have hvL_exit_marg : vL_exit ∈ G.marginalize S hS := by
          change vL_exit ∈ G.J ∪ (G.V \ S)
          exact Finset.mem_union_right _ hvL_exit_VS
        have hvR_exit_marg : vR_exit ∈ G.marginalize S hS := by
          change vR_exit ∈ G.J ∪ (G.V \ S)
          exact Finset.mem_union_right _ hvR_exit_VS
        -- L_marg_seg : Walk G vL_exit a, directed; its vertices ⊆ L_p.vertices.
        -- Similar for R_marg_seg.
        have hL_marg_ne : L_marg_seg.vertices ≠ [] := Walk.vertices_ne_nil L_marg_seg
        have hR_marg_ne : R_marg_seg.vertices ≠ [] := Walk.vertices_ne_nil R_marg_seg
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
        -- Interior of L_marg_seg ⊆ S ∪ T (by tracing back through L_p_inter_ST etc.)
        have hL_marg_inter_ST :
            ∀ x ∈ L_marg_seg.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
          intro x hx
          have h_t : x ∈ L_marg_seg.vertices.tail := List.mem_of_mem_dropLast hx
          have h_v : x ∈ L_marg_seg.vertices := List.mem_of_mem_tail h_t
          have h_L_p : x ∈ L_p.vertices := hL_marg_sub_L_p x h_v
          have h_x_p_drop : x ∈ p.vertices.dropLast := hL_p_sub x h_L_p
          -- For h_drop: x ∈ L_marg_seg.dropLast.
          -- We have L_marg_seg.tail.dropLast ⊆ L_marg_seg.dropLast when L_marg_seg.length ≥ 1.
          -- L_marg_seg.length = 0 → L_marg_seg.tail.dropLast = [].  hx is vacuous.
          by_cases h_L_marg_pos : L_marg_seg.length ≥ 1
          · have h_t_ne : L_marg_seg.vertices.tail ≠ [] :=
              Walk.tail_vertices_ne_nil_of_pos L_marg_seg h_L_marg_pos
            have h_drop_eq : L_marg_seg.vertices.dropLast
                = vL_exit :: L_marg_seg.vertices.tail.dropLast := by
              conv_lhs => rw [Walk.vertices_eq_head_cons_tail L_marg_seg]
              exact List.dropLast_cons_of_ne_nil h_t_ne
            have h_drop : x ∈ L_marg_seg.vertices.dropLast := by
              rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
            have h_L_p_drop : x ∈ L_p.vertices.dropLast :=
              hL_marg_drop_sub_L_p_drop x h_drop
            have h_x_p_tail : x ∈ p.vertices.tail := hL_p_drop_sub x h_L_p_drop
            have h_x_p_inter : x ∈ p.vertices.tail.dropLast :=
              mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
            exact hp_inter_ST x h_x_p_inter
          · have h_L_marg_zero : L_marg_seg.length = 0 := by omega
            -- L_marg_seg.length = 0 → L_marg_seg = nil → L_marg_seg.vertices.tail = [].
            -- So tail.dropLast = []. Contradiction with hx.
            match L_marg_seg, h_L_marg_zero with
            | .nil _ _, _ => simp [Walk.vertices, List.tail] at hx
        have hR_marg_inter_ST :
            ∀ x ∈ R_marg_seg.vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
          intro x hx
          have h_t : x ∈ R_marg_seg.vertices.tail := List.mem_of_mem_dropLast hx
          have h_v : x ∈ R_marg_seg.vertices := List.mem_of_mem_tail h_t
          have h_R_p : x ∈ R_p.vertices := hR_marg_sub_R_p x h_v
          have h_x_p_tail : x ∈ p.vertices.tail := hR_p_sub x h_R_p
          by_cases h_R_marg_pos : R_marg_seg.length ≥ 1
          · have h_t_ne : R_marg_seg.vertices.tail ≠ [] :=
              Walk.tail_vertices_ne_nil_of_pos R_marg_seg h_R_marg_pos
            have h_drop_eq : R_marg_seg.vertices.dropLast
                = vR_exit :: R_marg_seg.vertices.tail.dropLast := by
              conv_lhs => rw [Walk.vertices_eq_head_cons_tail R_marg_seg]
              exact List.dropLast_cons_of_ne_nil h_t_ne
            have h_drop : x ∈ R_marg_seg.vertices.dropLast := by
              rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
            have h_R_p_drop : x ∈ R_p.vertices.dropLast :=
              hR_marg_drop_sub_R_p_drop x h_drop
            have h_x_p_drop : x ∈ p.vertices.dropLast := hR_p_drop_sub x h_R_p_drop
            have h_x_p_inter : x ∈ p.vertices.tail.dropLast :=
              mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
            exact hp_inter_ST x h_x_p_inter
          · have h_R_marg_zero : R_marg_seg.length = 0 := by omega
            match R_marg_seg, h_R_marg_zero with
            | .nil _ _, _ => simp [Walk.vertices, List.tail] at hx
        -- Vertex bounds for L_marg_seg, R_marg_seg.
        have ha_notin_L_marg_drop : a ∉ L_marg_seg.vertices.dropLast := fun h_in =>
          ha_notin_L_p_drop (hL_marg_drop_sub_L_p_drop a h_in)
        have ha_notin_R_marg : a ∉ R_marg_seg.vertices := fun h_in =>
          ha_notin_R_p (hR_marg_sub_R_p a h_in)
        have hb_notin_L_marg : b ∉ L_marg_seg.vertices := fun h_in =>
          hb_notin_L_p (hL_marg_sub_L_p b h_in)
        have hb_notin_R_marg_drop : b ∉ R_marg_seg.vertices.dropLast := fun h_in =>
          hb_notin_R_p_drop (hR_marg_drop_sub_R_p_drop b h_in)
        by_cases hvL_vR_exit_eq : vL_exit = vR_exit
        · -- Degenerate β = γ.  Build sourced marg-bif with source β.
          subst hvL_vR_exit_eq
          have hvL_exit_ne_a : vL_exit ≠ a := by
            intro heq
            have h_in : vL_exit ∈ R_p.vertices :=
              hR_marg_sub_R_p _ (Walk.head_mem_vertices R_marg_seg)
            have h_p_tail : vL_exit ∈ p.vertices.tail := hR_p_sub _ h_in
            exact ha_p_tail (heq ▸ h_p_tail)
          have hvL_exit_ne_b : vL_exit ≠ b := by
            intro heq
            have h_in : vL_exit ∈ L_p.vertices :=
              hL_marg_sub_L_p _ (Walk.head_mem_vertices L_marg_seg)
            have h_p_drop : vL_exit ∈ p.vertices.dropLast := hL_p_sub _ h_in
            exact hb_p_drop (heq ▸ h_p_drop)
          have hL_marg_pos : L_marg_seg.length ≥ 1 :=
            Walk.length_pos_of_ne L_marg_seg hvL_exit_ne_a
          have hR_marg_pos : R_marg_seg.length ≥ 1 :=
            Walk.length_pos_of_ne R_marg_seg hvL_exit_ne_b
          -- Project L_marg_seg and R_marg_seg to marg with interior in T AND vertex tracking.
          obtain ⟨L_marg, hL_marg_dir', hL_marg_pos', hL_marg_vs_sub, hL_marg_drop_sub,
                  hL_marg_tail_sub, hL_marg_inter_T⟩ :=
            project_walk_marg_full (S := S) (T := T) (hS := hS)
              L_marg_seg hL_marg_dir hL_marg_pos hvL_exit_marg ha_marg
              hL_marg_inter_ST
          obtain ⟨R_marg, hR_marg_dir', hR_marg_pos', hR_marg_vs_sub, hR_marg_drop_sub,
                  hR_marg_tail_sub, hR_marg_inter_T⟩ :=
            project_walk_marg_full (S := S) (T := T) (hS := hS)
              R_marg_seg hR_marg_dir hR_marg_pos hvL_exit_marg hb_marg
              hR_marg_inter_ST
          -- Vertex bounds for L_marg, R_marg in marg.
          have ha_notin_L_marg' : a ∉ L_marg.vertices.dropLast := fun h_in =>
            ha_notin_L_marg_drop (hL_marg_drop_sub a h_in)
          have ha_notin_R_marg' : a ∉ R_marg.vertices := fun h_in =>
            ha_notin_R_marg (hR_marg_vs_sub a h_in)
          have hb_notin_L_marg' : b ∉ L_marg.vertices := fun h_in =>
            hb_notin_L_marg (hL_marg_vs_sub b h_in)
          have hb_notin_R_marg_drop' : b ∉ R_marg.vertices.dropLast := fun h_in =>
            hb_notin_R_marg_drop (hR_marg_drop_sub b h_in)
          -- Build mkBifurcation L_marg R_marg.
          refine ⟨Walk.mkBifurcation L_marg hL_marg_dir' hL_marg_pos' R_marg, ?_, ?_⟩
          · have h_src := Walk.mkBifurcation_isBifurcationSource
              L_marg hL_marg_dir' hL_marg_pos' R_marg hR_marg_dir' hR_marg_pos'
              hab_ne ha_notin_L_marg' ha_notin_R_marg' hb_notin_L_marg' hb_notin_R_marg_drop'
            exact Walk.isBifurcationSource_to_isBifurcation _ vL_exit h_src
          · intro x hx
            rw [vertices_tail_dropLast_mkBifurcation
                  L_marg hL_marg_dir' hL_marg_pos' R_marg hR_marg_pos'] at hx
            rcases List.mem_append.mp hx with hx_L | hx_R
            · rw [List.mem_reverse] at hx_L
              exact hL_marg_inter_T x hx_L
            · -- x ∈ R_marg.vertices.dropLast.  R_marg starts at vL_exit (the source).
              have h_R_t_ne : R_marg.vertices.tail ≠ [] :=
                Walk.tail_vertices_ne_nil_of_pos R_marg hR_marg_pos'
              rw [Walk.vertices_eq_head_cons_tail R_marg,
                  List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R
              rcases List.mem_cons.mp hx_R with rfl | hx_inner
              · -- x = vL_exit (= source post-subst). Need x ∈ T.
                -- Note: `rcases ... with rfl` substituted vL_exit → x, so
                -- the surviving name is `x` and hypotheses `hvL_exit_*` now
                -- have their types phrased in terms of `x`.
                have h_x_in_L_p : x ∈ L_p.vertices :=
                  hL_marg_sub_L_p _ (Walk.head_mem_vertices L_marg_seg)
                have h_x_in_p_drop : x ∈ p.vertices.dropLast :=
                  hL_p_sub _ h_x_in_L_p
                have h_x_in_R_p : x ∈ R_p.vertices :=
                  hR_marg_sub_R_p _ (Walk.head_mem_vertices R_marg_seg)
                have h_x_in_p_tail : x ∈ p.vertices.tail :=
                  hR_p_sub _ h_x_in_R_p
                have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
                  mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
                rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
                · exact absurd h_S hvL_exit_notS
                · exact h_T
              · exact hR_marg_inter_T x hx_inner
        · -- Non-degenerate β ≠ γ.  Build marg.L edge (vL_exit, vR_exit), then mkBifurcationBidir.
          exact backward_marg_to_g_bif_dir_hinge_cInS_betaNeGamma_one_orientation
            S T hS ha_VST hb_VST ha_marg hb_marg
            ⟨hab_ne, ha_p_tail, hb_p_drop, i, hp_split⟩ hp_inter hc_S
            hL_p_dir hR_p_dir hL_p_pos hR_p_pos
            hL_p_sub hR_p_sub hL_p_drop_sub hR_p_drop_sub
            hL_W_dir hL_marg_dir hL_W_pos hvL_exit_notS hL_W_inter hL_p_vs_eq
            hR_W_dir hR_marg_dir hR_W_pos hvR_exit_notS hR_W_inter hR_p_vs_eq
            hvL_vR_exit_eq
      · -- c ∉ S.  c ∈ G.marginalize, so c stays as the marg-bif source.
        -- Mirrors the c ∈ S β = γ case above, minus the
        -- `find_first_non_W_directed` step: L_p / R_p project to marg
        -- directly via `project_walk_marg_full` because c is already
        -- a marg vertex.
        have hc_in_G : c ∈ G :=
          Walk.source_in_G_of_directedWalk_pos L_p hL_p_dir hL_p_pos
        have hc_marg : c ∈ G.marginalize S hS := by
          change c ∈ G.J ∪ (G.V \ S)
          rcases Finset.mem_union.mp hc_in_G with hc_J | hc_V
          · exact Finset.mem_union_left _ hc_J
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hc_V, hc_S⟩)
        -- Project L_p and R_p to marg.
        obtain ⟨L_marg, hL_marg_dir', hL_marg_pos', hL_marg_vs_sub, hL_marg_drop_sub,
                _, hL_marg_inter_T⟩ :=
          project_walk_marg_full (S := S) (T := T) (hS := hS)
            L_p hL_p_dir hL_p_pos hc_marg ha_marg hL_p_inter_ST
        obtain ⟨R_marg, hR_marg_dir', hR_marg_pos', hR_marg_vs_sub, hR_marg_drop_sub,
                _, hR_marg_inter_T⟩ :=
          project_walk_marg_full (S := S) (T := T) (hS := hS)
            R_p hR_p_dir hR_p_pos hc_marg hb_marg hR_p_inter_ST
        -- Vertex bounds for L_marg, R_marg in marg.
        have ha_notin_L_marg : a ∉ L_marg.vertices.dropLast := fun h_in =>
          ha_notin_L_p_drop (hL_marg_drop_sub a h_in)
        have ha_notin_R_marg : a ∉ R_marg.vertices := fun h_in =>
          ha_notin_R_p (hR_marg_vs_sub a h_in)
        have hb_notin_L_marg : b ∉ L_marg.vertices := fun h_in =>
          hb_notin_L_p (hL_marg_vs_sub b h_in)
        have hb_notin_R_marg_drop : b ∉ R_marg.vertices.dropLast := fun h_in =>
          hb_notin_R_p_drop (hR_marg_drop_sub b h_in)
        -- Build mkBifurcation L_marg R_marg.
        refine ⟨Walk.mkBifurcation L_marg hL_marg_dir' hL_marg_pos' R_marg, ?_, ?_⟩
        · have h_src := Walk.mkBifurcation_isBifurcationSource
            L_marg hL_marg_dir' hL_marg_pos' R_marg hR_marg_dir' hR_marg_pos'
            hab_ne ha_notin_L_marg ha_notin_R_marg hb_notin_L_marg hb_notin_R_marg_drop
          exact Walk.isBifurcationSource_to_isBifurcation _ c h_src
        · intro x hx
          rw [vertices_tail_dropLast_mkBifurcation
                L_marg hL_marg_dir' hL_marg_pos' R_marg hR_marg_pos'] at hx
          rcases List.mem_append.mp hx with hx_L | hx_R
          · rw [List.mem_reverse] at hx_L
            exact hL_marg_inter_T x hx_L
          · -- x ∈ R_marg.vertices.dropLast.  R_marg starts at c (the source).
            have h_R_t_ne : R_marg.vertices.tail ≠ [] :=
              Walk.tail_vertices_ne_nil_of_pos R_marg hR_marg_pos'
            rw [Walk.vertices_eq_head_cons_tail R_marg,
                List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R
            rcases List.mem_cons.mp hx_R with rfl | hx_inner
            · -- x = c (head of R_marg).  Need x ∈ T.
              -- `c ∉ S` plus `c ∈ p.vertices.tail.dropLast` (via the
              -- standard L_p / R_p arm-source argument) lets us conclude
              -- `c ∈ T` from `hp_inter_ST`.
              have h_x_in_L_p : x ∈ L_p.vertices := Walk.head_mem_vertices L_p
              have h_x_in_p_drop : x ∈ p.vertices.dropLast :=
                hL_p_sub _ h_x_in_L_p
              have h_x_in_R_p : x ∈ R_p.vertices := Walk.head_mem_vertices R_p
              have h_x_in_p_tail : x ∈ p.vertices.tail :=
                hR_p_sub _ h_x_in_R_p
              have h_x_in_p_inter : x ∈ p.vertices.tail.dropLast :=
                mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
              rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
              · exact absurd h_S hc_S
              · exact h_T
            · exact hR_marg_inter_T x hx_inner
    · -- Bidirected hinge in p.  Delegate to the lifted top-level helper.
      exact backward_marg_to_g_bif_bidir_hinge_one_orientation S T hS
        ha_VST hb_VST ha_marg hb_marg p ⟨hab_ne, ha_p_tail, hb_p_drop, i, hp_split⟩
        hp_inter i hp_split h_dir
  -- Symmetry: hv comes with G.V \ (S ∪ T), so swapped roles work.
  constructor
  · -- (⟹) marg.Φ_L T → G.Φ_L (S∪T).
    rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · obtain ⟨q, hq_bif, hq_inter⟩ :=
        forward_one_orientation hu hv hu_marg hv_marg p hp_bif hp_inter
      exact Or.inl ⟨q, hq_bif, hq_inter⟩
    · obtain ⟨q, hq_bif, hq_inter⟩ :=
        forward_one_orientation hv hu hv_marg hu_marg p hp_bif hp_inter
      exact Or.inr ⟨q, hq_bif, hq_inter⟩
  · -- (⟸) G.Φ_L (S∪T) → marg.Φ_L T.
    rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · obtain ⟨q, hq_bif, hq_inter⟩ :=
        backward_one_orientation hu hv hu_marg hv_marg p hp_bif hp_inter
      exact Or.inl ⟨q, hq_bif, hq_inter⟩
    · obtain ⟨q, hq_bif, hq_inter⟩ :=
        backward_one_orientation hv hu hv_marg hu_marg p hp_bif hp_inter
      exact Or.inr ⟨q, hq_bif, hq_inter⟩

private lemma marg_L_field_eq {G : CDMG Node} (S T : Finset Node)
    (hS : S ⊆ G.V) (hT : T ⊆ G.V) (hDisj : Disjoint S T) :
    ((G.marginalize S hS).marginalize T
        (subset_sdiff_of_disjoint hT hDisj.symm)).L
      = (G.marginalize (S ∪ T) (Finset.union_subset hS hT)).L := by
  change (((G.V \ S) \ T) ×ˢ ((G.V \ S) \ T)).filter
          (fun e => e.1 ≠ e.2 ∧ (G.marginalize S hS).MarginalizationΦL T e.1 e.2)
        = ((G.V \ (S ∪ T)) ×ˢ (G.V \ (S ∪ T))).filter
          (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL (S ∪ T) e.1 e.2)
  have h_sd : (G.V \ S) \ T = G.V \ (S ∪ T) := sdiff_sdiff_left
  rw [h_sd]
  apply Finset.filter_congr
  intro e he
  rw [Finset.mem_product] at he
  refine and_congr Iff.rfl ?_
  exact marg_PhiL_iff S T hS hT hDisj he.1 he.2

-- ref: claim_3_17
-- For any CDMG `G : CDMG Node`, any two subsets `W₁, W₂ ⊆ G.V` with
-- `Disjoint W₁ W₂`, the LN's triple equality
--   `(G^{∖W₁})^{∖W₂} = (G^{∖W₂})^{∖W₁} = G^{∖(W₁ ∪ W₂)}`
-- decomposes into two binary CDMG equalities:
--   (a) `(G.marginalize W₁ hW₁).marginalize W₂ … =
--         G.marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)`,
--   (b) `(G.marginalize W₂ hW₂).marginalize W₁ … =
--         G.marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)`.
-- Transitivity of equality then recovers the LN's "swap symmetry"
-- `(G.marginalize W₁ hW₁).marginalize W₂ … =
--  (G.marginalize W₂ hW₂).marginalize W₁ …` from (a) ∧ (b).
/-
LN tex (rewritten canonical statement for `claim_3_17`, in essence):

  Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ V` with
  `W₁ ∩ W₂ = ∅`.  Then
    (a) `(G^{∖W₁})^{∖W₂} = G^{∖(W₁ ∪ W₂)}`,
    (b) `(G^{∖W₂})^{∖W₁} = G^{∖(W₁ ∪ W₂)}`.

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ V` two disjoint
  subsets of output nodes.  Then we have:
    `(G^{∖W₁})^{∖W₂} = (G^{∖W₂})^{∖W₁} = G^{∖(W₁ ∪ W₂)}`.
-/
-- ## Design choice
--
-- *One theorem returning a conjunction (Option A from the worker
--   prompt), not two separate top-level theorems.*  The LN's
--   `\begin{Lem}` block is one lemma joining three CDMGs in a triple
--   equality `A = B = C`; the rewritten canonical statement file
--   explicitly decomposes this into the conjunction of two binary
--   equalities (a) `A = C` and (b) `B = C`.  Lean has no native
--   triple-equality syntax, so a single theorem returning
--   `(a) ∧ (b)` is the literal Lean rendering, mirroring the
--   rewrite's decomposition.  Consumers reach `.1` for (a) and `.2`
--   for (b); the LN's "swap symmetry" reading
--   `(G.marginalize W₁ hW₁).marginalize W₂ … =
--    (G.marginalize W₂ hW₂).marginalize W₁ …` is recovered as
--   `.1.trans .2.symm` (so no separate `A = B` sub-claim is needed —
--   transitivity of `=` does it for free, as the rewrite's closing
--   remark licenses).  Splitting into two named theorems was
--   rejected because it would (i) duplicate the antecedents `hW₁`,
--   `hW₂`, `hDisj` at the theorem-head level, and (ii) diverge from
--   the rewrite's single-lemma packaging.  Matches the sibling
--   pattern in `HardInterventionsCommute.lean` (`claim_3_4`), which
--   also packages its two sub-claims as a single theorem returning
--   a conjunction.
--
-- *Conjunction order (a) ∧ (b), matching the rewrite and the LN
--   reading order.*  The rewrite's `enumerate[label=(\alph*)]` block
--   lists (a) `W₁`-then-`W₂` first, (b) `W₂`-then-`W₁` second; we
--   preserve that order in the Lean conjunction so the natural `.1`
--   / `.2` projections line up with the (a) / (b) labels of the
--   rewrite.
--
-- *Right-hand side `G.marginalize (W₁ ∪ W₂) (Finset.union_subset
--   hW₁ hW₂)`, with the union-subset proof term inlined.*  The proof
--   term `Finset.union_subset hW₁ hW₂ : W₁ ∪ W₂ ⊆ G.V` is a mathlib
--   one-liner not worth a named helper; both sub-claims share the
--   same right-hand side and the same proof term, so the conjunction
--   reads with literal `=`-symmetry between (a) and (b).  Note the
--   *joint* marginalisation does not consume `hDisj` — the LN-tex's
--   "Well-typedness" paragraph flagged that disjointness is needed
--   only for the iterated forms.
--
-- *Inner-`hW` for the nested marginalisations via
--   `subset_sdiff_of_disjoint`.*  The outer `.marginalize W₂` (in
--   (a)) and `.marginalize W₁` (in (b)) need a subset proof against
--   the carrier `(G.marginalize Wᵢ hWᵢ).V = G.V \ Wᵢ` of the
--   inner-marginalised CDMG, not against `G.V`.  The helper lemma
--   `subset_sdiff_of_disjoint` transports the hypothesis across the
--   carrier identity that the rewritten tex's "Well-typedness"
--   paragraph proves verbatim.  Inlining a `by`-block in the type
--   was rejected because it would (i) bloat the rendered statement
--   on the website, and (ii) duplicate the carrier-matching
--   reasoning at every use site.
--
-- *Three independent theorem hypotheses `hW₁ : W₁ ⊆ G.V`, `hW₂ : W₂
--   ⊆ G.V`, `hDisj : Disjoint W₁ W₂`, NOT two derived-subset proofs
--   (e.g. `hW₁ : W₁ ⊆ G.V` and `hW₂' : W₂ ⊆ G.V \ W₁`) baked into
--   the binders.*  The LN's premise block lists three independent
--   facts ("$W_1 \ins V$", "$W_2 \ins V$", "$W_1 \cap W_2 =
--   \emptyset$"), and the rewritten tex's "Well-typedness" paragraph
--   factors the typing precondition for the inner-`W₂` argument
--   exactly into the conjunction of `W₂ ⊆ G.V` and disjointness.
--   Baking the derived subset `W₂ ⊆ G.V \ W₁` into the binder would
--   (i) conflate the LN's clean premise list with an internal
--   calculation about `marginalize`'s domain, (ii) force every call
--   site to discharge the less-natural fact `W₂ ⊆ G.V \ W₁`
--   (downstream consumers will almost always have `W₂ ⊆ G.V` plus
--   disjointness, not the conjoined sdiff-subset on a plate), and
--   (iii) break the LN-level symmetry between the `W₁`-then-`W₂`
--   and `W₂`-then-`W₁` readings — one binder would carry
--   `W₂ ⊆ G.V \ W₁`, the other would need `W₁ ⊆ G.V \ W₂`, doubling
--   the derived plumbing.  The derived subset proofs are instead
--   supplied *at the marginalisation call sites inside the
--   signature* via `subset_sdiff_of_disjoint hW₂ hDisj.symm` and
--   `subset_sdiff_of_disjoint hW₁ hDisj`, keeping the theorem-head
--   binder list isomorphic to the LN's premise list.
--
-- *`Disjoint W₁ W₂`, not `W₁ ∩ W₂ = ∅`.*  The two are equivalent on
--   `Finset Node` (`Finset.disjoint_iff_inter_eq_empty`).  We pick
--   the `Disjoint`-typeclass form because (i) mathlib's
--   `Finset.subset_sdiff` is phrased against `Disjoint`, so the
--   helper lemma `subset_sdiff_of_disjoint` consumes it directly
--   without a wrapper rewrite, and (ii) `Disjoint` is the canonical
--   shape used everywhere in chapter 3 (`def_3_1`'s `hJV_disj`,
--   `def_3_14`'s `marginalize_hJV_disj`, the sibling
--   `claim_3_8`/`claim_3_11` disjoint-intervention rows).  The
--   semantic content is identical to the LN's literal "$W_1 \cap
--   W_2 = \emptyset$".
--
-- *CDMG equality (`=`) is read field-wise.*  Equality of two `CDMG`s
--   unfolds via the `structure` injectivity from `def_3_1` to the
--   conjunction of equalities on the four data fields `J`, `V`, `E`,
--   `L` (the five propositional fields of `def_3_1` are
--   propositional and Lean's proof irrelevance discharges them
--   automatically).  We do not bake the field-wise unpacking into
--   the *statement*; it is deferred to the proof per the rewritten
--   tex's closing remark "the conjunctive unpacking into the four
--   field-by-field equalities is deferred to the proof".
--
-- *`W₁` / `W₂` and `hW₁` / `hW₂` quantified at the theorem head,
--   matching `marginalize`'s binder convention.*  `def_3_14`
--   (`MarginalizationAK.lean`) takes `(W : Finset Node) (hW : W ⊆
--   G.V)` as explicit arguments; we reuse the same shape so call
--   sites `G.marginalize Wᵢ hWᵢ` parse identically here and at every
--   downstream consumer.  The binder shape
--   `(G : CDMG Node) (W₁ W₂ : Finset Node) (hW₁ hW₂ : … ⊆ G.V)
--    (hDisj : Disjoint W₁ W₂)` is a direct echo of `def_3_14`'s
--   signature with `W` / `hW` replicated for the two marginalisation
--   sets plus the disjointness rider that makes the iterated forms
--   well-typed.
--
-- *Degenerate cases admitted.*  All three quantifiers are read
--   universally; the (vacuously disjoint) degenerate cases
--   `W₁ = W₂ = ∅`, `W₁ = ∅` alone, and `W₂ = ∅` alone are all
--   admitted by this signature.  In each case the triple equality
--   collapses (e.g.\ `W₁ = W₂ = ∅` reduces to `G = G = G`); the
--   theorem remains true and the signature does not pre-emptively
--   exclude them.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize_comm
-- claim_3_17 -- start statement
theorem marginalize_comm (G : CDMG Node) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    (G.marginalize W₁ hW₁).marginalize W₂
        (subset_sdiff_of_disjoint hW₂ hDisj.symm)
      = G.marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)
    ∧
    (G.marginalize W₂ hW₂).marginalize W₁
        (subset_sdiff_of_disjoint hW₁ hDisj)
      = G.marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)
-- claim_3_17 -- end statement
:= by
  -- ## CDMG extensionality.
  have cdmgExt : ∀ {G₁ G₂ : CDMG Node},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨J₁, V₁, _, E₁, _, L₁, _, _, _⟩
           ⟨J₂, V₂, _, E₂, _, L₂, _, _, _⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL; rfl
  -- ## L-field equality.
  have hL_field_eq : ∀ (S T : Finset Node) (hS : S ⊆ G.V) (hT : T ⊆ G.V)
      (hDisj_ST : Disjoint S T),
      ((G.marginalize S hS).marginalize T
          (subset_sdiff_of_disjoint hT hDisj_ST.symm)).L
        = (G.marginalize (S ∪ T) (Finset.union_subset hS hT)).L := by
    intro S T hS hT hDisj_ST
    exact marg_L_field_eq S T hS hT hDisj_ST
  refine ⟨?_, ?_⟩
  · refine cdmgExt rfl ?_ ?_ ?_
    · exact sdiff_sdiff_left
    · exact marg_E_field_eq W₁ W₂ hW₁ hW₂ hDisj
    · exact hL_field_eq W₁ W₂ hW₁ hW₂ hDisj
  · -- (b): apply the auxiliaries with the roles of W₁/W₂ swapped.
    have heq : G.marginalize (W₂ ∪ W₁) (Finset.union_subset hW₂ hW₁)
             = G.marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂) := by
      congr 1
      exact Finset.union_comm W₂ W₁
    refine cdmgExt rfl ?_ ?_ ?_
    · change (G.V \ W₂) \ W₁ = G.V \ (W₁ ∪ W₂)
      rw [Finset.union_comm W₁ W₂]
      exact sdiff_sdiff_left
    · have h := marg_E_field_eq W₂ W₁ hW₂ hW₁ hDisj.symm
      rw [heq] at h
      exact h
    · have h := hL_field_eq W₂ W₁ hW₂ hW₁ hDisj.symm
      rw [heq] at h
      exact h
-- REFACTOR-BLOCK-ORIGINAL-END: marginalize_comm

end CDMG

namespace refactor_CDMG

-- ## Refactor replacements — Phase A (variable + subset_sdiff_of_disjoint)
--
-- Each replacement below is paired (where applicable) with the
-- corresponding original above via the same-file
-- `REFACTOR-BLOCK-ORIGINAL` / `REFACTOR-BLOCK-REPLACEMENT` marker
-- convention.  Identifiers are prefixed `refactor_*` so the
-- replacements coexist with the originals during the refactor window;
-- the Phase 7 cleanup script renames `refactor_<Name>` → `<Name>`
-- globally and strips the markers.
--
-- The variable line is a net-new (no paired ORIGINAL) marker block —
-- the namespace is freshly opened so the outer `Causality.CDMG`
-- `variable` does not propagate here.  `subset_sdiff_of_disjoint` is
-- a pure-`Finset` helper with no `CDMG` / `Walk` dependency; the body
-- is identical modulo the `refactor_` prefix.

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: variable_Node (was: refactor_variable_Node)
-- claim_3_17 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_17 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: variable_Node

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: subset_sdiff_of_disjoint (was: refactor_subset_sdiff_of_disjoint)
-- claim_3_17 --- start helper
private lemma refactor_subset_sdiff_of_disjoint {S T : Finset Node}
    {U : Finset Node} (hS : S ⊆ U) (hDisj : Disjoint S T) :
    S ⊆ U \ T
-- claim_3_17 --- end helper
:= Finset.subset_sdiff.mpr ⟨hS, hDisj⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: subset_sdiff_of_disjoint

-- ## Refactor replacements — Phase B (E-field machinery, 8 lemmas)
--
-- All E-field only — no L-field references — so the ports are
-- structural renames + the `WalkStep`-construction rewrite
-- (`Or.inl ⟨rfl, Or.inl h_edge⟩` → `.forwardE h_edge`) plus the
-- corresponding `Walk.cons` argument-arity drop (4-arg → 3-arg) and
-- the `IsDirectedWalk`-witness simplification (the cons-cell's
-- `refactor_IsDirectedWalk` on a `.forwardE` step reduces
-- definitionally to the tail's `refactor_IsDirectedWalk`, so the
-- triple `⟨rfl, h_edge, hq_tail_dir⟩` collapses to `hq_tail_dir`).
-- All walk-algebra and marg-membership helpers come from
-- `MargPreservesAncestors.lean` (`refactor_find_first_non_W_directed`,
-- `refactor_Walk.refactor_target_in_GV_of_directedWalk_pos`,
-- `refactor_Walk.refactor_vertices_eq_head_cons_tail`,
-- `refactor_Walk.refactor_tail_vertices_ne_nil_of_pos`,
-- `refactor_Walk.refactor_vertices_ne_nil`,
-- `refactor_Walk.refactor_head_mem_vertices`,
-- `refactor_expand_directed_walk_marginalize`,
-- `refactor_notW_of_mem_marginalize`).

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: project_walk_marg_with_interior_aux (was: refactor_project_walk_marg_with_interior_aux)
private lemma refactor_project_walk_marg_with_interior_aux
    {G : refactor_CDMG Node} {S T : Finset Node} {hS : S ⊆ G.V} :
    ∀ (n : ℕ) {u v : Node} (p : refactor_Walk G u v),
      p.refactor_length ≤ n →
      p.refactor_IsDirectedWalk → p.refactor_length ≥ 1 →
      u ∈ G.refactor_marginalize S hS → v ∈ G.refactor_marginalize S hS →
      (∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T) →
      ∃ (q : refactor_Walk (G.refactor_marginalize S hS) u v),
        q.refactor_IsDirectedWalk ∧ q.refactor_length ≥ 1 ∧
        (∀ x ∈ q.refactor_vertices.tail.dropLast, x ∈ T) := by
  intro n
  induction n with
  | zero =>
      intros u v p hp_len _ hp_pos _ _ _
      omega
  | succ k ih =>
      intros u v p hp_len hp_dir hp_pos hu hv h_inter
      have hv_notS : v ∉ S := refactor_notW_of_mem_marginalize hS hv
      obtain ⟨m, head, tail, h_head_dir, h_tail_dir, h_head_pos,
              hm_notS, h_head_inter, h_lens, h_p_eq⟩ :=
        refactor_find_first_non_W_directed S p hp_dir hp_pos hv_notS
      have hm_V : m ∈ G.V :=
        refactor_Walk.refactor_target_in_GV_of_directedWalk_pos
          head h_head_dir h_head_pos
      have hm_marg : m ∈ G.refactor_marginalize S hS := by
        change m ∈ G.J ∪ (G.V \ S)
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hm_V, hm_notS⟩)
      have h_edge : (u, m) ∈ (G.refactor_marginalize S hS).E := by
        change (u, m) ∈ ((G.J ∪ (G.V \ S)) ×ˢ (G.V \ S)).filter
              (fun e => G.refactor_MarginalizationΦE S e.1 e.2)
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨hu, ?_⟩
          exact Finset.mem_sdiff.mpr ⟨hm_V, hm_notS⟩
        · exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩
      have h_head_drop_ne : head.refactor_vertices.dropLast ≠ [] := by
        rw [refactor_Walk.refactor_vertices_eq_head_cons_tail head]
        have h_h_t_ne : head.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos head h_head_pos
        rw [List.dropLast_cons_of_ne_nil h_h_t_ne]
        simp
      have h_tail_vs_ne : tail.refactor_vertices ≠ [] :=
        refactor_Walk.refactor_vertices_ne_nil tail
      by_cases h_tail_pos : tail.refactor_length ≥ 1
      · have h_tail_t_ne : tail.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos tail h_tail_pos
        have h_tail_vs :
            tail.refactor_vertices = m :: tail.refactor_vertices.tail :=
          refactor_Walk.refactor_vertices_eq_head_cons_tail tail
        have hm_in_p_int : m ∈ p.refactor_vertices.tail.dropLast := by
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne,
              List.dropLast_append_of_ne_nil h_tail_vs_ne]
          apply List.mem_append.mpr
          right
          rw [h_tail_vs, List.dropLast_cons_of_ne_nil h_tail_t_ne]
          exact List.mem_cons_self
        have hm_in_T : m ∈ T := by
          rcases h_inter m hm_in_p_int with h_S | h_T
          · exact absurd h_S hm_notS
          · exact h_T
        have h_tail_inter :
            ∀ x ∈ tail.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
          intro x hx
          apply h_inter
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne,
              List.dropLast_append_of_ne_nil h_tail_vs_ne]
          apply List.mem_append.mpr
          right
          rw [h_tail_vs, List.dropLast_cons_of_ne_nil h_tail_t_ne]
          exact List.mem_cons_of_mem _ hx
        have h_tail_len : tail.refactor_length ≤ k := by omega
        obtain ⟨q_tail, hq_tail_dir, hq_tail_pos, hq_tail_inter⟩ :=
          ih tail h_tail_len h_tail_dir h_tail_pos hm_marg hv h_tail_inter
        refine ⟨refactor_Walk.cons m (.forwardE h_edge) q_tail,
                hq_tail_dir, ?_, ?_⟩
        · change q_tail.refactor_length + 1 ≥ 1; omega
        · intro x hx
          change x ∈ (u :: q_tail.refactor_vertices).tail.dropLast at hx
          rw [List.tail_cons] at hx
          have h_qtv :
              q_tail.refactor_vertices = m :: q_tail.refactor_vertices.tail :=
            refactor_Walk.refactor_vertices_eq_head_cons_tail q_tail
          rw [h_qtv] at hx
          have h_qtt_ne : q_tail.refactor_vertices.tail ≠ [] :=
            refactor_Walk.refactor_tail_vertices_ne_nil_of_pos q_tail hq_tail_pos
          rw [List.dropLast_cons_of_ne_nil h_qtt_ne] at hx
          rcases List.mem_cons.mp hx with rfl | hx_inner
          · exact hm_in_T
          · exact hq_tail_inter x hx_inner
      · have h_tail_zero : tail.refactor_length = 0 := by omega
        match tail, h_tail_zero with
        | .nil m' hm', _ =>
            refine ⟨refactor_Walk.cons m' (.forwardE h_edge)
                      (refactor_Walk.nil m' hv),
                    trivial, ?_, ?_⟩
            · change 1 ≥ 1; omega
            · intro x hx
              change x ∈ (u :: [m'] : List Node).tail.dropLast at hx
              simp at hx
-- REFACTOR-BLOCK-REPLACEMENT-END: project_walk_marg_with_interior_aux

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: project_walk_marg_with_interior (was: refactor_project_walk_marg_with_interior)
private lemma refactor_project_walk_marg_with_interior {G : refactor_CDMG Node}
    {S T : Finset Node} {hS : S ⊆ G.V}
    {u v : Node} (p : refactor_Walk G u v)
    (hp_dir : p.refactor_IsDirectedWalk) (hp_pos : p.refactor_length ≥ 1)
    (hu : u ∈ G.refactor_marginalize S hS)
    (hv : v ∈ G.refactor_marginalize S hS)
    (h_inter : ∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T) :
    ∃ (q : refactor_Walk (G.refactor_marginalize S hS) u v),
      q.refactor_IsDirectedWalk ∧ q.refactor_length ≥ 1 ∧
      (∀ x ∈ q.refactor_vertices.tail.dropLast, x ∈ T) :=
  refactor_project_walk_marg_with_interior_aux (S := S) (T := T) (hS := hS)
    p.refactor_length p le_rfl hp_dir hp_pos hu hv h_inter
-- REFACTOR-BLOCK-REPLACEMENT-END: project_walk_marg_with_interior

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: project_walk_marg_full_aux (was: refactor_project_walk_marg_full_aux)
-- Strengthened projection: returns both vertex bounds (vertices ⊆ source's vertices,
-- and respective .dropLast / .tail bounds) AND T-interior bound.
private lemma refactor_project_walk_marg_full_aux {G : refactor_CDMG Node}
    {S T : Finset Node} {hS : S ⊆ G.V} :
    ∀ (n : ℕ) {u v : Node} (p : refactor_Walk G u v),
      p.refactor_length ≤ n →
      p.refactor_IsDirectedWalk → p.refactor_length ≥ 1 →
      u ∈ G.refactor_marginalize S hS → v ∈ G.refactor_marginalize S hS →
      (∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T) →
      ∃ (q : refactor_Walk (G.refactor_marginalize S hS) u v),
        q.refactor_IsDirectedWalk ∧ q.refactor_length ≥ 1 ∧
        (∀ x ∈ q.refactor_vertices, x ∈ p.refactor_vertices) ∧
        (∀ x ∈ q.refactor_vertices.dropLast,
          x ∈ p.refactor_vertices.dropLast) ∧
        (∀ x ∈ q.refactor_vertices.tail, x ∈ p.refactor_vertices.tail) ∧
        (∀ x ∈ q.refactor_vertices.tail.dropLast, x ∈ T) := by
  intro n
  induction n with
  | zero =>
      intros u v p hp_len _ hp_pos _ _ _
      omega
  | succ k ih =>
      intros u v p hp_len hp_dir hp_pos hu hv h_inter
      have hv_notS : v ∉ S := refactor_notW_of_mem_marginalize hS hv
      obtain ⟨m, head, tail, h_head_dir, h_tail_dir, h_head_pos,
              hm_notS, h_head_inter, h_lens, h_p_eq⟩ :=
        refactor_find_first_non_W_directed S p hp_dir hp_pos hv_notS
      have hm_V : m ∈ G.V :=
        refactor_Walk.refactor_target_in_GV_of_directedWalk_pos
          head h_head_dir h_head_pos
      have hm_marg : m ∈ G.refactor_marginalize S hS := by
        change m ∈ G.J ∪ (G.V \ S)
        exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hm_V, hm_notS⟩)
      have h_edge : (u, m) ∈ (G.refactor_marginalize S hS).E := by
        change (u, m) ∈ ((G.J ∪ (G.V \ S)) ×ˢ (G.V \ S)).filter
              (fun e => G.refactor_MarginalizationΦE S e.1 e.2)
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨hu, ?_⟩
          exact Finset.mem_sdiff.mpr ⟨hm_V, hm_notS⟩
        · exact ⟨head, h_head_dir, h_head_pos, h_head_inter⟩
      -- p.vertices = head.vertices.dropLast ++ tail.vertices.
      have h_head_drop_ne : head.refactor_vertices.dropLast ≠ [] := by
        rw [refactor_Walk.refactor_vertices_eq_head_cons_tail head]
        have h_h_t_ne : head.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos head h_head_pos
        rw [List.dropLast_cons_of_ne_nil h_h_t_ne]
        simp
      have h_tail_vs_ne : tail.refactor_vertices ≠ [] :=
        refactor_Walk.refactor_vertices_ne_nil tail
      have h_u_in_head_drop : u ∈ head.refactor_vertices.dropLast := by
        rw [refactor_Walk.refactor_vertices_eq_head_cons_tail head,
            List.dropLast_cons_of_ne_nil
              (refactor_Walk.refactor_tail_vertices_ne_nil_of_pos
                head h_head_pos)]
        exact List.mem_cons_self
      have h_m_in_tail : m ∈ tail.refactor_vertices :=
        refactor_Walk.refactor_head_mem_vertices tail
      by_cases h_tail_pos : tail.refactor_length ≥ 1
      · have h_tail_t_ne : tail.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos tail h_tail_pos
        have h_tail_vs :
            tail.refactor_vertices = m :: tail.refactor_vertices.tail :=
          refactor_Walk.refactor_vertices_eq_head_cons_tail tail
        have hm_in_p_int : m ∈ p.refactor_vertices.tail.dropLast := by
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne,
              List.dropLast_append_of_ne_nil h_tail_vs_ne]
          apply List.mem_append.mpr
          right
          rw [h_tail_vs, List.dropLast_cons_of_ne_nil h_tail_t_ne]
          exact List.mem_cons_self
        have hm_in_T : m ∈ T := by
          rcases h_inter m hm_in_p_int with h_S | h_T
          · exact absurd h_S hm_notS
          · exact h_T
        have h_tail_inter :
            ∀ x ∈ tail.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
          intro x hx
          apply h_inter
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne,
              List.dropLast_append_of_ne_nil h_tail_vs_ne]
          apply List.mem_append.mpr
          right
          rw [h_tail_vs, List.dropLast_cons_of_ne_nil h_tail_t_ne]
          exact List.mem_cons_of_mem _ hx
        have h_tail_len : tail.refactor_length ≤ k := by omega
        obtain ⟨q_tail, hq_tail_dir, hq_tail_pos,
                hq_tail_sub, hq_tail_drop_sub, hq_tail_tail_sub, hq_tail_inter⟩ :=
          ih tail h_tail_len h_tail_dir h_tail_pos hm_marg hv h_tail_inter
        refine ⟨refactor_Walk.cons m (.forwardE h_edge) q_tail,
                hq_tail_dir, ?_, ?_, ?_, ?_, ?_⟩
        · change q_tail.refactor_length + 1 ≥ 1; omega
        · -- q.vertices ⊆ p.vertices.
          intro x hx
          change x ∈ u :: q_tail.refactor_vertices at hx
          rw [h_p_eq]
          rcases List.mem_cons.mp hx with rfl | hx_in
          · exact List.mem_append.mpr (Or.inl h_u_in_head_drop)
          · exact List.mem_append.mpr (Or.inr (hq_tail_sub x hx_in))
        · -- q.vertices.dropLast ⊆ p.vertices.dropLast.
          intro x hx
          have h_qt_vs_ne : q_tail.refactor_vertices ≠ [] :=
            refactor_Walk.refactor_vertices_ne_nil q_tail
          change x ∈ (u :: q_tail.refactor_vertices).dropLast at hx
          rw [List.dropLast_cons_of_ne_nil h_qt_vs_ne] at hx
          rw [h_p_eq, List.dropLast_append_of_ne_nil h_tail_vs_ne]
          rcases List.mem_cons.mp hx with rfl | hx_in
          · exact List.mem_append.mpr (Or.inl h_u_in_head_drop)
          · exact List.mem_append.mpr (Or.inr (hq_tail_drop_sub x hx_in))
        · -- q.vertices.tail ⊆ p.vertices.tail.
          intro x hx
          change x ∈ q_tail.refactor_vertices at hx
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne]
          -- head.vertices.dropLast.tail = head.vertices.tail.dropLast.
          -- We just need x ∈ p.vertices.tail.
          exact List.mem_append.mpr (Or.inr (hq_tail_sub x hx))
        · -- q.vertices.tail.dropLast ⊆ T.
          intro x hx
          change x ∈ (u :: q_tail.refactor_vertices).tail.dropLast at hx
          rw [List.tail_cons] at hx
          have h_qtv :
              q_tail.refactor_vertices = m :: q_tail.refactor_vertices.tail :=
            refactor_Walk.refactor_vertices_eq_head_cons_tail q_tail
          rw [h_qtv] at hx
          have h_qtt_ne : q_tail.refactor_vertices.tail ≠ [] :=
            refactor_Walk.refactor_tail_vertices_ne_nil_of_pos q_tail hq_tail_pos
          rw [List.dropLast_cons_of_ne_nil h_qtt_ne] at hx
          rcases List.mem_cons.mp hx with rfl | hx_inner
          · exact hm_in_T
          · exact hq_tail_inter x hx_inner
      · have h_tail_zero : tail.refactor_length = 0 := by omega
        have hmv_eq : m = v := by
          generalize htail_eq : tail.refactor_length = ℓ at h_tail_zero
          subst h_tail_zero
          match tail, htail_eq with
          | .nil _ _, _ => rfl
        subst hmv_eq
        refine ⟨refactor_Walk.cons m (.forwardE h_edge)
                  (refactor_Walk.nil m hv),
                trivial, ?_, ?_, ?_, ?_, ?_⟩
        · change 1 ≥ 1; omega
        · intro x hx
          change x ∈ ([u, m] : List Node) at hx
          rw [h_p_eq]
          rcases List.mem_cons.mp hx with rfl | hx_rest
          · exact List.mem_append.mpr (Or.inl h_u_in_head_drop)
          · rw [List.mem_singleton] at hx_rest
            subst hx_rest
            exact List.mem_append.mpr
              (Or.inr (refactor_Walk.refactor_head_mem_vertices _))
        · intro x hx
          change x ∈ ([u, m] : List Node).dropLast at hx
          simp [List.dropLast] at hx
          subst hx
          rw [h_p_eq, List.dropLast_append_of_ne_nil h_tail_vs_ne]
          exact List.mem_append.mpr (Or.inl h_u_in_head_drop)
        · intro x hx
          change x ∈ ([u, m] : List Node).tail at hx
          simp [List.tail] at hx
          subst hx
          rw [h_p_eq, List.tail_append_of_ne_nil h_head_drop_ne]
          apply List.mem_append.mpr
          right
          exact refactor_Walk.refactor_head_mem_vertices _
        · intro x hx
          change x ∈ (u :: [m] : List Node).tail.dropLast at hx
          simp at hx
-- REFACTOR-BLOCK-REPLACEMENT-END: project_walk_marg_full_aux

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: project_walk_marg_full (was: refactor_project_walk_marg_full)
private lemma refactor_project_walk_marg_full {G : refactor_CDMG Node}
    {S T : Finset Node} {hS : S ⊆ G.V}
    {u v : Node} (p : refactor_Walk G u v)
    (hp_dir : p.refactor_IsDirectedWalk) (hp_pos : p.refactor_length ≥ 1)
    (hu : u ∈ G.refactor_marginalize S hS)
    (hv : v ∈ G.refactor_marginalize S hS)
    (h_inter : ∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T) :
    ∃ (q : refactor_Walk (G.refactor_marginalize S hS) u v),
      q.refactor_IsDirectedWalk ∧ q.refactor_length ≥ 1 ∧
      (∀ x ∈ q.refactor_vertices, x ∈ p.refactor_vertices) ∧
      (∀ x ∈ q.refactor_vertices.dropLast,
        x ∈ p.refactor_vertices.dropLast) ∧
      (∀ x ∈ q.refactor_vertices.tail, x ∈ p.refactor_vertices.tail) ∧
      (∀ x ∈ q.refactor_vertices.tail.dropLast, x ∈ T) :=
  refactor_project_walk_marg_full_aux (S := S) (T := T) (hS := hS)
    p.refactor_length p le_rfl hp_dir hp_pos hu hv h_inter
-- REFACTOR-BLOCK-REPLACEMENT-END: project_walk_marg_full

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: mem_marg_of_notin_union_V (was: refactor_mem_marg_of_notin_union_V)
private lemma refactor_mem_marg_of_notin_union_V {G : refactor_CDMG Node}
    (S T : Finset Node) (hS : S ⊆ G.V) {u : Node}
    (hu : u ∈ G.J ∪ (G.V \ (S ∪ T))) :
    u ∈ G.refactor_marginalize S hS := by
  change u ∈ G.J ∪ (G.V \ S)
  rcases Finset.mem_union.mp hu with hJ | hVW
  · exact Finset.mem_union_left _ hJ
  · refine Finset.mem_union_right _ ?_
    rw [Finset.mem_sdiff] at hVW ⊢
    refine ⟨hVW.1, ?_⟩
    intro hu_in_S
    exact hVW.2 (Finset.mem_union_left _ hu_in_S)
-- REFACTOR-BLOCK-REPLACEMENT-END: mem_marg_of_notin_union_V

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: mem_marg_of_notin_union_VnoJ (was: refactor_mem_marg_of_notin_union_VnoJ)
private lemma refactor_mem_marg_of_notin_union_VnoJ {G : refactor_CDMG Node}
    (S T : Finset Node) (hS : S ⊆ G.V) {v : Node}
    (hv : v ∈ G.V \ (S ∪ T)) :
    v ∈ G.refactor_marginalize S hS := by
  change v ∈ G.J ∪ (G.V \ S)
  refine Finset.mem_union_right _ ?_
  rw [Finset.mem_sdiff] at hv ⊢
  refine ⟨hv.1, ?_⟩
  intro hv_in_S
  exact hv.2 (Finset.mem_union_left _ hv_in_S)
-- REFACTOR-BLOCK-REPLACEMENT-END: mem_marg_of_notin_union_VnoJ

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marg_PhiE_iff (was: refactor_marg_PhiE_iff)
-- ## E-membership iff (parametric in `S, T`).
private lemma refactor_marg_PhiE_iff {G : refactor_CDMG Node}
    (S T : Finset Node)
    (hS : S ⊆ G.V) (_hT : T ⊆ G.V) (_hDisj : Disjoint S T)
    {u v : Node}
    (hu : u ∈ G.J ∪ (G.V \ (S ∪ T))) (hv : v ∈ G.V \ (S ∪ T)) :
    (G.refactor_marginalize S hS).refactor_MarginalizationΦE T u v ↔
      G.refactor_MarginalizationΦE (S ∪ T) u v := by
  constructor
  · rintro ⟨p, hp_dir, hp_pos, hp_inter⟩
    obtain ⟨q, hq_dir, hq_len, _, _, _, hq_inter⟩ :=
      refactor_expand_directed_walk_marginalize p hp_dir
    refine ⟨q, hq_dir, ?_, ?_⟩
    · omega
    · intro x hx
      rcases hq_inter x hx with hxp | hxS
      · exact Finset.mem_union_right _ (hp_inter x hxp)
      · exact Finset.mem_union_left _ hxS
  · rintro ⟨q, hq_dir, hq_pos, hq_inter⟩
    have hu_marg : u ∈ G.refactor_marginalize S hS :=
      refactor_mem_marg_of_notin_union_V S T hS hu
    have hv_marg : v ∈ G.refactor_marginalize S hS :=
      refactor_mem_marg_of_notin_union_VnoJ S T hS hv
    have h_inter : ∀ x ∈ q.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
      intro x hx
      have hin := hq_inter x hx
      rcases Finset.mem_union.mp hin with hS_in | hT_in
      · exact Or.inl hS_in
      · exact Or.inr hT_in
    obtain ⟨p, hp_dir, hp_pos, hp_inter⟩ :=
      refactor_project_walk_marg_with_interior (S := S) (T := T) (hS := hS)
        q hq_dir hq_pos hu_marg hv_marg h_inter
    exact ⟨p, hp_dir, hp_pos, hp_inter⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: marg_PhiE_iff

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marg_E_field_eq (was: refactor_marg_E_field_eq)
-- ## E-field equality (parametric in `S, T`).
private lemma refactor_marg_E_field_eq {G : refactor_CDMG Node}
    (S T : Finset Node)
    (hS : S ⊆ G.V) (hT : T ⊆ G.V) (hDisj : Disjoint S T) :
    ((G.refactor_marginalize S hS).refactor_marginalize T
        (refactor_subset_sdiff_of_disjoint hT hDisj.symm)).E
      = (G.refactor_marginalize (S ∪ T) (Finset.union_subset hS hT)).E := by
  change ((G.J ∪ ((G.V \ S) \ T)) ×ˢ ((G.V \ S) \ T)).filter
          (fun e =>
            (G.refactor_marginalize S hS).refactor_MarginalizationΦE T e.1 e.2)
        = ((G.J ∪ (G.V \ (S ∪ T))) ×ˢ (G.V \ (S ∪ T))).filter
          (fun e => G.refactor_MarginalizationΦE (S ∪ T) e.1 e.2)
  have h_sd : (G.V \ S) \ T = G.V \ (S ∪ T) := sdiff_sdiff_left
  rw [h_sd]
  apply Finset.filter_congr
  intro e he
  rw [Finset.mem_product] at he
  exact refactor_marg_PhiE_iff S T hS hT hDisj he.1 he.2
-- REFACTOR-BLOCK-REPLACEMENT-END: marg_E_field_eq

-- ## Refactor replacements — Phase C (4 small L-field setup lemmas)
--
-- Net-new ports (no paired ORIGINAL block — these are `private
-- lemma`s with no markers in the original).  All four are pure
-- list-arithmetic about `refactor_vertices` / `dropLast` /
-- `tail`; the only structural shifts beyond the Phase B set are:
-- (i)  `Walk.mkBifurcation` / `Walk.mkBifurcationBidir` and their
--      `vertices_*` companions retarget to the `refactor_Walk.*`
--      variants from `MargPreservesAncestors.lean`;
-- (ii) `vertices_tail_dropLast_mkBifurcationBidir_Lpos`'s L-edge
--      hypothesis `(vL, vR) ∈ G.L` (ordered pair) becomes
--      `s(vL, vR) ∈ G.L` (Sym2 quotient) to match
--      `refactor_mkBifurcationBidir`'s signature.

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: mem_interior_of_arm_source (was: refactor_mem_interior_of_arm_source)
-- ## Helper: source uniqueness of bif `p` upgrades "c ∈ p.tail and
-- c ∈ p.dropLast" to "c ∈ p.tail.dropLast".
private lemma refactor_mem_interior_of_arm_source
    {G : refactor_CDMG Node} {u v : Node}
    {p : refactor_Walk G u v} (hu_p_tail : u ∉ p.refactor_vertices.tail)
    (hp_pos : p.refactor_length ≥ 1)
    {c : Node}
    (hc_p_tail : c ∈ p.refactor_vertices.tail)
    (hc_p_drop : c ∈ p.refactor_vertices.dropLast) :
    c ∈ p.refactor_vertices.tail.dropLast := by
  have h_p_tail_ne : p.refactor_vertices.tail ≠ [] :=
    refactor_Walk.refactor_tail_vertices_ne_nil_of_pos p hp_pos
  have h_p_vs_eq : p.refactor_vertices = u :: p.refactor_vertices.tail :=
    refactor_Walk.refactor_vertices_eq_head_cons_tail p
  have h_p_drop_eq :
      p.refactor_vertices.dropLast = u :: p.refactor_vertices.tail.dropLast := by
    conv_lhs => rw [h_p_vs_eq]
    exact List.dropLast_cons_of_ne_nil h_p_tail_ne
  rw [h_p_drop_eq] at hc_p_drop
  rcases List.mem_cons.mp hc_p_drop with h_c_eq_u | h_in
  · exact absurd (h_c_eq_u ▸ hc_p_tail) hu_p_tail
  · exact h_in
-- REFACTOR-BLOCK-REPLACEMENT-END: mem_interior_of_arm_source

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: vertices_tail_dropLast_mkBifurcation (was: refactor_vertices_tail_dropLast_mkBifurcation)
-- ## Helper: vertices_tail_dropLast for mkBifurcation with both arms positive.
private lemma refactor_vertices_tail_dropLast_mkBifurcation
    {G : refactor_CDMG Node} {c v w : Node}
    (qv : refactor_Walk G c v) (hqv_dir : qv.refactor_IsDirectedWalk)
    (hqv_pos : qv.refactor_length ≥ 1)
    (qw : refactor_Walk G c w) (_hqw_pos : qw.refactor_length ≥ 1) :
    (refactor_Walk.refactor_mkBifurcation qv hqv_dir hqv_pos qw).refactor_vertices.tail.dropLast
      = qv.refactor_vertices.tail.dropLast.reverse
          ++ qw.refactor_vertices.dropLast := by
  have h_vs :=
    refactor_Walk.refactor_vertices_mkBifurcation qv hqv_dir hqv_pos qw
  have h_rev_drop :
      qv.refactor_vertices.reverse.dropLast = qv.refactor_vertices.tail.reverse :=
    refactor_Walk.refactor_vertices_reverse_dropLast qv
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
  have h_qv_tail_ne : qv.refactor_vertices.tail ≠ [] :=
    refactor_Walk.refactor_tail_vertices_ne_nil_of_pos qv hqv_pos
  have h_qv_rev_drop_ne : qv.refactor_vertices.reverse.dropLast ≠ [] := by
    rw [h_rev_drop]
    intro hempty
    apply h_qv_tail_ne
    have : qv.refactor_vertices.tail = qv.refactor_vertices.tail.reverse.reverse := by
      rw [List.reverse_reverse]
    rw [this, hempty]; rfl
  have h_qw_vs_ne : qw.refactor_vertices ≠ [] :=
    refactor_Walk.refactor_vertices_ne_nil qw
  rw [h_vs]
  rw [List.tail_append_of_ne_nil h_qv_rev_drop_ne]
  rw [List.dropLast_append_of_ne_nil h_qw_vs_ne]
  rw [h_rev_drop, h_aux]
-- REFACTOR-BLOCK-REPLACEMENT-END: vertices_tail_dropLast_mkBifurcation

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: vertices_tail_dropLast_mkBifurcationBidir_Lpos (was: refactor_vertices_tail_dropLast_mkBifurcationBidir_Lpos)
-- ## Helper: vertices_tail_dropLast for mkBifurcationBidir with L positive.
-- Refactor: `(vL, vR) ∈ G.L` (ordered pair) → `s(vL, vR) ∈ G.L`
-- (Sym2 quotient) to match `refactor_mkBifurcationBidir`'s signature.
private lemma refactor_vertices_tail_dropLast_mkBifurcationBidir_Lpos
    {G : refactor_CDMG Node} {vL vR v1 v2 : Node}
    (L : refactor_Walk G vL v1) (hL_dir : L.refactor_IsDirectedWalk)
    (R : refactor_Walk G vR v2) (hLR : s(vL, vR) ∈ G.L)
    (hL_pos : L.refactor_length ≥ 1) :
    (refactor_Walk.refactor_mkBifurcationBidir L hL_dir R hLR).refactor_vertices.tail.dropLast
      = L.refactor_vertices.tail.dropLast.reverse
          ++ (vL :: R.refactor_vertices).dropLast := by
  have h_vs :=
    refactor_Walk.refactor_vertices_mkBifurcationBidir L hL_dir R hLR
  have h_rev_drop :
      L.refactor_vertices.reverse.dropLast = L.refactor_vertices.tail.reverse :=
    refactor_Walk.refactor_vertices_reverse_dropLast L
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
  have h_L_tail_ne : L.refactor_vertices.tail ≠ [] :=
    refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L hL_pos
  have h_L_rev_drop_ne : L.refactor_vertices.reverse.dropLast ≠ [] := by
    rw [h_rev_drop]
    intro hempty
    apply h_L_tail_ne
    have : L.refactor_vertices.tail = L.refactor_vertices.tail.reverse.reverse := by
      rw [List.reverse_reverse]
    rw [this, hempty]; rfl
  have h_cons_ne : (vL :: R.refactor_vertices) ≠ [] := by simp
  rw [h_vs]
  rw [List.tail_append_of_ne_nil h_L_rev_drop_ne]
  rw [List.dropLast_append_of_ne_nil h_cons_ne]
  rw [h_rev_drop, h_aux]
-- REFACTOR-BLOCK-REPLACEMENT-END: vertices_tail_dropLast_mkBifurcationBidir_Lpos

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: find_first_non_W_directed_inclusive (was: refactor_find_first_non_W_directed_inclusive)
-- ## Helper: inclusive variant of `refactor_find_first_non_W_directed`.
--
-- Unlike `refactor_find_first_non_W_directed` (which always returns a
-- non-trivial head, skipping the source `u`), this variant lets the source
-- `u` itself be the "first non-W" vertex: if `u ∉ W`, then `m := u`,
-- `head := nil`, `tail := p`.  Used by the backward bidirected-hinge case
-- where the bidirected hinge endpoints `s(vL, vR) ∈ G.L` might or might not
-- lie in `S`, so the "first non-S vertex starting from vL inclusive" search
-- needs to handle both possibilities uniformly.  The post-condition
-- `∀ x ∈ head.refactor_vertices.dropLast, x ∈ W` is *inclusive* of the source
-- (all of head's vertices except the target are in `W`); when `head` is
-- trivial this is vacuous.
private lemma refactor_find_first_non_W_directed_inclusive
    {G : refactor_CDMG Node} (W : Finset Node)
    {u v : Node} (p : refactor_Walk G u v)
    (hp_dir : p.refactor_IsDirectedWalk) (hv_notW : v ∉ W) :
    ∃ (m : Node) (head : refactor_Walk G u m) (tail : refactor_Walk G m v),
      head.refactor_IsDirectedWalk ∧ tail.refactor_IsDirectedWalk ∧
      m ∉ W ∧
      (∀ x ∈ head.refactor_vertices.dropLast, x ∈ W) ∧
      head.refactor_length + tail.refactor_length = p.refactor_length ∧
      p.refactor_vertices =
        head.refactor_vertices.dropLast ++ tail.refactor_vertices := by
  by_cases hu_W : u ∈ W
  · have hu_ne_v : u ≠ v := fun heq => hv_notW (heq ▸ hu_W)
    have hp_pos : p.refactor_length ≥ 1 :=
      refactor_Walk.refactor_length_pos_of_ne p hu_ne_v
    obtain ⟨m, head, tail, h_head_dir, h_tail_dir, h_head_pos, hm_notW,
            h_head_inter, h_lens, h_p_eq⟩ :=
      refactor_find_first_non_W_directed W p hp_dir hp_pos hv_notW
    refine ⟨m, head, tail, h_head_dir, h_tail_dir, hm_notW, ?_, h_lens, h_p_eq⟩
    intro x hx
    have h_head_t_ne : head.refactor_vertices.tail ≠ [] :=
      refactor_Walk.refactor_tail_vertices_ne_nil_of_pos head h_head_pos
    have h_head_drop_eq :
        head.refactor_vertices.dropLast = u :: head.refactor_vertices.tail.dropLast := by
      conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail head]
      exact List.dropLast_cons_of_ne_nil h_head_t_ne
    rw [h_head_drop_eq] at hx
    rcases List.mem_cons.mp hx with rfl | hx_rest
    · exact hu_W
    · exact h_head_inter x hx_rest
  · have hu_in_G : u ∈ G :=
      refactor_Walk.refactor_mem_of_mem_vertices p
        (refactor_Walk.refactor_head_mem_vertices p)
    refine ⟨u, refactor_Walk.nil u hu_in_G, p, trivial, hp_dir, hu_W, ?_, ?_, ?_⟩
    · intro x hx
      change x ∈ ([u] : List Node).dropLast at hx
      simp at hx
    · change 0 + p.refactor_length = p.refactor_length; omega
    · change p.refactor_vertices = ([u] : List Node).dropLast ++ p.refactor_vertices
      simp
-- REFACTOR-BLOCK-REPLACEMENT-END: find_first_non_W_directed_inclusive


-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: forward_marg_to_g_bif_one_orientation (was: refactor_forward_marg_to_g_bif_one_orientation)
set_option linter.style.longLine false in
private lemma refactor_forward_marg_to_g_bif_one_orientation
    {G : refactor_CDMG Node} (S T : Finset Node)
    (hS : S ⊆ G.V) {a b : Node}
    (ha_VST : a ∈ G.V \ (S ∪ T)) (hb_VST : b ∈ G.V \ (S ∪ T))
    (ha_marg : a ∈ G.refactor_marginalize S hS) (hb_marg : b ∈ G.refactor_marginalize S hS)
    (p : refactor_Walk (G.refactor_marginalize S hS) a b)
    (hp_bif : p.refactor_IsBifurcation)
    (hp_inter : ∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ T) :
    ∃ q : refactor_Walk G a b, q.refactor_IsBifurcation ∧
      ∀ x ∈ q.refactor_vertices.tail.dropLast, x ∈ S ∪ T := by
  have ha_notSuT : a ∉ S ∪ T := (Finset.mem_sdiff.mp ha_VST).2
  have hb_notSuT : b ∉ S ∪ T := (Finset.mem_sdiff.mp hb_VST).2
  have ha_notS : a ∉ S := fun h => ha_notSuT (Finset.mem_union_left _ h)
  have hb_notS : b ∉ S := fun h => hb_notSuT (Finset.mem_union_left _ h)
  have hp_pos : p.refactor_length ≥ 1 := refactor_Walk.refactor_length_pos_of_isBifurcation hp_bif
  obtain ⟨hab_ne, ha_p_tail, hb_p_drop, i, hp_split⟩ := hp_bif
  by_cases h_dir : p.refactor_IsBifurcationDirectedHingeWithSplit i
  · -- DIRECTED HINGE CASE: source `c` in marg.
    obtain ⟨c, L_p, R_p, hL_p_dir, hR_p_dir, hL_p_pos, hR_p_pos, _,
            hL_p_sub, hR_p_sub, hL_p_drop_sub, hR_p_drop_sub⟩ :=
      refactor_Walk.refactor_exists_arms_of_bifurcation_directed_hinge_strong p i h_dir
    -- c is the bifurcation source; trace c ∈ p.tail.dropLast → c ∈ T.
    have hc_in_L_p : c ∈ L_p.refactor_vertices := refactor_Walk.refactor_head_mem_vertices L_p
    have hc_in_R_p : c ∈ R_p.refactor_vertices := refactor_Walk.refactor_head_mem_vertices R_p
    have hc_in_p_drop : c ∈ p.refactor_vertices.dropLast := hL_p_sub _ hc_in_L_p
    have hc_in_p_tail : c ∈ p.refactor_vertices.tail := hR_p_sub _ hc_in_R_p
    have hc_in_p_inter : c ∈ p.refactor_vertices.tail.dropLast :=
      refactor_mem_interior_of_arm_source ha_p_tail hp_pos hc_in_p_tail hc_in_p_drop
    have hc_T : c ∈ T := hp_inter c hc_in_p_inter
    -- Expand each arm into G.
    obtain ⟨L_g, hL_g_dir, hL_g_len, hL_g_sub_S, hL_g_drop_sub_S,
            _, hL_g_tdL_sub_S⟩ :=
      refactor_expand_directed_walk_marginalize L_p hL_p_dir
    obtain ⟨R_g, hR_g_dir, hR_g_len, hR_g_sub_S, hR_g_drop_sub_S,
            _, hR_g_tdL_sub_S⟩ :=
      refactor_expand_directed_walk_marginalize R_p hR_p_dir
    have hL_g_pos : L_g.refactor_length ≥ 1 := by omega
    have hR_g_pos : R_g.refactor_length ≥ 1 := by omega
    -- Trace L_p's interior to T (similarly for R_p).
    have hL_p_inter_T : ∀ x ∈ L_p.refactor_vertices.tail.dropLast, x ∈ T := by
      intro x hx
      have h_t_ne : L_p.refactor_vertices.tail ≠ [] :=
        refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_p hL_p_pos
      have h_drop_eq : L_p.refactor_vertices.dropLast = c :: L_p.refactor_vertices.tail.dropLast := by
        conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_p]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have hx_L_p_drop : x ∈ L_p.refactor_vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have hx_p_tail : x ∈ p.refactor_vertices.tail := hL_p_drop_sub _ hx_L_p_drop
      have hx_L_p : x ∈ L_p.refactor_vertices := List.mem_of_mem_dropLast hx_L_p_drop
      have hx_p_drop : x ∈ p.refactor_vertices.dropLast := hL_p_sub _ hx_L_p
      have hx_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
        refactor_mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
      exact hp_inter _ hx_p_inter
    have hR_p_inter_T : ∀ x ∈ R_p.refactor_vertices.tail.dropLast, x ∈ T := by
      intro x hx
      have h_t_ne : R_p.refactor_vertices.tail ≠ [] :=
        refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_p hR_p_pos
      have h_drop_eq : R_p.refactor_vertices.dropLast = c :: R_p.refactor_vertices.tail.dropLast := by
        conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_p]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have hx_R_p_drop : x ∈ R_p.refactor_vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have hx_p_drop : x ∈ p.refactor_vertices.dropLast := hR_p_drop_sub _ hx_R_p_drop
      have hx_R_p : x ∈ R_p.refactor_vertices := List.mem_of_mem_dropLast hx_R_p_drop
      have hx_p_tail : x ∈ p.refactor_vertices.tail := hR_p_sub _ hx_R_p
      have hx_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
        refactor_mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
      exact hp_inter _ hx_p_inter
    -- Vertex bounds for L_g, R_g (a/b in correct positions).
    have ha_notin_L_g_drop : a ∉ L_g.refactor_vertices.dropLast := by
      intro h_in
      rcases hL_g_drop_sub_S a h_in with h_in_L_p | h_in_S
      · exact ha_p_tail (hL_p_drop_sub a h_in_L_p)
      · exact ha_notS h_in_S
    have ha_notin_R_g : a ∉ R_g.refactor_vertices := by
      intro h_in
      rcases hR_g_sub_S a h_in with h_in_R_p | h_in_S
      · exact ha_p_tail (hR_p_sub a h_in_R_p)
      · exact ha_notS h_in_S
    have hb_notin_L_g : b ∉ L_g.refactor_vertices := by
      intro h_in
      rcases hL_g_sub_S b h_in with h_in_L_p | h_in_S
      · exact hb_p_drop (hL_p_sub b h_in_L_p)
      · exact hb_notS h_in_S
    have hb_notin_R_g_drop : b ∉ R_g.refactor_vertices.dropLast := by
      intro h_in
      rcases hR_g_drop_sub_S b h_in with h_in_R_p | h_in_S
      · exact hb_p_drop (hR_p_drop_sub b h_in_R_p)
      · exact hb_notS h_in_S
    -- Build the bifurcation in G.
    refine ⟨refactor_Walk.refactor_mkBifurcation L_g hL_g_dir hL_g_pos R_g, ?_, ?_⟩
    · have h_src := refactor_Walk.refactor_mkBifurcation_isBifurcationSource L_g hL_g_dir hL_g_pos
                      R_g hR_g_dir hR_g_pos
                      hab_ne ha_notin_L_g_drop ha_notin_R_g hb_notin_L_g
                      hb_notin_R_g_drop
      exact refactor_Walk.refactor_isBifurcationSource_to_isBifurcation _ c h_src
    · intro x hx
      rw [refactor_vertices_tail_dropLast_mkBifurcation L_g hL_g_dir hL_g_pos R_g
            hR_g_pos] at hx
      rcases List.mem_append.mp hx with hx_L | hx_R
      · rw [List.mem_reverse] at hx_L
        rcases hL_g_tdL_sub_S x hx_L with hx_L_p_inter | hx_S
        · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p_inter)
        · exact Finset.mem_union_left _ hx_S
      · have h_R_t_ne : R_g.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_g hR_g_pos
        rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_g,
            List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R
        rcases List.mem_cons.mp hx_R with rfl | hx_inner
        · exact Finset.mem_union_right _ hc_T
        · rcases hR_g_tdL_sub_S x hx_inner with hx_R_p_inter | hx_S
          · exact Finset.mem_union_right _ (hR_p_inter_T x hx_R_p_inter)
          · exact Finset.mem_union_left _ hx_S
  · -- BIDIRECTED HINGE CASE.
    obtain ⟨vL_p, vR_p, L_p, R_p, hL_p_dir, hR_p_dir, hLR_p_marg, _,
            hL_p_sub, hR_p_sub, hL_p_drop_sub, hR_p_drop_sub⟩ :=
      refactor_Walk.refactor_exists_arms_of_bifurcation_bidir_hinge_strong
        p i hp_split h_dir
    -- Unfold marg.L via the Sym2-image iff (Batch-1 net-new helper in MPA).
    obtain ⟨e, he1_VS, he2_VS, _he_ne, h_phi_L_e, hs_eq⟩ :=
      (refactor_marginalize_L_iff G S hS).mp hLR_p_marg
    -- `Sym2.eq_iff` case-split: `s(vL_p, vR_p) = s(e.1, e.2)` admits two
    -- orientations; in either we obtain `vL_p, vR_p ∈ G.V \ S` and the
    -- symmetric `Φ_L S vL_p vR_p` (via `Or.symm` in the swap case).
    have h_pack : vL_p ∈ G.V \ S ∧ vR_p ∈ G.V \ S ∧
                  G.refactor_MarginalizationΦL S vL_p vR_p := by
      rcases Sym2.eq_iff.mp hs_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨he1_VS, he2_VS, h_phi_L_e⟩
      · exact ⟨he2_VS, he1_VS, h_phi_L_e.symm⟩
    obtain ⟨hvL_VS, hvR_VS, h_phi_L⟩ := h_pack
    have hvL_notS : vL_p ∉ S := (Finset.mem_sdiff.mp hvL_VS).2
    have hvR_notS : vR_p ∉ S := (Finset.mem_sdiff.mp hvR_VS).2
    have hvL_in_L_p : vL_p ∈ L_p.refactor_vertices := refactor_Walk.refactor_head_mem_vertices L_p
    have hvL_in_p_drop : vL_p ∈ p.refactor_vertices.dropLast := hL_p_sub _ hvL_in_L_p
    have hvR_in_R_p : vR_p ∈ R_p.refactor_vertices := refactor_Walk.refactor_head_mem_vertices R_p
    have hvR_in_p_tail : vR_p ∈ p.refactor_vertices.tail := hR_p_sub _ hvR_in_R_p
    -- Expand each arm into G (may have length 0 in the bid case).
    obtain ⟨L_g, hL_g_dir, hL_g_len, hL_g_sub_S, hL_g_drop_sub_S,
            _, hL_g_tdL_sub_S⟩ :=
      refactor_expand_directed_walk_marginalize L_p hL_p_dir
    obtain ⟨R_g, hR_g_dir, hR_g_len, hR_g_sub_S, hR_g_drop_sub_S,
            _, hR_g_tdL_sub_S⟩ :=
      refactor_expand_directed_walk_marginalize R_p hR_p_dir
    -- Helper: trace L_p's interior to T.
    have hL_p_inter_T : ∀ x ∈ L_p.refactor_vertices.tail.dropLast, x ∈ T := by
      intro x hx
      by_cases h_L_p_pos : L_p.refactor_length ≥ 1
      · have h_t_ne : L_p.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_p h_L_p_pos
        have h_drop_eq :
            L_p.refactor_vertices.dropLast = vL_p :: L_p.refactor_vertices.tail.dropLast := by
          conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_p]
          exact List.dropLast_cons_of_ne_nil h_t_ne
        have hx_L_p_drop : x ∈ L_p.refactor_vertices.dropLast := by
          rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
        have hx_p_tail : x ∈ p.refactor_vertices.tail := hL_p_drop_sub _ hx_L_p_drop
        have hx_L_p : x ∈ L_p.refactor_vertices := List.mem_of_mem_dropLast hx_L_p_drop
        have hx_p_drop : x ∈ p.refactor_vertices.dropLast := hL_p_sub _ hx_L_p
        have hx_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
          refactor_mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
        exact hp_inter _ hx_p_inter
      · have h_zero : L_p.refactor_length = 0 := by omega
        match L_p, h_zero with
        | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail, List.dropLast] at hx
    have hR_p_inter_T : ∀ x ∈ R_p.refactor_vertices.tail.dropLast, x ∈ T := by
      intro x hx
      by_cases h_R_p_pos : R_p.refactor_length ≥ 1
      · have h_t_ne : R_p.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_p h_R_p_pos
        have h_drop_eq :
            R_p.refactor_vertices.dropLast = vR_p :: R_p.refactor_vertices.tail.dropLast := by
          conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_p]
          exact List.dropLast_cons_of_ne_nil h_t_ne
        have hx_R_p_drop : x ∈ R_p.refactor_vertices.dropLast := by
          rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
        have hx_p_drop : x ∈ p.refactor_vertices.dropLast := hR_p_drop_sub _ hx_R_p_drop
        have hx_R_p : x ∈ R_p.refactor_vertices := List.mem_of_mem_dropLast hx_R_p_drop
        have hx_p_tail : x ∈ p.refactor_vertices.tail := hR_p_sub _ hx_R_p
        have hx_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
          refactor_mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
        exact hp_inter _ hx_p_inter
      · have h_zero : R_p.refactor_length = 0 := by omega
        match R_p, h_zero with
        | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail, List.dropLast] at hx
    -- vL_p ∈ T (when L_p.refactor_length ≥ 1, i.e., vL_p ≠ a).
    have hvL_T_if_L_p_pos : L_p.refactor_length ≥ 1 → vL_p ∈ T := by
      intro h_L_p_pos
      have h_t_ne : L_p.refactor_vertices.tail ≠ [] :=
        refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_p h_L_p_pos
      have hvL_in_L_p_drop : vL_p ∈ L_p.refactor_vertices.dropLast := by
        rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_p,
            List.dropLast_cons_of_ne_nil h_t_ne]
        exact List.mem_cons_self
      have hvL_p_tail : vL_p ∈ p.refactor_vertices.tail :=
        hL_p_drop_sub _ hvL_in_L_p_drop
      have hvL_p_inter : vL_p ∈ p.refactor_vertices.tail.dropLast :=
        refactor_mem_interior_of_arm_source ha_p_tail hp_pos hvL_p_tail hvL_in_p_drop
      exact hp_inter _ hvL_p_inter
    -- vR_p ∈ T (when R_p.refactor_length ≥ 1, i.e., vR_p ≠ b).
    have hvR_T_if_R_p_pos : R_p.refactor_length ≥ 1 → vR_p ∈ T := by
      intro h_R_p_pos
      have h_t_ne : R_p.refactor_vertices.tail ≠ [] :=
        refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_p h_R_p_pos
      have hvR_in_R_p_drop : vR_p ∈ R_p.refactor_vertices.dropLast := by
        rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_p,
            List.dropLast_cons_of_ne_nil h_t_ne]
        exact List.mem_cons_self
      have hvR_p_drop : vR_p ∈ p.refactor_vertices.dropLast :=
        hR_p_drop_sub _ hvR_in_R_p_drop
      have hvR_p_inter : vR_p ∈ p.refactor_vertices.tail.dropLast :=
        refactor_mem_interior_of_arm_source ha_p_tail hp_pos hvR_in_p_tail hvR_p_drop
      exact hp_inter _ hvR_p_inter
    -- Vertex bounds for L_g, R_g (a/b in correct positions).
    have ha_notin_L_g_drop : a ∉ L_g.refactor_vertices.dropLast := by
      intro h_in
      rcases hL_g_drop_sub_S a h_in with h_in_L_p | h_in_S
      · exact ha_p_tail (hL_p_drop_sub a h_in_L_p)
      · exact ha_notS h_in_S
    have ha_notin_R_g : a ∉ R_g.refactor_vertices := by
      intro h_in
      rcases hR_g_sub_S a h_in with h_in_R_p | h_in_S
      · exact ha_p_tail (hR_p_sub a h_in_R_p)
      · exact ha_notS h_in_S
    have hb_notin_L_g : b ∉ L_g.refactor_vertices := by
      intro h_in
      rcases hL_g_sub_S b h_in with h_in_L_p | h_in_S
      · exact hb_p_drop (hL_p_sub b h_in_L_p)
      · exact hb_notS h_in_S
    have hb_notin_R_g_drop : b ∉ R_g.refactor_vertices.dropLast := by
      intro h_in
      rcases hR_g_drop_sub_S b h_in with h_in_R_p | h_in_S
      · exact hb_p_drop (hR_p_drop_sub b h_in_R_p)
      · exact hb_notS h_in_S
    -- Case split on Φ_L S vL_p vR_p (Or).
    rcases h_phi_L with ⟨M, hM_bif, hM_W⟩ | ⟨M, hM_bif, hM_W⟩
    · -- Inl case: M : refactor_Walk G vL_p vR_p.
      have hM_split_ex : ∃ k, M.refactor_IsBifurcationWithSplit k := hM_bif.2.2.2
      obtain ⟨k_M, hM_split⟩ := hM_split_ex
      have hM_pos : M.refactor_length ≥ 1 := refactor_Walk.refactor_length_pos_of_isBifurcation hM_bif
      have hvL_M_tail : vL_p ∉ M.refactor_vertices.tail := hM_bif.2.1
      have hvR_M_drop : vR_p ∉ M.refactor_vertices.dropLast := hM_bif.2.2.1
      by_cases h_M_dir : M.refactor_IsBifurcationDirectedHingeWithSplit k_M
      · -- Inl + directed M-hinge.
        obtain ⟨c_M, M_L, M_R, hM_L_dir, hM_R_dir, hM_L_pos, hM_R_pos, hidx_M,
                hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
          refactor_Walk.refactor_exists_arms_of_bifurcation_directed_hinge_strong M k_M h_M_dir
        -- Combined L: M_L.refactor_comp L_g : c_M → a.
        -- Combined R: M_R.refactor_comp R_g : c_M → b.
        have hLc_dir : (M_L.refactor_comp L_g).refactor_IsDirectedWalk :=
          refactor_Walk.refactor_isDirectedWalk_comp M_L L_g hM_L_dir hL_g_dir
        have hRc_dir : (M_R.refactor_comp R_g).refactor_IsDirectedWalk :=
          refactor_Walk.refactor_isDirectedWalk_comp M_R R_g hM_R_dir hR_g_dir
        have hLc_pos : (M_L.refactor_comp L_g).refactor_length ≥ 1 := by
          rw [refactor_Walk.refactor_length_comp]; omega
        have hRc_pos : (M_R.refactor_comp R_g).refactor_length ≥ 1 := by
          rw [refactor_Walk.refactor_length_comp]; omega
        -- M_L.dropLast ⊆ S (via M's interior).
        have hM_L_drop_S : ∀ x ∈ M_L.refactor_vertices.dropLast, x ∈ S :=
          refactor_Walk.refactor_arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx))
        have hM_R_drop_S : ∀ x ∈ M_R.refactor_vertices.dropLast, x ∈ S :=
          refactor_Walk.refactor_arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub
        -- a ∉ M_L.dropLast (since a ∉ S).
        have ha_notin_M_L_drop : a ∉ M_L.refactor_vertices.dropLast := fun h_in =>
          ha_notS (hM_L_drop_S a h_in)
        have ha_notin_M_R_drop : a ∉ M_R.refactor_vertices.dropLast := fun h_in =>
          ha_notS (hM_R_drop_S a h_in)
        have hb_notin_M_L_drop : b ∉ M_L.refactor_vertices.dropLast := fun h_in =>
          hb_notS (hM_L_drop_S b h_in)
        have hb_notin_M_R_drop : b ∉ M_R.refactor_vertices.dropLast := fun h_in =>
          hb_notS (hM_R_drop_S b h_in)
        -- Vertex bounds for combined walks via vertices_comp.
        have h_Lc_vs :
            (M_L.refactor_comp L_g).refactor_vertices = M_L.refactor_vertices.dropLast ++ L_g.refactor_vertices :=
          refactor_Walk.refactor_vertices_comp M_L L_g
        have h_Rc_vs :
            (M_R.refactor_comp R_g).refactor_vertices = M_R.refactor_vertices.dropLast ++ R_g.refactor_vertices :=
          refactor_Walk.refactor_vertices_comp M_R R_g
        have h_L_g_ne : L_g.refactor_vertices ≠ [] := refactor_Walk.refactor_vertices_ne_nil L_g
        have h_R_g_ne : R_g.refactor_vertices ≠ [] := refactor_Walk.refactor_vertices_ne_nil R_g
        have h_Lc_drop : (M_L.refactor_comp L_g).refactor_vertices.dropLast
            = M_L.refactor_vertices.dropLast ++ L_g.refactor_vertices.dropLast := by
          rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
        have h_Rc_drop : (M_R.refactor_comp R_g).refactor_vertices.dropLast
            = M_R.refactor_vertices.dropLast ++ R_g.refactor_vertices.dropLast := by
          rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
        have ha_notin_Lc_drop : a ∉ (M_L.refactor_comp L_g).refactor_vertices.dropLast := by
          rw [h_Lc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact ha_notin_M_L_drop h_M
          · exact ha_notin_L_g_drop h_L
        have ha_notin_Rc : a ∉ (M_R.refactor_comp R_g).refactor_vertices := by
          rw [h_Rc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact ha_notin_M_R_drop h_M
          · exact ha_notin_R_g h_R
        have hb_notin_Lc : b ∉ (M_L.refactor_comp L_g).refactor_vertices := by
          rw [h_Lc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact hb_notin_M_L_drop h_M
          · exact hb_notin_L_g h_L
        have hb_notin_Rc_drop : b ∉ (M_R.refactor_comp R_g).refactor_vertices.dropLast := by
          rw [h_Rc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact hb_notin_M_R_drop h_M
          · exact hb_notin_R_g_drop h_R
        refine ⟨refactor_Walk.refactor_mkBifurcation (M_L.refactor_comp L_g) hLc_dir hLc_pos
                  (M_R.refactor_comp R_g), ?_, ?_⟩
        · have h_src := refactor_Walk.refactor_mkBifurcation_isBifurcationSource
              (M_L.refactor_comp L_g) hLc_dir hLc_pos (M_R.refactor_comp R_g) hRc_dir hRc_pos
              hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
          exact refactor_Walk.refactor_isBifurcationSource_to_isBifurcation _ c_M h_src
        · -- Interior bound: ∀ x ∈ (mkBifurcation Lc Rc).tail.dropLast, x ∈ S ∪ T.
          intro x hx
          rw [refactor_vertices_tail_dropLast_mkBifurcation (M_L.refactor_comp L_g) hLc_dir hLc_pos
                (M_R.refactor_comp R_g) hRc_pos] at hx
          rcases List.mem_append.mp hx with hx_L | hx_R
          · -- x ∈ (M_L.refactor_comp L_g).refactor_vertices.tail.dropLast.reverse.
            rw [List.mem_reverse] at hx_L
            -- x ∈ Lc.tail.dropLast → x ∈ Lc.tail ⊆ Lc.refactor_vertices.
            have hx_Lc : x ∈ (M_L.refactor_comp L_g).refactor_vertices :=
              List.mem_of_mem_tail (List.mem_of_mem_dropLast hx_L)
            rw [h_Lc_vs] at hx_Lc
            rcases List.mem_append.mp hx_Lc with hxM | hxL
            · -- x ∈ M_L.refactor_vertices.dropLast → x ∈ S.
              exact Finset.mem_union_left _ (hM_L_drop_S x hxM)
            · -- x ∈ L_g.refactor_vertices.
              -- Need: x ∈ S ∪ T.  Split based on x ∈ L_g.tail.dropLast or boundary.
              have hLg_vs_eq : L_g.refactor_vertices = vL_p :: L_g.refactor_vertices.tail :=
                refactor_Walk.refactor_vertices_eq_head_cons_tail L_g
              rw [hLg_vs_eq] at hxL
              rcases List.mem_cons.mp hxL with hxL_eq | hxL_tail
              · -- hxL_eq : x = vL_p.  Need x ∈ S ∪ T.
                by_cases h_L_p_pos : L_p.refactor_length ≥ 1
                · rw [hxL_eq]
                  exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                · -- L_p.refactor_length = 0 → vL_p = a → x = a → contradiction.
                  have h_L_p_zero : L_p.refactor_length = 0 := by omega
                  have hvL_eq_a : vL_p = a := by
                    by_contra h_ne
                    have := refactor_Walk.refactor_length_pos_of_ne L_p h_ne
                    omega
                  have hx_eq_a : x = a := hxL_eq.trans hvL_eq_a
                  rw [hx_eq_a] at hx_L
                  -- a ∈ Lc.tail.dropLast → a ∈ Lc.dropLast (via Lc.dropLast = c_M :: Lc.tail.dropLast).
                  have h_Lc_t_ne : (M_L.refactor_comp L_g).refactor_vertices.tail ≠ [] :=
                    refactor_Walk.refactor_tail_vertices_ne_nil_of_pos _ hLc_pos
                  have h_Lc_drop_eq :
                      (M_L.refactor_comp L_g).refactor_vertices.dropLast
                        = c_M :: (M_L.refactor_comp L_g).refactor_vertices.tail.dropLast := by
                    conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail (M_L.refactor_comp L_g)]
                    exact List.dropLast_cons_of_ne_nil h_Lc_t_ne
                  have hx_Lc_drop : a ∈ (M_L.refactor_comp L_g).refactor_vertices.dropLast := by
                    rw [h_Lc_drop_eq]; exact List.mem_cons_of_mem _ hx_L
                  exact absurd hx_Lc_drop ha_notin_Lc_drop
              · -- x ∈ L_g.refactor_vertices.tail.
                by_cases h_L_g_pos : L_g.refactor_length ≥ 1
                · have h_Lg_t_ne : L_g.refactor_vertices.tail ≠ [] :=
                    refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                  have h_Lg_t_last :=
                    refactor_Walk.refactor_tail_getLast_of_pos L_g h_L_g_pos
                  have h_Lg_decomp :
                      L_g.refactor_vertices.tail = L_g.refactor_vertices.tail.dropLast ++ [a] := by
                    have := List.dropLast_append_getLast h_Lg_t_ne
                    rw [h_Lg_t_last] at this
                    exact this.symm
                  rw [h_Lg_decomp] at hxL_tail
                  rcases List.mem_append.mp hxL_tail with hxL_int | hxL_a
                  · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                    · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                    · exact Finset.mem_union_left _ hx_S
                  · rw [List.mem_singleton] at hxL_a
                    rw [hxL_a] at hx_L
                    have h_Lc_t_ne : (M_L.refactor_comp L_g).refactor_vertices.tail ≠ [] :=
                      refactor_Walk.refactor_tail_vertices_ne_nil_of_pos _ hLc_pos
                    have h_Lc_drop_eq :
                        (M_L.refactor_comp L_g).refactor_vertices.dropLast
                          = c_M :: (M_L.refactor_comp L_g).refactor_vertices.tail.dropLast := by
                      conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail (M_L.refactor_comp L_g)]
                      exact List.dropLast_cons_of_ne_nil h_Lc_t_ne
                    have hx_Lc_drop : a ∈ (M_L.refactor_comp L_g).refactor_vertices.dropLast := by
                      rw [h_Lc_drop_eq]; exact List.mem_cons_of_mem _ hx_L
                    exact absurd hx_Lc_drop ha_notin_Lc_drop
                · -- L_g.refactor_length = 0 → L_g.tail = []. Contradiction with hxL_tail.
                  have h_L_g_zero : L_g.refactor_length = 0 := by omega
                  match L_g, h_L_g_zero with
                  | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hxL_tail
          · -- x ∈ (M_R.refactor_comp R_g).refactor_vertices.dropLast.
            rw [h_Rc_drop] at hx_R
            rcases List.mem_append.mp hx_R with hxM | hxR
            · exact Finset.mem_union_left _ (hM_R_drop_S x hxM)
            · -- x ∈ R_g.refactor_vertices.dropLast.
              by_cases h_R_g_pos : R_g.refactor_length ≥ 1
              · have h_Rg_t_ne : R_g.refactor_vertices.tail ≠ [] :=
                  refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_g h_R_g_pos
                have h_Rg_drop_eq :
                    R_g.refactor_vertices.dropLast = vR_p :: R_g.refactor_vertices.tail.dropLast := by
                  conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_g]
                  exact List.dropLast_cons_of_ne_nil h_Rg_t_ne
                rw [h_Rg_drop_eq] at hxR
                rcases List.mem_cons.mp hxR with hxR_eq | hxR_int
                · -- hxR_eq : x = vR_p.  Need x ∈ S ∪ T (vR_p ∉ S, so need ∈ T).
                  by_cases h_R_p_pos : R_p.refactor_length ≥ 1
                  · rw [hxR_eq]
                    exact Finset.mem_union_right _ (hvR_T_if_R_p_pos h_R_p_pos)
                  · -- R_p.refactor_length = 0 → vR_p = b → x = b → contradiction.
                    have h_R_p_zero : R_p.refactor_length = 0 := by omega
                    have hvR_eq_b : vR_p = b := by
                      by_contra h_ne
                      have := refactor_Walk.refactor_length_pos_of_ne R_p h_ne
                      omega
                    have hx_eq_b : x = b := hxR_eq.trans hvR_eq_b
                    rw [hx_eq_b] at hx_R
                    exact absurd hx_R (h_Rc_drop ▸ hb_notin_Rc_drop)
                · rcases hR_g_tdL_sub_S x hxR_int with hx_R_p | hx_S
                  · exact Finset.mem_union_right _ (hR_p_inter_T x hx_R_p)
                  · exact Finset.mem_union_left _ hx_S
              · -- R_g.refactor_length = 0 → R_g.dropLast = []. Contradiction with hxR.
                have h_R_g_zero : R_g.refactor_length = 0 := by omega
                match R_g, h_R_g_zero with
                | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.dropLast] at hxR
      · -- Inl + bid M-hinge.
        obtain ⟨vML, vMR, M_L, M_R, hM_L_dir, hM_R_dir, hMLR_G, _,
                hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
          refactor_Walk.refactor_exists_arms_of_bifurcation_bidir_hinge_strong M k_M hM_split h_M_dir
        -- M_L : refactor_Walk G vML vL_p. M_R : refactor_Walk G vMR vR_p. (vML, vMR) ∈ G.L.
        have hLc_dir : (M_L.refactor_comp L_g).refactor_IsDirectedWalk :=
          refactor_Walk.refactor_isDirectedWalk_comp M_L L_g hM_L_dir hL_g_dir
        have hRc_dir : (M_R.refactor_comp R_g).refactor_IsDirectedWalk :=
          refactor_Walk.refactor_isDirectedWalk_comp M_R R_g hM_R_dir hR_g_dir
        have hM_L_drop_S : ∀ x ∈ M_L.refactor_vertices.dropLast, x ∈ S :=
          refactor_Walk.refactor_arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx))
        have hM_R_drop_S : ∀ x ∈ M_R.refactor_vertices.dropLast, x ∈ S :=
          refactor_Walk.refactor_arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub
        have ha_notin_M_L_drop : a ∉ M_L.refactor_vertices.dropLast := fun h_in =>
          ha_notS (hM_L_drop_S a h_in)
        have ha_notin_M_R_drop : a ∉ M_R.refactor_vertices.dropLast := fun h_in =>
          ha_notS (hM_R_drop_S a h_in)
        have hb_notin_M_L_drop : b ∉ M_L.refactor_vertices.dropLast := fun h_in =>
          hb_notS (hM_L_drop_S b h_in)
        have hb_notin_M_R_drop : b ∉ M_R.refactor_vertices.dropLast := fun h_in =>
          hb_notS (hM_R_drop_S b h_in)
        have h_Lc_vs :
            (M_L.refactor_comp L_g).refactor_vertices = M_L.refactor_vertices.dropLast ++ L_g.refactor_vertices :=
          refactor_Walk.refactor_vertices_comp M_L L_g
        have h_Rc_vs :
            (M_R.refactor_comp R_g).refactor_vertices = M_R.refactor_vertices.dropLast ++ R_g.refactor_vertices :=
          refactor_Walk.refactor_vertices_comp M_R R_g
        have h_L_g_ne : L_g.refactor_vertices ≠ [] := refactor_Walk.refactor_vertices_ne_nil L_g
        have h_R_g_ne : R_g.refactor_vertices ≠ [] := refactor_Walk.refactor_vertices_ne_nil R_g
        have h_Lc_drop : (M_L.refactor_comp L_g).refactor_vertices.dropLast
            = M_L.refactor_vertices.dropLast ++ L_g.refactor_vertices.dropLast := by
          rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
        have h_Rc_drop : (M_R.refactor_comp R_g).refactor_vertices.dropLast
            = M_R.refactor_vertices.dropLast ++ R_g.refactor_vertices.dropLast := by
          rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
        have ha_notin_Lc_drop : a ∉ (M_L.refactor_comp L_g).refactor_vertices.dropLast := by
          rw [h_Lc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact ha_notin_M_L_drop h_M
          · exact ha_notin_L_g_drop h_L
        have ha_notin_Rc : a ∉ (M_R.refactor_comp R_g).refactor_vertices := by
          rw [h_Rc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact ha_notin_M_R_drop h_M
          · exact ha_notin_R_g h_R
        have hb_notin_Lc : b ∉ (M_L.refactor_comp L_g).refactor_vertices := by
          rw [h_Lc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact hb_notin_M_L_drop h_M
          · exact hb_notin_L_g h_L
        have hb_notin_Rc_drop : b ∉ (M_R.refactor_comp R_g).refactor_vertices.dropLast := by
          rw [h_Rc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact hb_notin_M_R_drop h_M
          · exact hb_notin_R_g_drop h_R
        refine ⟨refactor_Walk.refactor_mkBifurcationBidir (M_L.refactor_comp L_g) hLc_dir
                  (M_R.refactor_comp R_g) hMLR_G, ?_, ?_⟩
        · exact refactor_Walk.refactor_mkBifurcationBidir_isBifurcation (M_L.refactor_comp L_g) hLc_dir
            (M_R.refactor_comp R_g) hRc_dir hMLR_G hab_ne ha_notin_Lc_drop ha_notin_Rc
            hb_notin_Lc hb_notin_Rc_drop
        · -- Interior bound.
          intro x hx
          -- bif vertices = Lc.refactor_vertices.reverse.dropLast ++ (vML :: Rc.refactor_vertices).
          -- Need: x ∈ bif.refactor_vertices.tail.dropLast → x ∈ S ∪ T.
          -- We argue from x ∈ bif.refactor_vertices.
          have hx_bif_vs : x ∈
              (refactor_Walk.refactor_mkBifurcationBidir (M_L.refactor_comp L_g) hLc_dir
                (M_R.refactor_comp R_g) hMLR_G).refactor_vertices :=
            List.mem_of_mem_tail (List.mem_of_mem_dropLast hx)
          rw [refactor_Walk.refactor_vertices_mkBifurcationBidir
                (M_L.refactor_comp L_g) hLc_dir (M_R.refactor_comp R_g) hMLR_G] at hx_bif_vs
          rcases List.mem_append.mp hx_bif_vs with hx_Lc_rev | hx_Rc
          · -- x ∈ Lc.refactor_vertices.reverse.dropLast → x ∈ Lc.refactor_vertices and x ≠ a (Lc's target).
            have hx_Lc_vs : x ∈ (M_L.refactor_comp L_g).refactor_vertices := by
              have := List.mem_of_mem_dropLast hx_Lc_rev
              rwa [List.mem_reverse] at this
            -- x ≠ a, since otherwise hx_bif (tail.dropLast) would contradict by giving
            -- a in tail.dropLast.  Actually we need a stronger argument.
            -- We'll show x ∈ Lc.dropLast (excluding the target a).
            -- x ∈ Lc.reverse.dropLast → x is in Lc.reverse but not the last (= a).
            -- Equivalently, x ∈ Lc.tail (= Lc.reverse.dropLast.reverse).
            -- We have hx_Lc_rev : x ∈ Lc.reverse.dropLast.
            -- Lc.reverse = a :: ... (since Lc ends at a). Lc.reverse.dropLast drops the last.
            -- Hmm, this is getting complicated. Let me use a direct approach:
            -- Lc.reverse.dropLast = Lc.tail.reverse (refactor_Walk.refactor_vertices_reverse_dropLast).
            rw [refactor_Walk.refactor_vertices_reverse_dropLast (M_L.refactor_comp L_g)] at hx_Lc_rev
            -- hx_Lc_rev : x ∈ Lc.refactor_vertices.tail.reverse.
            rw [List.mem_reverse] at hx_Lc_rev
            -- hx_Lc_rev : x ∈ Lc.refactor_vertices.tail.
            -- x ∈ Lc.refactor_vertices.tail = (M_L.dropLast ++ L_g.refactor_vertices).tail.
            -- Case-split on M_L.refactor_length.
            by_cases h_M_L_pos : M_L.refactor_length ≥ 1
            · -- M_L.dropLast ≠ [].  Lc.tail = M_L.dropLast.tail ++ L_g.refactor_vertices.
              have h_M_L_drop_ne : M_L.refactor_vertices.dropLast ≠ [] := by
                have h_M_L_t_ne : M_L.refactor_vertices.tail ≠ [] :=
                  refactor_Walk.refactor_tail_vertices_ne_nil_of_pos M_L h_M_L_pos
                rw [refactor_Walk.refactor_vertices_eq_head_cons_tail M_L,
                    List.dropLast_cons_of_ne_nil h_M_L_t_ne]
                exact List.cons_ne_nil _ _
              rw [h_Lc_vs, List.tail_append_of_ne_nil h_M_L_drop_ne] at hx_Lc_rev
              rcases List.mem_append.mp hx_Lc_rev with hxM | hxL
              · -- x ∈ M_L.refactor_vertices.dropLast.tail.
                have hxM_in_drop : x ∈ M_L.refactor_vertices.dropLast :=
                  List.mem_of_mem_tail hxM
                exact Finset.mem_union_left _ (hM_L_drop_S x hxM_in_drop)
              · -- x ∈ L_g.refactor_vertices.  Same analysis as before (with vL_p, L_p.refactor_length cases).
                have hLg_vs_eq : L_g.refactor_vertices = vL_p :: L_g.refactor_vertices.tail :=
                  refactor_Walk.refactor_vertices_eq_head_cons_tail L_g
                rw [hLg_vs_eq] at hxL
                rcases List.mem_cons.mp hxL with hx_eq_vL | hxL_tail
                · -- x = vL_p.
                  by_cases h_L_p_pos : L_p.refactor_length ≥ 1
                  · rw [hx_eq_vL]
                    exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                  · -- L_p.refactor_length = 0 → vL_p = a → x = a, contradicting hx in bif.tail.dropLast.
                    have h_L_p_zero : L_p.refactor_length = 0 := by omega
                    have hvL_eq_a : vL_p = a := by
                      by_contra h_ne
                      have := refactor_Walk.refactor_length_pos_of_ne L_p h_ne
                      omega
                    -- x = vL_p = a. But hx_bif_vs derived from hx in bif.tail.dropLast.
                    -- a ∉ bif.tail.dropLast (a is the bif walk's head).
                    -- More concretely, we need a contradiction via hx.
                    have hx_a : x = a := hx_eq_vL.trans hvL_eq_a
                    rw [hx_a] at hx
                    -- hx : a ∈ bif.tail.dropLast → a ∈ bif.tail → false (a is bif's head).
                    -- Use the bif's IsBifurcation: head ∉ tail.
                    have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                      (M_L.refactor_comp L_g) hLc_dir (M_R.refactor_comp R_g) hRc_dir hMLR_G
                      hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                    have h_head_notin_tail := hbif_bif.2.1
                    -- h_head_notin_tail : a ∉ bif.refactor_vertices.tail.
                    have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                    exact absurd hx_bif_tail h_head_notin_tail
                · -- x ∈ L_g.refactor_vertices.tail.  Case-split on L_g.refactor_length.
                  by_cases h_L_g_pos : L_g.refactor_length ≥ 1
                  · have h_Lg_t_ne : L_g.refactor_vertices.tail ≠ [] :=
                      refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                    have h_Lg_t_last :=
                      refactor_Walk.refactor_tail_getLast_of_pos L_g h_L_g_pos
                    have h_Lg_decomp :
                        L_g.refactor_vertices.tail = L_g.refactor_vertices.tail.dropLast ++ [a] := by
                      have := List.dropLast_append_getLast h_Lg_t_ne
                      rw [h_Lg_t_last] at this
                      exact this.symm
                    rw [h_Lg_decomp] at hxL_tail
                    rcases List.mem_append.mp hxL_tail with hxL_int | hxL_a
                    · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                      · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                      · exact Finset.mem_union_left _ hx_S
                    · rw [List.mem_singleton] at hxL_a
                      rw [hxL_a] at hx
                      have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                        (M_L.refactor_comp L_g) hLc_dir (M_R.refactor_comp R_g) hRc_dir hMLR_G
                        hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                      have h_head_notin_tail := hbif_bif.2.1
                      have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                      exact absurd hx_bif_tail h_head_notin_tail
                  · -- L_g.refactor_length = 0 → L_g.tail = []. hxL_tail vacuous.
                    have h_L_g_zero : L_g.refactor_length = 0 := by omega
                    match L_g, h_L_g_zero with
                    | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hxL_tail
            · -- M_L.refactor_length = 0 → M_L = nil, vML = vL_p.
              -- M_L.dropLast = []. Lc.refactor_vertices = [] ++ L_g.refactor_vertices = L_g.refactor_vertices.
              -- Lc.refactor_vertices.tail = L_g.refactor_vertices.tail.
              have h_M_L_zero : M_L.refactor_length = 0 := by omega
              have hM_L_drop_empty : M_L.refactor_vertices.dropLast = [] := by
                match M_L, h_M_L_zero with
                | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.dropLast]
              rw [h_Lc_vs, hM_L_drop_empty, List.nil_append] at hx_Lc_rev
              -- hx_Lc_rev : x ∈ L_g.refactor_vertices.tail.
              by_cases h_L_g_pos : L_g.refactor_length ≥ 1
              · have h_Lg_t_ne : L_g.refactor_vertices.tail ≠ [] :=
                  refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                have h_Lg_t_last :=
                  refactor_Walk.refactor_tail_getLast_of_pos L_g h_L_g_pos
                have h_Lg_decomp :
                    L_g.refactor_vertices.tail = L_g.refactor_vertices.tail.dropLast ++ [a] := by
                  have := List.dropLast_append_getLast h_Lg_t_ne
                  rw [h_Lg_t_last] at this
                  exact this.symm
                rw [h_Lg_decomp] at hx_Lc_rev
                rcases List.mem_append.mp hx_Lc_rev with hxL_int | hxL_a
                · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                  · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                  · exact Finset.mem_union_left _ hx_S
                · rw [List.mem_singleton] at hxL_a
                  rw [hxL_a] at hx
                  have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                    (M_L.refactor_comp L_g) hLc_dir (M_R.refactor_comp R_g) hRc_dir hMLR_G
                    hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                  have h_head_notin_tail := hbif_bif.2.1
                  have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                  exact absurd hx_bif_tail h_head_notin_tail
              · -- L_g.refactor_length = 0 → L_g.tail = []. Contradiction.
                have h_L_g_zero : L_g.refactor_length = 0 := by omega
                match L_g, h_L_g_zero with
                | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hx_Lc_rev
          · -- x ∈ vML :: Rc.refactor_vertices.
            rcases List.mem_cons.mp hx_Rc with hx_eq_vML | hx_Rc_vs
            · -- x = vML.
              -- vML's status: either vML ∈ S (if M_L.refactor_length ≥ 1) or vML = vL_p
              -- (if M_L = nil), in which case the vL_p analysis applies.
              by_cases h_M_L_pos : M_L.refactor_length ≥ 1
              · -- vML ∈ M_L.dropLast (head). M_L.dropLast ⊆ S. So vML ∈ S.
                have h_M_L_t_ne : M_L.refactor_vertices.tail ≠ [] :=
                  refactor_Walk.refactor_tail_vertices_ne_nil_of_pos M_L h_M_L_pos
                have hvML_in_M_L_drop : vML ∈ M_L.refactor_vertices.dropLast := by
                  rw [refactor_Walk.refactor_vertices_eq_head_cons_tail M_L,
                      List.dropLast_cons_of_ne_nil h_M_L_t_ne]
                  exact List.mem_cons_self
                rw [hx_eq_vML]
                exact Finset.mem_union_left _ (hM_L_drop_S vML hvML_in_M_L_drop)
              · -- M_L.refactor_length = 0 → vML = vL_p. Then either vL_p ∈ T (L_p.refactor_length ≥ 1)
                -- or vL_p = a (then x = a contradicts hx).
                have h_M_L_zero : M_L.refactor_length = 0 := by omega
                have hvML_eq_vL : vML = vL_p := by
                  by_contra h_ne
                  have := refactor_Walk.refactor_length_pos_of_ne M_L h_ne
                  omega
                by_cases h_L_p_pos : L_p.refactor_length ≥ 1
                · rw [hx_eq_vML, hvML_eq_vL]
                  exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                · -- L_p.refactor_length = 0 → vL_p = a → vML = a → x = a → contradiction.
                  have h_L_p_zero : L_p.refactor_length = 0 := by omega
                  have hvL_eq_a : vL_p = a := by
                    by_contra h_ne
                    have := refactor_Walk.refactor_length_pos_of_ne L_p h_ne
                    omega
                  have hx_a : x = a := hx_eq_vML.trans (hvML_eq_vL.trans hvL_eq_a)
                  rw [hx_a] at hx
                  have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                    (M_L.refactor_comp L_g) hLc_dir (M_R.refactor_comp R_g) hRc_dir hMLR_G
                    hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                  have h_head_notin_tail := hbif_bif.2.1
                  have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                  exact absurd hx_bif_tail h_head_notin_tail
            · -- x ∈ Rc.refactor_vertices = M_R.dropLast ++ R_g.refactor_vertices.
              rw [h_Rc_vs] at hx_Rc_vs
              rcases List.mem_append.mp hx_Rc_vs with hxM | hxR
              · exact Finset.mem_union_left _ (hM_R_drop_S x hxM)
              · -- x ∈ R_g.refactor_vertices.
                have hRg_vs_eq : R_g.refactor_vertices = vR_p :: R_g.refactor_vertices.tail :=
                  refactor_Walk.refactor_vertices_eq_head_cons_tail R_g
                rw [hRg_vs_eq] at hxR
                rcases List.mem_cons.mp hxR with hx_eq_vR | hxR_tail
                · -- x = vR_p.
                  by_cases h_R_p_pos : R_p.refactor_length ≥ 1
                  · rw [hx_eq_vR]
                    exact Finset.mem_union_right _ (hvR_T_if_R_p_pos h_R_p_pos)
                  · -- R_p.refactor_length = 0 → vR_p = b → x = b → contradiction (b is bif's last).
                    have h_R_p_zero : R_p.refactor_length = 0 := by omega
                    have hvR_eq_b : vR_p = b := by
                      by_contra h_ne
                      have := refactor_Walk.refactor_length_pos_of_ne R_p h_ne
                      omega
                    have hx_b : x = b := hx_eq_vR.trans hvR_eq_b
                    rw [hx_b] at hx
                    -- hx : b ∈ bif.tail.dropLast.  b is bif's last.
                    have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                      (M_L.refactor_comp L_g) hLc_dir (M_R.refactor_comp R_g) hRc_dir hMLR_G
                      hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                    have h_last_notin_drop := hbif_bif.2.2.1
                    -- h_last_notin_drop : b ∉ bif.refactor_vertices.dropLast.
                    -- hx : b ∈ bif.refactor_vertices.tail.dropLast → b ∈ bif.refactor_vertices.dropLast.
                    -- (Because tail.dropLast ⊆ dropLast for non-trivial walks.)
                    have h_bif_t_ne : (refactor_Walk.refactor_mkBifurcationBidir (M_L.refactor_comp L_g) hLc_dir
                                         (M_R.refactor_comp R_g) hMLR_G).refactor_vertices.tail ≠ [] := by
                      have h_bif_pos := refactor_Walk.refactor_length_pos_of_isBifurcation hbif_bif
                      exact refactor_Walk.refactor_tail_vertices_ne_nil_of_pos _ h_bif_pos
                    have h_bif_drop_eq :
                        (refactor_Walk.refactor_mkBifurcationBidir (M_L.refactor_comp L_g) hLc_dir
                          (M_R.refactor_comp R_g) hMLR_G).refactor_vertices.dropLast
                        = a :: (refactor_Walk.refactor_mkBifurcationBidir (M_L.refactor_comp L_g) hLc_dir
                                  (M_R.refactor_comp R_g) hMLR_G).refactor_vertices.tail.dropLast := by
                      conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail _]
                      exact List.dropLast_cons_of_ne_nil h_bif_t_ne
                    have hx_bif_drop : b ∈ (refactor_Walk.refactor_mkBifurcationBidir (M_L.refactor_comp L_g) hLc_dir
                                              (M_R.refactor_comp R_g) hMLR_G).refactor_vertices.dropLast := by
                      rw [h_bif_drop_eq]; exact List.mem_cons_of_mem _ hx
                    exact absurd hx_bif_drop h_last_notin_drop
                · -- x ∈ R_g.refactor_vertices.tail.  Case-split on R_g.refactor_length.
                  by_cases h_R_g_pos : R_g.refactor_length ≥ 1
                  · have h_Rg_t_ne : R_g.refactor_vertices.tail ≠ [] :=
                      refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_g h_R_g_pos
                    have h_Rg_t_last :=
                      refactor_Walk.refactor_tail_getLast_of_pos R_g h_R_g_pos
                    have h_Rg_decomp :
                        R_g.refactor_vertices.tail = R_g.refactor_vertices.tail.dropLast ++ [b] := by
                      have := List.dropLast_append_getLast h_Rg_t_ne
                      rw [h_Rg_t_last] at this
                      exact this.symm
                    rw [h_Rg_decomp] at hxR_tail
                    rcases List.mem_append.mp hxR_tail with hxR_int | hxR_b
                    · rcases hR_g_tdL_sub_S x hxR_int with hx_R_p | hx_S
                      · exact Finset.mem_union_right _ (hR_p_inter_T x hx_R_p)
                      · exact Finset.mem_union_left _ hx_S
                    · rw [List.mem_singleton] at hxR_b
                      rw [hxR_b] at hx
                      have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                        (M_L.refactor_comp L_g) hLc_dir (M_R.refactor_comp R_g) hRc_dir hMLR_G
                        hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                      have h_last_notin_drop := hbif_bif.2.2.1
                      have h_bif_t_ne : (refactor_Walk.refactor_mkBifurcationBidir (M_L.refactor_comp L_g) hLc_dir
                                           (M_R.refactor_comp R_g) hMLR_G).refactor_vertices.tail ≠ [] := by
                        have h_bif_pos := refactor_Walk.refactor_length_pos_of_isBifurcation hbif_bif
                        exact refactor_Walk.refactor_tail_vertices_ne_nil_of_pos _ h_bif_pos
                      have h_bif_drop_eq :
                          (refactor_Walk.refactor_mkBifurcationBidir (M_L.refactor_comp L_g) hLc_dir
                            (M_R.refactor_comp R_g) hMLR_G).refactor_vertices.dropLast
                          = a :: (refactor_Walk.refactor_mkBifurcationBidir (M_L.refactor_comp L_g) hLc_dir
                                    (M_R.refactor_comp R_g) hMLR_G).refactor_vertices.tail.dropLast := by
                        conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail _]
                        exact List.dropLast_cons_of_ne_nil h_bif_t_ne
                      have hx_bif_drop : b ∈ (refactor_Walk.refactor_mkBifurcationBidir (M_L.refactor_comp L_g) hLc_dir
                                                (M_R.refactor_comp R_g) hMLR_G).refactor_vertices.dropLast := by
                        rw [h_bif_drop_eq]; exact List.mem_cons_of_mem _ hx
                      exact absurd hx_bif_drop h_last_notin_drop
                  · -- R_g.refactor_length = 0 → R_g.tail = []. Contradiction.
                    have h_R_g_zero : R_g.refactor_length = 0 := by omega
                    match R_g, h_R_g_zero with
                    | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hxR_tail
    · -- Inr case: M : refactor_Walk G vR_p vL_p.
      have hM_split_ex : ∃ k, M.refactor_IsBifurcationWithSplit k := hM_bif.2.2.2
      obtain ⟨k_M, hM_split⟩ := hM_split_ex
      have hM_pos : M.refactor_length ≥ 1 := refactor_Walk.refactor_length_pos_of_isBifurcation hM_bif
      -- For inr orientation: M.head = vR_p, M.tail's last = vL_p.
      have hvR_M_tail : vR_p ∉ M.refactor_vertices.tail := hM_bif.2.1
      have hvL_M_drop : vL_p ∉ M.refactor_vertices.dropLast := hM_bif.2.2.1
      by_cases h_M_dir : M.refactor_IsBifurcationDirectedHingeWithSplit k_M
      · -- Inr + directed M-hinge.
        obtain ⟨c_M, M_L, M_R, hM_L_dir, hM_R_dir, hM_L_pos, hM_R_pos, _,
                hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
          refactor_Walk.refactor_exists_arms_of_bifurcation_directed_hinge_strong M k_M h_M_dir
        -- M_L : refactor_Walk G c_M vR_p, M_R : refactor_Walk G c_M vL_p.
        -- Combined L (to a via vL_p): M_R.refactor_comp L_g : refactor_Walk G c_M a.
        -- Combined R (to b via vR_p): M_L.refactor_comp R_g : refactor_Walk G c_M b.
        have hLc_dir : (M_R.refactor_comp L_g).refactor_IsDirectedWalk :=
          refactor_Walk.refactor_isDirectedWalk_comp M_R L_g hM_R_dir hL_g_dir
        have hRc_dir : (M_L.refactor_comp R_g).refactor_IsDirectedWalk :=
          refactor_Walk.refactor_isDirectedWalk_comp M_L R_g hM_L_dir hR_g_dir
        have hLc_pos : (M_R.refactor_comp L_g).refactor_length ≥ 1 := by
          rw [refactor_Walk.refactor_length_comp]; omega
        have hRc_pos : (M_L.refactor_comp R_g).refactor_length ≥ 1 := by
          rw [refactor_Walk.refactor_length_comp]; omega
        -- M_L.dropLast ⊆ S, M_R.dropLast ⊆ S via M's interior.
        have hM_L_drop_S : ∀ x ∈ M_L.refactor_vertices.dropLast, x ∈ S :=
          refactor_Walk.refactor_arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx))
        have hM_R_drop_S : ∀ x ∈ M_R.refactor_vertices.dropLast, x ∈ S :=
          refactor_Walk.refactor_arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub
        have ha_notin_M_L_drop : a ∉ M_L.refactor_vertices.dropLast := fun h_in =>
          ha_notS (hM_L_drop_S a h_in)
        have ha_notin_M_R_drop : a ∉ M_R.refactor_vertices.dropLast := fun h_in =>
          ha_notS (hM_R_drop_S a h_in)
        have hb_notin_M_L_drop : b ∉ M_L.refactor_vertices.dropLast := fun h_in =>
          hb_notS (hM_L_drop_S b h_in)
        have hb_notin_M_R_drop : b ∉ M_R.refactor_vertices.dropLast := fun h_in =>
          hb_notS (hM_R_drop_S b h_in)
        have h_Lc_vs :
            (M_R.refactor_comp L_g).refactor_vertices = M_R.refactor_vertices.dropLast ++ L_g.refactor_vertices :=
          refactor_Walk.refactor_vertices_comp M_R L_g
        have h_Rc_vs :
            (M_L.refactor_comp R_g).refactor_vertices = M_L.refactor_vertices.dropLast ++ R_g.refactor_vertices :=
          refactor_Walk.refactor_vertices_comp M_L R_g
        have h_L_g_ne : L_g.refactor_vertices ≠ [] := refactor_Walk.refactor_vertices_ne_nil L_g
        have h_R_g_ne : R_g.refactor_vertices ≠ [] := refactor_Walk.refactor_vertices_ne_nil R_g
        have h_Lc_drop : (M_R.refactor_comp L_g).refactor_vertices.dropLast
            = M_R.refactor_vertices.dropLast ++ L_g.refactor_vertices.dropLast := by
          rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
        have h_Rc_drop : (M_L.refactor_comp R_g).refactor_vertices.dropLast
            = M_L.refactor_vertices.dropLast ++ R_g.refactor_vertices.dropLast := by
          rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
        have ha_notin_Lc_drop : a ∉ (M_R.refactor_comp L_g).refactor_vertices.dropLast := by
          rw [h_Lc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact ha_notin_M_R_drop h_M
          · exact ha_notin_L_g_drop h_L
        have ha_notin_Rc : a ∉ (M_L.refactor_comp R_g).refactor_vertices := by
          rw [h_Rc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact ha_notin_M_L_drop h_M
          · exact ha_notin_R_g h_R
        have hb_notin_Lc : b ∉ (M_R.refactor_comp L_g).refactor_vertices := by
          rw [h_Lc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact hb_notin_M_R_drop h_M
          · exact hb_notin_L_g h_L
        have hb_notin_Rc_drop : b ∉ (M_L.refactor_comp R_g).refactor_vertices.dropLast := by
          rw [h_Rc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact hb_notin_M_L_drop h_M
          · exact hb_notin_R_g_drop h_R
        refine ⟨refactor_Walk.refactor_mkBifurcation (M_R.refactor_comp L_g) hLc_dir hLc_pos
                  (M_L.refactor_comp R_g), ?_, ?_⟩
        · have h_src := refactor_Walk.refactor_mkBifurcation_isBifurcationSource
              (M_R.refactor_comp L_g) hLc_dir hLc_pos (M_L.refactor_comp R_g) hRc_dir hRc_pos
              hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
          exact refactor_Walk.refactor_isBifurcationSource_to_isBifurcation _ c_M h_src
        · intro x hx
          rw [refactor_vertices_tail_dropLast_mkBifurcation (M_R.refactor_comp L_g) hLc_dir hLc_pos
                (M_L.refactor_comp R_g) hRc_pos] at hx
          rcases List.mem_append.mp hx with hx_L | hx_R
          · rw [List.mem_reverse] at hx_L
            have hx_Lc : x ∈ (M_R.refactor_comp L_g).refactor_vertices :=
              List.mem_of_mem_tail (List.mem_of_mem_dropLast hx_L)
            rw [h_Lc_vs] at hx_Lc
            rcases List.mem_append.mp hx_Lc with hxM | hxL
            · exact Finset.mem_union_left _ (hM_R_drop_S x hxM)
            · have hLg_vs_eq : L_g.refactor_vertices = vL_p :: L_g.refactor_vertices.tail :=
                refactor_Walk.refactor_vertices_eq_head_cons_tail L_g
              rw [hLg_vs_eq] at hxL
              rcases List.mem_cons.mp hxL with hx_eq_vL | hxL_tail
              · by_cases h_L_p_pos : L_p.refactor_length ≥ 1
                · rw [hx_eq_vL]
                  exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                · have h_L_p_zero : L_p.refactor_length = 0 := by omega
                  have hvL_eq_a : vL_p = a := by
                    by_contra h_ne
                    have := refactor_Walk.refactor_length_pos_of_ne L_p h_ne
                    omega
                  have hx_eq_a : x = a := hx_eq_vL.trans hvL_eq_a
                  rw [hx_eq_a] at hx_L
                  have h_Lc_t_ne : (M_R.refactor_comp L_g).refactor_vertices.tail ≠ [] :=
                    refactor_Walk.refactor_tail_vertices_ne_nil_of_pos _ hLc_pos
                  have h_Lc_drop_eq :
                      (M_R.refactor_comp L_g).refactor_vertices.dropLast
                        = c_M :: (M_R.refactor_comp L_g).refactor_vertices.tail.dropLast := by
                    conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail (M_R.refactor_comp L_g)]
                    exact List.dropLast_cons_of_ne_nil h_Lc_t_ne
                  have hx_Lc_drop : a ∈ (M_R.refactor_comp L_g).refactor_vertices.dropLast := by
                    rw [h_Lc_drop_eq]; exact List.mem_cons_of_mem _ hx_L
                  exact absurd hx_Lc_drop ha_notin_Lc_drop
              · by_cases h_L_g_pos : L_g.refactor_length ≥ 1
                · have h_Lg_t_ne : L_g.refactor_vertices.tail ≠ [] :=
                    refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                  have h_Lg_t_last :=
                    refactor_Walk.refactor_tail_getLast_of_pos L_g h_L_g_pos
                  have h_Lg_decomp :
                      L_g.refactor_vertices.tail = L_g.refactor_vertices.tail.dropLast ++ [a] := by
                    have := List.dropLast_append_getLast h_Lg_t_ne
                    rw [h_Lg_t_last] at this
                    exact this.symm
                  rw [h_Lg_decomp] at hxL_tail
                  rcases List.mem_append.mp hxL_tail with hxL_int | hxL_a
                  · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                    · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                    · exact Finset.mem_union_left _ hx_S
                  · rw [List.mem_singleton] at hxL_a
                    rw [hxL_a] at hx_L
                    have h_Lc_t_ne : (M_R.refactor_comp L_g).refactor_vertices.tail ≠ [] :=
                      refactor_Walk.refactor_tail_vertices_ne_nil_of_pos _ hLc_pos
                    have h_Lc_drop_eq :
                        (M_R.refactor_comp L_g).refactor_vertices.dropLast
                          = c_M :: (M_R.refactor_comp L_g).refactor_vertices.tail.dropLast := by
                      conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail (M_R.refactor_comp L_g)]
                      exact List.dropLast_cons_of_ne_nil h_Lc_t_ne
                    have hx_Lc_drop : a ∈ (M_R.refactor_comp L_g).refactor_vertices.dropLast := by
                      rw [h_Lc_drop_eq]; exact List.mem_cons_of_mem _ hx_L
                    exact absurd hx_Lc_drop ha_notin_Lc_drop
                · have h_L_g_zero : L_g.refactor_length = 0 := by omega
                  match L_g, h_L_g_zero with
                  | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hxL_tail
          · rw [h_Rc_drop] at hx_R
            rcases List.mem_append.mp hx_R with hxM | hxR
            · exact Finset.mem_union_left _ (hM_L_drop_S x hxM)
            · by_cases h_R_g_pos : R_g.refactor_length ≥ 1
              · have h_Rg_t_ne : R_g.refactor_vertices.tail ≠ [] :=
                  refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_g h_R_g_pos
                have h_Rg_drop_eq :
                    R_g.refactor_vertices.dropLast = vR_p :: R_g.refactor_vertices.tail.dropLast := by
                  conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_g]
                  exact List.dropLast_cons_of_ne_nil h_Rg_t_ne
                rw [h_Rg_drop_eq] at hxR
                rcases List.mem_cons.mp hxR with hxR_eq | hxR_int
                · by_cases h_R_p_pos : R_p.refactor_length ≥ 1
                  · rw [hxR_eq]
                    exact Finset.mem_union_right _ (hvR_T_if_R_p_pos h_R_p_pos)
                  · have h_R_p_zero : R_p.refactor_length = 0 := by omega
                    have hvR_eq_b : vR_p = b := by
                      by_contra h_ne
                      have := refactor_Walk.refactor_length_pos_of_ne R_p h_ne
                      omega
                    have hx_eq_b : x = b := hxR_eq.trans hvR_eq_b
                    rw [hx_eq_b] at hx_R
                    exact absurd hx_R (h_Rc_drop ▸ hb_notin_Rc_drop)
                · rcases hR_g_tdL_sub_S x hxR_int with hx_R_p | hx_S
                  · exact Finset.mem_union_right _ (hR_p_inter_T x hx_R_p)
                  · exact Finset.mem_union_left _ hx_S
              · have h_R_g_zero : R_g.refactor_length = 0 := by omega
                match R_g, h_R_g_zero with
                | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.dropLast] at hxR
      · -- Inr + bid M-hinge.
        obtain ⟨vML, vMR, M_L, M_R, hM_L_dir, hM_R_dir, hMLR_G, _,
                hM_L_sub, hM_R_sub, hM_L_drop_sub, hM_R_drop_sub⟩ :=
          refactor_Walk.refactor_exists_arms_of_bifurcation_bidir_hinge_strong M k_M hM_split h_M_dir
        -- M_L : refactor_Walk G vML vR_p. M_R : refactor_Walk G vMR vL_p.
        -- s(vML, vMR) ∈ G.L from the bidirected hinge.
        -- Combined L (to a via vL_p): M_R.refactor_comp L_g : refactor_Walk G vMR a.
        -- Combined R (to b via vR_p): M_L.refactor_comp R_g : refactor_Walk G vML b.
        -- Hinge swap: refactor's `G.L : Finset (Sym2 Node)` is
        -- definitionally swap-symmetric; original code used
        -- `G.hL_symm hMLR_G` which has no counterpart under refactor.
        -- We rewrite via `Sym2.eq_swap` to align the orientation.
        have hMLR_sym : s(vMR, vML) ∈ G.L := by rw [Sym2.eq_swap]; exact hMLR_G
        have hLc_dir : (M_R.refactor_comp L_g).refactor_IsDirectedWalk :=
          refactor_Walk.refactor_isDirectedWalk_comp M_R L_g hM_R_dir hL_g_dir
        have hRc_dir : (M_L.refactor_comp R_g).refactor_IsDirectedWalk :=
          refactor_Walk.refactor_isDirectedWalk_comp M_L R_g hM_L_dir hR_g_dir
        have hM_L_drop_S : ∀ x ∈ M_L.refactor_vertices.dropLast, x ∈ S :=
          refactor_Walk.refactor_arm_dropLast_in_W hM_bif hM_W hM_L_drop_sub
            (fun x hx => hM_L_sub x (List.mem_of_mem_dropLast hx))
        have hM_R_drop_S : ∀ x ∈ M_R.refactor_vertices.dropLast, x ∈ S :=
          refactor_Walk.refactor_arm_dropLast_in_W hM_bif hM_W
            (fun x hx => hM_R_sub x (List.mem_of_mem_dropLast hx)) hM_R_drop_sub
        have ha_notin_M_L_drop : a ∉ M_L.refactor_vertices.dropLast := fun h_in =>
          ha_notS (hM_L_drop_S a h_in)
        have ha_notin_M_R_drop : a ∉ M_R.refactor_vertices.dropLast := fun h_in =>
          ha_notS (hM_R_drop_S a h_in)
        have hb_notin_M_L_drop : b ∉ M_L.refactor_vertices.dropLast := fun h_in =>
          hb_notS (hM_L_drop_S b h_in)
        have hb_notin_M_R_drop : b ∉ M_R.refactor_vertices.dropLast := fun h_in =>
          hb_notS (hM_R_drop_S b h_in)
        have h_Lc_vs :
            (M_R.refactor_comp L_g).refactor_vertices = M_R.refactor_vertices.dropLast ++ L_g.refactor_vertices :=
          refactor_Walk.refactor_vertices_comp M_R L_g
        have h_Rc_vs :
            (M_L.refactor_comp R_g).refactor_vertices = M_L.refactor_vertices.dropLast ++ R_g.refactor_vertices :=
          refactor_Walk.refactor_vertices_comp M_L R_g
        have h_L_g_ne : L_g.refactor_vertices ≠ [] := refactor_Walk.refactor_vertices_ne_nil L_g
        have h_R_g_ne : R_g.refactor_vertices ≠ [] := refactor_Walk.refactor_vertices_ne_nil R_g
        have h_Lc_drop : (M_R.refactor_comp L_g).refactor_vertices.dropLast
            = M_R.refactor_vertices.dropLast ++ L_g.refactor_vertices.dropLast := by
          rw [h_Lc_vs]; exact List.dropLast_append_of_ne_nil h_L_g_ne
        have h_Rc_drop : (M_L.refactor_comp R_g).refactor_vertices.dropLast
            = M_L.refactor_vertices.dropLast ++ R_g.refactor_vertices.dropLast := by
          rw [h_Rc_vs]; exact List.dropLast_append_of_ne_nil h_R_g_ne
        have ha_notin_Lc_drop : a ∉ (M_R.refactor_comp L_g).refactor_vertices.dropLast := by
          rw [h_Lc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact ha_notin_M_R_drop h_M
          · exact ha_notin_L_g_drop h_L
        have ha_notin_Rc : a ∉ (M_L.refactor_comp R_g).refactor_vertices := by
          rw [h_Rc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact ha_notin_M_L_drop h_M
          · exact ha_notin_R_g h_R
        have hb_notin_Lc : b ∉ (M_R.refactor_comp L_g).refactor_vertices := by
          rw [h_Lc_vs]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_L
          · exact hb_notin_M_R_drop h_M
          · exact hb_notin_L_g h_L
        have hb_notin_Rc_drop : b ∉ (M_L.refactor_comp R_g).refactor_vertices.dropLast := by
          rw [h_Rc_drop]
          intro h_in
          rcases List.mem_append.mp h_in with h_M | h_R
          · exact hb_notin_M_L_drop h_M
          · exact hb_notin_R_g_drop h_R
        refine ⟨refactor_Walk.refactor_mkBifurcationBidir (M_R.refactor_comp L_g) hLc_dir
                  (M_L.refactor_comp R_g) hMLR_sym, ?_, ?_⟩
        · exact refactor_Walk.refactor_mkBifurcationBidir_isBifurcation (M_R.refactor_comp L_g) hLc_dir
            (M_L.refactor_comp R_g) hRc_dir hMLR_sym hab_ne ha_notin_Lc_drop ha_notin_Rc
            hb_notin_Lc hb_notin_Rc_drop
        · -- Interior bound.
          intro x hx
          have hx_bif_vs : x ∈
              (refactor_Walk.refactor_mkBifurcationBidir (M_R.refactor_comp L_g) hLc_dir
                (M_L.refactor_comp R_g) hMLR_sym).refactor_vertices :=
            List.mem_of_mem_tail (List.mem_of_mem_dropLast hx)
          rw [refactor_Walk.refactor_vertices_mkBifurcationBidir
                (M_R.refactor_comp L_g) hLc_dir (M_L.refactor_comp R_g) hMLR_sym] at hx_bif_vs
          rcases List.mem_append.mp hx_bif_vs with hx_Lc_rev | hx_Rc
          · rw [refactor_Walk.refactor_vertices_reverse_dropLast (M_R.refactor_comp L_g)] at hx_Lc_rev
            rw [List.mem_reverse] at hx_Lc_rev
            by_cases h_M_R_pos : M_R.refactor_length ≥ 1
            · have h_M_R_drop_ne : M_R.refactor_vertices.dropLast ≠ [] := by
                have h_M_R_t_ne : M_R.refactor_vertices.tail ≠ [] :=
                  refactor_Walk.refactor_tail_vertices_ne_nil_of_pos M_R h_M_R_pos
                rw [refactor_Walk.refactor_vertices_eq_head_cons_tail M_R,
                    List.dropLast_cons_of_ne_nil h_M_R_t_ne]
                exact List.cons_ne_nil _ _
              rw [h_Lc_vs, List.tail_append_of_ne_nil h_M_R_drop_ne] at hx_Lc_rev
              rcases List.mem_append.mp hx_Lc_rev with hxM | hxL
              · have hxM_in_drop : x ∈ M_R.refactor_vertices.dropLast :=
                  List.mem_of_mem_tail hxM
                exact Finset.mem_union_left _ (hM_R_drop_S x hxM_in_drop)
              · have hLg_vs_eq : L_g.refactor_vertices = vL_p :: L_g.refactor_vertices.tail :=
                  refactor_Walk.refactor_vertices_eq_head_cons_tail L_g
                rw [hLg_vs_eq] at hxL
                rcases List.mem_cons.mp hxL with hx_eq_vL | hxL_tail
                · by_cases h_L_p_pos : L_p.refactor_length ≥ 1
                  · rw [hx_eq_vL]
                    exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                  · have h_L_p_zero : L_p.refactor_length = 0 := by omega
                    have hvL_eq_a : vL_p = a := by
                      by_contra h_ne
                      have := refactor_Walk.refactor_length_pos_of_ne L_p h_ne
                      omega
                    have hx_a : x = a := hx_eq_vL.trans hvL_eq_a
                    rw [hx_a] at hx
                    have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                      (M_R.refactor_comp L_g) hLc_dir (M_L.refactor_comp R_g) hRc_dir hMLR_sym
                      hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                    have h_head_notin_tail := hbif_bif.2.1
                    have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                    exact absurd hx_bif_tail h_head_notin_tail
                · by_cases h_L_g_pos : L_g.refactor_length ≥ 1
                  · have h_Lg_t_ne : L_g.refactor_vertices.tail ≠ [] :=
                      refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                    have h_Lg_t_last :=
                      refactor_Walk.refactor_tail_getLast_of_pos L_g h_L_g_pos
                    have h_Lg_decomp :
                        L_g.refactor_vertices.tail = L_g.refactor_vertices.tail.dropLast ++ [a] := by
                      have := List.dropLast_append_getLast h_Lg_t_ne
                      rw [h_Lg_t_last] at this
                      exact this.symm
                    rw [h_Lg_decomp] at hxL_tail
                    rcases List.mem_append.mp hxL_tail with hxL_int | hxL_a
                    · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                      · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                      · exact Finset.mem_union_left _ hx_S
                    · rw [List.mem_singleton] at hxL_a
                      rw [hxL_a] at hx
                      have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                        (M_R.refactor_comp L_g) hLc_dir (M_L.refactor_comp R_g) hRc_dir hMLR_sym
                        hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                      have h_head_notin_tail := hbif_bif.2.1
                      have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                      exact absurd hx_bif_tail h_head_notin_tail
                  · have h_L_g_zero : L_g.refactor_length = 0 := by omega
                    match L_g, h_L_g_zero with
                    | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hxL_tail
            · have h_M_R_zero : M_R.refactor_length = 0 := by omega
              have hM_R_drop_empty : M_R.refactor_vertices.dropLast = [] := by
                match M_R, h_M_R_zero with
                | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.dropLast]
              rw [h_Lc_vs, hM_R_drop_empty, List.nil_append] at hx_Lc_rev
              by_cases h_L_g_pos : L_g.refactor_length ≥ 1
              · have h_Lg_t_ne : L_g.refactor_vertices.tail ≠ [] :=
                  refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_g h_L_g_pos
                have h_Lg_t_last :=
                  refactor_Walk.refactor_tail_getLast_of_pos L_g h_L_g_pos
                have h_Lg_decomp :
                    L_g.refactor_vertices.tail = L_g.refactor_vertices.tail.dropLast ++ [a] := by
                  have := List.dropLast_append_getLast h_Lg_t_ne
                  rw [h_Lg_t_last] at this
                  exact this.symm
                rw [h_Lg_decomp] at hx_Lc_rev
                rcases List.mem_append.mp hx_Lc_rev with hxL_int | hxL_a
                · rcases hL_g_tdL_sub_S x hxL_int with hx_L_p | hx_S
                  · exact Finset.mem_union_right _ (hL_p_inter_T x hx_L_p)
                  · exact Finset.mem_union_left _ hx_S
                · rw [List.mem_singleton] at hxL_a
                  rw [hxL_a] at hx
                  have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                    (M_R.refactor_comp L_g) hLc_dir (M_L.refactor_comp R_g) hRc_dir hMLR_sym
                    hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                  have h_head_notin_tail := hbif_bif.2.1
                  have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                  exact absurd hx_bif_tail h_head_notin_tail
              · have h_L_g_zero : L_g.refactor_length = 0 := by omega
                match L_g, h_L_g_zero with
                | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hx_Lc_rev
          · -- x ∈ vMR :: Rc.refactor_vertices.
            rcases List.mem_cons.mp hx_Rc with hx_eq_vMR | hx_Rc_vs
            · -- x = vMR.
              by_cases h_M_R_pos : M_R.refactor_length ≥ 1
              · have h_M_R_t_ne : M_R.refactor_vertices.tail ≠ [] :=
                  refactor_Walk.refactor_tail_vertices_ne_nil_of_pos M_R h_M_R_pos
                have hvMR_in_M_R_drop : vMR ∈ M_R.refactor_vertices.dropLast := by
                  rw [refactor_Walk.refactor_vertices_eq_head_cons_tail M_R,
                      List.dropLast_cons_of_ne_nil h_M_R_t_ne]
                  exact List.mem_cons_self
                rw [hx_eq_vMR]
                exact Finset.mem_union_left _ (hM_R_drop_S vMR hvMR_in_M_R_drop)
              · -- M_R.refactor_length = 0 → vMR = vL_p.
                have h_M_R_zero : M_R.refactor_length = 0 := by omega
                have hvMR_eq_vL : vMR = vL_p := by
                  by_contra h_ne
                  have := refactor_Walk.refactor_length_pos_of_ne M_R h_ne
                  omega
                by_cases h_L_p_pos : L_p.refactor_length ≥ 1
                · rw [hx_eq_vMR, hvMR_eq_vL]
                  exact Finset.mem_union_right _ (hvL_T_if_L_p_pos h_L_p_pos)
                · have h_L_p_zero : L_p.refactor_length = 0 := by omega
                  have hvL_eq_a : vL_p = a := by
                    by_contra h_ne
                    have := refactor_Walk.refactor_length_pos_of_ne L_p h_ne
                    omega
                  have hx_a : x = a := hx_eq_vMR.trans (hvMR_eq_vL.trans hvL_eq_a)
                  rw [hx_a] at hx
                  have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                    (M_R.refactor_comp L_g) hLc_dir (M_L.refactor_comp R_g) hRc_dir hMLR_sym
                    hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                  have h_head_notin_tail := hbif_bif.2.1
                  have hx_bif_tail : a ∈ _ := List.mem_of_mem_dropLast hx
                  exact absurd hx_bif_tail h_head_notin_tail
            · rw [h_Rc_vs] at hx_Rc_vs
              rcases List.mem_append.mp hx_Rc_vs with hxM | hxR
              · exact Finset.mem_union_left _ (hM_L_drop_S x hxM)
              · have hRg_vs_eq : R_g.refactor_vertices = vR_p :: R_g.refactor_vertices.tail :=
                  refactor_Walk.refactor_vertices_eq_head_cons_tail R_g
                rw [hRg_vs_eq] at hxR
                rcases List.mem_cons.mp hxR with hx_eq_vR | hxR_tail
                · by_cases h_R_p_pos : R_p.refactor_length ≥ 1
                  · rw [hx_eq_vR]
                    exact Finset.mem_union_right _ (hvR_T_if_R_p_pos h_R_p_pos)
                  · have h_R_p_zero : R_p.refactor_length = 0 := by omega
                    have hvR_eq_b : vR_p = b := by
                      by_contra h_ne
                      have := refactor_Walk.refactor_length_pos_of_ne R_p h_ne
                      omega
                    have hx_b : x = b := hx_eq_vR.trans hvR_eq_b
                    rw [hx_b] at hx
                    have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                      (M_R.refactor_comp L_g) hLc_dir (M_L.refactor_comp R_g) hRc_dir hMLR_sym
                      hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                    have h_last_notin_drop := hbif_bif.2.2.1
                    have h_bif_t_ne :
                        (refactor_Walk.refactor_mkBifurcationBidir (M_R.refactor_comp L_g) hLc_dir
                            (M_L.refactor_comp R_g) hMLR_sym).refactor_vertices.tail ≠ [] := by
                      have h_bif_pos := refactor_Walk.refactor_length_pos_of_isBifurcation hbif_bif
                      exact refactor_Walk.refactor_tail_vertices_ne_nil_of_pos _ h_bif_pos
                    have h_bif_drop_eq :
                        (refactor_Walk.refactor_mkBifurcationBidir (M_R.refactor_comp L_g) hLc_dir
                            (M_L.refactor_comp R_g) hMLR_sym).refactor_vertices.dropLast
                        = a :: (refactor_Walk.refactor_mkBifurcationBidir (M_R.refactor_comp L_g) hLc_dir
                                    (M_L.refactor_comp R_g) hMLR_sym).refactor_vertices.tail.dropLast := by
                      conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail _]
                      exact List.dropLast_cons_of_ne_nil h_bif_t_ne
                    have hx_bif_drop : b ∈
                        (refactor_Walk.refactor_mkBifurcationBidir (M_R.refactor_comp L_g) hLc_dir
                            (M_L.refactor_comp R_g) hMLR_sym).refactor_vertices.dropLast := by
                      rw [h_bif_drop_eq]; exact List.mem_cons_of_mem _ hx
                    exact absurd hx_bif_drop h_last_notin_drop
                · by_cases h_R_g_pos : R_g.refactor_length ≥ 1
                  · have h_Rg_t_ne : R_g.refactor_vertices.tail ≠ [] :=
                      refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_g h_R_g_pos
                    have h_Rg_t_last :=
                      refactor_Walk.refactor_tail_getLast_of_pos R_g h_R_g_pos
                    have h_Rg_decomp :
                        R_g.refactor_vertices.tail = R_g.refactor_vertices.tail.dropLast ++ [b] := by
                      have := List.dropLast_append_getLast h_Rg_t_ne
                      rw [h_Rg_t_last] at this
                      exact this.symm
                    rw [h_Rg_decomp] at hxR_tail
                    rcases List.mem_append.mp hxR_tail with hxR_int | hxR_b
                    · rcases hR_g_tdL_sub_S x hxR_int with hx_R_p | hx_S
                      · exact Finset.mem_union_right _ (hR_p_inter_T x hx_R_p)
                      · exact Finset.mem_union_left _ hx_S
                    · rw [List.mem_singleton] at hxR_b
                      rw [hxR_b] at hx
                      have hbif_bif := refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
                        (M_R.refactor_comp L_g) hLc_dir (M_L.refactor_comp R_g) hRc_dir hMLR_sym
                        hab_ne ha_notin_Lc_drop ha_notin_Rc hb_notin_Lc hb_notin_Rc_drop
                      have h_last_notin_drop := hbif_bif.2.2.1
                      have h_bif_t_ne :
                          (refactor_Walk.refactor_mkBifurcationBidir (M_R.refactor_comp L_g) hLc_dir
                              (M_L.refactor_comp R_g) hMLR_sym).refactor_vertices.tail ≠ [] := by
                        have h_bif_pos := refactor_Walk.refactor_length_pos_of_isBifurcation hbif_bif
                        exact refactor_Walk.refactor_tail_vertices_ne_nil_of_pos _ h_bif_pos
                      have h_bif_drop_eq :
                          (refactor_Walk.refactor_mkBifurcationBidir (M_R.refactor_comp L_g) hLc_dir
                              (M_L.refactor_comp R_g) hMLR_sym).refactor_vertices.dropLast
                          = a :: (refactor_Walk.refactor_mkBifurcationBidir (M_R.refactor_comp L_g) hLc_dir
                                      (M_L.refactor_comp R_g) hMLR_sym).refactor_vertices.tail.dropLast := by
                        conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail _]
                        exact List.dropLast_cons_of_ne_nil h_bif_t_ne
                      have hx_bif_drop : b ∈
                          (refactor_Walk.refactor_mkBifurcationBidir (M_R.refactor_comp L_g) hLc_dir
                              (M_L.refactor_comp R_g) hMLR_sym).refactor_vertices.dropLast := by
                        rw [h_bif_drop_eq]; exact List.mem_cons_of_mem _ hx
                      exact absurd hx_bif_drop h_last_notin_drop
                  · have h_R_g_zero : R_g.refactor_length = 0 := by omega
                    match R_g, h_R_g_zero with
                    | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hxR_tail
-- REFACTOR-BLOCK-REPLACEMENT-END: forward_marg_to_g_bif_one_orientation

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: backward_marg_to_g_bif_bidir_hinge_one_orientation (was: refactor_backward_marg_to_g_bif_bidir_hinge_one_orientation)
-- ## Phase D.2 port — backward, bidirected-hinge bif, single orientation.
--
-- The novel refactor sites inside this lemma are confined to the
-- bifurcation-source extraction block: the original's
-- `(G.hL_subset hLR_G).1 / .2` pair (extracting `vL_h, vR_h ∈ G.V`
-- from an ordered-pair `hLR_G : (vL_h, vR_h) ∈ G.L`) becomes the
-- `Sym2.Mem`-quantified `G.hL_subset hLR_G (Sym2.mem_mk_left vL_h vR_h)`
-- and `G.hL_subset hLR_G (Sym2.mem_mk_right vL_h vR_h)`; the original's
-- `G.hL_irrefl hLR_G heq` (where `heq : vL_h = vR_h`) becomes
-- `G.hL_irrefl hLR_G (Sym2.mk_isDiag_iff.mpr heq)` (matching the exact
-- `Sym2.mk_isDiag_iff` idiom used in
-- `MarginalizationAK.refactor_marginalize_hL_irrefl`).  The
-- `s(β, γ) ∈ marg.L` assembly at the L-edge construction site goes via
-- `refactor_marginalize_L_iff` (Batch-1 net-new helper from
-- `MargPreservesAncestors`) rather than peeling
-- `Finset.mem_filter` + `Finset.mem_product` inline (which is ill-typed
-- on the post-refactor `Finset.image`-built `marg.L`).
set_option linter.style.longLine false in
private lemma refactor_backward_marg_to_g_bif_bidir_hinge_one_orientation
    {G : refactor_CDMG Node} (S T : Finset Node)
    (hS : S ⊆ G.V) {a b : Node}
    (ha_VST : a ∈ G.V \ (S ∪ T)) (hb_VST : b ∈ G.V \ (S ∪ T))
    (ha_marg : a ∈ G.refactor_marginalize S hS) (hb_marg : b ∈ G.refactor_marginalize S hS)
    (p : refactor_Walk G a b)
    (hp_bif : p.refactor_IsBifurcation)
    (hp_inter : ∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ S ∪ T)
    (i : ℕ) (hp_split : p.refactor_IsBifurcationWithSplit i)
    (h_not_dir : ¬ p.refactor_IsBifurcationDirectedHingeWithSplit i) :
    ∃ q : refactor_Walk (G.refactor_marginalize S hS) a b, q.refactor_IsBifurcation ∧
      ∀ x ∈ q.refactor_vertices.tail.dropLast, x ∈ T := by
  have ha_notSuT : a ∉ S ∪ T := (Finset.mem_sdiff.mp ha_VST).2
  have hb_notSuT : b ∉ S ∪ T := (Finset.mem_sdiff.mp hb_VST).2
  have ha_notS : a ∉ S := fun h => ha_notSuT (Finset.mem_union_left _ h)
  have hb_notS : b ∉ S := fun h => hb_notSuT (Finset.mem_union_left _ h)
  have hp_pos : p.refactor_length ≥ 1 :=
    refactor_Walk.refactor_length_pos_of_isBifurcation hp_bif
  obtain ⟨hab_ne, ha_p_tail, hb_p_drop, _⟩ := hp_bif
  have hp_inter_ST : ∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T :=
    fun x hx => Finset.mem_union.mp (hp_inter x hx)
  -- Extract bidirected hinge arms.
  obtain ⟨vL_h, vR_h, L_p, R_p, hL_p_dir, hR_p_dir, hLR_G, _,
          hL_p_sub, hR_p_sub, hL_p_drop_sub, hR_p_drop_sub⟩ :=
    refactor_Walk.refactor_exists_arms_of_bifurcation_bidir_hinge_strong
      p i hp_split h_not_dir
  -- Sym2-quantified hL_subset extracts vL_h, vR_h ∈ G.V.
  have hvL_h_V : vL_h ∈ G.V :=
    G.hL_subset hLR_G (Sym2.mem_mk_left vL_h vR_h)
  have hvR_h_V : vR_h ∈ G.V :=
    G.hL_subset hLR_G (Sym2.mem_mk_right vL_h vR_h)
  have hvL_h_g : vL_h ∈ G := Finset.mem_union_right _ hvL_h_V
  have hvR_h_g : vR_h ∈ G := Finset.mem_union_right _ hvR_h_V
  -- Sym2.IsDiag idiom: G.hL_irrefl returns ¬ s(vL_h, vR_h).IsDiag.
  have hvLR_h_ne : vL_h ≠ vR_h := fun heq =>
    G.hL_irrefl hLR_G (Sym2.mk_isDiag_iff.mpr heq)
  -- L_p, R_p vertex bounds.
  have ha_notin_L_p_drop : a ∉ L_p.refactor_vertices.dropLast := fun h_in =>
    ha_p_tail (hL_p_drop_sub a h_in)
  have ha_notin_R_p : a ∉ R_p.refactor_vertices := fun h_in =>
    ha_p_tail (hR_p_sub a h_in)
  have hb_notin_L_p : b ∉ L_p.refactor_vertices := fun h_in =>
    hb_p_drop (hL_p_sub b h_in)
  have hb_notin_R_p_drop : b ∉ R_p.refactor_vertices.dropLast := fun h_in =>
    hb_p_drop (hR_p_drop_sub b h_in)
  -- L_p, R_p interior ⊆ S ∨ T.
  have hL_p_inter_ST : ∀ x ∈ L_p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
    intro x hx
    by_cases h_L_p_pos : L_p.refactor_length ≥ 1
    · have h_t_ne : L_p.refactor_vertices.tail ≠ [] :=
        refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_p h_L_p_pos
      have h_drop_eq :
          L_p.refactor_vertices.dropLast = vL_h :: L_p.refactor_vertices.tail.dropLast := by
        conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_p]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have hx_L_p_drop : x ∈ L_p.refactor_vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have hx_p_tail : x ∈ p.refactor_vertices.tail := hL_p_drop_sub _ hx_L_p_drop
      have hx_L_p : x ∈ L_p.refactor_vertices := List.mem_of_mem_dropLast hx_L_p_drop
      have hx_p_drop : x ∈ p.refactor_vertices.dropLast := hL_p_sub _ hx_L_p
      have hx_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
        refactor_mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
      exact hp_inter_ST _ hx_p_inter
    · have h_zero : L_p.refactor_length = 0 := by omega
      match L_p, h_zero with
      | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hx
  have hR_p_inter_ST : ∀ x ∈ R_p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
    intro x hx
    by_cases h_R_p_pos : R_p.refactor_length ≥ 1
    · have h_t_ne : R_p.refactor_vertices.tail ≠ [] :=
        refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_p h_R_p_pos
      have h_drop_eq :
          R_p.refactor_vertices.dropLast = vR_h :: R_p.refactor_vertices.tail.dropLast := by
        conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_p]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have hx_R_p_drop : x ∈ R_p.refactor_vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have hx_p_drop : x ∈ p.refactor_vertices.dropLast := hR_p_drop_sub _ hx_R_p_drop
      have hx_R_p : x ∈ R_p.refactor_vertices := List.mem_of_mem_dropLast hx_R_p_drop
      have hx_p_tail : x ∈ p.refactor_vertices.tail := hR_p_sub _ hx_R_p
      have hx_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
        refactor_mem_interior_of_arm_source ha_p_tail hp_pos hx_p_tail hx_p_drop
      exact hp_inter_ST _ hx_p_inter
    · have h_zero : R_p.refactor_length = 0 := by omega
      match R_p, h_zero with
      | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hx
  -- Apply inclusive find_first_non_W on each arm.
  obtain ⟨β, L_head, L_tail, hL_head_dir, hL_tail_dir, hβ_notS,
          hL_head_dL_S, _hL_lens, hL_p_vs_eq⟩ :=
    refactor_find_first_non_W_directed_inclusive S L_p hL_p_dir ha_notS
  obtain ⟨γ, R_head, R_tail, hR_head_dir, hR_tail_dir, hγ_notS,
          hR_head_dL_S, _hR_lens, hR_p_vs_eq⟩ :=
    refactor_find_first_non_W_directed_inclusive S R_p hR_p_dir hb_notS
  -- β, γ ∈ G.V (target of L_head / R_head, or vL_h / vR_h if head is nil).
  have hβ_V : β ∈ G.V := by
    by_cases h_pos : L_head.refactor_length ≥ 1
    · exact refactor_Walk.refactor_target_in_GV_of_directedWalk_pos L_head hL_head_dir h_pos
    · have h_zero : L_head.refactor_length = 0 := by omega
      have h_vL_eq_β : vL_h = β := by
        match L_head, h_zero with
        | .nil _ _, _ => rfl
      rw [← h_vL_eq_β]; exact hvL_h_V
  have hγ_V : γ ∈ G.V := by
    by_cases h_pos : R_head.refactor_length ≥ 1
    · exact refactor_Walk.refactor_target_in_GV_of_directedWalk_pos R_head hR_head_dir h_pos
    · have h_zero : R_head.refactor_length = 0 := by omega
      have h_vR_eq_γ : vR_h = γ := by
        match R_head, h_zero with
        | .nil _ _, _ => rfl
      rw [← h_vR_eq_γ]; exact hvR_h_V
  -- β, γ ∈ G.V \ S → β, γ ∈ G.refactor_marginalize S hS.
  have hβ_VS : β ∈ G.V \ S := Finset.mem_sdiff.mpr ⟨hβ_V, hβ_notS⟩
  have hγ_VS : γ ∈ G.V \ S := Finset.mem_sdiff.mpr ⟨hγ_V, hγ_notS⟩
  have hβ_marg : β ∈ G.refactor_marginalize S hS := by
    change β ∈ G.J ∪ (G.V \ S); exact Finset.mem_union_right _ hβ_VS
  have hγ_marg : γ ∈ G.refactor_marginalize S hS := by
    change γ ∈ G.J ∪ (G.V \ S); exact Finset.mem_union_right _ hγ_VS
  -- Vertex memberships of L_head, R_head, L_tail, R_tail back into L_p / R_p / p.
  have hL_head_dL_sub_L_p : ∀ x ∈ L_head.refactor_vertices.dropLast,
      x ∈ L_p.refactor_vertices := by
    intro x hx; rw [hL_p_vs_eq]; exact List.mem_append.mpr (Or.inl hx)
  have hL_tail_sub_L_p : ∀ x ∈ L_tail.refactor_vertices, x ∈ L_p.refactor_vertices := by
    intro x hx; rw [hL_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
  have hR_head_dL_sub_R_p : ∀ x ∈ R_head.refactor_vertices.dropLast,
      x ∈ R_p.refactor_vertices := by
    intro x hx; rw [hR_p_vs_eq]; exact List.mem_append.mpr (Or.inl hx)
  have hR_tail_sub_R_p : ∀ x ∈ R_tail.refactor_vertices, x ∈ R_p.refactor_vertices := by
    intro x hx; rw [hR_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
  -- DropLast bounds for L_tail, R_tail (via L_p / R_p).
  have hL_tail_ne : L_tail.refactor_vertices ≠ [] :=
    refactor_Walk.refactor_vertices_ne_nil L_tail
  have hR_tail_ne : R_tail.refactor_vertices ≠ [] :=
    refactor_Walk.refactor_vertices_ne_nil R_tail
  have hL_tail_dL_sub_L_p_dL :
      ∀ x ∈ L_tail.refactor_vertices.dropLast, x ∈ L_p.refactor_vertices.dropLast := by
    intro x hx
    rw [hL_p_vs_eq, List.dropLast_append_of_ne_nil hL_tail_ne]
    exact List.mem_append.mpr (Or.inr hx)
  have hR_tail_dL_sub_R_p_dL :
      ∀ x ∈ R_tail.refactor_vertices.dropLast, x ∈ R_p.refactor_vertices.dropLast := by
    intro x hx
    rw [hR_p_vs_eq, List.dropLast_append_of_ne_nil hR_tail_ne]
    exact List.mem_append.mpr (Or.inr hx)
  -- L_tail's interior ⊆ S ∪ T.
  have hL_tail_inter_ST : ∀ x ∈ L_tail.refactor_vertices.tail.dropLast,
      x ∈ S ∨ x ∈ T := by
    intro x hx
    have h_t : x ∈ L_tail.refactor_vertices.tail := List.mem_of_mem_dropLast hx
    have h_v : x ∈ L_tail.refactor_vertices := List.mem_of_mem_tail h_t
    have h_L_p : x ∈ L_p.refactor_vertices := hL_tail_sub_L_p _ h_v
    have h_x_p_drop : x ∈ p.refactor_vertices.dropLast := hL_p_sub _ h_L_p
    by_cases h_pos : L_tail.refactor_length ≥ 1
    · have h_t_ne : L_tail.refactor_vertices.tail ≠ [] :=
        refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_tail h_pos
      have h_drop_eq :
          L_tail.refactor_vertices.dropLast = β :: L_tail.refactor_vertices.tail.dropLast := by
        conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_tail]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have h_drop : x ∈ L_tail.refactor_vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have h_L_p_drop : x ∈ L_p.refactor_vertices.dropLast := hL_tail_dL_sub_L_p_dL _ h_drop
      have h_x_p_tail : x ∈ p.refactor_vertices.tail := hL_p_drop_sub _ h_L_p_drop
      have h_x_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
        refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
      exact hp_inter_ST _ h_x_p_inter
    · have h_zero : L_tail.refactor_length = 0 := by omega
      match L_tail, h_zero with
      | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hx
  have hR_tail_inter_ST : ∀ x ∈ R_tail.refactor_vertices.tail.dropLast,
      x ∈ S ∨ x ∈ T := by
    intro x hx
    have h_t : x ∈ R_tail.refactor_vertices.tail := List.mem_of_mem_dropLast hx
    have h_v : x ∈ R_tail.refactor_vertices := List.mem_of_mem_tail h_t
    have h_R_p : x ∈ R_p.refactor_vertices := hR_tail_sub_R_p _ h_v
    have h_x_p_tail : x ∈ p.refactor_vertices.tail := hR_p_sub _ h_R_p
    by_cases h_pos : R_tail.refactor_length ≥ 1
    · have h_t_ne : R_tail.refactor_vertices.tail ≠ [] :=
        refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_tail h_pos
      have h_drop_eq :
          R_tail.refactor_vertices.dropLast = γ :: R_tail.refactor_vertices.tail.dropLast := by
        conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_tail]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have h_drop : x ∈ R_tail.refactor_vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have h_R_p_drop : x ∈ R_p.refactor_vertices.dropLast := hR_tail_dL_sub_R_p_dL _ h_drop
      have h_x_p_drop : x ∈ p.refactor_vertices.dropLast := hR_p_drop_sub _ h_R_p_drop
      have h_x_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
        refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
      exact hp_inter_ST _ h_x_p_inter
    · have h_zero : R_tail.refactor_length = 0 := by omega
      match R_tail, h_zero with
      | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hx
  -- Vertex bounds: a, b vs L_tail, R_tail.
  have ha_notin_L_tail_dL : a ∉ L_tail.refactor_vertices.dropLast := fun h_in =>
    ha_notin_L_p_drop (hL_tail_dL_sub_L_p_dL a h_in)
  have ha_notin_R_tail : a ∉ R_tail.refactor_vertices := fun h_in =>
    ha_notin_R_p (hR_tail_sub_R_p a h_in)
  have hb_notin_L_tail : b ∉ L_tail.refactor_vertices := fun h_in =>
    hb_notin_L_p (hL_tail_sub_L_p b h_in)
  have hb_notin_R_tail_dL : b ∉ R_tail.refactor_vertices.dropLast := fun h_in =>
    hb_notin_R_p_drop (hR_tail_dL_sub_R_p_dL b h_in)
  -- Case-split on β = γ.
  by_cases hβγ_eq : β = γ
  · -- β = γ.  Build mkBifurcation with source β.
    subst hβγ_eq
    have hβ_ne_a : β ≠ a := by
      intro heq
      have h_in_R_tail : β ∈ R_tail.refactor_vertices :=
        refactor_Walk.refactor_head_mem_vertices R_tail
      have h_in_R_p : β ∈ R_p.refactor_vertices := hR_tail_sub_R_p _ h_in_R_tail
      have h_p_tail : β ∈ p.refactor_vertices.tail := hR_p_sub _ h_in_R_p
      exact ha_p_tail (heq ▸ h_p_tail)
    have hβ_ne_b : β ≠ b := by
      intro heq
      have h_in_L_tail : β ∈ L_tail.refactor_vertices :=
        refactor_Walk.refactor_head_mem_vertices L_tail
      have h_in_L_p : β ∈ L_p.refactor_vertices := hL_tail_sub_L_p _ h_in_L_tail
      have h_p_drop : β ∈ p.refactor_vertices.dropLast := hL_p_sub _ h_in_L_p
      exact hb_p_drop (heq ▸ h_p_drop)
    have hL_tail_pos : L_tail.refactor_length ≥ 1 :=
      refactor_Walk.refactor_length_pos_of_ne L_tail hβ_ne_a
    have hR_tail_pos : R_tail.refactor_length ≥ 1 :=
      refactor_Walk.refactor_length_pos_of_ne R_tail hβ_ne_b
    -- Project L_tail, R_tail to marg.
    obtain ⟨L_marg, hL_marg_dir, hL_marg_pos, hL_marg_vs_sub, hL_marg_dL_sub,
            _, hL_marg_inter_T⟩ :=
      refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
        L_tail hL_tail_dir hL_tail_pos hβ_marg ha_marg hL_tail_inter_ST
    obtain ⟨R_marg, hR_marg_dir, hR_marg_pos, hR_marg_vs_sub, hR_marg_dL_sub,
            _, hR_marg_inter_T⟩ :=
      refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
        R_tail hR_tail_dir hR_tail_pos hβ_marg hb_marg hR_tail_inter_ST
    -- Vertex bounds in marg.
    have ha_notin_L_marg_dL : a ∉ L_marg.refactor_vertices.dropLast := fun h_in =>
      ha_notin_L_tail_dL (hL_marg_dL_sub a h_in)
    have ha_notin_R_marg : a ∉ R_marg.refactor_vertices := fun h_in =>
      ha_notin_R_tail (hR_marg_vs_sub a h_in)
    have hb_notin_L_marg : b ∉ L_marg.refactor_vertices := fun h_in =>
      hb_notin_L_tail (hL_marg_vs_sub b h_in)
    have hb_notin_R_marg_dL : b ∉ R_marg.refactor_vertices.dropLast := fun h_in =>
      hb_notin_R_tail_dL (hR_marg_dL_sub b h_in)
    -- Build the bifurcation.
    refine ⟨refactor_Walk.refactor_mkBifurcation L_marg hL_marg_dir hL_marg_pos R_marg, ?_, ?_⟩
    · have h_src := refactor_Walk.refactor_mkBifurcation_isBifurcationSource
        L_marg hL_marg_dir hL_marg_pos R_marg hR_marg_dir hR_marg_pos
        hab_ne ha_notin_L_marg_dL ha_notin_R_marg hb_notin_L_marg hb_notin_R_marg_dL
      exact refactor_Walk.refactor_isBifurcationSource_to_isBifurcation _ β h_src
    · intro x hx
      rw [refactor_vertices_tail_dropLast_mkBifurcation
            L_marg hL_marg_dir hL_marg_pos R_marg hR_marg_pos] at hx
      rcases List.mem_append.mp hx with hx_L | hx_R
      · rw [List.mem_reverse] at hx_L
        exact hL_marg_inter_T x hx_L
      · -- x ∈ R_marg.refactor_vertices.dropLast.  R_marg starts at β (the source).
        have h_R_t_ne : R_marg.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_marg hR_marg_pos
        rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
            List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R
        rcases List.mem_cons.mp hx_R with rfl | hx_inner
        · -- x = β.  Need β ∈ T via mem_interior_of_arm_source.
          have h_x_in_L_p : x ∈ L_p.refactor_vertices :=
            hL_tail_sub_L_p _ (refactor_Walk.refactor_head_mem_vertices L_tail)
          have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast :=
            hL_p_sub _ h_x_in_L_p
          have h_x_in_R_p : x ∈ R_p.refactor_vertices :=
            hR_tail_sub_R_p _ (refactor_Walk.refactor_head_mem_vertices R_tail)
          have h_x_in_p_tail : x ∈ p.refactor_vertices.tail :=
            hR_p_sub _ h_x_in_R_p
          have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
            refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
          rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
          · exact absurd h_S hβ_notS
          · exact h_T
        · exact hR_marg_inter_T x hx_inner
  · -- β ≠ γ.  Build L-edge s(β, γ) ∈ marg.L via Φ_L S.
    -- First, construct the G-bif witness using refactor_mkBifurcationBidir.
    -- Vertex bounds (since β ∉ S, γ ∉ S, and L_head/R_head interiors ⊆ S):
    have hβ_notin_L_head_dL : β ∉ L_head.refactor_vertices.dropLast := fun h_in =>
      hβ_notS (hL_head_dL_S β h_in)
    have hγ_notin_R_head_dL : γ ∉ R_head.refactor_vertices.dropLast := fun h_in =>
      hγ_notS (hR_head_dL_S γ h_in)
    -- R_head.refactor_vertices = R_head.refactor_vertices.dropLast ++ [γ] (via getLast).
    have hR_head_decomp :
        R_head.refactor_vertices = R_head.refactor_vertices.dropLast ++ [γ] := by
      have h_ne : R_head.refactor_vertices ≠ [] :=
        refactor_Walk.refactor_vertices_ne_nil R_head
      have h_last : R_head.refactor_vertices.getLast h_ne = γ :=
        refactor_Walk.refactor_vertices_getLast R_head
      have := List.dropLast_append_getLast h_ne
      rw [h_last] at this
      exact this.symm
    have hL_head_decomp :
        L_head.refactor_vertices = L_head.refactor_vertices.dropLast ++ [β] := by
      have h_ne : L_head.refactor_vertices ≠ [] :=
        refactor_Walk.refactor_vertices_ne_nil L_head
      have h_last : L_head.refactor_vertices.getLast h_ne = β :=
        refactor_Walk.refactor_vertices_getLast L_head
      have := List.dropLast_append_getLast h_ne
      rw [h_last] at this
      exact this.symm
    have hβ_notin_R_head : β ∉ R_head.refactor_vertices := by
      intro h_in
      rw [hR_head_decomp] at h_in
      rcases List.mem_append.mp h_in with h_dL | h_last
      · exact hβ_notS (hR_head_dL_S β h_dL)
      · rw [List.mem_singleton] at h_last; exact hβγ_eq h_last
    have hγ_notin_L_head : γ ∉ L_head.refactor_vertices := by
      intro h_in
      rw [hL_head_decomp] at h_in
      rcases List.mem_append.mp h_in with h_dL | h_last
      · exact hγ_notS (hL_head_dL_S γ h_dL)
      · rw [List.mem_singleton] at h_last; exact hβγ_eq h_last.symm
    -- G-bif IsBifurcation.
    have h_G_bif_is_bif :
        (refactor_Walk.refactor_mkBifurcationBidir L_head hL_head_dir
            R_head hLR_G).refactor_IsBifurcation :=
      refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
        L_head hL_head_dir R_head hR_head_dir hLR_G
        hβγ_eq hβ_notin_L_head_dL hβ_notin_R_head hγ_notin_L_head hγ_notin_R_head_dL
    -- G-bif's interior ⊆ S.
    have h_G_bif_inter_S :
        ∀ x ∈ (refactor_Walk.refactor_mkBifurcationBidir L_head hL_head_dir
                R_head hLR_G).refactor_vertices.tail.dropLast, x ∈ S := by
      intro x hx
      have h_bif_vs :=
        refactor_Walk.refactor_vertices_mkBifurcationBidir L_head hL_head_dir
          R_head hLR_G
      by_cases hL_head_pos : L_head.refactor_length ≥ 1
      · rw [refactor_vertices_tail_dropLast_mkBifurcationBidir_Lpos
              L_head hL_head_dir R_head hLR_G hL_head_pos] at hx
        rcases List.mem_append.mp hx with hx_L | hx_R
        · -- x ∈ L_head.refactor_vertices.tail.dropLast.reverse → x ∈ L_head.tail.dropLast.
          rw [List.mem_reverse] at hx_L
          have h_x_in_L_head_dL : x ∈ L_head.refactor_vertices.dropLast := by
            have h_t : x ∈ L_head.refactor_vertices.tail :=
              List.mem_of_mem_dropLast hx_L
            have h_t_ne : L_head.refactor_vertices.tail ≠ [] :=
              refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_head hL_head_pos
            have h_drop_eq :
                L_head.refactor_vertices.dropLast
                  = vL_h :: L_head.refactor_vertices.tail.dropLast := by
              conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_head]
              exact List.dropLast_cons_of_ne_nil h_t_ne
            rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx_L
          exact hL_head_dL_S x h_x_in_L_head_dL
        · -- x ∈ (vL_h :: R_head.refactor_vertices).dropLast.
          have h_R_head_ne : R_head.refactor_vertices ≠ [] :=
            refactor_Walk.refactor_vertices_ne_nil R_head
          rw [List.dropLast_cons_of_ne_nil h_R_head_ne] at hx_R
          rcases List.mem_cons.mp hx_R with rfl | hx_R_dL
          · have h_t_ne : L_head.refactor_vertices.tail ≠ [] :=
              refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_head hL_head_pos
            have hx_in_dL : x ∈ L_head.refactor_vertices.dropLast := by
              rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_head,
                  List.dropLast_cons_of_ne_nil h_t_ne]
              exact List.mem_cons_self
            exact hL_head_dL_S _ hx_in_dL
          · exact hR_head_dL_S x hx_R_dL
      · -- L_head.refactor_length = 0 → vL_h = β → L_head = nil.
        have h_zero : L_head.refactor_length = 0 := by omega
        have hvL_eq_β : vL_h = β := by
          match L_head, h_zero with
          | .nil _ _, _ => rfl
        have h_L_head_vs : L_head.refactor_vertices = [vL_h] := by
          match L_head, h_zero with
          | .nil _ _, _ => simp [refactor_Walk.refactor_vertices]
        rw [h_bif_vs, h_L_head_vs] at hx
        change x ∈ ((vL_h :: R_head.refactor_vertices) : List Node).tail.dropLast at hx
        change x ∈ R_head.refactor_vertices.dropLast at hx
        exact hR_head_dL_S x hx
    -- L-edge: s(β, γ) ∈ marg.L via Φ_L S (Sym2-image iff from MPA).
    have hβ_ne_γ : β ≠ γ := hβγ_eq
    have hβγ_in_margL : s(β, γ) ∈ (G.refactor_marginalize S hS).L := by
      refine (refactor_marginalize_L_iff G S hS).mpr
        ⟨(β, γ), hβ_VS, hγ_VS, hβ_ne_γ, ?_, rfl⟩
      -- Φ_L S β γ via the G-bif we just constructed.
      exact Or.inl ⟨refactor_Walk.refactor_mkBifurcationBidir L_head hL_head_dir
                      R_head hLR_G,
                    h_G_bif_is_bif, h_G_bif_inter_S⟩
    -- Construct marg arms via inline case-splits on L_tail.refactor_length
    -- and R_tail.refactor_length (cf. the original lemma's commentary on
    -- nil-vs-pos branches).
    by_cases hL_tail_pos : L_tail.refactor_length ≥ 1
    · -- L_tail.refactor_length ≥ 1.  Project L_tail to marg.
      obtain ⟨L_marg, hL_marg_dir, hL_marg_pos, hL_marg_vs, hL_marg_dL,
              _, hL_marg_inter⟩ :=
        refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
          L_tail hL_tail_dir hL_tail_pos hβ_marg ha_marg hL_tail_inter_ST
      have ha_notin_L_marg_dL : a ∉ L_marg.refactor_vertices.dropLast := fun h_in =>
        ha_notin_L_tail_dL (hL_marg_dL a h_in)
      have hb_notin_L_marg : b ∉ L_marg.refactor_vertices := fun h_in =>
        hb_notin_L_tail (hL_marg_vs b h_in)
      by_cases hR_tail_pos : R_tail.refactor_length ≥ 1
      · -- L_tail pos, R_tail pos.
        obtain ⟨R_marg, hR_marg_dir, hR_marg_pos, hR_marg_vs, hR_marg_dL,
                _, hR_marg_inter⟩ :=
          refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
            R_tail hR_tail_dir hR_tail_pos hγ_marg hb_marg hR_tail_inter_ST
        have ha_notin_R_marg : a ∉ R_marg.refactor_vertices := fun h_in =>
          ha_notin_R_tail (hR_marg_vs a h_in)
        have hb_notin_R_marg_dL : b ∉ R_marg.refactor_vertices.dropLast := fun h_in =>
          hb_notin_R_tail_dL (hR_marg_dL b h_in)
        refine ⟨refactor_Walk.refactor_mkBifurcationBidir L_marg hL_marg_dir R_marg
                  hβγ_in_margL, ?_, ?_⟩
        · exact refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
            L_marg hL_marg_dir R_marg hR_marg_dir hβγ_in_margL hab_ne ha_notin_L_marg_dL
            ha_notin_R_marg hb_notin_L_marg hb_notin_R_marg_dL
        · intro x hx
          rw [refactor_vertices_tail_dropLast_mkBifurcationBidir_Lpos
                L_marg hL_marg_dir R_marg hβγ_in_margL hL_marg_pos] at hx
          rcases List.mem_append.mp hx with hx_L | hx_R
          · rw [List.mem_reverse] at hx_L
            exact hL_marg_inter x hx_L
          · have h_R_marg_ne : R_marg.refactor_vertices ≠ [] :=
              refactor_Walk.refactor_vertices_ne_nil R_marg
            rw [List.dropLast_cons_of_ne_nil h_R_marg_ne] at hx_R
            rcases List.mem_cons.mp hx_R with rfl | hx_R_dL
            · -- x = β.
              have h_x_in_L_p : x ∈ L_p.refactor_vertices :=
                hL_tail_sub_L_p _ (refactor_Walk.refactor_head_mem_vertices L_tail)
              have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast :=
                hL_p_sub _ h_x_in_L_p
              have h_L_marg_t_ne : L_marg.refactor_vertices.tail ≠ [] :=
                refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_marg hL_marg_pos
              have hβ_in_L_marg_dL : x ∈ L_marg.refactor_vertices.dropLast := by
                rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_marg,
                    List.dropLast_cons_of_ne_nil h_L_marg_t_ne]
                exact List.mem_cons_self
              have hβ_in_L_tail_dL : x ∈ L_tail.refactor_vertices.dropLast :=
                hL_marg_dL _ hβ_in_L_marg_dL
              have hβ_in_L_p_dL : x ∈ L_p.refactor_vertices.dropLast :=
                hL_tail_dL_sub_L_p_dL _ hβ_in_L_tail_dL
              have h_x_in_p_tail : x ∈ p.refactor_vertices.tail :=
                hL_p_drop_sub _ hβ_in_L_p_dL
              have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
                refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
              rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
              · exact absurd h_S hβ_notS
              · exact h_T
            · -- x ∈ R_marg.refactor_vertices.dropLast.
              have h_R_t_ne : R_marg.refactor_vertices.tail ≠ [] :=
                refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_marg hR_marg_pos
              rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
                  List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R_dL
              rcases List.mem_cons.mp hx_R_dL with rfl | hx_R_inner
              · -- x = γ.
                have h_x_in_R_p : x ∈ R_p.refactor_vertices :=
                  hR_tail_sub_R_p _ (refactor_Walk.refactor_head_mem_vertices R_tail)
                have h_x_in_p_tail : x ∈ p.refactor_vertices.tail :=
                  hR_p_sub _ h_x_in_R_p
                have hγ_in_R_marg_dL : x ∈ R_marg.refactor_vertices.dropLast := by
                  rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
                      List.dropLast_cons_of_ne_nil h_R_t_ne]
                  exact List.mem_cons_self
                have hγ_in_R_tail_dL : x ∈ R_tail.refactor_vertices.dropLast :=
                  hR_marg_dL _ hγ_in_R_marg_dL
                have hγ_in_R_p_dL : x ∈ R_p.refactor_vertices.dropLast :=
                  hR_tail_dL_sub_R_p_dL _ hγ_in_R_tail_dL
                have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast :=
                  hR_p_drop_sub _ hγ_in_R_p_dL
                have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
                  refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
                rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
                · exact absurd h_S hγ_notS
                · exact h_T
              · exact hR_marg_inter x hx_R_inner
      · -- L_tail pos, R_tail = 0 → γ = b (after subst, b is eliminated).
        have h_R_zero : R_tail.refactor_length = 0 := by omega
        have hγb_eq : γ = b := by
          match R_tail, h_R_zero with
          | .nil _ _, _ => rfl
        subst hγb_eq
        refine ⟨refactor_Walk.refactor_mkBifurcationBidir L_marg hL_marg_dir
                  (refactor_Walk.nil γ hγ_marg) hβγ_in_margL, ?_, ?_⟩
        · refine refactor_Walk.refactor_mkBifurcationBidir_isBifurcation L_marg hL_marg_dir
            (refactor_Walk.nil γ hγ_marg) trivial hβγ_in_margL hab_ne ha_notin_L_marg_dL
            ?_ hb_notin_L_marg ?_
          · intro h_in
            change a ∈ ([γ] : List Node) at h_in
            rw [List.mem_singleton] at h_in
            exact ha_notin_R_tail
              (by rw [h_in]; exact refactor_Walk.refactor_head_mem_vertices R_tail)
          · intro h_in
            change γ ∈ ([γ] : List Node).dropLast at h_in
            simp at h_in
        · intro x hx
          rw [refactor_vertices_tail_dropLast_mkBifurcationBidir_Lpos
                L_marg hL_marg_dir (refactor_Walk.nil γ hγ_marg) hβγ_in_margL
                hL_marg_pos] at hx
          rcases List.mem_append.mp hx with hx_L | hx_R
          · rw [List.mem_reverse] at hx_L
            exact hL_marg_inter x hx_L
          · change x ∈ ((β :: [γ]) : List Node).dropLast at hx_R
            change x ∈ ([β, γ] : List Node).dropLast at hx_R
            simp [List.dropLast] at hx_R
            rw [hx_R]
            have h_β_in_L_p : β ∈ L_p.refactor_vertices :=
              hL_tail_sub_L_p _ (refactor_Walk.refactor_head_mem_vertices L_tail)
            have h_β_in_p_drop : β ∈ p.refactor_vertices.dropLast :=
              hL_p_sub _ h_β_in_L_p
            have h_L_marg_t_ne : L_marg.refactor_vertices.tail ≠ [] :=
              refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_marg hL_marg_pos
            have hβ_in_L_marg_dL : β ∈ L_marg.refactor_vertices.dropLast := by
              rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_marg,
                  List.dropLast_cons_of_ne_nil h_L_marg_t_ne]
              exact List.mem_cons_self
            have hβ_in_L_tail_dL : β ∈ L_tail.refactor_vertices.dropLast :=
              hL_marg_dL _ hβ_in_L_marg_dL
            have hβ_in_L_p_dL : β ∈ L_p.refactor_vertices.dropLast :=
              hL_tail_dL_sub_L_p_dL _ hβ_in_L_tail_dL
            have h_β_in_p_tail : β ∈ p.refactor_vertices.tail :=
              hL_p_drop_sub _ hβ_in_L_p_dL
            have h_β_in_p_inter : β ∈ p.refactor_vertices.tail.dropLast :=
              refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_β_in_p_tail h_β_in_p_drop
            rcases hp_inter_ST β h_β_in_p_inter with h_S | h_T
            · exact absurd h_S hβ_notS
            · exact h_T
    · -- L_tail.refactor_length = 0 → β = a (after subst, a is eliminated, β remains).
      have h_L_zero : L_tail.refactor_length = 0 := by omega
      have hβa_eq : β = a := by
        match L_tail, h_L_zero with
        | .nil _ _, _ => rfl
      subst hβa_eq
      by_cases hR_tail_pos : R_tail.refactor_length ≥ 1
      · -- L nil, R pos.  L_marg = nil β.  R_marg = projected R_tail.
        obtain ⟨R_marg, hR_marg_dir, hR_marg_pos, hR_marg_vs, hR_marg_dL,
                _, hR_marg_inter⟩ :=
          refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
            R_tail hR_tail_dir hR_tail_pos hγ_marg hb_marg hR_tail_inter_ST
        have hβ_notin_R_marg : β ∉ R_marg.refactor_vertices := fun h_in =>
          ha_notin_R_tail (hR_marg_vs β h_in)
        have hb_notin_R_marg_dL : b ∉ R_marg.refactor_vertices.dropLast := fun h_in =>
          hb_notin_R_tail_dL (hR_marg_dL b h_in)
        refine ⟨refactor_Walk.refactor_mkBifurcationBidir (refactor_Walk.nil β hβ_marg)
                  trivial R_marg hβγ_in_margL, ?_, ?_⟩
        · refine refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
            (refactor_Walk.nil β hβ_marg) trivial R_marg hR_marg_dir hβγ_in_margL hab_ne
            ?_ hβ_notin_R_marg ?_ hb_notin_R_marg_dL
          · intro h_in
            change β ∈ ([β] : List Node).dropLast at h_in
            simp at h_in
          · intro h_in
            change b ∈ ([β] : List Node) at h_in
            rw [List.mem_singleton] at h_in
            exact hab_ne h_in.symm
        · intro x hx
          have h_bif_vs : (refactor_Walk.refactor_mkBifurcationBidir
                            (refactor_Walk.nil β hβ_marg) trivial
                            R_marg hβγ_in_margL).refactor_vertices = β :: R_marg.refactor_vertices := by
            rw [refactor_Walk.refactor_vertices_mkBifurcationBidir]
            change ([β] : List Node).reverse.dropLast ++ (β :: R_marg.refactor_vertices)
                  = β :: R_marg.refactor_vertices
            simp
          rw [h_bif_vs] at hx
          change x ∈ R_marg.refactor_vertices.dropLast at hx
          have h_R_t_ne : R_marg.refactor_vertices.tail ≠ [] :=
            refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_marg hR_marg_pos
          rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
              List.dropLast_cons_of_ne_nil h_R_t_ne] at hx
          rcases List.mem_cons.mp hx with rfl | hx_inner
          · -- x = γ.
            have h_x_in_R_p : x ∈ R_p.refactor_vertices :=
              hR_tail_sub_R_p _ (refactor_Walk.refactor_head_mem_vertices R_tail)
            have h_x_in_p_tail : x ∈ p.refactor_vertices.tail :=
              hR_p_sub _ h_x_in_R_p
            have hγ_in_R_marg_dL : x ∈ R_marg.refactor_vertices.dropLast := by
              rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
                  List.dropLast_cons_of_ne_nil h_R_t_ne]
              exact List.mem_cons_self
            have hγ_in_R_tail_dL : x ∈ R_tail.refactor_vertices.dropLast :=
              hR_marg_dL _ hγ_in_R_marg_dL
            have hγ_in_R_p_dL : x ∈ R_p.refactor_vertices.dropLast :=
              hR_tail_dL_sub_R_p_dL _ hγ_in_R_tail_dL
            have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast :=
              hR_p_drop_sub _ hγ_in_R_p_dL
            have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
              refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
            rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
            · exact absurd h_S hγ_notS
            · exact h_T
          · exact hR_marg_inter x hx_inner
      · -- L nil, R nil → γ = b too.
        have h_R_zero : R_tail.refactor_length = 0 := by omega
        have hγb_eq : γ = b := by
          match R_tail, h_R_zero with
          | .nil _ _, _ => rfl
        subst hγb_eq
        refine ⟨refactor_Walk.refactor_mkBifurcationBidir (refactor_Walk.nil β hβ_marg) trivial
                  (refactor_Walk.nil γ hγ_marg) hβγ_in_margL, ?_, ?_⟩
        · refine refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
            (refactor_Walk.nil β hβ_marg) trivial (refactor_Walk.nil γ hγ_marg) trivial
            hβγ_in_margL hab_ne ?_ ?_ ?_ ?_
          · intro h_in
            change β ∈ ([β] : List Node).dropLast at h_in
            simp at h_in
          · intro h_in
            change β ∈ ([γ] : List Node) at h_in
            rw [List.mem_singleton] at h_in
            exact hβγ_eq h_in
          · intro h_in
            change γ ∈ ([β] : List Node) at h_in
            rw [List.mem_singleton] at h_in
            exact hβγ_eq h_in.symm
          · intro h_in
            change γ ∈ ([γ] : List Node).dropLast at h_in
            simp at h_in
        · intro x hx
          have h_bif_vs : (refactor_Walk.refactor_mkBifurcationBidir
                            (refactor_Walk.nil β hβ_marg) trivial
                            (refactor_Walk.nil γ hγ_marg) hβγ_in_margL).refactor_vertices
                              = [β, γ] := by
            rw [refactor_Walk.refactor_vertices_mkBifurcationBidir]
            change ([β] : List Node).reverse.dropLast ++ (β :: [γ]) = [β, γ]
            simp
          rw [h_bif_vs] at hx
          change x ∈ ([β, γ] : List Node).tail.dropLast at hx
          simp at hx
-- REFACTOR-BLOCK-REPLACEMENT-END: backward_marg_to_g_bif_bidir_hinge_one_orientation

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: backward_marg_to_g_bif_dir_hinge_cInS_betaNeGamma_one_orientation (was: refactor_backward_marg_to_g_bif_dir_hinge_cInS_betaNeGamma_one_orientation)
-- ## Phase D.3 port — backward, directed-hinge bif with source ∈ S and β ≠ γ.
--
-- The lemma constructs a `marg`-side bif whose hinge is *bidirected*:
-- the directed-hinge G-bif at source `c ∈ S` produces a single
-- `s(vL_exit, vR_exit) ∈ marg.L` edge (witnessed by Φ_L's directed-bif
-- disjunct, `Or.inl`), and the marg-side arms (`L_marg`, `R_marg`,
-- projected from `L_marg_seg`, `R_marg_seg` via
-- `refactor_project_walk_marg_full`) are stitched together with that
-- L-edge via `refactor_mkBifurcationBidir`.  The novel refactor sites:
--
-- * The L-edge construction uses `refactor_marginalize_L_iff.mpr` with
--   a Sym2 witness `s(vL_exit, vR_exit)` (D.2's pattern), rather than
--   the original's inline `Finset.mem_filter` + `Finset.mem_product`
--   chain that is ill-typed on the post-refactor `Finset.image`-built
--   `marg.L`.
-- * No `hL_subset` / `hL_irrefl` invocations appear: this lemma never
--   destructures an L-edge witness — it only *builds* one via
--   `mkBifurcation` (which by-construction lands in `Φ_L`), so the
--   Sym2.IsDiag / Sym2.mem_mk_left machinery from D.2 isn't needed.
-- * The four arm-length sub-cases (L_marg±, R_marg±) port mechanically
--   from the original; the `Walk.nil` → `refactor_Walk.nil` rename and
--   the `Walk.vertices_mkBifurcationBidir` reduction are the only
--   sites that touch refactor-specific machinery beyond the
--   uniform `refactor_*` rename cookbook.
set_option linter.style.longLine false in
private lemma refactor_backward_marg_to_g_bif_dir_hinge_cInS_betaNeGamma_one_orientation
    {G : refactor_CDMG Node} (S T : Finset Node) (hS : S ⊆ G.V)
    {a b : Node}
    (ha_VST : a ∈ G.V \ (S ∪ T)) (hb_VST : b ∈ G.V \ (S ∪ T))
    (ha_marg : a ∈ G.refactor_marginalize S hS) (hb_marg : b ∈ G.refactor_marginalize S hS)
    {p : refactor_Walk G a b}
    (hp_bif : p.refactor_IsBifurcation)
    (hp_inter : ∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ S ∪ T)
    {c : Node} (hc_S : c ∈ S)
    {L_p : refactor_Walk G c a} {R_p : refactor_Walk G c b}
    (hL_p_dir : L_p.refactor_IsDirectedWalk) (hR_p_dir : R_p.refactor_IsDirectedWalk)
    (hL_p_pos : L_p.refactor_length ≥ 1) (hR_p_pos : R_p.refactor_length ≥ 1)
    (hL_p_sub : ∀ x ∈ L_p.refactor_vertices, x ∈ p.refactor_vertices.dropLast)
    (hR_p_sub : ∀ x ∈ R_p.refactor_vertices, x ∈ p.refactor_vertices.tail)
    (hL_p_drop_sub : ∀ x ∈ L_p.refactor_vertices.dropLast, x ∈ p.refactor_vertices.tail)
    (hR_p_drop_sub : ∀ x ∈ R_p.refactor_vertices.dropLast, x ∈ p.refactor_vertices.dropLast)
    {vL_exit vR_exit : Node}
    {L_W_seg : refactor_Walk G c vL_exit} {L_marg_seg : refactor_Walk G vL_exit a}
    {R_W_seg : refactor_Walk G c vR_exit} {R_marg_seg : refactor_Walk G vR_exit b}
    (hL_W_dir : L_W_seg.refactor_IsDirectedWalk)
    (hL_marg_dir : L_marg_seg.refactor_IsDirectedWalk)
    (hL_W_pos : L_W_seg.refactor_length ≥ 1) (hvL_exit_notS : vL_exit ∉ S)
    (hL_W_inter : ∀ x ∈ L_W_seg.refactor_vertices.tail.dropLast, x ∈ S)
    (hL_p_vs_eq :
      L_p.refactor_vertices = L_W_seg.refactor_vertices.dropLast ++ L_marg_seg.refactor_vertices)
    (hR_W_dir : R_W_seg.refactor_IsDirectedWalk)
    (hR_marg_dir : R_marg_seg.refactor_IsDirectedWalk)
    (hR_W_pos : R_W_seg.refactor_length ≥ 1) (hvR_exit_notS : vR_exit ∉ S)
    (hR_W_inter : ∀ x ∈ R_W_seg.refactor_vertices.tail.dropLast, x ∈ S)
    (hR_p_vs_eq :
      R_p.refactor_vertices = R_W_seg.refactor_vertices.dropLast ++ R_marg_seg.refactor_vertices)
    (hvL_vR_exit_ne : vL_exit ≠ vR_exit) :
    ∃ q : refactor_Walk (G.refactor_marginalize S hS) a b, q.refactor_IsBifurcation ∧
      ∀ x ∈ q.refactor_vertices.tail.dropLast, x ∈ T := by
  -- Unpack hp_bif and derive ancillary facts.
  have hp_pos : p.refactor_length ≥ 1 :=
    refactor_Walk.refactor_length_pos_of_isBifurcation hp_bif
  obtain ⟨hab_ne, ha_p_tail, hb_p_drop, _⟩ := hp_bif
  have hp_inter_ST : ∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T :=
    fun x hx => Finset.mem_union.mp (hp_inter x hx)
  -- L_p, R_p vertex bounds.
  have ha_notin_L_p_drop : a ∉ L_p.refactor_vertices.dropLast := fun h_in =>
    ha_p_tail (hL_p_drop_sub a h_in)
  have ha_notin_R_p : a ∉ R_p.refactor_vertices := fun h_in =>
    ha_p_tail (hR_p_sub a h_in)
  have hb_notin_L_p : b ∉ L_p.refactor_vertices := fun h_in =>
    hb_p_drop (hL_p_sub b h_in)
  have hb_notin_R_p_drop : b ∉ R_p.refactor_vertices.dropLast := fun h_in =>
    hb_p_drop (hR_p_drop_sub b h_in)
  -- vL_exit, vR_exit ∈ G.V, ∈ G.V \ S, ∈ marg.
  have hvL_exit_GV : vL_exit ∈ G.V :=
    refactor_Walk.refactor_target_in_GV_of_directedWalk_pos L_W_seg hL_W_dir hL_W_pos
  have hvR_exit_GV : vR_exit ∈ G.V :=
    refactor_Walk.refactor_target_in_GV_of_directedWalk_pos R_W_seg hR_W_dir hR_W_pos
  have hvL_exit_VS : vL_exit ∈ G.V \ S :=
    Finset.mem_sdiff.mpr ⟨hvL_exit_GV, hvL_exit_notS⟩
  have hvR_exit_VS : vR_exit ∈ G.V \ S :=
    Finset.mem_sdiff.mpr ⟨hvR_exit_GV, hvR_exit_notS⟩
  have hvL_exit_marg : vL_exit ∈ G.refactor_marginalize S hS := by
    change vL_exit ∈ G.J ∪ (G.V \ S)
    exact Finset.mem_union_right _ hvL_exit_VS
  have hvR_exit_marg : vR_exit ∈ G.refactor_marginalize S hS := by
    change vR_exit ∈ G.J ∪ (G.V \ S)
    exact Finset.mem_union_right _ hvR_exit_VS
  -- L_marg_seg, R_marg_seg vertex subsets back into L_p, R_p.
  have hL_marg_ne : L_marg_seg.refactor_vertices ≠ [] :=
    refactor_Walk.refactor_vertices_ne_nil L_marg_seg
  have hR_marg_ne : R_marg_seg.refactor_vertices ≠ [] :=
    refactor_Walk.refactor_vertices_ne_nil R_marg_seg
  have hL_marg_sub_L_p :
      ∀ x ∈ L_marg_seg.refactor_vertices, x ∈ L_p.refactor_vertices := by
    intro x hx; rw [hL_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
  have hR_marg_sub_R_p :
      ∀ x ∈ R_marg_seg.refactor_vertices, x ∈ R_p.refactor_vertices := by
    intro x hx; rw [hR_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
  have hL_marg_drop_sub_L_p_drop :
      ∀ x ∈ L_marg_seg.refactor_vertices.dropLast,
        x ∈ L_p.refactor_vertices.dropLast := by
    intro x hx
    rw [hL_p_vs_eq, List.dropLast_append_of_ne_nil hL_marg_ne]
    exact List.mem_append.mpr (Or.inr hx)
  have hR_marg_drop_sub_R_p_drop :
      ∀ x ∈ R_marg_seg.refactor_vertices.dropLast,
        x ∈ R_p.refactor_vertices.dropLast := by
    intro x hx
    rw [hR_p_vs_eq, List.dropLast_append_of_ne_nil hR_marg_ne]
    exact List.mem_append.mpr (Or.inr hx)
  -- L_marg_seg, R_marg_seg interior ⊆ S ∨ T.
  have hL_marg_inter_ST :
      ∀ x ∈ L_marg_seg.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
    intro x hx
    by_cases h_L_marg_pos : L_marg_seg.refactor_length ≥ 1
    · have h_t_ne : L_marg_seg.refactor_vertices.tail ≠ [] :=
        refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_marg_seg h_L_marg_pos
      have h_drop_eq : L_marg_seg.refactor_vertices.dropLast
          = vL_exit :: L_marg_seg.refactor_vertices.tail.dropLast := by
        conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_marg_seg]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have h_drop : x ∈ L_marg_seg.refactor_vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have h_L_p_drop : x ∈ L_p.refactor_vertices.dropLast :=
        hL_marg_drop_sub_L_p_drop x h_drop
      have h_x_p_tail : x ∈ p.refactor_vertices.tail := hL_p_drop_sub x h_L_p_drop
      have h_v : x ∈ L_marg_seg.refactor_vertices := List.mem_of_mem_dropLast h_drop
      have h_L_p : x ∈ L_p.refactor_vertices := hL_marg_sub_L_p x h_v
      have h_x_p_drop : x ∈ p.refactor_vertices.dropLast := hL_p_sub x h_L_p
      have h_x_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
        refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
      exact hp_inter_ST x h_x_p_inter
    · have h_L_marg_zero : L_marg_seg.refactor_length = 0 := by omega
      match L_marg_seg, h_L_marg_zero with
      | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hx
  have hR_marg_inter_ST :
      ∀ x ∈ R_marg_seg.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
    intro x hx
    by_cases h_R_marg_pos : R_marg_seg.refactor_length ≥ 1
    · have h_t_ne : R_marg_seg.refactor_vertices.tail ≠ [] :=
        refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_marg_seg h_R_marg_pos
      have h_drop_eq : R_marg_seg.refactor_vertices.dropLast
          = vR_exit :: R_marg_seg.refactor_vertices.tail.dropLast := by
        conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg_seg]
        exact List.dropLast_cons_of_ne_nil h_t_ne
      have h_drop : x ∈ R_marg_seg.refactor_vertices.dropLast := by
        rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
      have h_R_p_drop : x ∈ R_p.refactor_vertices.dropLast :=
        hR_marg_drop_sub_R_p_drop x h_drop
      have h_x_p_drop : x ∈ p.refactor_vertices.dropLast := hR_p_drop_sub x h_R_p_drop
      have h_v : x ∈ R_marg_seg.refactor_vertices := List.mem_of_mem_dropLast h_drop
      have h_R_p : x ∈ R_p.refactor_vertices := hR_marg_sub_R_p x h_v
      have h_x_p_tail : x ∈ p.refactor_vertices.tail := hR_p_sub x h_R_p
      have h_x_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
        refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
      exact hp_inter_ST x h_x_p_inter
    · have h_R_marg_zero : R_marg_seg.refactor_length = 0 := by omega
      match R_marg_seg, h_R_marg_zero with
      | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hx
  -- L_marg_seg, R_marg_seg vertex bounds for a, b.
  have ha_notin_L_marg_drop : a ∉ L_marg_seg.refactor_vertices.dropLast := fun h_in =>
    ha_notin_L_p_drop (hL_marg_drop_sub_L_p_drop a h_in)
  have ha_notin_R_marg : a ∉ R_marg_seg.refactor_vertices := fun h_in =>
    ha_notin_R_p (hR_marg_sub_R_p a h_in)
  have hb_notin_L_marg : b ∉ L_marg_seg.refactor_vertices := fun h_in =>
    hb_notin_L_p (hL_marg_sub_L_p b h_in)
  have hb_notin_R_marg_drop : b ∉ R_marg_seg.refactor_vertices.dropLast := fun h_in =>
    hb_notin_R_p_drop (hR_marg_drop_sub_R_p_drop b h_in)
  -- Step 1: Build the marg.L edge s(vL_exit, vR_exit) ∈ marg.L via a
  -- G-bifurcation `mkBifurcation L_W_seg R_W_seg` with directed-hinge
  -- source `c`.
  -- L_W_seg.refactor_vertices.dropLast ⊆ S (source c ∈ S + interior ⊆ S).
  have hL_W_drop_S : ∀ x ∈ L_W_seg.refactor_vertices.dropLast, x ∈ S := by
    intro x hx
    have h_tail_ne : L_W_seg.refactor_vertices.tail ≠ [] :=
      refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_W_seg hL_W_pos
    have h_drop_eq : L_W_seg.refactor_vertices.dropLast
        = c :: L_W_seg.refactor_vertices.tail.dropLast := by
      conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_W_seg]
      exact List.dropLast_cons_of_ne_nil h_tail_ne
    rw [h_drop_eq] at hx
    rcases List.mem_cons.mp hx with rfl | hx_rest
    · exact hc_S
    · exact hL_W_inter x hx_rest
  have hR_W_drop_S : ∀ x ∈ R_W_seg.refactor_vertices.dropLast, x ∈ S := by
    intro x hx
    have h_tail_ne : R_W_seg.refactor_vertices.tail ≠ [] :=
      refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_W_seg hR_W_pos
    have h_drop_eq : R_W_seg.refactor_vertices.dropLast
        = c :: R_W_seg.refactor_vertices.tail.dropLast := by
      conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_W_seg]
      exact List.dropLast_cons_of_ne_nil h_tail_ne
    rw [h_drop_eq] at hx
    rcases List.mem_cons.mp hx with rfl | hx_rest
    · exact hc_S
    · exact hR_W_inter x hx_rest
  -- L_W_seg.refactor_vertices = L_W_seg.refactor_vertices.dropLast ++ [vL_exit].
  have hL_W_decomp :
      L_W_seg.refactor_vertices = L_W_seg.refactor_vertices.dropLast ++ [vL_exit] := by
    have h_ne : L_W_seg.refactor_vertices ≠ [] :=
      refactor_Walk.refactor_vertices_ne_nil L_W_seg
    have h_last : L_W_seg.refactor_vertices.getLast h_ne = vL_exit :=
      refactor_Walk.refactor_vertices_getLast L_W_seg
    have := List.dropLast_append_getLast h_ne
    rw [h_last] at this; exact this.symm
  have hR_W_decomp :
      R_W_seg.refactor_vertices = R_W_seg.refactor_vertices.dropLast ++ [vR_exit] := by
    have h_ne : R_W_seg.refactor_vertices ≠ [] :=
      refactor_Walk.refactor_vertices_ne_nil R_W_seg
    have h_last : R_W_seg.refactor_vertices.getLast h_ne = vR_exit :=
      refactor_Walk.refactor_vertices_getLast R_W_seg
    have := List.dropLast_append_getLast h_ne
    rw [h_last] at this; exact this.symm
  have hvL_exit_notin_L_W_drop :
      vL_exit ∉ L_W_seg.refactor_vertices.dropLast := fun h_in =>
    hvL_exit_notS (hL_W_drop_S vL_exit h_in)
  have hvR_exit_notin_R_W_drop :
      vR_exit ∉ R_W_seg.refactor_vertices.dropLast := fun h_in =>
    hvR_exit_notS (hR_W_drop_S vR_exit h_in)
  have hvL_exit_notin_R_W : vL_exit ∉ R_W_seg.refactor_vertices := by
    intro h_in
    rw [hR_W_decomp] at h_in
    rcases List.mem_append.mp h_in with h_dL | h_last
    · exact hvL_exit_notS (hR_W_drop_S vL_exit h_dL)
    · rw [List.mem_singleton] at h_last
      exact hvL_vR_exit_ne h_last
  have hvR_exit_notin_L_W : vR_exit ∉ L_W_seg.refactor_vertices := by
    intro h_in
    rw [hL_W_decomp] at h_in
    rcases List.mem_append.mp h_in with h_dL | h_last
    · exact hvR_exit_notS (hL_W_drop_S vR_exit h_dL)
    · rw [List.mem_singleton] at h_last
      exact hvL_vR_exit_ne h_last.symm
  -- G-bifurcation source c with hinge between vL_exit and vR_exit.
  have h_G_bif_src :
      (refactor_Walk.refactor_mkBifurcation L_W_seg hL_W_dir hL_W_pos
        R_W_seg).refactor_IsBifurcationSource c :=
    refactor_Walk.refactor_mkBifurcation_isBifurcationSource L_W_seg hL_W_dir hL_W_pos
      R_W_seg hR_W_dir hR_W_pos
      hvL_vR_exit_ne hvL_exit_notin_L_W_drop hvL_exit_notin_R_W
      hvR_exit_notin_L_W hvR_exit_notin_R_W_drop
  have h_G_bif_is_bif :
      (refactor_Walk.refactor_mkBifurcation L_W_seg hL_W_dir hL_W_pos
        R_W_seg).refactor_IsBifurcation :=
    refactor_Walk.refactor_isBifurcationSource_to_isBifurcation _ c h_G_bif_src
  -- G-bifurcation's interior ⊆ S.
  have h_G_bif_inter_S :
      ∀ x ∈ (refactor_Walk.refactor_mkBifurcation L_W_seg hL_W_dir hL_W_pos
              R_W_seg).refactor_vertices.tail.dropLast, x ∈ S := by
    intro x hx
    rw [refactor_vertices_tail_dropLast_mkBifurcation
          L_W_seg hL_W_dir hL_W_pos R_W_seg hR_W_pos] at hx
    rcases List.mem_append.mp hx with hx_L | hx_R
    · rw [List.mem_reverse] at hx_L
      exact hL_W_inter x hx_L
    · exact hR_W_drop_S x hx_R
  -- The marg.L edge (Sym2-image unwrap via refactor_marginalize_L_iff).
  have hvLvR_in_margL : s(vL_exit, vR_exit) ∈ (G.refactor_marginalize S hS).L := by
    refine (refactor_marginalize_L_iff G S hS).mpr
      ⟨(vL_exit, vR_exit), hvL_exit_VS, hvR_exit_VS, hvL_vR_exit_ne, ?_, rfl⟩
    exact Or.inl ⟨refactor_Walk.refactor_mkBifurcation L_W_seg hL_W_dir hL_W_pos R_W_seg,
                  h_G_bif_is_bif, h_G_bif_inter_S⟩
  -- Step 2-4: Case-split on L_marg_seg.refactor_length, R_marg_seg.refactor_length and
  -- assemble via `refactor_mkBifurcationBidir` with hinge s(vL_exit, vR_exit).
  by_cases hL_marg_pos : L_marg_seg.refactor_length ≥ 1
  · -- L_marg_seg positive.  Project to marg.
    obtain ⟨L_marg, hL_marg_dir', hL_marg_pos', hL_marg_vs, hL_marg_dL,
            _, hL_marg_inter⟩ :=
      refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
        L_marg_seg hL_marg_dir hL_marg_pos hvL_exit_marg ha_marg hL_marg_inter_ST
    have ha_notin_L_marg_dL : a ∉ L_marg.refactor_vertices.dropLast := fun h_in =>
      ha_notin_L_marg_drop (hL_marg_dL a h_in)
    have hb_notin_L_marg' : b ∉ L_marg.refactor_vertices := fun h_in =>
      hb_notin_L_marg (hL_marg_vs b h_in)
    by_cases hR_marg_pos : R_marg_seg.refactor_length ≥ 1
    · -- L+, R+.
      obtain ⟨R_marg, hR_marg_dir', hR_marg_pos', hR_marg_vs, hR_marg_dL,
              _, hR_marg_inter⟩ :=
        refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
          R_marg_seg hR_marg_dir hR_marg_pos hvR_exit_marg hb_marg hR_marg_inter_ST
      have ha_notin_R_marg' : a ∉ R_marg.refactor_vertices := fun h_in =>
        ha_notin_R_marg (hR_marg_vs a h_in)
      have hb_notin_R_marg_dL : b ∉ R_marg.refactor_vertices.dropLast := fun h_in =>
        hb_notin_R_marg_drop (hR_marg_dL b h_in)
      refine ⟨refactor_Walk.refactor_mkBifurcationBidir L_marg hL_marg_dir' R_marg
                hvLvR_in_margL, ?_, ?_⟩
      · exact refactor_Walk.refactor_mkBifurcationBidir_isBifurcation L_marg hL_marg_dir'
          R_marg hR_marg_dir' hvLvR_in_margL hab_ne
          ha_notin_L_marg_dL ha_notin_R_marg' hb_notin_L_marg' hb_notin_R_marg_dL
      · intro x hx
        rw [refactor_vertices_tail_dropLast_mkBifurcationBidir_Lpos
              L_marg hL_marg_dir' R_marg hvLvR_in_margL hL_marg_pos'] at hx
        rcases List.mem_append.mp hx with hx_L | hx_R
        · rw [List.mem_reverse] at hx_L
          exact hL_marg_inter x hx_L
        · have h_R_marg_ne : R_marg.refactor_vertices ≠ [] :=
            refactor_Walk.refactor_vertices_ne_nil R_marg
          rw [List.dropLast_cons_of_ne_nil h_R_marg_ne] at hx_R
          rcases List.mem_cons.mp hx_R with rfl | hx_R_dL
          · -- x = vL_exit.
            have h_x_in_L_p : x ∈ L_p.refactor_vertices :=
              hL_marg_sub_L_p _ (refactor_Walk.refactor_head_mem_vertices L_marg_seg)
            have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast :=
              hL_p_sub _ h_x_in_L_p
            have h_L_marg_t_ne : L_marg.refactor_vertices.tail ≠ [] :=
              refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_marg hL_marg_pos'
            have hvL_in_L_marg_dL : x ∈ L_marg.refactor_vertices.dropLast := by
              rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_marg,
                  List.dropLast_cons_of_ne_nil h_L_marg_t_ne]
              exact List.mem_cons_self
            have hvL_in_L_marg_seg_dL : x ∈ L_marg_seg.refactor_vertices.dropLast :=
              hL_marg_dL _ hvL_in_L_marg_dL
            have hvL_in_L_p_dL : x ∈ L_p.refactor_vertices.dropLast :=
              hL_marg_drop_sub_L_p_drop _ hvL_in_L_marg_seg_dL
            have h_x_in_p_tail : x ∈ p.refactor_vertices.tail :=
              hL_p_drop_sub _ hvL_in_L_p_dL
            have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
              refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
            rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
            · exact absurd h_S hvL_exit_notS
            · exact h_T
          · -- x ∈ R_marg.refactor_vertices.dropLast.
            have h_R_t_ne : R_marg.refactor_vertices.tail ≠ [] :=
              refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_marg hR_marg_pos'
            rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
                List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R_dL
            rcases List.mem_cons.mp hx_R_dL with rfl | hx_R_inner
            · -- x = vR_exit.
              have h_x_in_R_p : x ∈ R_p.refactor_vertices :=
                hR_marg_sub_R_p _ (refactor_Walk.refactor_head_mem_vertices R_marg_seg)
              have h_x_in_p_tail : x ∈ p.refactor_vertices.tail :=
                hR_p_sub _ h_x_in_R_p
              have hvR_in_R_marg_dL : x ∈ R_marg.refactor_vertices.dropLast := by
                rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
                    List.dropLast_cons_of_ne_nil h_R_t_ne]
                exact List.mem_cons_self
              have hvR_in_R_marg_seg_dL : x ∈ R_marg_seg.refactor_vertices.dropLast :=
                hR_marg_dL _ hvR_in_R_marg_dL
              have hvR_in_R_p_dL : x ∈ R_p.refactor_vertices.dropLast :=
                hR_marg_drop_sub_R_p_drop _ hvR_in_R_marg_seg_dL
              have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast :=
                hR_p_drop_sub _ hvR_in_R_p_dL
              have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
                refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
              rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
              · exact absurd h_S hvR_exit_notS
              · exact h_T
            · exact hR_marg_inter x hx_R_inner
    · -- L+, R nil → vR_exit = b (after subst, b is eliminated).
      have h_R_zero : R_marg_seg.refactor_length = 0 := by omega
      have hvR_b_eq : vR_exit = b := by
        match R_marg_seg, h_R_zero with
        | .nil _ _, _ => rfl
      subst hvR_b_eq
      refine ⟨refactor_Walk.refactor_mkBifurcationBidir L_marg hL_marg_dir'
                (refactor_Walk.nil vR_exit hvR_exit_marg) hvLvR_in_margL, ?_, ?_⟩
      · refine refactor_Walk.refactor_mkBifurcationBidir_isBifurcation L_marg hL_marg_dir'
          (refactor_Walk.nil vR_exit hvR_exit_marg) trivial hvLvR_in_margL hab_ne
          ha_notin_L_marg_dL ?_ hb_notin_L_marg' ?_
        · intro h_in
          change a ∈ ([vR_exit] : List Node) at h_in
          rw [List.mem_singleton] at h_in
          exact ha_notin_R_marg
            (by rw [h_in]; exact refactor_Walk.refactor_head_mem_vertices R_marg_seg)
        · intro h_in
          change vR_exit ∈ ([vR_exit] : List Node).dropLast at h_in
          simp at h_in
      · intro x hx
        rw [refactor_vertices_tail_dropLast_mkBifurcationBidir_Lpos
              L_marg hL_marg_dir' (refactor_Walk.nil vR_exit hvR_exit_marg) hvLvR_in_margL
              hL_marg_pos'] at hx
        rcases List.mem_append.mp hx with hx_L | hx_R
        · rw [List.mem_reverse] at hx_L
          exact hL_marg_inter x hx_L
        · -- x ∈ (vL_exit :: [vR_exit]).dropLast = [vL_exit].
          change x ∈ ((vL_exit :: [vR_exit]) : List Node).dropLast at hx_R
          change x ∈ ([vL_exit, vR_exit] : List Node).dropLast at hx_R
          simp [List.dropLast] at hx_R
          rw [hx_R]
          have h_x_in_L_p : vL_exit ∈ L_p.refactor_vertices :=
            hL_marg_sub_L_p _ (refactor_Walk.refactor_head_mem_vertices L_marg_seg)
          have h_x_in_p_drop : vL_exit ∈ p.refactor_vertices.dropLast :=
            hL_p_sub _ h_x_in_L_p
          have h_L_marg_t_ne : L_marg.refactor_vertices.tail ≠ [] :=
            refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_marg hL_marg_pos'
          have hvL_in_L_marg_dL : vL_exit ∈ L_marg.refactor_vertices.dropLast := by
            rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_marg,
                List.dropLast_cons_of_ne_nil h_L_marg_t_ne]
            exact List.mem_cons_self
          have hvL_in_L_marg_seg_dL : vL_exit ∈ L_marg_seg.refactor_vertices.dropLast :=
            hL_marg_dL _ hvL_in_L_marg_dL
          have hvL_in_L_p_dL : vL_exit ∈ L_p.refactor_vertices.dropLast :=
            hL_marg_drop_sub_L_p_drop _ hvL_in_L_marg_seg_dL
          have h_x_in_p_tail : vL_exit ∈ p.refactor_vertices.tail :=
            hL_p_drop_sub _ hvL_in_L_p_dL
          have h_x_in_p_inter : vL_exit ∈ p.refactor_vertices.tail.dropLast :=
            refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
          rcases hp_inter_ST vL_exit h_x_in_p_inter with h_S | h_T
          · exact absurd h_S hvL_exit_notS
          · exact h_T
  · -- L_marg_seg nil → vL_exit = a (after subst, a is eliminated).
    have h_L_zero : L_marg_seg.refactor_length = 0 := by omega
    have hvL_a_eq : vL_exit = a := by
      match L_marg_seg, h_L_zero with
      | .nil _ _, _ => rfl
    subst hvL_a_eq
    by_cases hR_marg_pos : R_marg_seg.refactor_length ≥ 1
    · -- L nil, R+.
      obtain ⟨R_marg, hR_marg_dir', hR_marg_pos', hR_marg_vs, hR_marg_dL,
              _, hR_marg_inter⟩ :=
        refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
          R_marg_seg hR_marg_dir hR_marg_pos hvR_exit_marg hb_marg hR_marg_inter_ST
      have hvL_exit_notin_R_marg : vL_exit ∉ R_marg.refactor_vertices := fun h_in =>
        ha_notin_R_marg (hR_marg_vs vL_exit h_in)
      have hb_notin_R_marg_dL : b ∉ R_marg.refactor_vertices.dropLast := fun h_in =>
        hb_notin_R_marg_drop (hR_marg_dL b h_in)
      refine ⟨refactor_Walk.refactor_mkBifurcationBidir
                (refactor_Walk.nil vL_exit hvL_exit_marg) trivial R_marg
                hvLvR_in_margL, ?_, ?_⟩
      · refine refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
          (refactor_Walk.nil vL_exit hvL_exit_marg)
          trivial R_marg hR_marg_dir' hvLvR_in_margL hab_ne ?_ hvL_exit_notin_R_marg
          ?_ hb_notin_R_marg_dL
        · intro h_in
          change vL_exit ∈ ([vL_exit] : List Node).dropLast at h_in
          simp at h_in
        · intro h_in
          change b ∈ ([vL_exit] : List Node) at h_in
          rw [List.mem_singleton] at h_in
          exact hab_ne h_in.symm
      · intro x hx
        have h_bif_vs :
            (refactor_Walk.refactor_mkBifurcationBidir
              (refactor_Walk.nil vL_exit hvL_exit_marg) trivial R_marg
              hvLvR_in_margL).refactor_vertices = vL_exit :: R_marg.refactor_vertices := by
          rw [refactor_Walk.refactor_vertices_mkBifurcationBidir]
          change ([vL_exit] : List Node).reverse.dropLast ++ (vL_exit :: R_marg.refactor_vertices)
                = vL_exit :: R_marg.refactor_vertices
          simp
        rw [h_bif_vs] at hx
        change x ∈ R_marg.refactor_vertices.dropLast at hx
        have h_R_t_ne : R_marg.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_marg hR_marg_pos'
        rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
            List.dropLast_cons_of_ne_nil h_R_t_ne] at hx
        rcases List.mem_cons.mp hx with rfl | hx_inner
        · -- x = vR_exit.
          have h_x_in_R_p : x ∈ R_p.refactor_vertices :=
            hR_marg_sub_R_p _ (refactor_Walk.refactor_head_mem_vertices R_marg_seg)
          have h_x_in_p_tail : x ∈ p.refactor_vertices.tail :=
            hR_p_sub _ h_x_in_R_p
          have hvR_in_R_marg_dL : x ∈ R_marg.refactor_vertices.dropLast := by
            rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
                List.dropLast_cons_of_ne_nil h_R_t_ne]
            exact List.mem_cons_self
          have hvR_in_R_marg_seg_dL : x ∈ R_marg_seg.refactor_vertices.dropLast :=
            hR_marg_dL _ hvR_in_R_marg_dL
          have hvR_in_R_p_dL : x ∈ R_p.refactor_vertices.dropLast :=
            hR_marg_drop_sub_R_p_drop _ hvR_in_R_marg_seg_dL
          have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast :=
            hR_p_drop_sub _ hvR_in_R_p_dL
          have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
            refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
          rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
          · exact absurd h_S hvR_exit_notS
          · exact h_T
        · exact hR_marg_inter x hx_inner
    · -- L nil, R nil → vR_exit = b.
      have h_R_zero : R_marg_seg.refactor_length = 0 := by omega
      have hvR_b_eq : vR_exit = b := by
        match R_marg_seg, h_R_zero with
        | .nil _ _, _ => rfl
      subst hvR_b_eq
      refine ⟨refactor_Walk.refactor_mkBifurcationBidir
                (refactor_Walk.nil vL_exit hvL_exit_marg) trivial
                (refactor_Walk.nil vR_exit hvR_exit_marg) hvLvR_in_margL, ?_, ?_⟩
      · refine refactor_Walk.refactor_mkBifurcationBidir_isBifurcation
          (refactor_Walk.nil vL_exit hvL_exit_marg) trivial
          (refactor_Walk.nil vR_exit hvR_exit_marg) trivial hvLvR_in_margL hab_ne
          ?_ ?_ ?_ ?_
        · intro h_in
          change vL_exit ∈ ([vL_exit] : List Node).dropLast at h_in
          simp at h_in
        · intro h_in
          change vL_exit ∈ ([vR_exit] : List Node) at h_in
          rw [List.mem_singleton] at h_in
          exact hvL_vR_exit_ne h_in
        · intro h_in
          change vR_exit ∈ ([vL_exit] : List Node) at h_in
          rw [List.mem_singleton] at h_in
          exact hvL_vR_exit_ne h_in.symm
        · intro h_in
          change vR_exit ∈ ([vR_exit] : List Node).dropLast at h_in
          simp at h_in
      · intro x hx
        have h_bif_vs :
            (refactor_Walk.refactor_mkBifurcationBidir
              (refactor_Walk.nil vL_exit hvL_exit_marg) trivial
              (refactor_Walk.nil vR_exit hvR_exit_marg) hvLvR_in_margL).refactor_vertices
              = [vL_exit, vR_exit] := by
          rw [refactor_Walk.refactor_vertices_mkBifurcationBidir]
          change ([vL_exit] : List Node).reverse.dropLast ++ (vL_exit :: [vR_exit])
                = [vL_exit, vR_exit]
          simp
        rw [h_bif_vs] at hx
        change x ∈ ([vL_exit, vR_exit] : List Node).tail.dropLast at hx
        simp at hx
-- REFACTOR-BLOCK-REPLACEMENT-END: backward_marg_to_g_bif_dir_hinge_cInS_betaNeGamma_one_orientation

-- ## Refactor replacements — Phase E (assembly: Φ_L iff + L-field equality)
--
-- Two net-new ports (no paired ORIGINAL — `marg_PhiL_iff` and
-- `marg_L_field_eq` were `private lemma`s with no markers in the
-- original).  The Φ_L iff wires the three Phase D auxiliaries
-- (`refactor_forward_marg_to_g_bif_one_orientation`,
-- `refactor_backward_marg_to_g_bif_bidir_hinge_one_orientation`,
-- `refactor_backward_marg_to_g_bif_dir_hinge_cInS_betaNeGamma_one_orientation`)
-- into a single iff between `marg.Φ_L T` and `G.Φ_L (S ∪ T)`.  The
-- `L`-field equality lifts that iff to a `Finset` equality on the
-- post-refactor `marg.L : Finset (Sym2 Node)`.
--
-- The only structurally-new refactor surface in this phase is the
-- extra `Finset.image` layer in `refactor_marg_L_field_eq`: under
-- refactor, `marg.L` is built as `(filter …).image (fun e => s(e.1, e.2))`,
-- so the proof becomes `congr 1` (peeling the outer `.image` of an
-- identical `fun e => s(e.1, e.2)`) followed by the same
-- `Finset.filter_congr` step the original used on its filter-only
-- `marg.L`.  The Φ_L iff body itself ports one-to-one from the
-- original; the Sym2-witness machinery was already absorbed into the
-- Phase D ports underneath.

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marg_PhiL_iff (was: refactor_marg_PhiL_iff)
-- ## Φ_L membership iff (parametric in `S, T`).
private lemma refactor_marg_PhiL_iff {G : refactor_CDMG Node} (S T : Finset Node)
    (hS : S ⊆ G.V) (_hT : T ⊆ G.V) (_hDisj : Disjoint S T)
    {u v : Node}
    (hu : u ∈ G.V \ (S ∪ T)) (hv : v ∈ G.V \ (S ∪ T)) :
    (G.refactor_marginalize S hS).refactor_MarginalizationΦL T u v ↔
      G.refactor_MarginalizationΦL (S ∪ T) u v := by
  have hu_g : u ∈ G := Finset.mem_union_right _ (Finset.mem_sdiff.mp hu).1
  have hv_g : v ∈ G := Finset.mem_union_right _ (Finset.mem_sdiff.mp hv).1
  have hu_notSuT : u ∉ S ∪ T := (Finset.mem_sdiff.mp hu).2
  have hv_notSuT : v ∉ S ∪ T := (Finset.mem_sdiff.mp hv).2
  have hu_notS : u ∉ S := fun h => hu_notSuT (Finset.mem_union_left _ h)
  have hv_notS : v ∉ S := fun h => hv_notSuT (Finset.mem_union_left _ h)
  have hu_notT : u ∉ T := fun h => hu_notSuT (Finset.mem_union_right _ h)
  have hv_notT : v ∉ T := fun h => hv_notSuT (Finset.mem_union_right _ h)
  have hu_marg : u ∈ G.refactor_marginalize S hS :=
    refactor_mem_marg_of_notin_union_VnoJ S T hS hu
  have hv_marg : v ∈ G.refactor_marginalize S hS :=
    refactor_mem_marg_of_notin_union_VnoJ S T hS hv
  -- Forward direction: delegate to D.1.
  have forward_one_orientation :
      ∀ {a b : Node},
        a ∈ G.V \ (S ∪ T) → b ∈ G.V \ (S ∪ T) →
        a ∈ G.refactor_marginalize S hS → b ∈ G.refactor_marginalize S hS →
        ∀ (p : refactor_Walk (G.refactor_marginalize S hS) a b),
          p.refactor_IsBifurcation →
          (∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ T) →
          ∃ q : refactor_Walk G a b, q.refactor_IsBifurcation ∧
            ∀ x ∈ q.refactor_vertices.tail.dropLast, x ∈ S ∪ T :=
    fun ha_VST hb_VST ha_marg hb_marg p hp_bif hp_inter =>
      refactor_forward_marg_to_g_bif_one_orientation S T hS ha_VST hb_VST ha_marg hb_marg
        p hp_bif hp_inter
  -- Backward direction helper: inline case-split, delegating heavy
  -- branches to D.2 (bidirected hinge) and D.3 (directed hinge with
  -- source ∈ S, β ≠ γ).
  have backward_one_orientation :
      ∀ {a b : Node},
        a ∈ G.V \ (S ∪ T) → b ∈ G.V \ (S ∪ T) →
        a ∈ G.refactor_marginalize S hS → b ∈ G.refactor_marginalize S hS →
        ∀ (p : refactor_Walk G a b),
          p.refactor_IsBifurcation →
          (∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ S ∪ T) →
          ∃ q : refactor_Walk (G.refactor_marginalize S hS) a b, q.refactor_IsBifurcation ∧
            ∀ x ∈ q.refactor_vertices.tail.dropLast, x ∈ T := by
    intro a b ha_VST hb_VST ha_marg hb_marg p hp_bif hp_inter
    have ha_notSuT : a ∉ S ∪ T := (Finset.mem_sdiff.mp ha_VST).2
    have hb_notSuT : b ∉ S ∪ T := (Finset.mem_sdiff.mp hb_VST).2
    have ha_notS : a ∉ S := fun h => ha_notSuT (Finset.mem_union_left _ h)
    have hb_notS : b ∉ S := fun h => hb_notSuT (Finset.mem_union_left _ h)
    have ha_notT : a ∉ T := fun h => ha_notSuT (Finset.mem_union_right _ h)
    have hb_notT : b ∉ T := fun h => hb_notSuT (Finset.mem_union_right _ h)
    have hp_pos : p.refactor_length ≥ 1 :=
      refactor_Walk.refactor_length_pos_of_isBifurcation hp_bif
    obtain ⟨hab_ne, ha_p_tail, hb_p_drop, i, hp_split⟩ := hp_bif
    have hp_inter_ST : ∀ x ∈ p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T :=
      fun x hx => Finset.mem_union.mp (hp_inter x hx)
    by_cases h_dir : p.refactor_IsBifurcationDirectedHingeWithSplit i
    · -- DIRECTED HINGE: c = bif source.
      obtain ⟨c, L_p, R_p, hL_p_dir, hR_p_dir, hL_p_pos, hR_p_pos, hidx,
              hL_p_sub, hR_p_sub, hL_p_drop_sub, hR_p_drop_sub⟩ :=
        refactor_Walk.refactor_exists_arms_of_bifurcation_directed_hinge_strong p i h_dir
      have ha_notin_L_p_drop : a ∉ L_p.refactor_vertices.dropLast := fun h_in =>
        ha_p_tail (hL_p_drop_sub a h_in)
      have ha_notin_R_p : a ∉ R_p.refactor_vertices := fun h_in =>
        ha_p_tail (hR_p_sub a h_in)
      have hb_notin_L_p : b ∉ L_p.refactor_vertices := fun h_in =>
        hb_p_drop (hL_p_sub b h_in)
      have hb_notin_R_p_drop : b ∉ R_p.refactor_vertices.dropLast := fun h_in =>
        hb_p_drop (hR_p_drop_sub b h_in)
      -- L_p, R_p interior ⊆ S ∨ T.
      have hL_p_inter_ST :
          ∀ x ∈ L_p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
        intro x hx
        have h_x_in_L_p_tail : x ∈ L_p.refactor_vertices.tail := List.mem_of_mem_dropLast hx
        have h_x_in_L_p : x ∈ L_p.refactor_vertices := List.mem_of_mem_tail h_x_in_L_p_tail
        have h_L_p_t_ne : L_p.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_p hL_p_pos
        have h_L_p_drop_eq :
            L_p.refactor_vertices.dropLast = c :: L_p.refactor_vertices.tail.dropLast := by
          conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_p]
          exact List.dropLast_cons_of_ne_nil h_L_p_t_ne
        have h_x_in_L_p_drop : x ∈ L_p.refactor_vertices.dropLast := by
          rw [h_L_p_drop_eq]; exact List.mem_cons_of_mem _ hx
        have h_x_in_p_tail : x ∈ p.refactor_vertices.tail := hL_p_drop_sub x h_x_in_L_p_drop
        have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast := hL_p_sub x h_x_in_L_p
        have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
          refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
        exact hp_inter_ST x h_x_in_p_inter
      have hR_p_inter_ST :
          ∀ x ∈ R_p.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
        intro x hx
        have h_x_in_R_p_tail : x ∈ R_p.refactor_vertices.tail := List.mem_of_mem_dropLast hx
        have h_x_in_R_p : x ∈ R_p.refactor_vertices := List.mem_of_mem_tail h_x_in_R_p_tail
        have h_R_p_t_ne : R_p.refactor_vertices.tail ≠ [] :=
          refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_p hR_p_pos
        have h_R_p_drop_eq :
            R_p.refactor_vertices.dropLast = c :: R_p.refactor_vertices.tail.dropLast := by
          conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_p]
          exact List.dropLast_cons_of_ne_nil h_R_p_t_ne
        have h_x_in_R_p_drop : x ∈ R_p.refactor_vertices.dropLast := by
          rw [h_R_p_drop_eq]; exact List.mem_cons_of_mem _ hx
        have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast := hR_p_drop_sub x h_x_in_R_p_drop
        have h_x_in_p_tail : x ∈ p.refactor_vertices.tail := hR_p_sub x h_x_in_R_p
        have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
          refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
        exact hp_inter_ST x h_x_in_p_inter
      by_cases hc_S : c ∈ S
      · -- c ∈ S.  Apply refactor_find_first_non_W_directed S on L_p and R_p.
        obtain ⟨vL_exit, L_W_seg, L_marg_seg, hL_W_dir, hL_marg_dir, hL_W_pos,
                hvL_exit_notS, hL_W_inter, _, hL_p_vs_eq⟩ :=
          refactor_find_first_non_W_directed S L_p hL_p_dir hL_p_pos ha_notS
        obtain ⟨vR_exit, R_W_seg, R_marg_seg, hR_W_dir, hR_marg_dir, hR_W_pos,
                hvR_exit_notS, hR_W_inter, _, hR_p_vs_eq⟩ :=
          refactor_find_first_non_W_directed S R_p hR_p_dir hR_p_pos hb_notS
        have hvL_exit_GV : vL_exit ∈ G.V :=
          refactor_Walk.refactor_target_in_GV_of_directedWalk_pos L_W_seg hL_W_dir hL_W_pos
        have hvR_exit_GV : vR_exit ∈ G.V :=
          refactor_Walk.refactor_target_in_GV_of_directedWalk_pos R_W_seg hR_W_dir hR_W_pos
        have hvL_exit_VS : vL_exit ∈ G.V \ S :=
          Finset.mem_sdiff.mpr ⟨hvL_exit_GV, hvL_exit_notS⟩
        have hvR_exit_VS : vR_exit ∈ G.V \ S :=
          Finset.mem_sdiff.mpr ⟨hvR_exit_GV, hvR_exit_notS⟩
        have hvL_exit_marg : vL_exit ∈ G.refactor_marginalize S hS := by
          change vL_exit ∈ G.J ∪ (G.V \ S)
          exact Finset.mem_union_right _ hvL_exit_VS
        have hvR_exit_marg : vR_exit ∈ G.refactor_marginalize S hS := by
          change vR_exit ∈ G.J ∪ (G.V \ S)
          exact Finset.mem_union_right _ hvR_exit_VS
        have hL_marg_ne : L_marg_seg.refactor_vertices ≠ [] :=
          refactor_Walk.refactor_vertices_ne_nil L_marg_seg
        have hR_marg_ne : R_marg_seg.refactor_vertices ≠ [] :=
          refactor_Walk.refactor_vertices_ne_nil R_marg_seg
        have hL_marg_sub_L_p :
            ∀ x ∈ L_marg_seg.refactor_vertices, x ∈ L_p.refactor_vertices := by
          intro x hx; rw [hL_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
        have hR_marg_sub_R_p :
            ∀ x ∈ R_marg_seg.refactor_vertices, x ∈ R_p.refactor_vertices := by
          intro x hx; rw [hR_p_vs_eq]; exact List.mem_append.mpr (Or.inr hx)
        have hL_marg_drop_sub_L_p_drop :
            ∀ x ∈ L_marg_seg.refactor_vertices.dropLast,
              x ∈ L_p.refactor_vertices.dropLast := by
          intro x hx
          rw [hL_p_vs_eq, List.dropLast_append_of_ne_nil hL_marg_ne]
          exact List.mem_append.mpr (Or.inr hx)
        have hR_marg_drop_sub_R_p_drop :
            ∀ x ∈ R_marg_seg.refactor_vertices.dropLast,
              x ∈ R_p.refactor_vertices.dropLast := by
          intro x hx
          rw [hR_p_vs_eq, List.dropLast_append_of_ne_nil hR_marg_ne]
          exact List.mem_append.mpr (Or.inr hx)
        have hL_marg_inter_ST :
            ∀ x ∈ L_marg_seg.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
          intro x hx
          have h_t : x ∈ L_marg_seg.refactor_vertices.tail := List.mem_of_mem_dropLast hx
          have h_v : x ∈ L_marg_seg.refactor_vertices := List.mem_of_mem_tail h_t
          have h_L_p : x ∈ L_p.refactor_vertices := hL_marg_sub_L_p x h_v
          have h_x_p_drop : x ∈ p.refactor_vertices.dropLast := hL_p_sub x h_L_p
          by_cases h_L_marg_pos : L_marg_seg.refactor_length ≥ 1
          · have h_t_ne : L_marg_seg.refactor_vertices.tail ≠ [] :=
              refactor_Walk.refactor_tail_vertices_ne_nil_of_pos L_marg_seg h_L_marg_pos
            have h_drop_eq : L_marg_seg.refactor_vertices.dropLast
                = vL_exit :: L_marg_seg.refactor_vertices.tail.dropLast := by
              conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail L_marg_seg]
              exact List.dropLast_cons_of_ne_nil h_t_ne
            have h_drop : x ∈ L_marg_seg.refactor_vertices.dropLast := by
              rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
            have h_L_p_drop : x ∈ L_p.refactor_vertices.dropLast :=
              hL_marg_drop_sub_L_p_drop x h_drop
            have h_x_p_tail : x ∈ p.refactor_vertices.tail := hL_p_drop_sub x h_L_p_drop
            have h_x_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
              refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
            exact hp_inter_ST x h_x_p_inter
          · have h_L_marg_zero : L_marg_seg.refactor_length = 0 := by omega
            match L_marg_seg, h_L_marg_zero with
            | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hx
        have hR_marg_inter_ST :
            ∀ x ∈ R_marg_seg.refactor_vertices.tail.dropLast, x ∈ S ∨ x ∈ T := by
          intro x hx
          have h_t : x ∈ R_marg_seg.refactor_vertices.tail := List.mem_of_mem_dropLast hx
          have h_v : x ∈ R_marg_seg.refactor_vertices := List.mem_of_mem_tail h_t
          have h_R_p : x ∈ R_p.refactor_vertices := hR_marg_sub_R_p x h_v
          have h_x_p_tail : x ∈ p.refactor_vertices.tail := hR_p_sub x h_R_p
          by_cases h_R_marg_pos : R_marg_seg.refactor_length ≥ 1
          · have h_t_ne : R_marg_seg.refactor_vertices.tail ≠ [] :=
              refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_marg_seg h_R_marg_pos
            have h_drop_eq : R_marg_seg.refactor_vertices.dropLast
                = vR_exit :: R_marg_seg.refactor_vertices.tail.dropLast := by
              conv_lhs => rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg_seg]
              exact List.dropLast_cons_of_ne_nil h_t_ne
            have h_drop : x ∈ R_marg_seg.refactor_vertices.dropLast := by
              rw [h_drop_eq]; exact List.mem_cons_of_mem _ hx
            have h_R_p_drop : x ∈ R_p.refactor_vertices.dropLast :=
              hR_marg_drop_sub_R_p_drop x h_drop
            have h_x_p_drop : x ∈ p.refactor_vertices.dropLast := hR_p_drop_sub x h_R_p_drop
            have h_x_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
              refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_p_tail h_x_p_drop
            exact hp_inter_ST x h_x_p_inter
          · have h_R_marg_zero : R_marg_seg.refactor_length = 0 := by omega
            match R_marg_seg, h_R_marg_zero with
            | .nil _ _, _ => simp [refactor_Walk.refactor_vertices, List.tail] at hx
        have ha_notin_L_marg_drop : a ∉ L_marg_seg.refactor_vertices.dropLast := fun h_in =>
          ha_notin_L_p_drop (hL_marg_drop_sub_L_p_drop a h_in)
        have ha_notin_R_marg : a ∉ R_marg_seg.refactor_vertices := fun h_in =>
          ha_notin_R_p (hR_marg_sub_R_p a h_in)
        have hb_notin_L_marg : b ∉ L_marg_seg.refactor_vertices := fun h_in =>
          hb_notin_L_p (hL_marg_sub_L_p b h_in)
        have hb_notin_R_marg_drop : b ∉ R_marg_seg.refactor_vertices.dropLast := fun h_in =>
          hb_notin_R_p_drop (hR_marg_drop_sub_R_p_drop b h_in)
        by_cases hvL_vR_exit_eq : vL_exit = vR_exit
        · -- Degenerate β = γ.
          subst hvL_vR_exit_eq
          have hvL_exit_ne_a : vL_exit ≠ a := by
            intro heq
            have h_in : vL_exit ∈ R_p.refactor_vertices :=
              hR_marg_sub_R_p _ (refactor_Walk.refactor_head_mem_vertices R_marg_seg)
            have h_p_tail : vL_exit ∈ p.refactor_vertices.tail := hR_p_sub _ h_in
            exact ha_p_tail (heq ▸ h_p_tail)
          have hvL_exit_ne_b : vL_exit ≠ b := by
            intro heq
            have h_in : vL_exit ∈ L_p.refactor_vertices :=
              hL_marg_sub_L_p _ (refactor_Walk.refactor_head_mem_vertices L_marg_seg)
            have h_p_drop : vL_exit ∈ p.refactor_vertices.dropLast := hL_p_sub _ h_in
            exact hb_p_drop (heq ▸ h_p_drop)
          have hL_marg_pos : L_marg_seg.refactor_length ≥ 1 :=
            refactor_Walk.refactor_length_pos_of_ne L_marg_seg hvL_exit_ne_a
          have hR_marg_pos : R_marg_seg.refactor_length ≥ 1 :=
            refactor_Walk.refactor_length_pos_of_ne R_marg_seg hvL_exit_ne_b
          obtain ⟨L_marg, hL_marg_dir', hL_marg_pos', hL_marg_vs_sub, hL_marg_drop_sub,
                  hL_marg_tail_sub, hL_marg_inter_T⟩ :=
            refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
              L_marg_seg hL_marg_dir hL_marg_pos hvL_exit_marg ha_marg
              hL_marg_inter_ST
          obtain ⟨R_marg, hR_marg_dir', hR_marg_pos', hR_marg_vs_sub, hR_marg_drop_sub,
                  hR_marg_tail_sub, hR_marg_inter_T⟩ :=
            refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
              R_marg_seg hR_marg_dir hR_marg_pos hvL_exit_marg hb_marg
              hR_marg_inter_ST
          have ha_notin_L_marg' : a ∉ L_marg.refactor_vertices.dropLast := fun h_in =>
            ha_notin_L_marg_drop (hL_marg_drop_sub a h_in)
          have ha_notin_R_marg' : a ∉ R_marg.refactor_vertices := fun h_in =>
            ha_notin_R_marg (hR_marg_vs_sub a h_in)
          have hb_notin_L_marg' : b ∉ L_marg.refactor_vertices := fun h_in =>
            hb_notin_L_marg (hL_marg_vs_sub b h_in)
          have hb_notin_R_marg_drop' : b ∉ R_marg.refactor_vertices.dropLast := fun h_in =>
            hb_notin_R_marg_drop (hR_marg_drop_sub b h_in)
          refine ⟨refactor_Walk.refactor_mkBifurcation L_marg hL_marg_dir' hL_marg_pos' R_marg, ?_, ?_⟩
          · have h_src := refactor_Walk.refactor_mkBifurcation_isBifurcationSource
              L_marg hL_marg_dir' hL_marg_pos' R_marg hR_marg_dir' hR_marg_pos'
              hab_ne ha_notin_L_marg' ha_notin_R_marg' hb_notin_L_marg' hb_notin_R_marg_drop'
            exact refactor_Walk.refactor_isBifurcationSource_to_isBifurcation _ vL_exit h_src
          · intro x hx
            rw [refactor_vertices_tail_dropLast_mkBifurcation
                  L_marg hL_marg_dir' hL_marg_pos' R_marg hR_marg_pos'] at hx
            rcases List.mem_append.mp hx with hx_L | hx_R
            · rw [List.mem_reverse] at hx_L
              exact hL_marg_inter_T x hx_L
            · have h_R_t_ne : R_marg.refactor_vertices.tail ≠ [] :=
                refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_marg hR_marg_pos'
              rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
                  List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R
              rcases List.mem_cons.mp hx_R with rfl | hx_inner
              · have h_x_in_L_p : x ∈ L_p.refactor_vertices :=
                  hL_marg_sub_L_p _ (refactor_Walk.refactor_head_mem_vertices L_marg_seg)
                have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast :=
                  hL_p_sub _ h_x_in_L_p
                have h_x_in_R_p : x ∈ R_p.refactor_vertices :=
                  hR_marg_sub_R_p _ (refactor_Walk.refactor_head_mem_vertices R_marg_seg)
                have h_x_in_p_tail : x ∈ p.refactor_vertices.tail :=
                  hR_p_sub _ h_x_in_R_p
                have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
                  refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
                rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
                · exact absurd h_S hvL_exit_notS
                · exact h_T
              · exact hR_marg_inter_T x hx_inner
        · -- Non-degenerate β ≠ γ.  Delegate to D.3.
          exact refactor_backward_marg_to_g_bif_dir_hinge_cInS_betaNeGamma_one_orientation
            S T hS ha_VST hb_VST ha_marg hb_marg
            ⟨hab_ne, ha_p_tail, hb_p_drop, i, hp_split⟩ hp_inter hc_S
            hL_p_dir hR_p_dir hL_p_pos hR_p_pos
            hL_p_sub hR_p_sub hL_p_drop_sub hR_p_drop_sub
            hL_W_dir hL_marg_dir hL_W_pos hvL_exit_notS hL_W_inter hL_p_vs_eq
            hR_W_dir hR_marg_dir hR_W_pos hvR_exit_notS hR_W_inter hR_p_vs_eq
            hvL_vR_exit_eq
      · -- c ∉ S.  c stays as the marg-bif source.
        have hc_in_G : c ∈ G :=
          refactor_Walk.refactor_source_in_G_of_directedWalk_pos L_p hL_p_dir hL_p_pos
        have hc_marg : c ∈ G.refactor_marginalize S hS := by
          change c ∈ G.J ∪ (G.V \ S)
          rcases Finset.mem_union.mp hc_in_G with hc_J | hc_V
          · exact Finset.mem_union_left _ hc_J
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hc_V, hc_S⟩)
        obtain ⟨L_marg, hL_marg_dir', hL_marg_pos', hL_marg_vs_sub, hL_marg_drop_sub,
                _, hL_marg_inter_T⟩ :=
          refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
            L_p hL_p_dir hL_p_pos hc_marg ha_marg hL_p_inter_ST
        obtain ⟨R_marg, hR_marg_dir', hR_marg_pos', hR_marg_vs_sub, hR_marg_drop_sub,
                _, hR_marg_inter_T⟩ :=
          refactor_project_walk_marg_full (S := S) (T := T) (hS := hS)
            R_p hR_p_dir hR_p_pos hc_marg hb_marg hR_p_inter_ST
        have ha_notin_L_marg : a ∉ L_marg.refactor_vertices.dropLast := fun h_in =>
          ha_notin_L_p_drop (hL_marg_drop_sub a h_in)
        have ha_notin_R_marg : a ∉ R_marg.refactor_vertices := fun h_in =>
          ha_notin_R_p (hR_marg_vs_sub a h_in)
        have hb_notin_L_marg : b ∉ L_marg.refactor_vertices := fun h_in =>
          hb_notin_L_p (hL_marg_vs_sub b h_in)
        have hb_notin_R_marg_drop : b ∉ R_marg.refactor_vertices.dropLast := fun h_in =>
          hb_notin_R_p_drop (hR_marg_drop_sub b h_in)
        refine ⟨refactor_Walk.refactor_mkBifurcation L_marg hL_marg_dir' hL_marg_pos' R_marg, ?_, ?_⟩
        · have h_src := refactor_Walk.refactor_mkBifurcation_isBifurcationSource
            L_marg hL_marg_dir' hL_marg_pos' R_marg hR_marg_dir' hR_marg_pos'
            hab_ne ha_notin_L_marg ha_notin_R_marg hb_notin_L_marg hb_notin_R_marg_drop
          exact refactor_Walk.refactor_isBifurcationSource_to_isBifurcation _ c h_src
        · intro x hx
          rw [refactor_vertices_tail_dropLast_mkBifurcation
                L_marg hL_marg_dir' hL_marg_pos' R_marg hR_marg_pos'] at hx
          rcases List.mem_append.mp hx with hx_L | hx_R
          · rw [List.mem_reverse] at hx_L
            exact hL_marg_inter_T x hx_L
          · have h_R_t_ne : R_marg.refactor_vertices.tail ≠ [] :=
              refactor_Walk.refactor_tail_vertices_ne_nil_of_pos R_marg hR_marg_pos'
            rw [refactor_Walk.refactor_vertices_eq_head_cons_tail R_marg,
                List.dropLast_cons_of_ne_nil h_R_t_ne] at hx_R
            rcases List.mem_cons.mp hx_R with rfl | hx_inner
            · have h_x_in_L_p : x ∈ L_p.refactor_vertices :=
                refactor_Walk.refactor_head_mem_vertices L_p
              have h_x_in_p_drop : x ∈ p.refactor_vertices.dropLast :=
                hL_p_sub _ h_x_in_L_p
              have h_x_in_R_p : x ∈ R_p.refactor_vertices :=
                refactor_Walk.refactor_head_mem_vertices R_p
              have h_x_in_p_tail : x ∈ p.refactor_vertices.tail :=
                hR_p_sub _ h_x_in_R_p
              have h_x_in_p_inter : x ∈ p.refactor_vertices.tail.dropLast :=
                refactor_mem_interior_of_arm_source ha_p_tail hp_pos h_x_in_p_tail h_x_in_p_drop
              rcases hp_inter_ST x h_x_in_p_inter with h_S | h_T
              · exact absurd h_S hc_S
              · exact h_T
            · exact hR_marg_inter_T x hx_inner
    · -- Bidirected hinge: delegate to D.2.
      exact refactor_backward_marg_to_g_bif_bidir_hinge_one_orientation S T hS
        ha_VST hb_VST ha_marg hb_marg p ⟨hab_ne, ha_p_tail, hb_p_drop, i, hp_split⟩
        hp_inter i hp_split h_dir
  -- Final assembly: 4 inner branches over the Or in MarginalizationΦL.
  constructor
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · obtain ⟨q, hq_bif, hq_inter⟩ :=
        forward_one_orientation hu hv hu_marg hv_marg p hp_bif hp_inter
      exact Or.inl ⟨q, hq_bif, hq_inter⟩
    · obtain ⟨q, hq_bif, hq_inter⟩ :=
        forward_one_orientation hv hu hv_marg hu_marg p hp_bif hp_inter
      exact Or.inr ⟨q, hq_bif, hq_inter⟩
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · obtain ⟨q, hq_bif, hq_inter⟩ :=
        backward_one_orientation hu hv hu_marg hv_marg p hp_bif hp_inter
      exact Or.inl ⟨q, hq_bif, hq_inter⟩
    · obtain ⟨q, hq_bif, hq_inter⟩ :=
        backward_one_orientation hv hu hv_marg hu_marg p hp_bif hp_inter
      exact Or.inr ⟨q, hq_bif, hq_inter⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: marg_PhiL_iff

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marg_L_field_eq (was: refactor_marg_L_field_eq)
-- ## L-field equality (parametric in `S, T`).
--
-- Refactor port: under `refactor_marginalize`, `marg.L` is built as
-- `(filter …).image (fun e => s(e.1, e.2))` rather than the original's
-- bare filter on ordered pairs.  The proof peels the outer
-- `Finset.image` layer via `congr 1` (the image function `fun e => s(e.1, e.2)`
-- is identical on both sides), reducing to filter equality on the inner
-- ordered-pair Finset, which the original's `Finset.filter_congr` step
-- handles unchanged (after the `sdiff_sdiff_left` rewrite that lines up the
-- product carriers).  The inner `Iff` step still closes via
-- `refactor_marg_PhiL_iff`.
private lemma refactor_marg_L_field_eq {G : refactor_CDMG Node} (S T : Finset Node)
    (hS : S ⊆ G.V) (hT : T ⊆ G.V) (hDisj : Disjoint S T) :
    ((G.refactor_marginalize S hS).refactor_marginalize T
        (refactor_subset_sdiff_of_disjoint hT hDisj.symm)).L
      = (G.refactor_marginalize (S ∪ T) (Finset.union_subset hS hT)).L := by
  change ((((G.V \ S) \ T) ×ˢ ((G.V \ S) \ T)).filter
            (fun e => e.1 ≠ e.2 ∧
              (G.refactor_marginalize S hS).refactor_MarginalizationΦL T e.1 e.2)).image
              (fun e => s(e.1, e.2))
        = (((G.V \ (S ∪ T)) ×ˢ (G.V \ (S ∪ T))).filter
            (fun e => e.1 ≠ e.2 ∧ G.refactor_MarginalizationΦL (S ∪ T) e.1 e.2)).image
              (fun e => s(e.1, e.2))
  have h_sd : (G.V \ S) \ T = G.V \ (S ∪ T) := sdiff_sdiff_left
  rw [h_sd]
  congr 1
  apply Finset.filter_congr
  intro e he
  rw [Finset.mem_product] at he
  refine and_congr Iff.rfl ?_
  exact refactor_marg_PhiL_iff S T hS hT hDisj he.1 he.2
-- REFACTOR-BLOCK-REPLACEMENT-END: marg_L_field_eq

-- ## Refactor replacements — Phase F (main theorem `marginalize_comm`).
--
-- Two structural shifts from the original:
--   1. `CDMG` → `refactor_CDMG`: the structure drops from 9 fields to 8
--      (no `hL_symm`, since `Sym2` makes bidirected-edge symmetry
--      definitional).  The local `cdmgExt` `have`-lemma's `rintro`
--      destructure shrinks to 8 anonymous slots accordingly.
--   2. `marginalize` → `refactor_marginalize`: under the refactor,
--      `.L : Finset (Sym2 Node)` rather than `Finset (Node × Node)`,
--      but `refactor_marg_L_field_eq` absorbs the extra
--      `Finset.image` layer internally, so the assembly at the
--      `marginalize_comm` level remains a verbatim
--      `refine ⟨?_, ?_⟩` + four field equalities per conjunct.
-- `subset_sdiff_of_disjoint` and `marg_{E,L}_field_eq` calls switch
-- to their `refactor_*` twins; all other plumbing
-- (`sdiff_sdiff_left`, `Finset.union_comm`,
-- `Finset.union_subset`) is pure-`Finset` and ports verbatim.
set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marginalize_comm (was: refactor_marginalize_comm)
-- claim_3_17 -- start statement
theorem refactor_marginalize_comm (G : refactor_CDMG Node) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    (G.refactor_marginalize W₁ hW₁).refactor_marginalize W₂
        (refactor_subset_sdiff_of_disjoint hW₂ hDisj.symm)
      = G.refactor_marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)
    ∧
    (G.refactor_marginalize W₂ hW₂).refactor_marginalize W₁
        (refactor_subset_sdiff_of_disjoint hW₁ hDisj)
      = G.refactor_marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)
-- claim_3_17 -- end statement
:= by
  -- ## refactor_CDMG extensionality (8-field destructure; no `hL_symm`).
  have cdmgExt : ∀ {G₁ G₂ : refactor_CDMG Node},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨J₁, V₁, _, E₁, _, L₁, _, _⟩
           ⟨J₂, V₂, _, E₂, _, L₂, _, _⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL; rfl
  -- ## L-field equality.
  have hL_field_eq : ∀ (S T : Finset Node) (hS : S ⊆ G.V) (hT : T ⊆ G.V)
      (hDisj_ST : Disjoint S T),
      ((G.refactor_marginalize S hS).refactor_marginalize T
          (refactor_subset_sdiff_of_disjoint hT hDisj_ST.symm)).L
        = (G.refactor_marginalize (S ∪ T) (Finset.union_subset hS hT)).L := by
    intro S T hS hT hDisj_ST
    exact refactor_marg_L_field_eq S T hS hT hDisj_ST
  refine ⟨?_, ?_⟩
  · refine cdmgExt rfl ?_ ?_ ?_
    · exact sdiff_sdiff_left
    · exact refactor_marg_E_field_eq W₁ W₂ hW₁ hW₂ hDisj
    · exact hL_field_eq W₁ W₂ hW₁ hW₂ hDisj
  · -- (b): apply the auxiliaries with the roles of W₁/W₂ swapped.
    have heq : G.refactor_marginalize (W₂ ∪ W₁) (Finset.union_subset hW₂ hW₁)
             = G.refactor_marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂) := by
      congr 1
      exact Finset.union_comm W₂ W₁
    refine cdmgExt rfl ?_ ?_ ?_
    · change (G.V \ W₂) \ W₁ = G.V \ (W₁ ∪ W₂)
      rw [Finset.union_comm W₁ W₂]
      exact sdiff_sdiff_left
    · have h := refactor_marg_E_field_eq W₂ W₁ hW₂ hW₁ hDisj.symm
      rw [heq] at h
      exact h
    · have h := hL_field_eq W₂ W₁ hW₂ hW₁ hDisj.symm
      rw [heq] at h
      exact h
-- REFACTOR-BLOCK-REPLACEMENT-END: marginalize_comm

end refactor_CDMG

end Causality
