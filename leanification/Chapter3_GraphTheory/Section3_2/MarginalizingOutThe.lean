import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGTypes
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard
import Chapter3_GraphTheory.Section3_2.MarginalizationAK
import Chapter3_GraphTheory.Section3_2.TwoDisjointNode

-- The proof body uses `show` extensively to make definitional rewrites
-- explicit at the reader's level (rather than `change`, which the style
-- linter prefers — but where every `show` here is followed by a tactic
-- consuming the surfaced goal, so `show` reads more naturally).  The
-- linter is silenced file-wide to keep the build noise-free; semantics
-- are unchanged.
set_option linter.style.show false

namespace Causality

/-!
# Marginalizing out the output part of splitted nodes equals hard intervention (`claim_3_19`)

This file formalises the LN lemma `claim_3_19`
(`\label{marginalizing-out-the-output-part-of-splitted-nodes-equals-hard-intervention}`
in `graphs.tex`): for any CDMG `G = (J, V, E, L)` and any subset
`W ⊆ V` of output nodes, the CDMG obtained by first node-splitting on
`W` (SWIG, `def_3_12` `nodeSplittingHard`) and then marginalising out
the output-side copies `W^o` (`def_3_14` `marginalize`) is the same
CDMG as the hard-intervention `G_{doit(W)}` (`def_3_10`
`hardInterventionOn`):
`G_{doit(W)} ≅ (G_{swig(W)})^{∖ W^o}, w ↦ w^i`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_19_statement_MarginalizingOutThe.tex`, verified equivalent
to the LN block.  `addition_to_the_LN` is empty for this row.  The
rewrite spells the LN's literal one-clause map "`w ↦ w^i`" out as the
full three-case bijection
`φ : G_{doit(W)} → (G_{swig(W)})^{∖ W^o}` that is the identity on
`J`, the identity on `V ∖ W`, and `w ↦ w^i` on `W` (per the LN-critic
working-phase subtlety `isomorphism_map_unspecified_outside_W`,
made explicit by the rewrite).

## Carrier-mismatch wrinkle (the load-bearing Lean-shape decision)

The LHS `G.hardInterventionOn W _` lives in `CDMG Node` (hard
intervention preserves the carrier).  The RHS
`(G.nodeSplittingHard hG W hW).marginalize (W.image .copy0) _` lives
in `CDMG (SplitNode Node)`: `nodeSplittingHard` (`def_3_12`) lifts
the carrier from `Node` to `SplitNode Node`, and `marginalize`
(`def_3_14`) preserves the (lifted) carrier.  `Node` and
`SplitNode Node` are not Lean-equal as types, so a literal `=`
between the two CDMGs is not type-correct.  The LN's "$\cong$" is
rendered via `claim_3_7`'s `eqViaNodeMap` predicate, with the
bijection function `toCopy1 W : Node → SplitNode Node`
(`def_3_11` `NodeSplittingOn`) realising the LN's three-case `φ`
literally:
* `toCopy1 W v = .unsplit v` for `v ∉ W` (i.e.\ `v ∈ J ∪ (V ∖ W)`),
  which is the LN's "identity on `J ∪ (V ∖ W)`" branch under the
  carrier-lift `Node ↪ SplitNode Node`;
* `toCopy1 W w = .copy1 w` for `w ∈ W`, which is the LN's
  "`w ↦ w^i`" branch under the SWIG-side reading
  `.copy1 ↔ ^i` (the input-copy convention fixed by `def_3_12`).

Same paradigm as `claim_3_15` (`AddingInterventionNodesSwig`) and
`claim_3_7` (`TwoDisjointNode`); the choice of operand order on
`eqViaNodeMap` follows the LN's explicitly-stated direction
`φ : LHS → RHS` (see the Design choice block on the theorem for the
contrast with `claim_3_15`, which has no LN-specified direction).

The body is filled in by `prove_claim_in_lean` (Manager B), following
the to-be-written tex proof at
`tex/claim_3_19_proof_MarginalizingOutThe.tex`.
-/

-- ## Post-refactor port (`cdmg_typed_edges`)
--
-- The block below is the refactor twin of this row's declarations
-- against the `cdmg_typed_edges` redesign of `def_3_1` / `def_3_4` —
-- same mathematical content, retyped against `CDMG`,
-- `SplitNode`, and the typed `WalkStep` / `Walk`
-- inductives.  J / V / E sub-goals of the main theorem port mechanically;
-- the L sub-goal is restructured around `Sym2.map` and `Sym2.mem_iff`.
namespace CDMG
open CDMG

-- claim_3_19 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_19 --- end helper

-- Refactor port of `subset_J_union_V_of_subset_V` — mechanical rename
-- pass; body identical.
-- claim_3_19 --- start helper
private lemma subset_J_union_V_of_subset_V
    {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.V) : W ⊆ G.J ∪ G.V
-- claim_3_19 --- end helper
:= fun _ hv => Finset.mem_union_right _ (hW hv)

-- Refactor port of `image_copy0_subset_nodeSplittingHard_V` —
-- mechanical rename pass; `nodeSplittingHard.V` unchanged in shape.
-- claim_3_19 --- start helper
private lemma image_copy0_subset_nodeSplittingHard_V
    {G : CDMG Node} {hG : G.IsCADMG}
    {W : Finset Node} {hW : W ⊆ G.V} :
    W.image SplitNode.copy0 ⊆ (G.nodeSplittingHard hG W hW).V
-- claim_3_19 --- end helper
:= by
  intro x hx
  change x ∈ (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
  exact Finset.mem_union_right _ hx

-- Refactor port of `swig_edge_source_notMem_W_copy0`.  The SWIG's E
-- field is unchanged in shape under the refactor (the refactor only
-- touches L), so this lemma carries over verbatim modulo the type
-- and helper renames.
private lemma swig_edge_source_notMem_W_copy0
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.V)
    {e : SplitNode Node × SplitNode Node}
    (he : e ∈ (G.nodeSplittingHard hG W hW).E) :
    e.1 ∉ W.image SplitNode.copy0 := by
  change e ∈ G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2)) at he
  obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he
  intro hContra
  obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
  unfold toCopy1 at hweq
  split_ifs at hweq

-- Refactor port of `swig_vertices_ne_nil`.  The 4-arg `.cons _ _ _ _`
-- pattern collapses to the 3-arg `.cons _ _ _` pattern (the typed
-- `WalkStep` replaces the original's stored ordered-pair +
-- WalkStep Prop pair).
private lemma swig_vertices_ne_nil
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.V) :
    ∀ {a b : SplitNode Node}
      (p : Walk (G.nodeSplittingHard hG W hW) a b),
      p.vertices ≠ []
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ => by simp [Walk.vertices]

-- Refactor port of `swig_middle_vertex_mem_tail_dropLast`.  Signature
-- shape change: drops the pair `c : Node × Node` and the WalkStep Prop
-- `h : WalkStep`, replaced by the typed `s : WalkStep`
-- (mirroring the `Walk.cons` 3-arg shape).
private lemma swig_middle_vertex_mem_tail_dropLast
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.V)
    {a b : SplitNode Node} (w : SplitNode Node)
    (s : WalkStep (G.nodeSplittingHard hG W hW) a w)
    {bMid : SplitNode Node}
    (s' : WalkStep (G.nodeSplittingHard hG W hW) w bMid)
    (r : Walk (G.nodeSplittingHard hG W hW) bMid b) :
    w ∈ (Walk.cons w s
              (Walk.cons bMid s' r)).vertices.tail.dropLast := by
  have hr_ne : r.vertices ≠ [] := swig_vertices_ne_nil hG hW r
  change w ∈ (a :: w :: r.vertices).tail.dropLast
  rw [List.tail_cons]
  rw [List.dropLast_cons_of_ne_nil hr_ne]
  exact List.mem_cons.mpr (Or.inl rfl)

-- Refactor port of `swig_marginalization_phi_E_W_copy0_iff`.  The
-- `Walk.IsDirectedWalk` Prop-level conjunction collapses to a
-- constructor case-split on `WalkStep`: only `.forwardE`
-- survives in directed walks; `.backwardE` / `.bidir` reduce to
-- `False`.  Length-1 construction in the reverse direction uses
-- `Walk.cons _ (.forwardE _) (Walk.nil _ _)`.
private lemma swig_marginalization_phi_E_W_copy0_iff
    (G : CDMG Node) (hG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V)
    (u v : SplitNode Node) :
    (G.nodeSplittingHard hG W hW).MarginalizationΦE
        (W.image SplitNode.copy0) u v
      ↔ (u, v) ∈ (G.nodeSplittingHard hG W hW).E := by
  constructor
  · rintro ⟨p, hp_dir, hp_len, hp_inter⟩
    cases p with
    | nil v' hv' =>
      simp [Walk.length] at hp_len
    | cons mid s q =>
      cases s with
      | backwardE _ =>
        simp only [Walk.IsDirectedWalk] at hp_dir
      | bidir _ =>
        simp only [Walk.IsDirectedWalk] at hp_dir
      | forwardE h_edge =>
        cases q with
        | nil v' hv' =>
          exact h_edge
        | cons w' s' r =>
          cases s' with
          | backwardE _ =>
            simp only [Walk.IsDirectedWalk] at hp_dir
          | bidir _ =>
            simp only [Walk.IsDirectedWalk] at hp_dir
          | forwardE h_edge' =>
            have h_w_mem : mid ∈ W.image SplitNode.copy0 :=
              hp_inter mid
                (swig_middle_vertex_mem_tail_dropLast hG hW mid
                  (.forwardE h_edge) (.forwardE h_edge') r)
            exact (swig_edge_source_notMem_W_copy0 hG hW h_edge' h_w_mem).elim
  · intro h_edge
    have hv_in : v ∈ G.nodeSplittingHard hG W hW := by
      show v ∈ (G.nodeSplittingHard hG W hW).J
              ∪ (G.nodeSplittingHard hG W hW).V
      refine Finset.mem_union_right _ ?_
      exact ((G.nodeSplittingHard hG W hW).hE_subset h_edge).2
    refine ⟨Walk.cons v (.forwardE h_edge) (Walk.nil v hv_in),
      ?_, ?_, ?_⟩
    · trivial
    · show 0 + 1 ≥ 1; omega
    · intro x hx
      simp [Walk.vertices, List.tail] at hx

-- Refactor port of `swig_bif_with_split_cons_form` — pattern-match
-- structure shifts from 4-arg cons to 3-arg cons; existential drops
-- the ordered-pair / Prop pair, replaced by the typed `s`.
private lemma swig_bif_with_split_cons_form
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.V) :
    ∀ {a b : SplitNode Node}
      (q : Walk (G.nodeSplittingHard hG W hW) a b) (i : ℕ),
      q.IsBifurcationWithSplit i →
      ∃ (mid : SplitNode Node)
        (s : WalkStep (G.nodeSplittingHard hG W hW) a mid)
        (r : Walk (G.nodeSplittingHard hG W hW) mid b),
        q = Walk.cons mid s r
  | _, _, .nil _ _, _, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
  | _, _, .cons mid s r, _, _ => ⟨mid, s, r, rfl⟩

-- Refactor port of `swig_marginalization_phi_L_W_copy0_iff`.  The
-- bifurcation-walk Prop-level disjunction collapses to a constructor
-- case-split on `WalkStep`; the `hL_symm` invocation in the
-- reverse direction's "other-orientation" branch is replaced by
-- `Sym2.eq_swap` (`s(v, u) = s(u, v)` definitionally on `Sym2`).
-- The conclusion changes from `(u, v) ∈ swig.L` (ordered-pair) to
-- `s(u, v) ∈ swig.L` (`Sym2`-quotient).
private lemma swig_marginalization_phi_L_W_copy0_iff
    (G : CDMG Node) (hG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V)
    (u v : SplitNode Node) :
    (G.nodeSplittingHard hG W hW).MarginalizationΦL
        (W.image SplitNode.copy0) u v
      ↔ s(u, v) ∈ (G.nodeSplittingHard hG W hW).L := by
  have bifSplitAux :
      ∀ {a b : SplitNode Node} (i : ℕ)
        (p : Walk (G.nodeSplittingHard hG W hW) a b),
        p.IsBifurcationWithSplit i →
        (∀ x ∈ p.vertices.tail.dropLast, x ∈ W.image SplitNode.copy0) →
        s(a, b) ∈ (G.nodeSplittingHard hG W hW).L := by
    intro a b i
    induction i generalizing a b with
    | zero =>
      intro p hSpl hInter
      cases p with
      | nil v' hv' =>
        simp only [Walk.IsBifurcationWithSplit] at hSpl
      | cons mid s q =>
        cases q with
        | nil v' hv' =>
          cases s with
          | forwardE _ =>
            simp only [Walk.IsBifurcationWithSplit] at hSpl
          | backwardE _ =>
            simp only [Walk.IsBifurcationWithSplit] at hSpl
          | bidir h_L =>
            exact h_L
        | cons w' s' r =>
          cases s with
          | forwardE _ =>
            simp only [Walk.IsBifurcationWithSplit] at hSpl
          | backwardE h_first =>
            cases s' with
            | backwardE _ =>
              simp only [Walk.IsBifurcationWithSplit,
                Walk.IsDirectedWalk] at hSpl
            | bidir _ =>
              simp only [Walk.IsBifurcationWithSplit,
                Walk.IsDirectedWalk] at hSpl
            | forwardE h_edge' =>
              have h_w_mem : mid ∈ W.image SplitNode.copy0 :=
                hInter mid
                  (swig_middle_vertex_mem_tail_dropLast hG hW mid
                    (.backwardE h_first) (.forwardE h_edge') r)
              exact (swig_edge_source_notMem_W_copy0 hG hW h_edge' h_w_mem).elim
          | bidir h_first =>
            cases s' with
            | backwardE _ =>
              simp only [Walk.IsBifurcationWithSplit,
                Walk.IsDirectedWalk] at hSpl
            | bidir _ =>
              simp only [Walk.IsBifurcationWithSplit,
                Walk.IsDirectedWalk] at hSpl
            | forwardE h_edge' =>
              have h_w_mem : mid ∈ W.image SplitNode.copy0 :=
                hInter mid
                  (swig_middle_vertex_mem_tail_dropLast hG hW mid
                    (.bidir h_first) (.forwardE h_edge') r)
              exact (swig_edge_source_notMem_W_copy0 hG hW h_edge' h_w_mem).elim
    | succ k ih =>
      intro p hSpl hInter
      cases p with
      | nil v' hv' =>
        simp only [Walk.IsBifurcationWithSplit] at hSpl
      | cons mid s q =>
        cases s with
        | forwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
        | bidir _ =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
        | backwardE h_edge =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
          obtain ⟨wMid, s', r, hq_eq⟩ :=
            swig_bif_with_split_cons_form hG hW q k hSpl
          have h_w_mem : mid ∈ W.image SplitNode.copy0 := by
            apply hInter
            rw [hq_eq]
            exact swig_middle_vertex_mem_tail_dropLast hG hW mid
              (.backwardE h_edge) s' r
          exact (swig_edge_source_notMem_W_copy0 hG hW h_edge h_w_mem).elim
  constructor
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · obtain ⟨_, _, _, i, hi⟩ := hp_bif
      exact bifSplitAux i p hi hp_inter
    · obtain ⟨_, _, _, i, hi⟩ := hp_bif
      have h := bifSplitAux i p hi hp_inter
      rwa [show (s(u, v) : Sym2 (SplitNode Node)) = s(v, u) from Sym2.eq_swap]
  · intro h_edge
    have hv_in : v ∈ G.nodeSplittingHard hG W hW := by
      show v ∈ (G.nodeSplittingHard hG W hW).J
              ∪ (G.nodeSplittingHard hG W hW).V
      refine Finset.mem_union_right _ ?_
      exact (G.nodeSplittingHard hG W hW).hL_subset h_edge (Sym2.mem_mk_right u v)
    have hu_ne_v : u ≠ v := fun h_eq =>
      (G.nodeSplittingHard hG W hW).hL_irrefl h_edge
        (Sym2.mk_isDiag_iff.mpr h_eq)
    refine Or.inl ⟨Walk.cons v (.bidir h_edge) (Walk.nil v hv_in),
      ?_, ?_⟩
    · refine ⟨hu_ne_v, ?_, ?_, 0, ?_⟩
      · intro h_mem
        exact hu_ne_v (List.mem_singleton.mp h_mem)
      · intro h_mem
        exact hu_ne_v (List.mem_singleton.mp h_mem).symm
      · trivial
    · intro x hx
      exact (List.not_mem_nil hx).elim

-- Refactor port of `marginalize_swig_eq_doit`.  J / V / E sub-goals
-- port mechanically (the refactor leaves these fields untouched);
-- the L sub-goal is restructured around `Sym2.map` and `Sym2.ind`.
set_option maxHeartbeats 800000 in
-- claim_3_19 -- start statement
theorem marginalize_swig_eq_doit (G : CDMG Node)
    (hG : G.IsCADMG) (W : Finset Node) (hW : W ⊆ G.V) :
    eqViaNodeMap
        (G.hardInterventionOn W (subset_J_union_V_of_subset_V hW))
        ((G.nodeSplittingHard hG W hW).marginalize
            (W.image SplitNode.copy0)
            image_copy0_subset_nodeSplittingHard_V)
        (toCopy1 W)
-- claim_3_19 -- end statement
:= by
  refine ⟨?_, ?_, ?_, ?_⟩
  -- ===== Clause (a): J equality =====
  · change (G.J ∪ W).image (toCopy1 W)
        = G.J.image SplitNode.unsplit ∪ W.image SplitNode.copy1
    rw [Finset.image_union]
    have hGJ : G.J.image (toCopy1 W) = G.J.image SplitNode.unsplit := by
      refine Finset.image_congr ?_
      intro j hj
      have hjJ : j ∈ G.J := Finset.mem_coe.mp hj
      have hj_notW : j ∉ W := by
        intro hjW
        exact Finset.disjoint_left.mp G.hJV_disj hjJ (hW hjW)
      show toCopy1 W j = SplitNode.unsplit j
      unfold toCopy1
      rw [if_neg hj_notW]
    have hW1 : W.image (toCopy1 W) = W.image SplitNode.copy1 := by
      refine Finset.image_congr ?_
      intro w hw
      have hwW : w ∈ W := Finset.mem_coe.mp hw
      show toCopy1 W w = SplitNode.copy1 w
      unfold toCopy1
      rw [if_pos hwW]
    rw [hGJ, hW1]
  -- ===== Clause (b): V equality =====
  · change (G.V \ W).image (toCopy1 W)
        = ((G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0)
            \ (W.image SplitNode.copy0)
    have hLHS : (G.V \ W).image (toCopy1 W)
                  = (G.V \ W).image SplitNode.unsplit := by
      refine Finset.image_congr ?_
      intro v hv
      have hvSdiff : v ∈ G.V \ W := Finset.mem_coe.mp hv
      have hv_notW : v ∉ W := (Finset.mem_sdiff.mp hvSdiff).2
      show toCopy1 W v = SplitNode.unsplit v
      unfold toCopy1
      rw [if_neg hv_notW]
    rw [hLHS]
    apply Finset.ext
    intro x
    constructor
    · intro hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hx, ?_⟩
      intro hx_inW
      obtain ⟨v, _, hveq⟩ := Finset.mem_image.mp hx
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hx_inW
      rw [← hveq] at hweq
      cases hweq
    · intro hx
      obtain ⟨hx_union, hx_notC0⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp hx_union with hxA | hxB
      · exact hxA
      · exact absurd hxB hx_notC0
  -- ===== Clause (c): E directed-edge equality =====
  · change (G.E.filter (fun e => e.2 ∉ W)).image
            (Prod.map (toCopy1 W) (toCopy1 W))
        = (((G.nodeSplittingHard hG W hW).J
              ∪ ((G.nodeSplittingHard hG W hW).V \
                  (W.image SplitNode.copy0)))
              ×ˢ
              ((G.nodeSplittingHard hG W hW).V \
                (W.image SplitNode.copy0))).filter
            (fun e =>
              (G.nodeSplittingHard hG W hW).MarginalizationΦE
                (W.image SplitNode.copy0) e.1 e.2)
    have hC0eqC1 : ∀ {x : Node}, x ∉ W → toCopy0 W x = toCopy1 W x := by
      intro x hx
      unfold toCopy0 toCopy1
      rw [if_neg hx, if_neg hx]
    apply Finset.ext
    intro pair
    constructor
    · intro hpair
      obtain ⟨e, he, hPM⟩ := Finset.mem_image.mp hpair
      obtain ⟨he_E, he_notW⟩ := Finset.mem_filter.mp he
      obtain ⟨he1_in, he2_V⟩ := G.hE_subset he_E
      have hPM_eq : pair = (toCopy1 W e.1, toCopy1 W e.2) := by
        rw [← hPM]; rfl
      have h_swig_E : pair ∈ (G.nodeSplittingHard hG W hW).E := by
        change pair ∈ G.E.image
          (fun e => (toCopy1 W e.1, toCopy0 W e.2))
        refine Finset.mem_image.mpr ⟨e, he_E, ?_⟩
        rw [hPM_eq]
        rw [hC0eqC1 he_notW]
      have hSub := (G.nodeSplittingHard hG W hW).hE_subset h_swig_E
      have hpair1_notC0 : pair.1 ∉ W.image SplitNode.copy0 :=
        swig_edge_source_notMem_W_copy0 hG hW h_swig_E
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · rcases Finset.mem_union.mp hSub.1 with hJ | hV
          · exact Finset.mem_union_left _ hJ
          · exact Finset.mem_union_right _
              (Finset.mem_sdiff.mpr ⟨hV, hpair1_notC0⟩)
        · refine Finset.mem_sdiff.mpr ⟨hSub.2, ?_⟩
          rw [hPM_eq]
          show toCopy1 W e.2 ∉ W.image SplitNode.copy0
          unfold toCopy1
          rw [if_neg he_notW]
          intro hContra
          obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
          cases hweq
      · exact (swig_marginalization_phi_E_W_copy0_iff
          G hG W hW _ _).mpr h_swig_E
    · intro hpair
      obtain ⟨hProd, hPhi⟩ := Finset.mem_filter.mp hpair
      have h_swig_E : pair ∈ (G.nodeSplittingHard hG W hW).E :=
        (swig_marginalization_phi_E_W_copy0_iff G hG W hW _ _).mp hPhi
      change pair ∈ G.E.image
        (fun e => (toCopy1 W e.1, toCopy0 W e.2)) at h_swig_E
      obtain ⟨e, he_E, hpair_eq⟩ := Finset.mem_image.mp h_swig_E
      obtain ⟨_, hv⟩ := Finset.mem_product.mp hProd
      obtain ⟨_, hv_notC0⟩ := Finset.mem_sdiff.mp hv
      have he2_notW : e.2 ∉ W := by
        intro he2W
        apply hv_notC0
        have h2 : pair.2 = toCopy0 W e.2 := by rw [← hpair_eq]
        rw [h2]
        show toCopy0 W e.2 ∈ W.image SplitNode.copy0
        unfold toCopy0
        rw [if_pos he2W]
        exact Finset.mem_image.mpr ⟨e.2, he2W, rfl⟩
      refine Finset.mem_image.mpr ⟨e, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨he_E, he2_notW⟩
      · show Prod.map (toCopy1 W) (toCopy1 W) e = pair
        rw [← hpair_eq]
        show (toCopy1 W e.1, toCopy1 W e.2)
              = (toCopy1 W e.1, toCopy0 W e.2)
        rw [hC0eqC1 he2_notW]
  -- ===== Clause (d): L bidirected-edge equality =====
  · change (G.L.filter (fun s => ∀ v ∈ s, v ∉ W)).image
            (Sym2.map (toCopy1 W))
        = ((((G.nodeSplittingHard hG W hW).V \
                (W.image SplitNode.copy0))
              ×ˢ
              ((G.nodeSplittingHard hG W hW).V \
                (W.image SplitNode.copy0))).filter
            (fun e => e.1 ≠ e.2
              ∧ (G.nodeSplittingHard hG W hW).MarginalizationΦL
                  (W.image SplitNode.copy0) e.1 e.2)).image
            (fun e => s(e.1, e.2))
    have hToCopy1_unsplit : ∀ {x : Node}, x ∉ W →
        toCopy1 W x = SplitNode.unsplit x := by
      intro x hx
      unfold toCopy1
      rw [if_neg hx]
    have hToCopy0_unsplit : ∀ {x : Node}, x ∉ W →
        toCopy0 W x = SplitNode.unsplit x := by
      intro x hx
      unfold toCopy0
      rw [if_neg hx]
    apply Finset.ext
    refine Sym2.ind (fun a b => ?_)
    constructor
    · -- Forward (⇒): s(a, b) ∈ image of G.L.filter → s(a, b) ∈ image of (... filter ...)
      intro hLHS
      obtain ⟨s_src, hs_src_filter, hs_src_map⟩ := Finset.mem_image.mp hLHS
      obtain ⟨hs_src_L, hs_src_notW⟩ := Finset.mem_filter.mp hs_src_filter
      induction s_src using Sym2.ind with | _ a₀ b₀ =>
      -- hs_src_map : Sym2.map (toCopy1 W) s(a₀, b₀) = s(a, b)
      have ha₀_notW : a₀ ∉ W := hs_src_notW a₀ (Sym2.mem_mk_left _ _)
      have hb₀_notW : b₀ ∉ W := hs_src_notW b₀ (Sym2.mem_mk_right _ _)
      have ha₀_V : a₀ ∈ G.V := G.hL_subset hs_src_L (Sym2.mem_mk_left _ _)
      have hb₀_V : b₀ ∈ G.V := G.hL_subset hs_src_L (Sym2.mem_mk_right _ _)
      have hab₀_ne : a₀ ≠ b₀ := fun h_eq =>
        G.hL_irrefl hs_src_L (Sym2.mk_isDiag_iff.mpr h_eq)
      -- Build swig.L membership of s(.unsplit a₀, .unsplit b₀)
      have h_swig_L : s(SplitNode.unsplit a₀, SplitNode.unsplit b₀)
                        ∈ (G.nodeSplittingHard hG W hW).L := by
        change s(SplitNode.unsplit a₀, SplitNode.unsplit b₀)
                ∈ G.L.image (Sym2.map (toCopy0 W))
        refine Finset.mem_image.mpr ⟨s(a₀, b₀), hs_src_L, ?_⟩
        show Sym2.map (toCopy0 W) s(a₀, b₀)
              = s(SplitNode.unsplit a₀, SplitNode.unsplit b₀)
        rw [Sym2.map_mk, hToCopy0_unsplit ha₀_notW, hToCopy0_unsplit hb₀_notW]
      -- Use witness pair (toCopy1 W a₀, toCopy1 W b₀)
      refine Finset.mem_image.mpr
        ⟨(toCopy1 W a₀, toCopy1 W b₀), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨?_, ?_⟩
          · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · show toCopy1 W a₀ ∈ (G.nodeSplittingHard hG W hW).V
              change toCopy1 W a₀ ∈
                (G.V \ W).image SplitNode.unsplit
                  ∪ W.image SplitNode.copy0
              rw [hToCopy1_unsplit ha₀_notW]
              refine Finset.mem_union_left _ ?_
              exact Finset.mem_image.mpr
                ⟨a₀, Finset.mem_sdiff.mpr ⟨ha₀_V, ha₀_notW⟩, rfl⟩
            · rw [hToCopy1_unsplit ha₀_notW]
              intro hContra
              obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
              cases hweq
          · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · change toCopy1 W b₀ ∈
                (G.V \ W).image SplitNode.unsplit
                  ∪ W.image SplitNode.copy0
              rw [hToCopy1_unsplit hb₀_notW]
              refine Finset.mem_union_left _ ?_
              exact Finset.mem_image.mpr
                ⟨b₀, Finset.mem_sdiff.mpr ⟨hb₀_V, hb₀_notW⟩, rfl⟩
            · rw [hToCopy1_unsplit hb₀_notW]
              intro hContra
              obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
              cases hweq
        · show toCopy1 W a₀ ≠ toCopy1 W b₀
          rw [hToCopy1_unsplit ha₀_notW, hToCopy1_unsplit hb₀_notW]
          intro h_eq
          injection h_eq with h_inj
          exact hab₀_ne h_inj
        · -- Φ_L: use the iff helper
          refine (swig_marginalization_phi_L_W_copy0_iff
            G hG W hW _ _).mpr ?_
          show s(toCopy1 W a₀, toCopy1 W b₀)
                ∈ (G.nodeSplittingHard hG W hW).L
          rw [hToCopy1_unsplit ha₀_notW, hToCopy1_unsplit hb₀_notW]
          exact h_swig_L
      · -- s(toCopy1 W a₀, toCopy1 W b₀) = s(a, b)
        show s(toCopy1 W a₀, toCopy1 W b₀) = s(a, b)
        rw [← Sym2.map_mk]
        exact hs_src_map
    · -- Reverse (⇐)
      intro hRHS
      obtain ⟨pair, hpair_filter, hpair_eq⟩ := Finset.mem_image.mp hRHS
      obtain ⟨hpair_prod, hpair_ne, hPhi⟩ := Finset.mem_filter.mp hpair_filter
      have h_swig_L : s(pair.1, pair.2) ∈ (G.nodeSplittingHard hG W hW).L :=
        (swig_marginalization_phi_L_W_copy0_iff G hG W hW _ _).mp hPhi
      change s(pair.1, pair.2)
        ∈ G.L.image (Sym2.map (toCopy0 W)) at h_swig_L
      obtain ⟨s₀, hs₀_L, hs₀_map⟩ := Finset.mem_image.mp h_swig_L
      induction s₀ using Sym2.ind with | _ a₀ b₀ =>
      -- hs₀_map : Sym2.map (toCopy0 W) s(a₀, b₀) = s(pair.1, pair.2)
      have hpair1_notC0 : pair.1 ∉ W.image SplitNode.copy0 :=
        (Finset.mem_sdiff.mp (Finset.mem_product.mp hpair_prod).1).2
      have hpair2_notC0 : pair.2 ∉ W.image SplitNode.copy0 :=
        (Finset.mem_sdiff.mp (Finset.mem_product.mp hpair_prod).2).2
      -- Derive a₀ ∉ W using the contradiction approach
      have ha₀_notW : a₀ ∉ W := by
        intro ha₀W
        have h_tc0_eq : toCopy0 W a₀ = SplitNode.copy0 a₀ := by
          unfold toCopy0; rw [if_pos ha₀W]
        have h_mem : toCopy0 W a₀ ∈ s(pair.1, pair.2) := by
          rw [← hs₀_map, Sym2.map_mk]
          exact Sym2.mem_mk_left _ _
        rcases Sym2.mem_iff.mp h_mem with h_eq | h_eq
        · apply hpair1_notC0
          rw [← h_eq, h_tc0_eq]
          exact Finset.mem_image.mpr ⟨a₀, ha₀W, rfl⟩
        · apply hpair2_notC0
          rw [← h_eq, h_tc0_eq]
          exact Finset.mem_image.mpr ⟨a₀, ha₀W, rfl⟩
      have hb₀_notW : b₀ ∉ W := by
        intro hb₀W
        have h_tc0_eq : toCopy0 W b₀ = SplitNode.copy0 b₀ := by
          unfold toCopy0; rw [if_pos hb₀W]
        have h_mem : toCopy0 W b₀ ∈ s(pair.1, pair.2) := by
          rw [← hs₀_map, Sym2.map_mk]
          exact Sym2.mem_mk_right _ _
        rcases Sym2.mem_iff.mp h_mem with h_eq | h_eq
        · apply hpair1_notC0
          rw [← h_eq, h_tc0_eq]
          exact Finset.mem_image.mpr ⟨b₀, hb₀W, rfl⟩
        · apply hpair2_notC0
          rw [← h_eq, h_tc0_eq]
          exact Finset.mem_image.mpr ⟨b₀, hb₀W, rfl⟩
      -- Use s(a₀, b₀) as witness in G.L.filter
      refine Finset.mem_image.mpr ⟨s(a₀, b₀), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨hs₀_L, ?_⟩
        intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact ha₀_notW
        · exact hb₀_notW
      · -- Sym2.map (toCopy1 W) s(a₀, b₀) = s(a, b)
        show Sym2.map (toCopy1 W) s(a₀, b₀) = s(a, b)
        rw [Sym2.map_mk, hToCopy1_unsplit ha₀_notW, hToCopy1_unsplit hb₀_notW]
        -- Goal: s(.unsplit a₀, .unsplit b₀) = s(a, b)
        -- From hs₀_map: s(toCopy0 W a₀, toCopy0 W b₀) = s(pair.1, pair.2)
        -- After rewriting hToCopy0: s(.unsplit a₀, .unsplit b₀) = s(pair.1, pair.2)
        -- From hpair_eq: s(pair.1, pair.2) = s(a, b)
        rw [show (s(SplitNode.unsplit a₀, SplitNode.unsplit b₀) : Sym2 _)
                = s(pair.1, pair.2) by
              rw [← hToCopy0_unsplit ha₀_notW, ← hToCopy0_unsplit hb₀_notW,
                  ← Sym2.map_mk]
              exact hs₀_map]
        exact hpair_eq

end CDMG

end Causality
