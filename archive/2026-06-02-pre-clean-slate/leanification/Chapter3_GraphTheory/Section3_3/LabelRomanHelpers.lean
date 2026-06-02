import Chapter3_GraphTheory.Section3_3.WalkPrefixSuffix
import Chapter3_GraphTheory.Section3_3.SigmaBlockedReversal

/-!
# Helpers for `claim_3_27` (`lem:replace_walk`)

This file collects the structural lemmas used by the proof of
`Walk.replace_walk` in `LabelRoman.lean`. They were planned as
L1 -- L7 in `workspace_claim_3_27.md` §2.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

/-! ### L1 -- `IsDirected` is preserved by `append` / `prefix` / `suffix` -/

/-- `IsDirected` of an appended walk splits into directedness of each part. -/
theorem isDirected_split_append :
    ∀ {u v w : α} (p₁ : Walk G u v) (p₂ : Walk G v w),
      (p₁.append p₂).IsDirected → p₁.IsDirected ∧ p₂.IsDirected := by
  intro u v w p₁
  induction p₁ with
  | nil _ =>
    intro p₂ h
    rw [Walk.nil_append] at h
    exact ⟨by trivial, h⟩
  | @cons _ _ _ s p ih =>
    intro p₂ h
    rw [Walk.cons_append] at h
    cases s with
    | forward _ =>
      simp only [Walk.isDirected_cons_forward] at h
      obtain ⟨h1, h2⟩ := ih p₂ h
      exact ⟨by simp only [Walk.isDirected_cons_forward]; exact h1, h2⟩
    | backward _ => simp at h
    | bidir _ => simp at h

/-- Appending two directed walks gives a directed walk. -/
theorem isDirected_append :
    ∀ {u v w : α} (p₁ : Walk G u v) (p₂ : Walk G v w),
      p₁.IsDirected → p₂.IsDirected → (p₁.append p₂).IsDirected := by
  intro u v w p₁
  induction p₁ with
  | nil _ => intro p₂ _ h₂; simpa using h₂
  | @cons _ _ _ s p ih =>
    intro p₂ h_dir h₂
    cases s with
    | forward _ =>
      simp only [Walk.cons_append, Walk.isDirected_cons_forward] at h_dir ⊢
      exact ih p₂ h_dir h₂
    | backward _ => simp at h_dir
    | bidir _ => simp at h_dir

/-- `IsDirected` projects onto the prefix. -/
theorem isDirected_prefix :
    ∀ {u v : α} (π : Walk G u v) (i : ℕ),
      π.IsDirected → (π.prefix i).IsDirected := by
  intro u v π
  induction π with
  | nil _ => intro i _; rw [Walk.prefix_nil]; trivial
  | @cons _ _ _ s p ih =>
    intro i hdir
    cases i with
    | zero => rw [Walk.prefix_cons_zero]; trivial
    | succ i =>
      cases s with
      | forward _ =>
        simp only [Walk.prefix_cons_succ, Walk.isDirected_cons_forward] at hdir ⊢
        exact ih i hdir
      | backward _ => simp at hdir
      | bidir _    => simp at hdir

/-- `IsDirected` projects onto the suffix. -/
theorem isDirected_suffix :
    ∀ {u v : α} (π : Walk G u v) (j : ℕ),
      π.IsDirected → (π.suffix j).IsDirected := by
  intro u v π
  induction π with
  | nil _ => intro j _; rw [Walk.suffix_nil]; trivial
  | @cons _ _ _ s p ih =>
    intro j hdir
    cases j with
    | zero => simpa using hdir
    | succ j =>
      cases s with
      | forward _ =>
        simp only [Walk.isDirected_cons_forward] at hdir
        change (p.suffix j).IsDirected
        exact ih j hdir
      | backward _ => simp at hdir
      | bidir _    => simp at hdir

/-! ### L3 -- directed walks have no collider positions -/

/-- A directed walk has no collider at any position. -/
theorem not_isColliderAt_of_isDirected :
    ∀ {u v : α} (π : Walk G u v) (k : ℕ),
      π.IsDirected → ¬ π.IsColliderAt k := by
  intro u v π
  induction π with
  | nil _ => intro k _ h; simp at h
  | @cons _ _ _ s p ih =>
    intro k hdir h
    cases p with
    | nil _ => simp at h
    | @cons _ _ _ s' p' =>
      cases k with
      | zero => simp at h
      | succ k =>
        cases k with
        | zero =>
          -- collider at 1
          rw [Walk.isColliderAt_cons_cons_one] at h
          -- Need to derive contradiction. s, s' must both contribute arrowheads at the joint.
          cases s with
          | forward _ =>
            -- s.HasArrowheadAtTarget = True (forward). So need s'.HasArrowheadAtSource = False.
            -- From hdir on cons (forward _) (cons s' _), s' is also forward.
            simp only [Walk.isDirected_cons_forward] at hdir
            cases s' with
            | forward _ => simp at h
            | backward _ => simp at hdir
            | bidir _ => simp at hdir
          | backward _ => simp at hdir
          | bidir _ => simp at hdir
        | succ k =>
          -- collider at k+2 on cons s (cons s' p') ↔ collider at k+1 on cons s' p'
          simp only [Walk.isColliderAt_cons_cons_succ_succ] at h
          have hdir' : (Walk.cons s' p').IsDirected := by
            cases s with
            | forward _ => simpa [Walk.isDirected_cons_forward] using hdir
            | backward _ => simp at hdir
            | bidir _ => simp at hdir
          exact ih (k + 1) hdir' h

end Walk

namespace WalkStep

variable {G : CDMG α}

/-! ### Vertices on a single step lie in `G` -/

/-- The source vertex of any walk step lies in the ambient graph. -/
theorem source_mem_G {a b : α} (s : WalkStep G a b) : a ∈ G := by
  cases s with
  | forward h =>
    -- (a, b) ∈ G.E ⊆ (J ∪ V) × V
    have := G.E_subset h
    simp only [Set.mem_prod] at this
    exact CDMG.mem_iff.mpr this.1
  | backward h =>
    -- backward: (b, a) ∈ G.E
    have := G.E_subset h
    simp only [Set.mem_prod] at this
    -- this.2 : a ∈ V
    exact CDMG.mem_iff.mpr (Or.inr this.2)
  | bidir h =>
    have := G.L_subset h
    simp only [Set.mem_prod] at this
    exact CDMG.mem_iff.mpr (Or.inr this.1)

/-- The target vertex of any walk step lies in the ambient graph. -/
theorem target_mem_G {a b : α} (s : WalkStep G a b) : b ∈ G := by
  cases s with
  | forward h =>
    have := G.E_subset h
    simp only [Set.mem_prod] at this
    exact CDMG.mem_iff.mpr (Or.inr this.2)
  | backward h =>
    have := G.E_subset h
    simp only [Set.mem_prod] at this
    exact CDMG.mem_iff.mpr this.1
  | bidir h =>
    have := G.L_subset h
    simp only [Set.mem_prod] at this
    exact CDMG.mem_iff.mpr (Or.inr this.2)

end WalkStep

namespace Walk

variable {G : CDMG α}

/-! ### Vertices on a walk lie in `G` (positions `> 0`) -/

/-- On a non-trivial walk `π`, both endpoints lie in `G`. -/
theorem endpoints_mem_G_of_pos :
    ∀ {u v : α} (π : Walk G u v), 1 ≤ π.length → u ∈ G ∧ v ∈ G := by
  intro u v π
  induction π with
  | nil _ => intro h; simp at h
  | @cons _ _ _ s p ih =>
    intro _
    refine ⟨s.source_mem_G, ?_⟩
    cases p with
    | nil _ => exact s.target_mem_G
    | @cons _ _ _ s'' p' =>
      have : 1 ≤ (Walk.cons s'' p').length := by simp [Walk.length_cons]
      exact (ih this).2

/-- Every position strictly inside a walk lies in `G`. -/
theorem nodeAt_mem_G_of_lt_length :
    ∀ {u v : α} (π : Walk G u v) {k : ℕ},
      k < π.length → π.nodeAt k ∈ G := by
  intro u v π
  induction π with
  | nil _ => intro k h; simp at h
  | @cons _ _ _ s p ih =>
    intro k hk
    -- nodeAt at position k on cons s p; cases on k.
    cases k with
    | zero =>
      -- nodeAt 0 = source = a (where s : WalkStep G a _)
      exact s.source_mem_G
    | succ k =>
      -- nodeAt (k+1) = p.nodeAt k
      simp only [Walk.nodeAt_cons_succ]
      simp only [Walk.length_cons, Nat.add_lt_add_iff_right] at hk
      exact ih hk

/-- Every position `0 < k ≤ π.length` on a walk lies in `G`. -/
theorem nodeAt_mem_G_of_pos_le_length :
    ∀ {u v : α} (π : Walk G u v) {k : ℕ},
      0 < k → k ≤ π.length → π.nodeAt k ∈ G := by
  intro u v π k hk hk_le
  rcases Nat.lt_or_eq_of_le hk_le with hlt | heq
  · exact nodeAt_mem_G_of_lt_length π hlt
  · -- k = π.length: π.nodeAt π.length = v, which is the target of the walk.
    subst heq
    rw [Walk.nodeAt_length]
    exact (endpoints_mem_G_of_pos π hk).2

end Walk

namespace CDMG

variable {G : CDMG α}

/-! ### L6 -- `Anc` and `AncSet` transitivity -/

/-- If `u ∈ Anc^G(v)` and `v ∈ Anc^G(w)`, then `u ∈ Anc^G(w)`. -/
theorem anc_trans {u v w : α} (h₁ : u ∈ G.Anc v) (h₂ : v ∈ G.Anc w) :
    u ∈ G.Anc w := by
  obtain ⟨hu_mem, π₁, hπ₁⟩ := h₁
  obtain ⟨_, π₂, hπ₂⟩ := h₂
  exact ⟨hu_mem, π₁.append π₂, Walk.isDirected_append π₁ π₂ hπ₁ hπ₂⟩

/-- If `u ∈ Anc^G(v)` and `v ∈ AncSet^G(C)`, then `u ∈ AncSet^G(C)`. -/
theorem ancSet_of_anc_ancSet {u v : α} {C : Set α}
    (h₁ : u ∈ G.Anc v) (h₂ : v ∈ G.AncSet C) :
    u ∈ G.AncSet C := by
  rw [mem_AncSet] at h₂ ⊢
  obtain ⟨c, hcC, hvc⟩ := h₂
  exact ⟨c, hcC, anc_trans h₁ hvc⟩

end CDMG

namespace Walk

variable {G : CDMG α}

/-! ### L2 -- directed walks between `Sc`-related vertices stay in the SCC

If `π : Walk G u v` is directed and `u ∈ Sc^G(v)`, then every position
on `π` lies in `Sc^G(v)`.

The argument: at position `k`, the prefix `π.prefix k` is a directed
walk `u → π.nodeAt k`, witnessing `u ∈ Anc^G(π.nodeAt k)` and
`π.nodeAt k ∈ Desc^G(u)`. The suffix `π.suffix k` is a directed walk
`π.nodeAt k → v`, witnessing `π.nodeAt k ∈ Anc^G(v)`. Combined with
`u ∈ Sc^G(v) = Anc^G(v) ∩ Desc^G(v)` we obtain
`π.nodeAt k ∈ Anc^G(v) ∩ Desc^G(v) = Sc^G(v)`.
-/

/-- A directed walk from `u` to `v` with `u ∈ Sc^G(v)` has every
position in `Sc^G(v)`. -/
theorem directed_walk_in_Sc {u v : α} (π : Walk G u v)
    (h_dir : π.IsDirected) (h_sc : u ∈ G.Sc v) :
    ∀ k, k ≤ π.length → π.nodeAt k ∈ G.Sc v := by
  intro k hk
  -- Extract prefix and suffix.
  have h_pre_dir : (π.prefix k).IsDirected := isDirected_prefix π k h_dir
  have h_suf_dir : (π.suffix k).IsDirected := isDirected_suffix π k h_dir
  have h_u_mem : u ∈ G := h_sc.1.1
  -- π.nodeAt 0 = u for the prefix's source.
  have h_pre_source : (π.prefix k).nodeAt 0 = u := by
    rw [Walk.nodeAt_zero]
  -- Need to deduce π.nodeAt k ∈ G to talk about Anc/Desc.
  have h_node_mem : π.nodeAt k ∈ G := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · -- k = 0
      subst h0; rw [Walk.nodeAt_zero]
      exact h_u_mem
    · exact nodeAt_mem_G_of_pos_le_length π h0 hk
  -- Build u ∈ Anc^G (π.nodeAt k) via the directed prefix.
  have h_u_anc_node : u ∈ G.Anc (π.nodeAt k) := by
    refine ⟨h_u_mem, ?_⟩
    refine ⟨π.prefix k, ?_⟩
    exact h_pre_dir
  -- π.nodeAt k ∈ Desc^G(u) via the same prefix.
  have h_node_desc_u : π.nodeAt k ∈ G.Desc u := by
    refine ⟨h_node_mem, ?_⟩
    refine ⟨π.prefix k, ?_⟩
    exact h_pre_dir
  -- π.nodeAt k ∈ Anc^G(v) via the directed suffix.
  have h_node_anc_v : π.nodeAt k ∈ G.Anc v := by
    refine ⟨h_node_mem, ?_⟩
    -- suffix from k: Walk G (π.nodeAt k) v.
    refine ⟨π.suffix k, ?_⟩
    exact h_suf_dir
  -- u ∈ Desc^G(v): from h_sc.2.
  have h_u_desc_v : u ∈ G.Desc v := h_sc.2
  -- π.nodeAt k ∈ Desc^G(v): apply Desc-transitivity via u.
  -- We have v → u (h_u_desc_v gives π_uv with directed walk v → u)
  -- and u → π.nodeAt k (h_node_desc_u).
  have h_node_desc_v : π.nodeAt k ∈ G.Desc v := by
    obtain ⟨_, π_vu, hπ_vu⟩ := h_u_desc_v
    obtain ⟨_, π_uw, hπ_uw⟩ := h_node_desc_u
    refine ⟨h_node_mem, ?_⟩
    refine ⟨π_vu.append π_uw, ?_⟩
    exact isDirected_append π_vu π_uw hπ_vu hπ_uw
  exact ⟨h_node_anc_v, h_node_desc_v⟩

/-! ### Interior of a directed walk inside an SCC is unblockable -/

end Walk

namespace WalkStep

variable {G : CDMG α}

/-- Two `IsForward` steps with all three vertices in `Sc^G(scenter)` form
an unblockable joint. -/
theorem isUnblockableJoint_forward_forward_in_Sc {a b c scenter : α}
    (s : WalkStep G a b) (s' : WalkStep G b c)
    (h_s_fwd : s.IsForward) (h_s'_fwd : s'.IsForward)
    (_h_a : a ∈ G.Sc scenter) (h_b : b ∈ G.Sc scenter) (h_c : c ∈ G.Sc scenter) :
    s.IsUnblockableJoint s' := by
  refine ⟨?_, ?_, ?_⟩
  · -- ¬ collider: s' forward → HasArrowheadAtSource s' = False.
    cases s' with
    | forward _ => intro ⟨_, h_src⟩; simp at h_src
    | backward _ => simp at h_s'_fwd
    | bidir _ => simp at h_s'_fwd
  · -- s.IsBackward → ...: s is forward, vacuous.
    intro h_back
    cases s with
    | forward _ => simp at h_back
    | backward _ => simp at h_s_fwd
    | bidir _ => simp at h_s_fwd
  · -- s'.IsForward → c ∈ Sc^G(b): Sc-equivalence between b and scenter.
    intro _
    refine ⟨?_, ?_⟩
    · obtain ⟨c_mem, ⟨p_c_sc, hp_c_sc⟩⟩ := h_c.1
      obtain ⟨_, ⟨p_sc_b, hp_sc_b⟩⟩ := h_b.2
      exact ⟨c_mem, ⟨p_c_sc.append p_sc_b, Walk.isDirected_append _ _ hp_c_sc hp_sc_b⟩⟩
    · obtain ⟨_, ⟨p_b_sc, hp_b_sc⟩⟩ := h_b.1
      obtain ⟨c_mem, ⟨p_sc_c, hp_sc_c⟩⟩ := h_c.2
      exact ⟨c_mem, ⟨p_b_sc.append p_sc_c, Walk.isDirected_append _ _ hp_b_sc hp_sc_c⟩⟩

end WalkStep

namespace Walk

variable {G : CDMG α}

/-- Every interior position of a directed walk whose vertices all lie
in `Sc^G(scenter)` is an unblockable non-collider. -/
theorem isUnblockableNonColliderAt_interior_of_directed_in_Sc :
    ∀ {u w : α} (π : Walk G u w) {scenter : α},
      π.IsDirected →
      (∀ k, k ≤ π.length → π.nodeAt k ∈ G.Sc scenter) →
      ∀ k, 0 < k → k < π.length → π.IsUnblockableNonColliderAt k := by
  intro u w π
  induction π with
  | nil _ =>
    intro _ _ _ k _ h_lt
    simp [Walk.length_nil] at h_lt
  | @cons _ _ _ s p ih =>
    intro scenter h_dir h_inSc k h_pos h_lt
    cases p with
    | nil _ =>
      simp [Walk.length_cons, Walk.length_nil] at h_lt
      omega
    | @cons _ _ _ s' p' =>
      cases k with
      | zero => omega
      | succ k =>
        cases k with
        | zero =>
          -- k = 1: head joint, between s and s', both forward.
          rw [Walk.isUnblockableNonColliderAt_cons_cons_one]
          have h_s_fwd : s.IsForward := by
            cases s with
            | forward _ => simp
            | backward _ => simp at h_dir
            | bidir _ => simp at h_dir
          have h_s'_fwd : s'.IsForward := by
            cases s with
            | forward _ =>
              simp only [Walk.isDirected_cons_forward] at h_dir
              cases s' with
              | forward _ => simp
              | backward _ => simp at h_dir
              | bidir _ => simp at h_dir
            | backward _ => simp at h_dir
            | bidir _ => simp at h_dir
          -- Extract the three vertices' Sc-membership in their reduced forms.
          have h_n0_raw := h_inSc 0 (by simp [Walk.length_cons])
          have h_n1_raw := h_inSc 1 (by simp [Walk.length_cons])
          have h_n2_raw := h_inSc 2 (by simp [Walk.length_cons])
          simp only [Walk.nodeAt_cons_zero, Walk.nodeAt_cons_succ,
            Walk.nodeAt_zero] at h_n0_raw h_n1_raw h_n2_raw
          exact WalkStep.isUnblockableJoint_forward_forward_in_Sc s s'
            h_s_fwd h_s'_fwd h_n0_raw h_n1_raw h_n2_raw
        | succ k =>
          -- k + 2: recurse via cons_cons_succ_succ.
          rw [Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]
          -- Now need (cons s' p').IsUnblockableNonColliderAt (k + 1).
          -- Apply ih on (cons s' p').
          have h_tail_dir : (Walk.cons s' p').IsDirected := by
            cases s with
            | forward _ => simpa [Walk.isDirected_cons_forward] using h_dir
            | backward _ => simp at h_dir
            | bidir _ => simp at h_dir
          have h_tail_inSc : ∀ kk, kk ≤ (Walk.cons s' p').length →
              (Walk.cons s' p').nodeAt kk ∈ G.Sc scenter := by
            intro kk hkk
            have := h_inSc (kk + 1) (by
              simp only [Walk.length_cons] at hkk ⊢
              omega)
            simpa using this
          have h_tail_pos : 0 < k + 1 := Nat.succ_pos _
          have h_tail_lt : k + 1 < (Walk.cons s' p').length := by
            simp [Walk.length_cons] at h_lt ⊢; omega
          exact ih h_tail_dir h_tail_inSc (k + 1) h_tail_pos h_tail_lt

/-! ### L4 -- interior positions of a directed walk in `Sc^G(w)` are
unblockable non-colliders -/

/-- On a directed walk every internal step is `forward`, so the joint
two-step pattern `forward ?, forward ?'` makes the joint a non-collider
with strict outgoing arrow on the right only. With every node on the
walk lying in `Sc^G(w)`, this strict outgoing arrow's target lies in
`Sc^G(joint)` (the SCC of `w` and the joint coincide). Hence the joint
is unblockable. -/
theorem isUnblockableJoint_of_directed_in_Sc {a b c : α} {w : α}
    (s : WalkStep G a b) (s' : WalkStep G b c)
    (hdir : (Walk.cons s (Walk.cons s' (Walk.nil c))).IsDirected)
    (_hac_in : a ∈ G.Sc w) (hb_in : b ∈ G.Sc w) (hc_in : c ∈ G.Sc w) :
    s.IsUnblockableJoint s' := by
  -- Extract that s and s' are forward.
  have hs_fwd : s.IsForward := by
    cases s with
    | forward _ => simp
    | backward _ => simp at hdir
    | bidir _ => simp at hdir
  have hs'_fwd : s'.IsForward := by
    cases s with
    | forward _ =>
      simp only [Walk.isDirected_cons_forward] at hdir
      cases s' with
      | forward _ => simp
      | backward _ => simp at hdir
      | bidir _ => simp at hdir
    | backward _ => simp at hdir
    | bidir _ => simp at hdir
  -- Derive Sc^G(w) = Sc^G(b).
  have hSc_eq_b : G.Sc w = G.Sc b := by
    apply Set.eq_of_subset_of_subset
    · intro x ⟨hx_anc, hx_desc⟩
      refine ⟨?_, ?_⟩
      · -- x ∈ Anc^G(b): chain x → w (from hx_anc) with w → b (b ∈ Desc^G(w)).
        obtain ⟨_, πw_b, hπw_b⟩ := hb_in.2
        -- πw_b : Walk G w b is directed.
        obtain ⟨hx_mem, πx_w, hπx_w⟩ := hx_anc
        exact ⟨hx_mem, πx_w.append πw_b, isDirected_append _ _ hπx_w hπw_b⟩
      · -- x ∈ Desc^G(b): directed walk b → x.
        -- We have b ∈ Anc^G(w): directed walk b → w; w → x: from hx_desc.
        obtain ⟨_, πb_w, hπb_w⟩ := hb_in.1
        obtain ⟨hx_mem, πw_x, hπw_x⟩ := hx_desc
        exact ⟨hx_mem, πb_w.append πw_x, isDirected_append _ _ hπb_w hπw_x⟩
    · intro x ⟨hx_anc, hx_desc⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨_, πb_w, hπb_w⟩ := hb_in.1
        obtain ⟨hx_mem, πx_b, hπx_b⟩ := hx_anc
        exact ⟨hx_mem, πx_b.append πb_w, isDirected_append _ _ hπx_b hπb_w⟩
      · obtain ⟨_, πw_b, hπw_b⟩ := hb_in.2
        obtain ⟨hx_mem, πb_x, hπb_x⟩ := hx_desc
        exact ⟨hx_mem, πw_b.append πb_x, isDirected_append _ _ hπw_b hπb_x⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Not a collider: s' is forward so HasArrowheadAtSource s' = False.
    cases s' with
    | forward _ => intro ⟨_, h⟩; simp at h
    | backward _ => simp at hs'_fwd
    | bidir _ => simp at hs'_fwd
  · -- s.IsBackward → a ∈ Sc^G b: but s is forward, so IsBackward is False.
    intro hback; cases s with
    | forward _ => simp at hback
    | backward _ => simp at hs_fwd
    | bidir _ => simp at hs_fwd
  · -- s'.IsForward → c ∈ Sc^G b: by assumption, c ∈ Sc^G(w) = Sc^G(b).
    intro _
    rw [← hSc_eq_b]
    exact hc_in

/-! ### Prefix / suffix transport of collider / non-collider predicates -/

/-- Transport of `IsColliderAt` from `π.prefix i` to `π` at strict-interior
positions (`k < i`). The endpoint case `k = i` is excluded because
collider-ness is intrinsic to the joint of two adjacent steps and the
prefix loses information about the step at position `i`. -/
theorem isColliderAt_prefix_of_lt :
    ∀ {u v : α} (π : Walk G u v) (i k : ℕ),
      k < i → ((π.prefix i).IsColliderAt k ↔ π.IsColliderAt k) := by
  intro u v π
  induction π with
  | nil _ =>
    intro i k _
    rw [Walk.prefix_nil]
    exact Iff.rfl
  | @cons _ _ _ s p ih =>
    intro i k hk
    cases i with
    | zero => omega
    | succ i =>
      cases p with
      | nil _ =>
        -- π.prefix (i+1) = cons s ((nil _).prefix i) = cons s (nil _)
        rw [Walk.prefix_cons_succ, Walk.prefix_nil]
        exact Iff.rfl
      | @cons _ _ _ s' p' =>
        rw [Walk.prefix_cons_succ]
        cases k with
        | zero =>
          -- IsColliderAt at position 0 is False on both sides.
          cases i with
          | zero =>
            rw [Walk.prefix_cons_zero]
            exact Iff.rfl
          | succ i' =>
            rw [Walk.prefix_cons_succ]
            exact Iff.rfl
        | succ k =>
          cases k with
          | zero =>
            -- IsColliderAt 1: joint between s and (cons s' p').prefix i's first step.
            cases i with
            | zero =>
              -- hk : 0+1 < 0+1 contradicts
              omega
            | succ i' =>
              rw [Walk.prefix_cons_succ]
              show (Walk.cons s (Walk.cons s' (p'.prefix i'))).IsColliderAt 1 ↔
                (Walk.cons s (Walk.cons s' p')).IsColliderAt 1
              rw [Walk.isColliderAt_cons_cons_one, Walk.isColliderAt_cons_cons_one]
          | succ k =>
            -- IsColliderAt (k+2): recurse via cons_cons_succ_succ.
            cases i with
            | zero =>
              -- hk : k + 2 < 1 impossible
              omega
            | succ i' =>
              -- LHS: (cons s (cons s' (p'.prefix i'))).IsColliderAt (k+1+1)
              -- RHS: (cons s (cons s' p')).IsColliderAt (k+1+1)
              rw [Walk.prefix_cons_succ]
              show (Walk.cons s (Walk.cons s' (p'.prefix i'))).IsColliderAt (k + 2) ↔
                (Walk.cons s (Walk.cons s' p')).IsColliderAt (k + 2)
              rw [Walk.isColliderAt_cons_cons_succ_succ,
                Walk.isColliderAt_cons_cons_succ_succ]
              have hk' : k + 1 < i' + 1 := by omega
              have hih := ih (i' + 1) (k + 1) hk'
              rw [Walk.prefix_cons_succ] at hih
              exact hih

/-- Transport of `IsColliderAt` from `π.suffix j` to `π` at any positive
position. -/
theorem isColliderAt_suffix_of_pos :
    ∀ {u v : α} (π : Walk G u v) (j k : ℕ),
      0 < k →
      ((π.suffix j).IsColliderAt k ↔ π.IsColliderAt (j + k)) := by
  intro u v π
  induction π with
  | nil _ =>
    intro j k _
    rw [Walk.suffix_nil]
    exact Walk.isColliderAt_nil _ _
  | @cons _ _ _ s p ih =>
    intro j k hk
    cases j with
    | zero =>
      -- π.suffix 0 = π, and j + k = k.
      simp only [Nat.zero_add, Walk.suffix_cons_zero]
      rfl
    | succ j =>
      -- π.suffix (j+1) = p.suffix j
      simp only [Walk.suffix_cons_succ]
      cases k with
      | zero => omega
      | succ k =>
        have ih' := ih j (k + 1) (Nat.succ_pos _)
        have h_shift : j + 1 + (k + 1) = (j + k + 1) + 1 := by omega
        rw [h_shift]
        have h_unfold : (Walk.cons s p).IsColliderAt ((j + k + 1) + 1) ↔
            p.IsColliderAt (j + k + 1) := by
          cases p with
          | nil _ =>
            simp only [Walk.isColliderAt_cons_nil, Walk.isColliderAt_nil]
          | @cons _ _ _ s' p' =>
            simp only [Walk.isColliderAt_cons_cons_succ_succ]
        rw [h_unfold]
        have h_arg : j + k + 1 = j + (k + 1) := by omega
        rw [h_arg]
        exact ih'

/-! ### Prefix / suffix transport for `IsUnblockableNonColliderAt` -/

/-- Transport of `IsUnblockableNonColliderAt` from `π.prefix i` to `π` at
strict-interior positions (`k < i`). -/
theorem isUnblockableNonColliderAt_prefix_of_lt :
    ∀ {u v : α} (π : Walk G u v) (i k : ℕ),
      k < i →
      ((π.prefix i).IsUnblockableNonColliderAt k ↔
        π.IsUnblockableNonColliderAt k) := by
  intro u v π
  induction π with
  | nil _ =>
    intro i k _
    rw [Walk.prefix_nil]
    exact Iff.rfl
  | @cons _ _ _ s p ih =>
    intro i k hk
    cases i with
    | zero => omega
    | succ i =>
      cases p with
      | nil _ =>
        rw [Walk.prefix_cons_succ, Walk.prefix_nil]
        exact Iff.rfl
      | @cons _ _ _ s' p' =>
        rw [Walk.prefix_cons_succ]
        cases k with
        | zero =>
          cases i with
          | zero =>
            rw [Walk.prefix_cons_zero]
            exact Iff.rfl
          | succ i' =>
            rw [Walk.prefix_cons_succ]
            exact Iff.rfl
        | succ k =>
          cases k with
          | zero =>
            cases i with
            | zero => omega
            | succ i' =>
              rw [Walk.prefix_cons_succ]
              show (Walk.cons s (Walk.cons s' (p'.prefix i'))).IsUnblockableNonColliderAt 1 ↔
                (Walk.cons s (Walk.cons s' p')).IsUnblockableNonColliderAt 1
              rw [Walk.isUnblockableNonColliderAt_cons_cons_one,
                Walk.isUnblockableNonColliderAt_cons_cons_one]
          | succ k =>
            cases i with
            | zero => omega
            | succ i' =>
              rw [Walk.prefix_cons_succ]
              show (Walk.cons s (Walk.cons s' (p'.prefix i'))).IsUnblockableNonColliderAt (k + 2) ↔
                (Walk.cons s (Walk.cons s' p')).IsUnblockableNonColliderAt (k + 2)
              rw [Walk.isUnblockableNonColliderAt_cons_cons_succ_succ,
                Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]
              have hk' : k + 1 < i' + 1 := by omega
              have hih := ih (i' + 1) (k + 1) hk'
              rw [Walk.prefix_cons_succ] at hih
              exact hih

/-- Transport of `IsUnblockableNonColliderAt` from `π.suffix j` to `π` at
any positive position. -/
theorem isUnblockableNonColliderAt_suffix_of_pos :
    ∀ {u v : α} (π : Walk G u v) (j k : ℕ),
      0 < k →
      ((π.suffix j).IsUnblockableNonColliderAt k ↔
        π.IsUnblockableNonColliderAt (j + k)) := by
  intro u v π
  induction π with
  | nil _ =>
    intro j k _
    rw [Walk.suffix_nil]
    exact Iff.rfl
  | @cons _ _ _ s p ih =>
    intro j k hk
    cases j with
    | zero =>
      simp only [Nat.zero_add, Walk.suffix_cons_zero]
      rfl
    | succ j =>
      simp only [Walk.suffix_cons_succ]
      cases k with
      | zero => omega
      | succ k =>
        have ih' := ih j (k + 1) (Nat.succ_pos _)
        have h_shift : j + 1 + (k + 1) = (j + k + 1) + 1 := by omega
        rw [h_shift]
        have h_unfold : (Walk.cons s p).IsUnblockableNonColliderAt ((j + k + 1) + 1) ↔
            p.IsUnblockableNonColliderAt (j + k + 1) := by
          cases p with
          | nil _ =>
            simp only [Walk.isUnblockableNonColliderAt_cons_nil,
              Walk.isUnblockableNonColliderAt_nil]
          | @cons _ _ _ s' p' =>
            simp only [Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]
        rw [h_unfold]
        have h_arg : j + k + 1 = j + (k + 1) := by omega
        rw [h_arg]
        exact ih'

/-! ### Append-shift transport of `IsColliderAt` / `IsUnblockableNonColliderAt` -/

/-- For positions strictly inside the right walk, `IsColliderAt`
on an appended walk shifts cleanly. -/
theorem isColliderAt_append_shift_pos :
    ∀ {u v w : α} (p₁ : Walk G u v) (p₂ : Walk G v w) (k' : ℕ),
      0 < k' →
      ((p₁.append p₂).IsColliderAt (p₁.length + k') ↔ p₂.IsColliderAt k') := by
  intro u v w p₁
  induction p₁ with
  | nil _ =>
    intro p₂ k' _
    simp only [Walk.nil_append, Walk.length_nil, Nat.zero_add]
  | @cons _ _ _ s p ih =>
    intro p₂ k' hk
    -- (cons s p).length + k' = p.length + 1 + k' = (p.length + k') + 1
    -- (cons s p).append p₂ = cons s (p.append p₂)
    rw [Walk.cons_append, Walk.length_cons]
    -- Goal: (cons s (p.append p₂)).IsColliderAt (p.length + 1 + k') ↔ p₂.IsColliderAt k'
    -- For p.length + 1 + k' ≥ 2 (when k' ≥ 1), use cons_cons_succ_succ ... but this
    -- requires p.append p₂ to be a `cons`.  We do that by casing on p first.
    cases p with
    | nil _ =>
      -- p = nil → p.append p₂ = p₂; (cons s p).length = 1; position 1 + k'.
      simp only [Walk.nil_append, Walk.length_nil, Nat.zero_add] at *
      -- Goal: (cons s p₂).IsColliderAt (1 + k') ↔ p₂.IsColliderAt k'.
      cases p₂ with
      | nil _ =>
        -- (cons s nil).IsColliderAt (1+k') = False (cons_nil)
        -- nil.IsColliderAt k' = False.
        rw [Walk.isColliderAt_cons_nil, Walk.isColliderAt_nil]
      | @cons _ _ _ s' p' =>
        -- (cons s (cons s' p')).IsColliderAt (1+k') ↔ (cons s' p').IsColliderAt k'
        cases k' with
        | zero => omega
        | succ k'' =>
          have heq : 1 + (k'' + 1) = (k'' + 1) + 1 := by omega
          rw [heq, Walk.isColliderAt_cons_cons_succ_succ]
    | @cons _ _ _ s' p' =>
      -- p = cons s' p'. p.append p₂ = cons s' (p'.append p₂).
      -- p.length = p'.length + 1.
      -- Goal: (cons s (cons s' (p'.append p₂))).IsColliderAt (p'.length + 1 + 1 + k')
      --        ↔ p₂.IsColliderAt k'.
      rw [Walk.cons_append, Walk.length_cons]
      -- Position p'.length + 1 + 1 + k' = (p'.length + 1 + k') + 1.
      have h_eq : p'.length + 1 + 1 + k' = (p'.length + 1 + k') + 1 := by omega
      rw [h_eq]
      -- The LHS is now (cons s _).IsColliderAt (... + 1).
      -- We want to apply cons_cons_succ_succ, which expects (cons s (cons s' rest)).IsColliderAt (k+2).
      have h_eq2 : (p'.length + 1 + k') + 1 = (p'.length + k') + 2 := by omega
      rw [h_eq2, Walk.isColliderAt_cons_cons_succ_succ]
      -- LHS: (cons s' (p'.append p₂)).IsColliderAt (p'.length + k' + 1)
      -- Apply IH on (cons s' p') with p₂ and k'.
      have ih' := ih p₂ k' hk
      rw [Walk.cons_append, Walk.length_cons] at ih'
      -- ih': (cons s' (p'.append p₂)).IsColliderAt (p'.length + 1 + k') ↔ p₂.IsColliderAt k'
      have h_eq3 : p'.length + k' + 1 = p'.length + 1 + k' := by omega
      rw [h_eq3]
      exact ih'

/-- Same shift for `IsUnblockableNonColliderAt`. -/
theorem isUnblockableNonColliderAt_append_shift_pos :
    ∀ {u v w : α} (p₁ : Walk G u v) (p₂ : Walk G v w) (k' : ℕ),
      0 < k' →
      ((p₁.append p₂).IsUnblockableNonColliderAt (p₁.length + k') ↔
        p₂.IsUnblockableNonColliderAt k') := by
  intro u v w p₁
  induction p₁ with
  | nil _ =>
    intro p₂ k' _
    simp only [Walk.nil_append, Walk.length_nil, Nat.zero_add]
  | @cons _ _ _ s p ih =>
    intro p₂ k' hk
    rw [Walk.cons_append, Walk.length_cons]
    cases p with
    | nil _ =>
      simp only [Walk.nil_append, Walk.length_nil, Nat.zero_add] at *
      cases p₂ with
      | nil _ =>
        rw [Walk.isUnblockableNonColliderAt_cons_nil, Walk.isUnblockableNonColliderAt_nil]
      | @cons _ _ _ s' p' =>
        cases k' with
        | zero => omega
        | succ k'' =>
          have heq : 1 + (k'' + 1) = (k'' + 1) + 1 := by omega
          rw [heq, Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]
    | @cons _ _ _ s' p' =>
      rw [Walk.cons_append, Walk.length_cons]
      have h_eq : p'.length + 1 + 1 + k' = (p'.length + 1 + k') + 1 := by omega
      rw [h_eq]
      have h_eq2 : (p'.length + 1 + k') + 1 = (p'.length + k') + 2 := by omega
      rw [h_eq2, Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]
      have ih' := ih p₂ k' hk
      rw [Walk.cons_append, Walk.length_cons] at ih'
      have h_eq3 : p'.length + k' + 1 = p'.length + 1 + k' := by omega
      rw [h_eq3]
      exact ih'

/-! ### Spliced-walk transports

These helpers package the per-position transports of
`nodeAt` / `IsColliderAt` / `IsUnblockableNonColliderAt`
across the three-way splice
`(π.prefix i).append (σ.append (π.suffix j))`.
-/

/-- `nodeAt` on the spliced walk equals `nodeAt` on `π` for positions
in the prefix part (`k ≤ i ≤ π.length`). -/
theorem nodeAt_splice_pre {u v : α} {i j : ℕ} (π : Walk G u v)
    (σ : Walk G (π.nodeAt i) (π.nodeAt j))
    (h_i_le : i ≤ π.length) {k : ℕ} (h_k_le : k ≤ i) :
    ((π.prefix i).append (σ.append (π.suffix j))).nodeAt k = π.nodeAt k := by
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π h_i_le
  rw [Walk.nodeAt_append_le _ _ (by rw [h_pre_len]; exact h_k_le)]
  rw [Walk.nodeAt_prefix π h_k_le h_i_le]

/-- `nodeAt` on the spliced walk equals `nodeAt` on `σ` for positions
in the middle part. -/
theorem nodeAt_splice_mid {u v : α} {i j : ℕ} (π : Walk G u v)
    (σ : Walk G (π.nodeAt i) (π.nodeAt j))
    (h_i_le : i ≤ π.length) {k' : ℕ} (h_k'_le : k' ≤ σ.length) :
    ((π.prefix i).append (σ.append (π.suffix j))).nodeAt (i + k') = σ.nodeAt k' := by
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π h_i_le
  have outer := Walk.nodeAt_append_add_left (π.prefix i) (σ.append (π.suffix j)) k'
  rw [h_pre_len] at outer
  rw [outer]
  rw [Walk.nodeAt_append_le _ _ h_k'_le]

/-- `nodeAt` on the spliced walk equals `nodeAt` on `π` shifted, for
positions in the suffix part. -/
theorem nodeAt_splice_suf {u v : α} {i j : ℕ} (π : Walk G u v)
    (σ : Walk G (π.nodeAt i) (π.nodeAt j))
    (h_i_le : i ≤ π.length) (h_j_le : j ≤ π.length)
    {k' : ℕ} (h_k'_le : k' ≤ π.length - j) :
    ((π.prefix i).append (σ.append (π.suffix j))).nodeAt (i + σ.length + k') =
      π.nodeAt (j + k') := by
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π h_i_le
  rw [Nat.add_assoc]
  -- Goal: nodeAt (i + (σ.length + k'))
  have outer := Walk.nodeAt_append_add_left (π.prefix i) (σ.append (π.suffix j))
    (σ.length + k')
  rw [h_pre_len] at outer
  rw [outer]
  rw [Walk.nodeAt_append_add_left]
  rw [Walk.nodeAt_suffix π (by omega)]

/-- `IsColliderAt` on the spliced walk transports to `π` for positions
in the prefix part (`k < i`). -/
theorem isColliderAt_splice_pre {u v : α} {i j : ℕ} (π : Walk G u v)
    (σ : Walk G (π.nodeAt i) (π.nodeAt j))
    (h_i_le : i ≤ π.length) {k : ℕ} (h_k_lt : k < i) :
    ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt k ↔
      π.IsColliderAt k := by
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π h_i_le
  rw [Walk.isColliderAt_append_lt_length _ _ (by rw [h_pre_len]; exact h_k_lt)]
  rw [Walk.isColliderAt_prefix_of_lt π i k h_k_lt]

/-- `IsColliderAt` on the spliced walk transports to `σ` for positions
in the middle part. -/
theorem isColliderAt_splice_mid {u v : α} {i j : ℕ} (π : Walk G u v)
    (σ : Walk G (π.nodeAt i) (π.nodeAt j))
    (h_i_le : i ≤ π.length) {k' : ℕ}
    (h_k'_pos : 0 < k') (h_k'_lt : k' < σ.length) :
    ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt (i + k') ↔
      σ.IsColliderAt k' := by
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π h_i_le
  have outer := Walk.isColliderAt_append_shift_pos (π.prefix i) (σ.append (π.suffix j))
    k' h_k'_pos
  rw [h_pre_len] at outer
  rw [outer]
  rw [Walk.isColliderAt_append_lt_length _ _ h_k'_lt]

/-- `IsColliderAt` on the spliced walk transports to `π` (shifted) for
positions in the suffix part. -/
theorem isColliderAt_splice_suf {u v : α} {i j : ℕ} (π : Walk G u v)
    (σ : Walk G (π.nodeAt i) (π.nodeAt j))
    (h_i_le : i ≤ π.length) {k' : ℕ} (h_k'_pos : 0 < k') :
    ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt
      (i + σ.length + k') ↔ π.IsColliderAt (j + k') := by
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π h_i_le
  rw [Nat.add_assoc]
  -- Goal: IsColliderAt (i + (σ.length + k'))
  -- Apply outer append_shift_pos via i = (π.prefix i).length:
  have outer := Walk.isColliderAt_append_shift_pos (π.prefix i) (σ.append (π.suffix j))
    (σ.length + k') (by omega)
  rw [h_pre_len] at outer
  rw [outer]
  -- Goal: (σ.append (π.suffix j)).IsColliderAt (σ.length + k') ↔ π.IsColliderAt (j + k')
  rw [Walk.isColliderAt_append_shift_pos σ _ k' h_k'_pos]
  rw [Walk.isColliderAt_suffix_of_pos π j k' h_k'_pos]

/-- `IsUnblockableNonColliderAt` on the spliced walk transports to `σ`
for positions in the middle part. -/
theorem isUnblockableNonColliderAt_splice_mid {u v : α} {i j : ℕ}
    (π : Walk G u v) (σ : Walk G (π.nodeAt i) (π.nodeAt j))
    (h_i_le : i ≤ π.length) {k' : ℕ}
    (h_k'_pos : 0 < k') (h_k'_lt : k' < σ.length) :
    ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt (i + k') ↔
      σ.IsUnblockableNonColliderAt k' := by
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π h_i_le
  have outer := Walk.isUnblockableNonColliderAt_append_shift_pos
    (π.prefix i) (σ.append (π.suffix j)) k' h_k'_pos
  rw [h_pre_len] at outer
  rw [outer]
  rw [Walk.isUnblockableNonColliderAt_append_lt_length _ _ h_k'_lt]

/-- `IsUnblockableNonColliderAt` on the spliced walk transports to `π`
for positions in the prefix part. -/
theorem isUnblockableNonColliderAt_splice_pre {u v : α} {i j : ℕ}
    (π : Walk G u v) (σ : Walk G (π.nodeAt i) (π.nodeAt j))
    (h_i_le : i ≤ π.length) {k : ℕ} (h_k_lt : k < i) :
    ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt k ↔
      π.IsUnblockableNonColliderAt k := by
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π h_i_le
  rw [Walk.isUnblockableNonColliderAt_append_lt_length _ _
    (by rw [h_pre_len]; exact h_k_lt)]
  rw [Walk.isUnblockableNonColliderAt_prefix_of_lt π i k h_k_lt]

/-- `IsUnblockableNonColliderAt` on the spliced walk transports to `π`
(shifted) for positions in the suffix part. -/
theorem isUnblockableNonColliderAt_splice_suf {u v : α} {i j : ℕ}
    (π : Walk G u v) (σ : Walk G (π.nodeAt i) (π.nodeAt j))
    (h_i_le : i ≤ π.length) {k' : ℕ} (h_k'_pos : 0 < k') :
    ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
      (i + σ.length + k') ↔ π.IsUnblockableNonColliderAt (j + k') := by
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π h_i_le
  rw [Nat.add_assoc]
  have outer := Walk.isUnblockableNonColliderAt_append_shift_pos
    (π.prefix i) (σ.append (π.suffix j)) (σ.length + k') (by omega)
  rw [h_pre_len] at outer
  rw [outer]
  rw [Walk.isUnblockableNonColliderAt_append_shift_pos σ _ k' h_k'_pos]
  rw [Walk.isUnblockableNonColliderAt_suffix_of_pos π j k' h_k'_pos]

/-! ### Walk decomposition helpers -/

/-- A walk of positive length decomposes as a `cons`. -/
theorem walk_pos_eq_cons :
    ∀ {u v : α} (π : Walk G u v), 1 ≤ π.length →
      ∃ (w : α) (s : WalkStep G u w) (p : Walk G w v), π = Walk.cons s p := by
  intro u v π h
  cases π with
  | nil _ => simp at h
  | @cons _ w _ s p => exact ⟨w, s, p, rfl⟩

/-- A walk of positive length ends with a step: `π = p.append (cons s (nil v))`
for some prefix `p` and last step `s`. -/
theorem walk_pos_eq_append_last :
    ∀ {u v : α} (π : Walk G u v), 1 ≤ π.length →
      ∃ (w : α) (p : Walk G u w) (s : WalkStep G w v),
        π = p.append (Walk.cons s (Walk.nil v)) := by
  intro u v π h
  induction π with
  | nil _ => simp at h
  | @cons u w _ s p ih =>
    cases p with
    | nil _ =>
      -- π = cons s (nil _), length 1; the "last step" is `s` itself.
      refine ⟨u, Walk.nil u, s, ?_⟩
      rw [Walk.nil_append]
    | @cons _ _ _ s'' p' =>
      have h_tail : 1 ≤ (Walk.cons s'' p').length := by simp [Walk.length_cons]
      obtain ⟨w_last, p_tail, s_last, h_tail_eq⟩ := ih h_tail
      refine ⟨w_last, Walk.cons s p_tail, s_last, ?_⟩
      rw [Walk.cons_append, ← h_tail_eq]

/-- Appending the trivial walk on the right does nothing. -/
theorem append_nil :
    ∀ {u v : α} (p : Walk G u v), p.append (Walk.nil v) = p := by
  intro u v p
  induction p with
  | nil _ => rfl
  | @cons _ _ _ s p ih => rw [Walk.cons_append, ih]

/-! ### Joint-position helpers: no collider when the relevant side has no
arrowhead at the joint vertex.

These factor the standard observation that a collider at position
`p₁.length` on `p₁.append p₂` requires arrowhead-at-target on the
last step of `p₁` AND arrowhead-at-source on the first step of `p₂`.
If either side fails the relevant arrowhead test, no collider.
-/

/-- If the first step of the right walk has no source-arrowhead, the
joint at position `p₁.length` on `p₁.append (cons s p₂')` is not a
collider. -/
theorem not_isColliderAt_append_cons_at_left_length :
    ∀ {u v w x : α} (p₁ : Walk G u v) (s : WalkStep G v w) (p₂' : Walk G w x),
      ¬ s.HasArrowheadAtSource →
      ¬ (p₁.append (Walk.cons s p₂')).IsColliderAt p₁.length := by
  intro u v w x p₁
  induction p₁ with
  | nil _ =>
    intro s p₂' _ h_coll
    rw [Walk.nil_append, Walk.length_nil] at h_coll
    cases p₂' with
    | nil _ =>
      exact (Walk.isColliderAt_cons_nil _ _).mp h_coll
    | cons _ _ =>
      exact (Walk.isColliderAt_cons_cons_zero _ _ _).mp h_coll
  | @cons _ _ _ s_head p ih =>
    intro s p₂' h_no_src h_coll
    rw [Walk.cons_append, Walk.length_cons] at h_coll
    -- h_coll : (cons s_head (p.append (cons s p₂'))).IsColliderAt (p.length + 1)
    cases p with
    | nil _ =>
      rw [Walk.nil_append] at h_coll
      simp only [Walk.length_nil, Nat.zero_add, Walk.isColliderAt_cons_cons_one] at h_coll
      exact h_no_src h_coll.2
    | @cons _ _ _ s_p rest_p =>
      rw [Walk.cons_append, Walk.length_cons] at h_coll
      -- h_coll : (cons s_head (cons s_p (rest_p.append (cons s p₂')))).IsColliderAt (rest_p.length + 1 + 1)
      have h_eq : rest_p.length + 1 + 1 = rest_p.length + 2 := rfl
      rw [h_eq] at h_coll
      simp only [Walk.isColliderAt_cons_cons_succ_succ] at h_coll
      -- Apply ih on (cons s_p rest_p).
      apply ih s p₂' h_no_src
      rw [Walk.cons_append, Walk.length_cons]
      exact h_coll

/-- Appending the trivial right walk: no collider at the joint
(position `p₁.length` = endpoint of `p₁.append (nil _)`). -/
theorem not_isColliderAt_append_nil_at_left_length :
    ∀ {u v : α} (p₁ : Walk G u v),
      ¬ (p₁.append (Walk.nil v)).IsColliderAt p₁.length := by
  intro u v p₁
  rw [Walk.append_nil]
  exact (Walk.isNonColliderAt_length p₁).2

/-- A length-0 walk has equal source and target endpoints. -/
theorem source_eq_target_of_length_zero :
    ∀ {u v : α} (π : Walk G u v), π.length = 0 → u = v := by
  intro u v π
  cases π with
  | nil _ => intros; rfl
  | cons _ _ => intro h; simp [Walk.length_cons] at h

/-- `nil_append`-style identity for a length-0 walk in front: appending a walk after
a length-0 walk (with the necessary endpoint equation) gives the original walk
modulo the endpoint cast. -/
theorem length_zero_append :
    ∀ {u v w : α} (σ : Walk G u v) (q : Walk G v w) (hσ : σ.length = 0),
      σ.append q =
        (Walk.source_eq_target_of_length_zero σ hσ).symm ▸ q := by
  intro u v w σ q hσ
  cases σ with
  | nil _ =>
    rw [Walk.nil_append]
  | cons _ _ => simp [Walk.length_cons] at hσ

/-- Reverse of an appended walk. -/
theorem reverse_append :
    ∀ {u v w : α} (p₁ : Walk G u v) (p₂ : Walk G v w),
      (p₁.append p₂).reverse = p₂.reverse.append p₁.reverse := by
  intro u v w p₁ p₂
  induction p₁ with
  | nil _ =>
    rw [Walk.nil_append, Walk.reverse_nil, Walk.append_nil]
  | @cons _ _ _ s p ih =>
    rw [Walk.cons_append, Walk.reverse_cons, Walk.reverse_cons, ih, Walk.append_assoc]

/-- `Sc` is symmetric. -/
theorem mem_Sc_symm {G : CDMG α} {u v : α} (h : u ∈ G.Sc v) : v ∈ G.Sc u := by
  obtain ⟨h_anc, h_desc⟩ := h
  -- u ∈ Anc^G(v): u ∈ G ∧ ∃ walk u → v directed.
  -- u ∈ Desc^G(v): u ∈ G ∧ ∃ walk v → u directed.
  -- Goal: v ∈ Anc^G(u) ∧ v ∈ Desc^G(u).
  -- For v ∈ Anc^G(u): need v ∈ G ∧ ∃ walk v → u directed.
  -- We have walk v → u directed from h_desc.
  -- For v ∈ G: from h_desc's walk (if non-trivial v is source of step) OR v = u from trivial walk.
  obtain ⟨u_mem, π_uv, hπ_uv_dir⟩ := h_anc
  obtain ⟨_, π_vu, hπ_vu_dir⟩ := h_desc
  -- v ∈ G: π_vu : Walk G v u. If non-trivial, first step's source = v ∈ G.
  -- If trivial, u = v, so v ∈ G via u_mem.
  have h_v_mem : v ∈ G := by
    cases π_vu with
    | nil _ => exact u_mem
    | @cons _ _ _ s _ => exact s.source_mem_G
  exact ⟨⟨h_v_mem, π_vu, hπ_vu_dir⟩, ⟨h_v_mem, π_uv, hπ_uv_dir⟩⟩

/-- Reversing a walk twice is the identity. -/
theorem reverse_reverse :
    ∀ {u v : α} (π : Walk G u v), π.reverse.reverse = π := by
  intro u v π
  induction π with
  | nil _ => rfl
  | @cons _ _ _ s p ih =>
    rw [Walk.reverse_cons]
    rw [Walk.reverse_append]
    rw [ih]
    rw [Walk.reverse_cons, Walk.reverse_nil, Walk.nil_append]
    have h_step : s.reverse.reverse = s := by cases s <;> rfl
    rw [h_step]
    rfl

/-- Helper: the first step of `σ.append q` has no source-arrowhead whenever:
either (i) `σ.IsDirected` (so its first step is forward), or
(ii) `σ.length = 0` and `q`'s first step has no source-arrowhead. -/
theorem first_step_no_source_of_directed_append :
    ∀ {u v w : α} (σ : Walk G u v) (q : Walk G v w)
      (a : α) (s : WalkStep G u a) (rest : Walk G a w),
    σ.IsDirected →
    σ.append q = Walk.cons s rest →
    (∀ (a' : α) (s' : WalkStep G v a') (rest' : Walk G a' w),
        q = Walk.cons s' rest' → ¬ s'.HasArrowheadAtSource) →
    ¬ s.HasArrowheadAtSource := by
  intro u v w σ q a s rest hσ_dir h_eq h_q h_src
  cases σ with
  | nil _ =>
    -- σ = nil u; σ.append q = q. So q = cons s rest.
    rw [Walk.nil_append] at h_eq
    exact h_q a s rest h_eq h_src
  | @cons _ _ _ sσ σrest =>
    -- σ = cons sσ σrest, so σ.append q = cons sσ (σrest.append q).
    -- From h_eq: cons sσ (σrest.append q) = cons s rest. So sσ = s.
    rw [Walk.cons_append] at h_eq
    obtain ⟨h_av, h_sa, _⟩ := Walk.cons.inj h_eq
    subst h_av
    have : sσ = s := eq_of_heq h_sa
    subst this
    -- σ.IsDirected forces sσ to be forward.
    cases sσ with
    | forward _ => simp at h_src
    | backward _ => simp at hσ_dir
    | bidir _ => simp at hσ_dir

/-- Dual: the first step of `σ.append q` HAS a source-arrowhead whenever:
either (i) `σ.reverse.IsDirected` (so σ's first step is backward, with source-arrowhead),
or (ii) `σ.length = 0` and `q`'s first step has a source-arrowhead. -/
theorem first_step_has_source_of_reverseDirected_append :
    ∀ {u v w : α} (σ : Walk G u v) (q : Walk G v w)
      (a : α) (s : WalkStep G u a) (rest : Walk G a w),
    σ.reverse.IsDirected →
    σ.append q = Walk.cons s rest →
    (∀ (a' : α) (s' : WalkStep G v a') (rest' : Walk G a' w),
        q = Walk.cons s' rest' → s'.HasArrowheadAtSource) →
    s.HasArrowheadAtSource := by
  intro u v w σ q a s rest hσ_rev_dir h_eq h_q
  cases σ with
  | nil _ =>
    -- σ = nil u; σ.append q = q. So q = cons s rest.
    rw [Walk.nil_append] at h_eq
    exact h_q a s rest h_eq
  | @cons _ _ _ sσ σrest =>
    rw [Walk.cons_append] at h_eq
    obtain ⟨h_av, h_sa, _⟩ := Walk.cons.inj h_eq
    subst h_av
    have : sσ = s := eq_of_heq h_sa
    subst this
    -- σ.reverse.IsDirected forces sσ to be backward.
    rw [Walk.reverse_cons] at hσ_rev_dir
    obtain ⟨_, h_last⟩ := isDirected_split_append _ _ hσ_rev_dir
    cases sσ with
    | forward _ => simp at h_last
    | backward _ => simp
    | bidir _ => simp at h_last

/-! ### Support / `nodeAt` bridge -/

/-- The `k`-th element of `π.support` equals `π.nodeAt k`. -/
theorem support_getElem_eq_nodeAt :
    ∀ {u v : α} (π : Walk G u v) {k : ℕ} (h : k < π.support.length),
      π.support[k] = π.nodeAt k := by
  intro u v π
  induction π with
  | nil _ =>
    intro k hk
    simp only [Walk.support_nil, List.length_singleton] at hk
    -- k < 1 so k = 0
    have : k = 0 := Nat.lt_one_iff.mp hk
    subst this
    rfl
  | @cons _ _ _ s p ih =>
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      simp only [Walk.support_cons, List.length_cons] at hk
      have hk' : k < p.support.length := Nat.lt_of_succ_lt_succ hk
      change p.support[k] = p.nodeAt k
      exact ih hk'

/-- From `¬ π.IsPath` extract two positions `p < q ≤ π.length` whose
nodes coincide. -/
theorem exists_dup_positions_of_not_isPath :
    ∀ {u v : α} (π : Walk G u v), ¬ π.IsPath →
      ∃ p q : ℕ, p < q ∧ q ≤ π.length ∧ π.nodeAt p = π.nodeAt q := by
  intro u v π hnp
  have hsup_len : π.support.length = π.length + 1 := Walk.support_length π
  have hndup : ¬ π.support.Nodup := hnp
  rw [List.nodup_iff_getElem?_ne_getElem?] at hndup
  simp only [ne_eq, not_forall, not_not] at hndup
  obtain ⟨p, q, hpq, hq, heq⟩ := hndup
  refine ⟨p, q, hpq, ?_, ?_⟩
  · rw [hsup_len] at hq; omega
  · -- support[p]? = support[q]? plus both in-range → support[p] = support[q] → nodeAt p = nodeAt q
    have hp_lt : p < π.support.length := lt_trans hpq hq
    have h1 : π.support[p]? = some π.support[p] := List.getElem?_eq_getElem hp_lt
    have h2 : π.support[q]? = some π.support[q] := List.getElem?_eq_getElem hq
    rw [h1, h2, Option.some_inj] at heq
    rw [← support_getElem_eq_nodeAt π hp_lt, ← support_getElem_eq_nodeAt π hq]
    exact heq

/-! ### Walk substitution along an endpoint equality -/

/-- Casting a walk via an equality of source vertices preserves length. -/
theorem length_subst_left {a b v : α} (h : a = b) (π : Walk G a v) :
    (h ▸ π : Walk G b v).length = π.length := by
  subst h; rfl

/-- Casting a walk via an equality of source vertices preserves `IsDirected`. -/
theorem isDirected_subst_left {a b v : α} (h : a = b) (π : Walk G a v) :
    (h ▸ π : Walk G b v).IsDirected ↔ π.IsDirected := by
  subst h; rfl

/-- Casting a walk via an equality of source vertices preserves `IsPath`. -/
theorem isPath_subst_left {a b v : α} (h : a = b) (π : Walk G a v) :
    (h ▸ π : Walk G b v).IsPath ↔ π.IsPath := by
  subst h; rfl

/-- Casting a walk via an equality of source vertices preserves
`nodeAt` lookups. -/
theorem nodeAt_subst_left {a b v : α} (h : a = b) (π : Walk G a v) (k : ℕ) :
    (h ▸ π : Walk G b v).nodeAt k = π.nodeAt k := by
  subst h; rfl

/-! ### Support of `append` and `reverse` -/

/-- Support of an appended walk: prefix's support concatenated with
the suffix's support minus the duplicated joint vertex. -/
theorem support_append :
    ∀ {u v w : α} (p : Walk G u v) (q : Walk G v w),
      (p.append q).support = p.support ++ q.support.tail := by
  intro u v w p
  induction p with
  | nil x => intro q; cases q <;> simp
  | @cons _ _ _ s p ih =>
    intro q
    simp only [Walk.cons_append, Walk.support_cons, ih, List.cons_append]

/-- Support of a reversed walk equals the reverse of the original
support. -/
theorem support_reverse :
    ∀ {u v : α} (π : Walk G u v), π.reverse.support = π.support.reverse := by
  intro u v π
  induction π with
  | nil _ => rfl
  | @cons _ _ _ s p ih =>
    rw [Walk.reverse_cons, support_append, ih]
    simp only [Walk.support_cons, Walk.support_nil, List.tail_cons,
      List.reverse_cons]

/-- A reversed walk is a path iff the original is. -/
theorem isPath_reverse_iff :
    ∀ {u v : α} (π : Walk G u v), π.reverse.IsPath ↔ π.IsPath := by
  intro u v π
  simp only [Walk.IsPath, support_reverse, List.nodup_reverse]

/-! ### Loop-erasure / `exists_path_of_directed` -/

/-- Extracts a directed path from a directed walk. Iteratively
loop-erases via the spliced shorter walk
`(π.prefix p).append (π.suffix q)` whenever a duplicate `p < q` with
`π.nodeAt p = π.nodeAt q` exists; well-founded recursion on `π.length`. -/
theorem exists_path_of_directed :
    ∀ {u v : α} (π : Walk G u v), π.IsDirected →
      ∃ σ : Walk G u v, σ.IsDirected ∧ σ.IsPath := by
  -- Strong induction on π.length packaged as an outer statement.
  suffices h : ∀ n, ∀ {u v : α} (π : Walk G u v),
      π.length ≤ n → π.IsDirected →
        ∃ σ : Walk G u v, σ.IsDirected ∧ σ.IsPath by
    intro u v π hdir; exact h π.length π le_rfl hdir
  intro n
  induction n with
  | zero =>
    intro u v π hlen hdir
    have hπlen : π.length = 0 := Nat.le_zero.mp hlen
    -- length-0 walks are nil, hence paths.
    cases π with
    | nil => exact ⟨Walk.nil u, by trivial, by simp [Walk.IsPath]⟩
    | cons _ _ => simp [Walk.length_cons] at hπlen
  | succ n ih =>
    intro u v π hlen hdir
    by_cases hpath : π.IsPath
    · exact ⟨π, hdir, hpath⟩
    · -- Extract a duplicate.
      obtain ⟨p, q, hpq, hq, heq⟩ := exists_dup_positions_of_not_isPath π hpath
      have hp_le : p ≤ π.length := le_trans (le_of_lt hpq) hq
      -- Construct spliced walk σ' := (π.prefix p) ⧺ (cast (π.suffix q))
      let suf' : Walk G (π.nodeAt p) v := heq.symm ▸ π.suffix q
      let σ' : Walk G u v := (π.prefix p).append suf'
      -- σ' is directed: both halves are directed.
      have hpre_dir : (π.prefix p).IsDirected := isDirected_prefix π p hdir
      have hsuf_dir : (π.suffix q).IsDirected := isDirected_suffix π q hdir
      have hsuf'_dir : suf'.IsDirected := by
        change (heq.symm ▸ π.suffix q : Walk G (π.nodeAt p) v).IsDirected
        rw [isDirected_subst_left heq.symm (π.suffix q)]
        exact hsuf_dir
      have hσ_dir : σ'.IsDirected := isDirected_append _ _ hpre_dir hsuf'_dir
      -- σ' has length < π.length.
      have hpre_len : (π.prefix p).length = p := Walk.length_prefix π hp_le
      have hsuf_len : (π.suffix q).length = π.length - q := Walk.length_suffix π hq
      have hsuf'_len : suf'.length = π.length - q := by
        change (heq.symm ▸ π.suffix q : Walk G (π.nodeAt p) v).length = π.length - q
        rw [length_subst_left heq.symm (π.suffix q)]
        exact hsuf_len
      have hσ_len : σ'.length = p + (π.length - q) := by
        rw [Walk.length_append, hpre_len, hsuf'_len]
      have hlt : σ'.length < π.length := by
        rw [hσ_len]
        have hqp : π.length - q < π.length - p := by omega
        omega
      -- Apply IH at the smaller length.
      have hbound : σ'.length ≤ n := by omega
      exact ih σ' hbound hσ_dir

/-! ### Reverse-directed analogs -/

/-- If a walk's reverse is directed and every position lies in `Sc^G(scenter)`,
every interior position is an unblockable non-collider. Mirror of
`isUnblockableNonColliderAt_interior_of_directed_in_Sc` via `_reverse_iff`. -/
theorem isUnblockableNonColliderAt_interior_of_reverseDirected_in_Sc :
    ∀ {u w : α} (π : Walk G u w) {scenter : α},
      π.reverse.IsDirected →
      (∀ k, k ≤ π.length → π.nodeAt k ∈ G.Sc scenter) →
      ∀ k, 0 < k → k < π.length → π.IsUnblockableNonColliderAt k := by
  intro u w π scenter h_rev_dir h_inSc k h_pos h_lt
  -- Build h_rev_inSc for π.reverse via `nodeAt_reverse`.
  have h_rev_inSc : ∀ ℓ, ℓ ≤ π.reverse.length → π.reverse.nodeAt ℓ ∈ G.Sc scenter := by
    intro ℓ hℓ
    have hℓ' : ℓ ≤ π.length := by rw [Walk.length_reverse] at hℓ; exact hℓ
    rw [Walk.nodeAt_reverse π hℓ']
    exact h_inSc (π.length - ℓ) (by omega)
  -- Apply forward version to π.reverse at position π.length - k.
  have h_pos_rev : 0 < π.length - k := by omega
  have h_lt_rev : π.length - k < π.reverse.length := by
    rw [Walk.length_reverse]; omega
  have h_at_rev : π.reverse.IsUnblockableNonColliderAt (π.length - k) :=
    isUnblockableNonColliderAt_interior_of_directed_in_Sc π.reverse
      h_rev_dir h_rev_inSc (π.length - k) h_pos_rev h_lt_rev
  -- Transport π.reverse.IsUnblockableNonColliderAt (π.length - k) to π via _reverse_iff
  -- with k' = π.length - k:  π.reverse.IsUnblockableNonColliderAt (π.length - k) ↔
  --                          π.IsUnblockableNonColliderAt (π.length - (π.length - k)).
  have h_iff := Walk.isUnblockableNonColliderAt_reverse_iff π (π.length - k)
  have h_at_π : π.IsUnblockableNonColliderAt (π.length - (π.length - k)) := h_iff.mp h_at_rev
  have h_eq : π.length - (π.length - k) = k := by omega
  rw [h_eq] at h_at_π
  exact h_at_π

/-- A walk whose reverse is directed has no colliders anywhere. -/
theorem not_isColliderAt_of_isReverseDirected :
    ∀ {u w : α} (π : Walk G u w) (k : ℕ),
      π.reverse.IsDirected → ¬ π.IsColliderAt k := by
  intro u w π k h_rev_dir h_coll
  have hk : k ≤ π.length := le_of_lt (Walk.isColliderAt_lt_length _ h_coll)
  -- π.IsColliderAt k ↔ π.reverse.IsColliderAt (π.length - k), via isColliderAt_reverse_iff.
  have h_at_rev : π.reverse.IsColliderAt (π.length - k) := by
    rw [Walk.isColliderAt_reverse_iff π (π.length - k)]
    rw [show π.length - (π.length - k) = k from by omega]
    exact h_coll
  exact not_isColliderAt_of_isDirected π.reverse _ h_rev_dir h_at_rev

/-! ### Walk append left-cancellation -/

/-- Left-cancellation for `Walk.append`: if `p₁.append p₂ = p₁'.append p₂'` and the
prefix lengths agree, then the prefixes are equal as walks. This is the walk analog
of `List.append_left_inj`. -/
theorem append_left_inj :
    ∀ {u v w : α} (p₁ p₁' : Walk G u v) (p₂ p₂' : Walk G v w),
      p₁.append p₂ = p₁'.append p₂' → p₁.length = p₁'.length →
      p₁ = p₁' ∧ p₂ = p₂' := by
  intro u v w p₁
  induction p₁ with
  | nil _ =>
    intro p₁' p₂ p₂' h_eq h_len
    cases p₁' with
    | nil _ =>
      rw [Walk.nil_append, Walk.nil_append] at h_eq
      exact ⟨rfl, h_eq⟩
    | @cons _ _ _ s p =>
      simp [Walk.length_nil, Walk.length_cons] at h_len
  | @cons _ _ _ s p ih =>
    intro p₁' p₂ p₂' h_eq h_len
    cases p₁' with
    | nil _ =>
      simp [Walk.length_nil, Walk.length_cons] at h_len
    | @cons _ wx _ s' p' =>
      rw [Walk.cons_append, Walk.cons_append] at h_eq
      have h_len' : p.length = p'.length := by
        simp [Walk.length_cons] at h_len; exact h_len
      -- From cons.inj, derive structural equalities.
      have ⟨h_wx_eq, h_s_eq, h_rest_eq⟩ := Walk.cons.inj h_eq
      subst h_wx_eq
      have h_s_eq' : s = s' := eq_of_heq h_s_eq
      subst h_s_eq'
      have h_app_eq : p.append p₂ = p'.append p₂' := eq_of_heq h_rest_eq
      obtain ⟨h_p_eq, h_p₂_eq⟩ := ih p' p₂ p₂' h_app_eq h_len'
      subst h_p_eq
      exact ⟨rfl, h_p₂_eq⟩

/-! ### (ii.b) first-collider induction

The hypothesis bundle uses an auxiliary vertex variable `wi` (= `π.nodeAt i`) and a
separate equality, instead of embedding `π.nodeAt i` directly in the type of the
walk-step. This prevents motive-incorrect-type errors during the induction's
structural rewrites. -/

/-- For sub-case (ii.b) of `replace_walk`: given a walk `π` with positions `i + n < π.length`,
`0 < i`, `0 < n`, an arrow-at-target left edge at position `i`, and an arrow-at-source right
edge at position `i + n`, there is a collider position `k ∈ [i, i + n]` of `π` with
`π.nodeAt i ∈ G.Anc (π.nodeAt k)`. -/
theorem exists_collider_with_anc :
    ∀ {u v : α} (π : Walk G u v) (n : ℕ),
      ∀ {i : ℕ}, 0 < n → 0 < i → i + n < π.length →
      (∃ (wim1 wi : α) (p_pre : Walk G u wim1) (s_left : WalkStep G wim1 wi)
          (rest : Walk G wi v),
        π = p_pre.append (Walk.cons s_left rest) ∧
        wi = π.nodeAt i ∧
        p_pre.length = i - 1 ∧
        s_left.HasArrowheadAtTarget) →
      (∃ (wjp1 wj : α) (s_right : WalkStep G wj wjp1) (p_pre_j : Walk G u wj)
          (rest_j : Walk G wjp1 v),
        π = p_pre_j.append (Walk.cons s_right rest_j) ∧
        wj = π.nodeAt (i + n) ∧
        p_pre_j.length = i + n ∧
        s_right.HasArrowheadAtSource) →
      ∃ k, i ≤ k ∧ k ≤ i + n ∧ π.IsColliderAt k ∧ π.nodeAt i ∈ G.Anc (π.nodeAt k) := by
  intro u v π n
  induction n with
  | zero => intros; omega
  | succ n' ih =>
    intro i hn_pos hi_pos hijπ h_arr_left h_arr_right
    classical
    obtain ⟨wim1, wi, p_pre, s_left, rest, h_decomp, h_wi_eq, h_p_pre_len, h_s_left_arr⟩ :=
      h_arr_left
    -- Subst wi with π.nodeAt i.
    subst h_wi_eq
    -- Now s_left : WalkStep G wim1 (π.nodeAt i); same as before, but the subst was explicit.
    -- Extract π's step at position i (first step of `rest`).
    have h_rest_pos : 1 ≤ rest.length := by
      have h_len_eq : (p_pre.append (Walk.cons s_left rest)).length =
          p_pre.length + 1 + rest.length := by
        rw [Walk.length_append, Walk.length_cons]; omega
      have hπ_len : π.length = p_pre.length + 1 + rest.length := by
        have h1 : π.length = (p_pre.append (Walk.cons s_left rest)).length := by
          exact congrArg Walk.length h_decomp
        rw [h1, h_len_eq]
      omega
    obtain ⟨wip1, s_at_i, rest_at_i, h_rest_eq⟩ := walk_pos_eq_cons rest h_rest_pos
    have hπ_full : π = p_pre.append (Walk.cons s_left (Walk.cons s_at_i rest_at_i)) :=
      h_decomp.trans (congrArg (p_pre.append ·)
        (congrArg (Walk.cons s_left) h_rest_eq))
    have h_pos_form : (p_pre.length + 1 : ℕ) = i := by omega
    have h_vi_mem : π.nodeAt i ∈ G :=
      nodeAt_mem_G_of_pos_le_length π hi_pos (le_of_lt (by omega : i < π.length))
    -- Case on collider at i.
    by_cases h_coll_i : π.IsColliderAt i
    · exact ⟨i, le_refl i, by omega, h_coll_i, ⟨h_vi_mem, Walk.nil _, by trivial⟩⟩
    · -- ¬ collider at i.  s_at_i is forward.
      -- π.IsColliderAt i (via hπ_full) ↔ joint condition at (p_pre.length + 1).
      -- Show: ¬ s_at_i.HasArrowheadAtSource.
      have h_no_src : ¬ s_at_i.HasArrowheadAtSource := by
        intro hsrc
        apply h_coll_i
        have h_at_p : (p_pre.append (Walk.cons s_left (Walk.cons s_at_i rest_at_i))).IsColliderAt
            (p_pre.length + 1) :=
          (Walk.isColliderAt_append_cons_cons_one p_pre s_left s_at_i rest_at_i).mpr
            ⟨h_s_left_arr, hsrc⟩
        have h_at_W : π.IsColliderAt (p_pre.length + 1) := by
          rw [hπ_full]; exact h_at_p
        convert h_at_W using 2
        omega
      have h_s_at_i_fwd : s_at_i.IsForward := by
        cases s_at_i with
        | forward _ => simp
        | backward _ => simp at h_no_src
        | bidir _ => simp at h_no_src
      have h_s_at_i_arr : s_at_i.HasArrowheadAtTarget := by
        cases s_at_i with
        | forward _ => simp
        | backward _ => simp at h_s_at_i_fwd
        | bidir _ => simp at h_s_at_i_fwd
      -- π.nodeAt (i + 1) = wip1.
      have h_wip1_eq : wip1 = π.nodeAt (i + 1) := by
        have h_at_i1 : π.nodeAt (i + 1) = wip1 := by
          have h_full : π.nodeAt (i + 1) =
              (p_pre.append (Walk.cons s_left (Walk.cons s_at_i rest_at_i))).nodeAt (i + 1) :=
            congrArg (fun w => w.nodeAt (i + 1)) hπ_full
          rw [h_full]
          have h_pos : i + 1 = p_pre.length + 2 := by omega
          rw [h_pos]
          rw [Walk.nodeAt_append_add_left p_pre _ 2]
          -- (cons s_left (cons s_at_i rest_at_i)).nodeAt 2 = (cons s_at_i rest_at_i).nodeAt 1 = rest_at_i.nodeAt 0 = wip1.
          rw [Walk.nodeAt_cons_succ, Walk.nodeAt_cons_succ, Walk.nodeAt_zero]
        exact h_at_i1.symm
      -- π.nodeAt i ∈ G.Anc wip1 via forward step.
      have h_anc_step : π.nodeAt i ∈ G.Anc wip1 := by
        refine ⟨h_vi_mem, ?_⟩
        cases s_at_i with
        | forward h_e => exact ⟨Walk.cons (WalkStep.forward h_e) (Walk.nil _), by trivial⟩
        | backward _ => simp at h_s_at_i_fwd
        | bidir _ => simp at h_s_at_i_fwd
      -- Case on n'.
      rcases Nat.eq_zero_or_pos n' with hn'_zero | hn'_pos
      · -- n = 1: collider at i + 1.
        subst hn'_zero
        rw [Nat.add_zero] at h_arr_right hijπ
        obtain ⟨wjp1, wj, s_right, p_pre_j, rest_j, h_decomp_j, h_wj_eq, h_p_pre_j_len, h_s_right_arr⟩ :=
          h_arr_right
        -- We have wj = π.nodeAt (i + 1).
        -- Build π.IsColliderAt (i + 1).
        -- π = p_pre_j ⧺ cons s_right rest_j with p_pre_j.length = i + 1.
        -- π.IsColliderAt (i + 1) iff (last step of p_pre_j).HasArrowheadAtTarget ∧ s_right.HasArrowheadAtSource.
        -- p_pre_j has length i + 1 ≥ 1 (since i ≥ 1).  Extract its last step.
        have h_p_pre_j_pos : 1 ≤ p_pre_j.length := by omega
        obtain ⟨w_pj_last, p_pj_pre, s_p_pre_j_last, h_p_pre_j_eq⟩ :=
          walk_pos_eq_append_last p_pre_j h_p_pre_j_pos
        -- p_pj_pre.length = (i + 1) - 1 = i.
        have h_p_pj_pre_len : p_pj_pre.length = i := by
          have h1 : p_pre_j.length = p_pj_pre.length +
              (Walk.cons s_p_pre_j_last (Walk.nil _)).length := by
            rw [h_p_pre_j_eq, Walk.length_append]
          rw [Walk.length_cons, Walk.length_nil] at h1
          omega
        -- π = (p_pj_pre ⧺ cons s_p_pre_j_last (nil _)) ⧺ cons s_right rest_j.
        -- = p_pj_pre ⧺ cons s_p_pre_j_last (cons s_right rest_j).
        have h_alt_decomp : π = p_pj_pre.append (Walk.cons s_p_pre_j_last
            (Walk.cons s_right rest_j)) := by
          rw [h_decomp_j, h_p_pre_j_eq]
          rw [Walk.append_assoc, Walk.cons_append, Walk.nil_append]
        -- π.IsColliderAt (p_pj_pre.length + 1) iff s_p_pre_j_last.HasArrowheadAtTarget ∧ s_right.HasArrowheadAtSource.
        -- Derive w_pj_last = π.nodeAt i first (so types align for append_left_inj).
        have h_w_pj_last_eq : w_pj_last = π.nodeAt i := by
          have h1 : π.nodeAt p_pj_pre.length =
              (p_pj_pre.append (Walk.cons s_p_pre_j_last (Walk.cons s_right rest_j))).nodeAt
                p_pj_pre.length :=
            congrArg (fun w => w.nodeAt p_pj_pre.length) h_alt_decomp
          rw [Walk.nodeAt_append_le _ _ (le_refl _)] at h1
          rw [Walk.nodeAt_length] at h1
          rw [h_p_pj_pre_len] at h1
          exact h1.symm
        -- Now we can identify types.
        subst h_w_pj_last_eq
        -- Now p_pj_pre : Walk G u (π.nodeAt i), and s_p_pre_j_last : WalkStep G (π.nodeAt i) wj.
        have hπ_alt_full :
            π = (p_pre.append (Walk.cons s_left (Walk.nil _))).append
              (Walk.cons s_at_i rest_at_i) := by
          have h1 : (p_pre.append (Walk.cons s_left (Walk.nil (π.nodeAt i)))).append
              (Walk.cons s_at_i rest_at_i) =
              p_pre.append (Walk.cons s_left (Walk.cons s_at_i rest_at_i)) := by
            rw [Walk.append_assoc, Walk.cons_append, Walk.nil_append]
          exact hπ_full.trans h1.symm
        have h_prefix_len :
            (p_pre.append (Walk.cons s_left (Walk.nil (π.nodeAt i)))).length =
              p_pj_pre.length := by
          rw [Walk.length_append, Walk.length_cons, Walk.length_nil]; omega
        have h_walks_eq :
            (p_pre.append (Walk.cons s_left (Walk.nil _))).append
                (Walk.cons s_at_i rest_at_i) =
              p_pj_pre.append (Walk.cons s_p_pre_j_last (Walk.cons s_right rest_j)) :=
          hπ_alt_full.symm.trans h_alt_decomp
        obtain ⟨_, h_tail_eq⟩ :=
          append_left_inj (p_pre.append (Walk.cons s_left (Walk.nil (π.nodeAt i))))
            p_pj_pre (Walk.cons s_at_i rest_at_i)
            (Walk.cons s_p_pre_j_last (Walk.cons s_right rest_j))
            h_walks_eq h_prefix_len
        -- h_tail_eq : cons s_at_i rest_at_i = cons s_p_pre_j_last (cons s_right rest_j).
        obtain ⟨h_w_eq, h_s_eq, _h_rest_eq⟩ := Walk.cons.inj h_tail_eq
        -- subst h_w_eq to align types.
        subst h_w_eq
        have h_s_eq' : s_at_i = s_p_pre_j_last := eq_of_heq h_s_eq
        have h_coll_at_alt :
            (p_pj_pre.append (Walk.cons s_p_pre_j_last
                (Walk.cons s_right rest_j))).IsColliderAt (p_pj_pre.length + 1) := by
          rw [Walk.isColliderAt_append_cons_cons_one]
          refine ⟨?_, h_s_right_arr⟩
          rw [← h_s_eq']
          exact h_s_at_i_arr
        have h_eq_coll :
            π.IsColliderAt (p_pj_pre.length + 1) =
              (p_pj_pre.append (Walk.cons s_p_pre_j_last
                (Walk.cons s_right rest_j))).IsColliderAt (p_pj_pre.length + 1) :=
          congrArg (fun w : Walk G u v => w.IsColliderAt (p_pj_pre.length + 1)) h_alt_decomp
        have h_coll_at : π.IsColliderAt (p_pj_pre.length + 1) := h_eq_coll ▸ h_coll_at_alt
        -- Conclude: collider at p_pj_pre.length + 1 = i + 1.
        refine ⟨i + 1, by omega, by omega, ?_, ?_⟩
        · convert h_coll_at using 2
          omega
        · rw [h_wip1_eq] at h_anc_step
          exact h_anc_step
      · -- n' ≥ 1.  Recurse with i + 1.
        -- Build new arrow-left for i + 1.
        have h_arr_left_next :
            ∃ (wim1' wi' : α) (p_pre' : Walk G u wim1') (s_left' : WalkStep G wim1' wi')
              (rest' : Walk G wi' v),
            π = p_pre'.append (Walk.cons s_left' rest') ∧
            wi' = π.nodeAt (i + 1) ∧
            p_pre'.length = (i + 1) - 1 ∧
            s_left'.HasArrowheadAtTarget := by
          refine ⟨π.nodeAt i, wip1, p_pre.append (Walk.cons s_left (Walk.nil _)),
            s_at_i, rest_at_i, ?_, h_wip1_eq, ?_, h_s_at_i_arr⟩
          · -- π = (p_pre ⧺ cons s_left (nil _)) ⧺ cons s_at_i rest_at_i.
            have h_alt : (p_pre.append (Walk.cons s_left (Walk.nil (π.nodeAt i)))).append
                (Walk.cons s_at_i rest_at_i) =
                p_pre.append (Walk.cons s_left (Walk.cons s_at_i rest_at_i)) := by
              rw [Walk.append_assoc, Walk.cons_append, Walk.nil_append]
            exact hπ_full.trans h_alt.symm
          · rw [Walk.length_append, Walk.length_cons, Walk.length_nil]; omega
        -- Build new arrow-right for i + 1 + n' = i + (n' + 1) = i + n.
        have h_arr_right_next :
            ∃ (wjp1' wj' : α) (s_right' : WalkStep G wj' wjp1') (p_pre_j' : Walk G u wj')
              (rest_j' : Walk G wjp1' v),
            π = p_pre_j'.append (Walk.cons s_right' rest_j') ∧
            wj' = π.nodeAt ((i + 1) + n') ∧
            p_pre_j'.length = (i + 1) + n' ∧
            s_right'.HasArrowheadAtSource := by
          have h_idx_eq : (i + 1) + n' = i + (n' + 1) := by omega
          rw [h_idx_eq]; exact h_arr_right
        have hi1_pos : 0 < i + 1 := by omega
        have hi1n'π : (i + 1) + n' < π.length := by
          have : i + (n' + 1) < π.length := hijπ
          omega
        obtain ⟨k', h_k'_ge, h_k'_le, h_πColl, h_anc⟩ :=
          ih hn'_pos hi1_pos hi1n'π h_arr_left_next h_arr_right_next
        refine ⟨k', by omega, by omega, h_πColl, ?_⟩
        rw [h_wip1_eq] at h_anc_step
        exact CDMG.anc_trans h_anc_step h_anc

end Walk

end Causality
