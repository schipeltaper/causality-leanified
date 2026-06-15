import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable

namespace Causality

/-!
# Acyclic ⟹ every non-collider position is blockable (`claim_3_20`)

This file formalises the LN remark `claim_3_20`
(`\label{rem-AcyclicNonCollidersBlockable}` in `graphs.tex`):

> If `G` is acyclic then all non-colliders are blockable.

The authoritative spec is the canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/`
`claim_3_20_statement_AcyclicNonCollidersBlockable.tex`,
verified equivalent to the LN block augmented with one operator
clarification:

* `[acyclic_does_not_imply_directed_in_text]` — in this remark `G` is a
  CDMG (per the surrounding context); "acyclic" means CDMG-acyclic per
  `def_3_6`.  The edge orientations needed to define (non-)colliders are
  already part of the ambient structure.

After the rewrite the LN's prose unfolds into the universally-
quantified implication: for every CDMG `G` with `G.IsAcyclic`, every
walk `π : Walk G u v` (per `def_3_4` item i.), and every position
`k : ℕ`, `π.IsNonCollider k → π.IsBlockableNonCollider k`, where the
per-position predicates are reused verbatim from `def_3_15`
(`CollidersAndNon.lean`) and `def_3_16` (`BlockableAndUnblockable.lean`).

## Lean shape

* `G : CDMG Node` explicit, mirroring the LN's "Let `G` be a CDMG"
  standing hypothesis.
* `hG : G.IsAcyclic` from `def_3_6` (`Acyclicity.lean`) — the
  acyclicity hypothesis is named exactly as in the LN.
* `{u v : Node}` implicit (synthesised from the walk's type), `(π :
  Walk G u v)` and `(k : ℕ)` explicit, mirroring the binder shape of
  `def_3_16`'s `IsBlockableNonCollider`.
* Conclusion is the implication
  `π.IsNonCollider k → π.IsBlockableNonCollider k`, exactly as the
  canonical tex spells it.
* No separate `k ≤ π.length` hypothesis is needed: `IsNonCollider`
  already carries `k ≤ p.length` as a conjunct, so out-of-range `k`
  makes the antecedent `False` and the implication vacuous — matching
  the LN's "for every position `k ∈ {0, …, n}`" scoping.

The proof follows the tex proof at
`tex/claim_3_20_proof_AcyclicNonCollidersBlockable.tex`.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited from
--   `def_3_15` (`CollidersAndNon.lean`) and `def_3_16`
--   (`BlockableAndUnblockable.lean`): both per-position predicates
--   require this shape, so the wrapped main theorem signature below
--   does not type-check without it.  Matches the chapter convention
--   set by every prior file in this chapter — including the directly
--   analogous claim-row `claim_3_19` (`MarginalizingOutThe.lean`),
--   which uses the same `{Node : Type*} [DecidableEq Node]` shape at
--   its own statement-typing helper block.
--
-- *Three-dash `--- start helper` / `--- end helper` markers, not
--   two-dash `-- start statement`.*  Lean 4's `variable` auto-binding
--   folds the implicit `Node` and the `DecidableEq Node` instance
--   into the theorem below — they are *statement-typing
--   infrastructure*, not the formalised LN content of this row, and
--   the `start statement` / `end statement` markers must wrap only
--   the LN-meaningful declaration head (the `theorem
--   acyclic_non_colliders_blockable …` line itself).  Wrapping the
--   `variable` line with three-dash helper markers is the standard
--   chapter-3 convention: see the analogous helper block in
--   `def_3_15`, `def_3_16`, and `claim_3_19` for prior art.
-- claim_3_20 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_20 --- end helper

-- Proof helpers (no markers).  Walk-position infrastructure used by
-- the main proof to extract the `WalkStep` relations at the two
-- walk-incident edges of an interior position `k`.  These are
-- proof-only — removing them would not break the wrapped main
-- theorem signature — so they carry no marker comments per the
-- chapter convention.

-- The length of a walk's vertex list is one more than its edge count.
private lemma Walk.vertices_length_eq {G : CDMG Node}
    {u v : Node} (p : Walk G u v) :
    p.vertices.length = p.length + 1 := by
  induction p with
  | nil _ _ => rfl
  | cons _ _ _ q ih => simp [Walk.vertices, Walk.length, ih]

-- The first vertex of a walk equals its source.
private lemma Walk.vertices_head?_eq_source {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices[0]? = some u
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ _ => rfl

-- At any in-range edge index `k < p.length`, the walk exposes the
-- vertex at position `k`, the vertex at position `k + 1`, the edge at
-- position `k`, and the `WalkStep` relation connecting them.  This is
-- the structural workhorse the main proof uses to read off the two
-- walk-incident edges at the interior position.
private lemma Walk.walkStep_at {G : CDMG Node} {u w : Node}
    (p : Walk G u w) (k : ℕ) (hk : k < p.length) :
    ∃ (xk xkp1 : Node) (a : Node × Node),
      p.vertices[k]? = some xk ∧
      p.vertices[k + 1]? = some xkp1 ∧
      p.edges[k]? = some a ∧
      G.WalkStep xk a xkp1 := by
  induction p generalizing k with
  | nil v hv => simp [Walk.length] at hk
  | @cons u_o w_o mid c step q ih =>
      cases k with
      | zero =>
          refine ⟨u_o, mid, c, ?_, ?_, ?_, step⟩
          · rfl
          · change q.vertices[0]? = some mid
            exact Walk.vertices_head?_eq_source q
          · rfl
      | succ k' =>
          have hkq : k' < q.length := by
            have hlen : (Walk.cons mid c step q).length = q.length + 1 := rfl
            omega
          obtain ⟨xk, xkp1, ae, hv_k, hv_kp1, he_k, hWS⟩ := ih k' hkq
          refine ⟨xk, xkp1, ae, ?_, ?_, ?_, hWS⟩
          · change q.vertices[k']? = some xk; exact hv_k
          · change q.vertices[k' + 1]? = some xkp1; exact hv_kp1
          · change q.edges[k']? = some ae; exact he_k

-- Caller-side convenience version: given vertex Option-memberships at
-- positions `k` and `k + 1`, return the walk-edge and its `WalkStep`
-- relation at index `k`.  This avoids `subst`-direction subtleties in
-- the main proof by letting the caller supply the desired variable
-- names for the walk-vertices upfront.
private lemma Walk.walkStep_at_vertices {G : CDMG Node} {u w : Node}
    (p : Walk G u w) {k : ℕ} {xk xkp1 : Node}
    (hv_k : p.vertices[k]? = some xk)
    (hv_kp1 : p.vertices[k + 1]? = some xkp1) :
    ∃ a, p.edges[k]? = some a ∧ G.WalkStep xk a xkp1 := by
  have hk_lt : k < p.length := by
    have h_vert_len : p.vertices.length = p.length + 1 := Walk.vertices_length_eq p
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hv_kp1
    omega
  obtain ⟨xk', xkp1', a, hv_k', hv_kp1', he_k, hWS⟩ := Walk.walkStep_at p k hk_lt
  have heq_xk : xk' = xk := Option.some.inj (hv_k'.symm.trans hv_k)
  have heq_xkp1 : xkp1' = xkp1 := Option.some.inj (hv_kp1'.symm.trans hv_kp1)
  rw [heq_xk, heq_xkp1] at hWS
  exact ⟨a, he_k, hWS⟩


-- ## Design choice — proof structure
--
-- *Conclusion is `IsBlockableNonCollider`, the positive-disjunction
--   form.*  `IsBlockableNonCollider` (`def_3_16`,
--   `BlockableAndUnblockable.lean`) reads off the LN's elaboration
--   disjunction directly: end-position OR outgoing walk-edge of
--   `v_k` to a node outside `G.Sc vk`.  `IsUnblockableNonCollider`
--   is the derived complement on the non-collider sub-class.
--   Stating the conclusion this way lets the proof be
--   *constructive* — exhibit a disjunction witness — rather than
--   negation-by-contradiction on `IsUnblockableNonCollider`.
--
-- *High-level proof structure: case-split on `k`, mirroring the
--   tex twin's Cases A / B / C
--   (`tex/claim_3_20_proof_AcyclicNonCollidersBlockable.tex`).*
--   Cases A (`k = 0`) and B (`k = π.length`) pick the end-position
--   disjuncts of `IsBlockableNonCollider` directly via
--   `Or.inl` / `Or.inr ∘ Or.inl`; both end-positions automatically
--   satisfy the predicate's `IsNonCollider` conjunct (vacuous via
--   the `1 ≤ k` guard of `IsCollider` at `k = 0`; vacuous via the
--   missing `p.edges[k]?` lookup at `k = π.length`), so the witness
--   is the disjunct label.  Case C (interior, `1 ≤ k < π.length`)
--   is the substantive case: extract an outgoing walk-edge
--   `(v_k, w) ∈ G.E` at slot `i* ∈ {k - 1, k}` from the
--   `IsNonCollider` precondition's `ah_π(k) ≤ 1` count combined
--   with the `WalkStep` relation (Step C.1 of the twin); prove
--   `w ∉ G.Sc vk` (Step C.2 — see the next paragraph for why);
--   plug `(v_k, w)` and `w ∉ G.Sc vk` into the matching
--   `∃`-disjunct of `IsBlockableNonCollider` (Step C.3).
--
-- *Why acyclicity does the work in Step C.2 — `G.IsAcyclic` forces
--   `G.Sc vk = {vk}`.*  The LN's one-line remark "if G is acyclic
--   then all non-colliders are blockable" hides the following.
--   Assume `w ∈ G.Sc vk` and the outgoing walk-edge `(vk, w) ∈ G.E`
--   from Step C.1.  Then `w ∈ G.Anc vk`, so there exists a
--   directed walk `ρ : w ⤳ vk` in `G`; prepending the edge
--   `(vk, w)` yields a directed walk `vk ⤳ vk` of length `≥ 1`,
--   contradicting `hG : G.IsAcyclic` (`def_3_6`) unless `w = vk`
--   — but `w = vk` would make `(vk, vk) ∈ G.E` a length-one
--   directed cycle, which `hG` also rules out.  So every outgoing
--   walk-edge of `vk` necessarily lands strictly outside `G.Sc vk`,
--   exactly the witness the disjunction-form predicate
--   asks for at every interior non-collider position.  We re-
--   derive this contrapositive *pointwise* on the witness `w`
--   we already have, rather than factoring out a separate
--   `∀ v, G.Sc v = {v}` lemma and specialising — pointwise is
--   cheaper, stays close to the tex twin, and avoids committing
--   to a `Set` extensionality formulation that downstream rows do
--   not depend on.
--
-- *Uses file-level helpers.*
--   `Walk.walkStep_at` and `Walk.walkStep_at_vertices` (above) are
--   structural infrastructure on walk vertex/edge data.  Both are
--   `private`, matching the chapter convention of keeping
--   single-file proof support outside the public namespace.
-- ref: claim_3_20
-- claim_3_20 -- start statement
theorem acyclic_non_colliders_blockable
    (G : CDMG Node) (hG : G.IsAcyclic)
    {u v : Node} (π : Walk G u v) (k : ℕ) :
    π.IsNonCollider k → π.IsBlockableNonCollider k
-- claim_3_20 -- end statement
:= by
  intro hk_nc
  refine ⟨hk_nc, ?_⟩
  -- Case A — left end position (k = 0).
  by_cases h0 : k = 0
  · exact Or.inl h0
  -- Case B — right end position (k = π.length).
  by_cases hn : k = π.length
  · exact Or.inr (Or.inl hn)
  -- Case C — interior position (1 ≤ k ∧ k < π.length).
  have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h0
  obtain ⟨hk_le, h_notCol⟩ := hk_nc
  have hk_lt : k < π.length := lt_of_le_of_ne hk_le hn
  -- Step C.1: extract walk data at indices k and k - 1.
  obtain ⟨vk, vkp1, a_k, hv_k, hv_kp1, he_k, hWS_k⟩ :=
    Walk.walkStep_at π k hk_lt
  have hkm1_lt : k - 1 < π.length := by omega
  obtain ⟨vkm1, _, _, hv_km1, _, _, _⟩ :=
    Walk.walkStep_at π (k - 1) hkm1_lt
  have hk_succ : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hv_k' : π.vertices[k - 1 + 1]? = some vk := by rw [hk_succ]; exact hv_k
  obtain ⟨a_km1, he_km1, hWS_km1⟩ :=
    Walk.walkStep_at_vertices π hv_km1 hv_k'
  -- Step C.1 cont.: from ¬ IsCollider derive ¬ G.into vk a_km1 ∨ ¬ G.into vk a_k.
  have h_notBothInto : ¬ (G.into vk a_km1 ∧ G.into vk a_k) := by
    rintro ⟨h1, h2⟩
    exact h_notCol ⟨hk_pos, vk, a_km1, a_k, hv_k, he_km1, he_k, h1, h2⟩
  rcases not_and_or.mp h_notBothInto with hni_km1 | hni_k
  · -- Sub-case (O1): ¬ G.into vk a_km1 forces a_km1 = (vk, vkm1) ∈ G.E.
    rcases hWS_km1 with ⟨ha_eq, ha_EL⟩ | ⟨ha_eq, ha_E⟩
    · -- Forward writing → into vk. Contradiction.
      exfalso; apply hni_km1
      rcases ha_EL with ha_E | ha_L
      · left
        refine ⟨ha_E, ?_⟩
        rw [ha_eq]
      · right
        refine ⟨ha_L, ?_⟩
        right; rw [ha_eq]
    · -- Backward writing: outgoing walk-edge (vk, vkm1) ∈ G.E.
      have h_edge_in_E : (vk, vkm1) ∈ G.E := ha_eq ▸ ha_E
      have he_km1_eq : π.edges[k - 1]? = some (vk, vkm1) := ha_eq ▸ he_km1
      -- Step C.2: vkm1 ∉ G.Sc vk via the cycle-construction acyclicity argument.
      have h_vkm1_not_Sc : vkm1 ∉ G.Sc vk := by
        intro h_in_Sc
        have h_vkm1_Anc : vkm1 ∈ G.Anc vk := h_in_Sc.1
        obtain ⟨_, ρ, h_ρ_dir⟩ := h_vkm1_Anc
        have hstep : G.WalkStep vk (vk, vkm1) vkm1 :=
          Or.inl ⟨rfl, Or.inl h_edge_in_E⟩
        let ρ_tilde : Walk G vk vk := Walk.cons vkm1 (vk, vkm1) hstep ρ
        have h_ρt_dir : ρ_tilde.IsDirectedWalk := ⟨rfl, h_edge_in_E, h_ρ_dir⟩
        have h_ρt_len : ρ_tilde.length ≥ 1 := by
          change ρ.length + 1 ≥ 1; omega
        have h_vk_in_G : vk ∈ G := (G.hE_subset h_edge_in_E).1
        exact hG vk h_vk_in_G ⟨ρ_tilde, h_ρt_dir, h_ρt_len⟩
      -- Step C.3: package as the (k - 1)-slot disjunct.
      exact Or.inr (Or.inr (Or.inl
        ⟨hk_pos, vkm1, vk, hv_km1, hv_k, he_km1_eq, h_edge_in_E, h_vkm1_not_Sc⟩))
  · -- Sub-case (O2): ¬ G.into vk a_k forces a_k = (vk, vkp1) ∈ G.E.
    rcases hWS_k with ⟨ha_eq, ha_EL⟩ | ⟨ha_eq, ha_E⟩
    · rcases ha_EL with ha_E | ha_L
      · -- Forward writing a_k = (vk, vkp1) ∈ E: outgoing walk-edge.
        have h_edge_in_E : (vk, vkp1) ∈ G.E := ha_eq ▸ ha_E
        have he_k_eq : π.edges[k]? = some (vk, vkp1) := ha_eq ▸ he_k
        -- Step C.2: vkp1 ∉ G.Sc vk via acyclicity.
        have h_vkp1_not_Sc : vkp1 ∉ G.Sc vk := by
          intro h_in_Sc
          have h_vkp1_Anc : vkp1 ∈ G.Anc vk := h_in_Sc.1
          obtain ⟨_, ρ, h_ρ_dir⟩ := h_vkp1_Anc
          have hstep : G.WalkStep vk (vk, vkp1) vkp1 :=
            Or.inl ⟨rfl, Or.inl h_edge_in_E⟩
          let ρ_tilde : Walk G vk vk := Walk.cons vkp1 (vk, vkp1) hstep ρ
          have h_ρt_dir : ρ_tilde.IsDirectedWalk := ⟨rfl, h_edge_in_E, h_ρ_dir⟩
          have h_ρt_len : ρ_tilde.length ≥ 1 := by
            change ρ.length + 1 ≥ 1; omega
          have h_vk_in_G : vk ∈ G := (G.hE_subset h_edge_in_E).1
          exact hG vk h_vk_in_G ⟨ρ_tilde, h_ρt_dir, h_ρt_len⟩
        -- Step C.3: package as the k-slot disjunct.
        exact Or.inr (Or.inr (Or.inr
          ⟨vk, vkp1, hv_k, hv_kp1, he_k_eq, h_edge_in_E, h_vkp1_not_Sc⟩))
      · -- Forward L: a_k = (vk, vkp1) ∈ L → into vk via L-clause. Contradiction.
        exfalso; apply hni_k
        right
        refine ⟨ha_L, ?_⟩
        left; rw [ha_eq]
    · -- Backward: a_k = (vkp1, vk) ∈ E → into vk via E-clause. Contradiction.
      exfalso; apply hni_k
      left
      refine ⟨ha_E, ?_⟩
      rw [ha_eq]

end CDMG

end Causality
