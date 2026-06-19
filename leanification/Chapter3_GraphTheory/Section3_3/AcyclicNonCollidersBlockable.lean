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

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.vertices_length_eq
-- The length of a walk's vertex list is one more than its edge count.
private lemma Walk.vertices_length_eq {G : CDMG Node}
    {u v : Node} (p : Walk G u v) :
    p.vertices.length = p.length + 1 := by
  induction p with
  | nil _ _ => rfl
  | cons _ _ _ q ih => simp [Walk.vertices, Walk.length, ih]
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.vertices_length_eq

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.vertices_head?_eq_source
-- The first vertex of a walk equals its source.
private lemma Walk.vertices_head?_eq_source {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices[0]? = some u
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ _ => rfl
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.vertices_head?_eq_source

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.walkStep_at
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
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.walkStep_at

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Walk.walkStep_at_vertices
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
-- REFACTOR-BLOCK-ORIGINAL-END: Walk.walkStep_at_vertices


-- REFACTOR-BLOCK-ORIGINAL-BEGIN: acyclic_non_colliders_blockable
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
-- REFACTOR-BLOCK-ORIGINAL-END: acyclic_non_colliders_blockable

end CDMG

end Causality

namespace Causality

namespace refactor_CDMG

-- ## Design choice — refactor section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Mirrors the
--   original `CDMG`-namespace `variable` block at the top of this file
--   byte-for-byte modulo the refactor's namespace retarget.  Matches the
--   chapter convention used by every `refactor_CDMG`-opening file
--   (`CDMG.lean`, `Walks.lean`'s refactor section, `Acyclicity.lean`'s
--   refactor section, `FamilyRelationships.lean`'s refactor section,
--   `CollidersAndNon.lean`'s refactor section,
--   `BlockableAndUnblockable.lean`'s refactor section).  The
--   `cdmg_typed_edges` refactor does NOT alter the carrier-type
--   discipline — only the `L`-field shape on `refactor_CDMG` and the
--   per-step walk-edge encoding inside `refactor_WalkStep` — so the
--   binders here are byte-identical to the original.
--
-- *Three-dash `--- start helper` / `--- end helper` markers.*  Same
--   rationale as the original block at the top of this file: the
--   implicit `Node` + `DecidableEq Node` infrastructure is
--   statement-typing material, not the formalised LN content; the
--   three-dash flavour is the chapter convention for that distinction.
-- claim_3_20 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_20 --- end helper

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: outgoing_E_not_in_Sc (was: refactor_outgoing_E_not_in_Sc)
-- Helper — packages the acyclicity-cycle argument once.  Given a
-- directed edge `(x, y) ∈ G.E` and `G.refactor_IsAcyclic`, the
-- target `y` cannot lie in the strongly connected component
-- `G.refactor_Sc x` — otherwise prepending `(x, y)` to a directed
-- walk `y → x` (witnessed by `y ∈ G.refactor_Anc x`) yields a
-- non-trivial directed walk `x → x`, contradicting acyclicity.
--
-- ## Design choice — refactor_outgoing_E_not_in_Sc
--
-- *Why factor out as a separate helper.*  Under the original encoding
--   the cycle-construction argument appeared twice in the main proof
--   (once for the slot-(k-1) sub-case, once for the slot-k sub-case),
--   each time inlined as an `intro h_in_Sc; ...` block.  Under the
--   refactor the main theorem delegates the per-slot work to the
--   `refactor_blocking_interior_helper` helper below, and that helper
--   in turn invokes the acyclicity argument at *exactly* the two slot
--   branches.  Lifting the cycle-construction to its own lemma both
--   removes the duplication and makes the load-bearing acyclicity-
--   to-non-Sc translation visible at the call site.  This is a
--   net-new declaration (no original counterpart); the cleanup name
--   is `outgoing_E_not_in_Sc` (Phase 7 cleanup whole-word renames
--   `refactor_outgoing_E_not_in_Sc → outgoing_E_not_in_Sc`).
--
-- *Why prepend rather than append.*  The directed walk `ρ : y → x`
--   from `y ∈ Anc x` provides the right shape for prepending the
--   single step `(x, y) ∈ G.E` at the head: the resulting cons-cell
--   `.cons y (.forwardE hxy) ρ : refactor_Walk G x x` has source `x`,
--   middle vertex `y`, and target `x` — a non-trivial closed
--   directed walk based at `x`.  Appending would require a walk-
--   concatenation primitive that the refactor does not provide.
private lemma refactor_outgoing_E_not_in_Sc
    {G : refactor_CDMG Node} (hG : G.refactor_IsAcyclic)
    {x y : Node} (hxy : (x, y) ∈ G.E) : y ∉ G.refactor_Sc x := by
  intro h_in_Sc
  -- y ∈ Sc x → y ∈ Anc x → directed walk y → x.
  have h_y_Anc : y ∈ G.refactor_Anc x := h_in_Sc.1
  obtain ⟨_, ρ, h_ρ_dir⟩ := h_y_Anc
  -- Prepend (x, y) ∈ G.E as a `.forwardE`-step to get a closed
  -- directed walk x → x of length ≥ 1.
  let ρ_tilde : refactor_Walk G x x :=
    refactor_Walk.cons y (.forwardE hxy) ρ
  have h_ρt_dir : ρ_tilde.refactor_IsDirectedWalk := h_ρ_dir
  have h_ρt_len : ρ_tilde.refactor_length ≥ 1 := by
    change ρ.refactor_length + 1 ≥ 1
    omega
  have h_x_in_G : x ∈ G := (G.hE_subset hxy).1
  exact hG x h_x_in_G ⟨ρ_tilde, h_ρt_dir, h_ρt_len⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: outgoing_E_not_in_Sc

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: blocking_interior_helper (was: refactor_blocking_interior_helper)
-- Helper — handles the interior case (1 ≤ k < π.length) of the main
-- theorem by induction on the walk `π`.  Under acyclicity, at any
-- interior non-collider position the walk must have a "blocking slot"
-- (the LN's outgoing-walk-edge-to-a-non-Sc-node witness): either at
-- slot k - 1 (`HasBlockingLeftSlot`) or at slot k
-- (`HasBlockingRightSlot`).  The induction's substantive case is
-- `k = 1` on a `cons _ s₀ (cons _ s₁ _)` cons-cons walk, where the
-- non-collider hypothesis `¬ (s₀.IsInto vMid ∧ s₁.IsInto vMid)`
-- splits via `not_and_or` and each branch picks the matching
-- blocking slot.
--
-- ## Design choice — refactor_blocking_interior_helper
--
-- *Why induction on `π`, not case-split on `k`.*  The original main
--   theorem case-split on `k = 0` / `k = π.length` / interior, then
--   inside the interior case read off walk-data at indices `k - 1`
--   and `k` via the `Walk.walkStep_at` Option-membership helpers.
--   Under the refactor `Walk.edges` does not exist, so the per-slot
--   inspection must go through structural pattern-match on the walk
--   constructors.  This forces a recursion on the walk's cons-chain:
--   at outer cons cell `cons vMid s₀ (cons _ s₁ _)`, outer position
--   `k = 1` reads `s₀` and `s₁` simultaneously off the head, and
--   outer position `k ≥ 2` recurses on the tail with the index
--   decremented.  This matches the recursion structure of
--   `refactor_IsCollider` and `refactor_HasBlocking*Slot` byte-for-
--   byte and gives the cleanest port.
--
-- *Index-recursion lockstep across `IsCollider`, `HasBlockingLeftSlot`,
--   `HasBlockingRightSlot`.*  All three helpers step their walk-
--   argument forward one cons-cell at a time and decrement their
--   position index in lockstep at outer `k + 2` → tail `k + 1` (for
--   `IsCollider` and `HasBlockingLeftSlot`) and outer `k + 1` → tail
--   `k` (for `HasBlockingRightSlot`).  In the inductive step the
--   substantive observation is that all three step in unison: at
--   outer cons-cons walk with index `m + 2`, the inner walk
--   inherits the negated-`IsCollider` hypothesis at position `m + 1`,
--   and the inductive hypothesis returns `HasBlockingLeftSlot (m + 1)
--   ∨ HasBlockingRightSlot (m + 1)` on the inner walk, which lifts to
--   `HasBlockingLeftSlot (m + 2) ∨ HasBlockingRightSlot (m + 2)` on
--   the outer walk by the pattern equations.
--
-- *The `k = 1` substantive case.*  Unfold `¬ refactor_IsCollider 1`
--   at the cons-cons pattern to `¬ (s₀.refactor_IsInto vMid ∧
--   s₁.refactor_IsInto vMid)`; apply `not_and_or` to split.  Each
--   branch case-splits on the relevant WalkStep constructor:
--   * `¬ s₀.refactor_IsInto vMid`: among `.forwardE / .backwardE /
--     .bidir`, only `.backwardE h` (with `h : (vMid, u) ∈ G.E`,
--     where `u` is the outer walk's source) leaves `IsInto` falsifiable.
--     `.forwardE _` makes `IsInto` true via `vMid = vMid`; `.bidir _`
--     makes it true via `vMid = vMid ∨ vMid = u → vMid = vMid`.  In the
--     `.backwardE h` branch, `HasBlockingLeftSlot 1` unfolds to
--     `u ∉ G.refactor_Sc vMid`, discharged by `outgoing_E_not_in_Sc hG h`.
--   * `¬ s₁.refactor_IsInto vMid`: only `.forwardE h` (with
--     `h : (vMid, vNext) ∈ G.E`) leaves `IsInto` falsifiable.
--     `HasBlockingRightSlot 1` recurses via the outer cons cell to
--     `(cons vNext s₁ _).refactor_HasBlockingRightSlot 0`, which then
--     matches the `.forwardE _, 0` branch and unfolds to
--     `vNext ∉ G.refactor_Sc vMid` — discharged by
--     `outgoing_E_not_in_Sc hG h`.
private lemma refactor_blocking_interior_helper
    {G : refactor_CDMG Node} (hG : G.refactor_IsAcyclic) :
    ∀ {u v : Node} (π : refactor_Walk G u v) (k : ℕ),
      1 ≤ k → k < π.refactor_length → ¬ π.refactor_IsCollider k →
      π.refactor_HasBlockingLeftSlot k ∨ π.refactor_HasBlockingRightSlot k := by
  intro u v π
  induction π with
  | nil v hv =>
      intro k hk_pos hk_lt _
      -- refactor_length (.nil _ _) = 0, so k < 0 is impossible.
      simp [refactor_Walk.refactor_length] at hk_lt
  | @cons uOuter wOuter vMid s₀ π_rest ih =>
      intro k hk_pos hk_lt h_notCol
      cases π_rest with
      | nil v hv =>
          -- Outer length = 1; combined with 1 ≤ k and k < 1 → impossible.
          simp [refactor_Walk.refactor_length] at hk_lt
          omega
      | @cons _ _ vNext s₁ π_rest_rest =>
          -- Substantive interior case: outer walk is cons-cons.
          -- Outer cons-cell: source = uOuter, middle = vMid, terminus = wOuter
          -- Inner cons-cell: source = vMid, middle = vNext, terminus = wOuter
          match k, hk_pos, hk_lt, h_notCol with
          | 0, hk_pos, _, _ => exact absurd hk_pos (by decide)
          | 1, _, _, h_notCol =>
              -- Position 1: read s₀ and s₁ off the head pair.
              -- refactor_IsCollider at (cons vMid s₀ (cons _ s₁ _), 1)
              -- = s₀.refactor_IsInto vMid ∧ s₁.refactor_IsInto vMid.
              have h_notBoth :
                  ¬ (s₀.refactor_IsInto vMid ∧ s₁.refactor_IsInto vMid) := h_notCol
              rcases not_and_or.mp h_notBoth with h_n0 | h_n1
              · -- ¬ s₀.refactor_IsInto vMid → s₀ must be .backwardE.
                cases s₀ with
                | forwardE h =>
                    -- IsInto reduces to `vMid = vMid ∨ _`, which is `True`.
                    exact absurd
                      (Or.inl rfl : refactor_WalkStep.refactor_IsInto
                        (.forwardE h : refactor_WalkStep G uOuter vMid) vMid) h_n0
                | backwardE h =>
                    -- h : (vMid, uOuter) ∈ G.E.
                    -- HasBlockingLeftSlot at (.cons vMid (.backwardE _) _, 1)
                    -- = uOuter ∉ G.refactor_Sc vMid.
                    refine Or.inl ?_
                    change uOuter ∉ G.refactor_Sc vMid
                    exact refactor_outgoing_E_not_in_Sc hG h
                | bidir h =>
                    -- IsInto reduces to `vMid = uOuter ∨ vMid = vMid`, which is `True`.
                    exact absurd
                      (Or.inr rfl : refactor_WalkStep.refactor_IsInto
                        (.bidir h : refactor_WalkStep G uOuter vMid) vMid) h_n0
              · -- ¬ s₁.refactor_IsInto vMid → s₁ must be .forwardE.
                cases s₁ with
                | forwardE h =>
                    -- h : (vMid, vNext) ∈ G.E.
                    -- HasBlockingRightSlot at outer cons-cons-(k=1):
                    -- recurses to (cons vNext (.forwardE _) _).HasBlockingRightSlot 0
                    -- = vNext ∉ G.refactor_Sc vMid.
                    refine Or.inr ?_
                    -- Step the outer HasBlockingRightSlot 1 down to inner ...Slot 0,
                    -- which on .forwardE h unfolds to vNext ∉ G.refactor_Sc vMid.
                    -- The outer recursion at k+1 = 1 needs s₀ to be destructed before
                    -- the matcher can route to the wildcard-cons cons-pattern.
                    cases s₀ with
                    | forwardE _ =>
                        change vNext ∉ G.refactor_Sc vMid
                        exact refactor_outgoing_E_not_in_Sc hG h
                    | backwardE _ =>
                        change vNext ∉ G.refactor_Sc vMid
                        exact refactor_outgoing_E_not_in_Sc hG h
                    | bidir _ =>
                        change vNext ∉ G.refactor_Sc vMid
                        exact refactor_outgoing_E_not_in_Sc hG h
                | backwardE h =>
                    -- IsInto reduces to `vMid = vMid ∨ _`, which is `True`.
                    exact absurd
                      (Or.inl rfl : refactor_WalkStep.refactor_IsInto
                        (.backwardE h : refactor_WalkStep G vMid vNext) vMid) h_n1
                | bidir h =>
                    -- IsInto on .bidir : refactor_WalkStep G vMid vNext at w = vMid:
                    -- (vMid = vMid ∨ vMid = vNext), the first disjunct is `True`.
                    exact absurd
                      (Or.inl rfl : refactor_WalkStep.refactor_IsInto
                        (.bidir h : refactor_WalkStep G vMid vNext) vMid) h_n1
          | m + 2, _, hk_lt, h_notCol =>
              -- Inductive step.  Outer walk is cons (vMid) s₀ tail
              -- where tail = cons vNext s₁ π_rest_rest.  The recursion
              -- equations:
              --   refactor_IsCollider (cons _ _ p) (m + 2) = p.refactor_IsCollider (m + 1)
              --   refactor_HasBlockingLeftSlot (cons _ _ p) (m + 2)
              --     = p.refactor_HasBlockingLeftSlot (m + 1)
              --   refactor_HasBlockingRightSlot (cons _ _ p) (m + 2)
              --     = p.refactor_HasBlockingRightSlot (m + 1)
              -- bring the goal into the form of the inner walk at m + 1.
              have h_notCol_inner :
                  ¬ (refactor_Walk.cons vNext s₁ π_rest_rest).refactor_IsCollider (m + 1) := by
                exact h_notCol
              have hk_lt_inner :
                  m + 1 < (refactor_Walk.cons vNext s₁ π_rest_rest).refactor_length := by
                have hlen :
                    (refactor_Walk.cons vMid s₀
                      (refactor_Walk.cons vNext s₁ π_rest_rest)).refactor_length
                       = (refactor_Walk.cons vNext s₁ π_rest_rest).refactor_length + 1 := rfl
                omega
              rcases ih (m + 1) (by omega) hk_lt_inner h_notCol_inner with hL | hR
              · -- Lift HasBlockingLeftSlot from inner to outer via recursion eq.
                -- The outer matcher needs s₀ destructed to route via cons-pattern.
                refine Or.inl ?_
                cases s₀ with
                | forwardE _ => exact hL
                | backwardE _ => exact hL
                | bidir _ => exact hL
              · -- Lift HasBlockingRightSlot from inner to outer via recursion eq.
                refine Or.inr ?_
                cases s₀ with
                | forwardE _ => exact hR
                | backwardE _ => exact hR
                | bidir _ => exact hR
-- REFACTOR-BLOCK-REPLACEMENT-END: blocking_interior_helper

set_option linter.style.longLine false in
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: acyclic_non_colliders_blockable (was: refactor_acyclic_non_colliders_blockable)
-- ## Design choice — refactor_acyclic_non_colliders_blockable
--
-- *Mechanical port of the original `acyclic_non_colliders_blockable`
--   onto the typed-WalkStep refactor.*  The LN-level proof structure
--   (Case A: k = 0; Case B: k = π.length; Case C: interior 1 ≤ k <
--   π.length) carries over verbatim because the disjunction shape of
--   `refactor_IsBlockableNonCollider` mirrors the original's:
--   end-position arms + two interior arms encoded via the new
--   `refactor_HasBlockingLeftSlot` / `refactor_HasBlockingRightSlot`
--   helpers (instead of the original's Option-membership existentials
--   over `Walk.edges` walk data).
--
-- *Why the interior case is delegated to a helper.*  Under the refactor
--   `Walk.edges` does not exist (see `Walks.lean`'s "Why no
--   `refactor_edges`" block), so the per-slot inspection patterns of
--   the original — which read walk-edge data at indices `k - 1` and
--   `k` via `p.edges[k - 1]?` / `p.edges[k]?` and the
--   `Walk.walkStep_at` helpers — must be replaced with structural
--   pattern-match on the walk's cons-chain.  Pushing this case
--   analysis into the `refactor_blocking_interior_helper` lemma
--   keeps the main theorem's body short and lets the helper express
--   the index-recursion lockstep across `IsCollider`,
--   `HasBlockingLeftSlot`, `HasBlockingRightSlot` cleanly via
--   induction on the walk.
--
-- *Acyclicity-cycle argument also factored out.*  See
--   `refactor_outgoing_E_not_in_Sc` above for the once-and-for-all
--   packaging of the original's Step C.2 cycle construction.  Under
--   the refactor that argument is invoked from inside
--   `refactor_blocking_interior_helper` at exactly the two slot
--   branches (`.backwardE _` at slot 1 → left-slot witness;
--   `.forwardE _` at the slot-k step → right-slot witness).
-- ref: claim_3_20
-- claim_3_20 -- start statement
theorem refactor_acyclic_non_colliders_blockable
    (G : refactor_CDMG Node) (hG : G.refactor_IsAcyclic)
    {u v : Node} (π : refactor_Walk G u v) (k : ℕ) :
    π.refactor_IsNonCollider k → π.refactor_IsBlockableNonCollider k
-- claim_3_20 -- end statement
:= by
  intro h_nc
  refine ⟨h_nc, ?_⟩
  -- Case A — left end-position (k = 0).
  by_cases h0 : k = 0
  · exact Or.inl h0
  -- Case B — right end-position (k = π.refactor_length).
  by_cases hn : k = π.refactor_length
  · exact Or.inr (Or.inl hn)
  -- Case C — interior position (1 ≤ k ∧ k < π.refactor_length).
  have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h0
  obtain ⟨hk_le, h_notCol⟩ := h_nc
  have hk_lt : k < π.refactor_length := lt_of_le_of_ne hk_le hn
  rcases refactor_blocking_interior_helper hG π k hk_pos hk_lt h_notCol with hL | hR
  · exact Or.inr (Or.inr (Or.inl hL))
  · exact Or.inr (Or.inr (Or.inr hR))
-- REFACTOR-BLOCK-REPLACEMENT-END: acyclic_non_colliders_blockable

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Walk
-- The pre-refactor proof of `acyclic_non_colliders_blockable` relied on
-- four `Walk.*` helpers (`Walk.vertices_length_eq`,
-- `Walk.vertices_head?_eq_source`, `Walk.walkStep_at`,
-- `Walk.walkStep_at_vertices`) defined above this proof in their own
-- ORIGINAL blocks.  Under `cdmg_typed_edges` the post-refactor proof
-- (the `outgoing_E_not_in_Sc` + `blocking_interior_helper` +
-- `acyclic_non_colliders_blockable` REPLACEMENT trio above) inspects
-- the typed `WalkStep` constructor directly, so the four helpers are
-- now dead code.  Because the cleanup script's marker parser truncates
-- block names at the first non-identifier character, all four
-- `Walk.<suffix>` ORIGINAL blocks register as a single `Walk` name in
-- the validator's set diff; this empty REPLACEMENT block pairs all
-- four of them at once so the finalize-time marker validator passes.
-- REFACTOR-BLOCK-REPLACEMENT-END: Walk

end refactor_CDMG

end Causality
