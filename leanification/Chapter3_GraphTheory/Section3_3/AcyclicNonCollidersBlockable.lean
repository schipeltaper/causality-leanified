import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable

namespace Causality

/-!
# Acyclic ⟹ every non-collider position is blockable (`claim_3_20`)

This file formalises the LN remark `claim_3_20`
(`\label{rem-AcyclicNonCollidersBlockable}` in `graphs.tex`):

> If `G` is acyclic then all non-colliders are blockable.

The authoritative spec is the rewritten canonical tex statement at
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

## Intended Lean shape

* `G : CDMG Node` explicit, mirroring the LN's "Let `G` be a CDMG"
  standing hypothesis.
* `hG : G.IsAcyclic` from `def_3_6` (`Acyclicity.lean`) — the
  acyclicity hypothesis is named exactly as in the LN.
* `{u v : Node}` implicit (synthesised from the walk's type), `(π :
  Walk G u v)` and `(k : ℕ)` explicit, mirroring the binder shape of
  `def_3_16`'s `IsBlockableNonCollider`.
* Conclusion is the implication
  `π.IsNonCollider k → π.IsBlockableNonCollider k`, exactly as the
  rewritten canonical tex spells it.
* No separate `k ≤ π.length` hypothesis is needed: `IsNonCollider`
  already carries `k ≤ p.length` as a conjunct, so out-of-range `k`
  makes the antecedent `False` and the implication vacuous — matching
  the LN's "for every position `k ∈ {0, …, n}`" scoping.

The proof body is filled in by `prove_claim_in_lean` (Manager B),
following the to-be-written tex proof at
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

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: acyclic_non_colliders_blockable
-- ref: claim_3_20
-- If `G` is an acyclic CDMG (`def_3_6`), then for every walk `π` in
-- `G` (`def_3_4` item i.) and every position `k`, being a non-collider
-- at `k` (`def_3_15` item i.) implies being a blockable non-collider
-- at `k` (`def_3_16`).
/-
LN tex (rewritten canonical statement for `claim_3_20`):

  Let G = (J, V, E, L) be a CDMG and suppose G is acyclic (def_3_6).
  Then, for every integer n ≥ 0, every walk
    π = (v_0, a_0, v_1, a_1, ..., v_{n-1}, a_{n-1}, v_n)
  in G (def_3_4 item i.), and every position k ∈ {0, 1, ..., n}, the
  following implication holds:
    (k is a non-collider on π per def_3_15 item i.)
      ⟹  (k is a blockable non-collider on π per def_3_16).
-/
-- ## Design choice
--
-- *Per-walk-per-position implication shape: `(π, k)` universally
--   quantified at the binder level, the implication
--   `IsNonCollider k → IsBlockableNonCollider k` in the
--   conclusion.*  The LN's one-liner "all non-colliders are
--   blockable" universally quantifies over both the walk `π` and
--   the position `k`.  Because the per-position predicates
--   `IsNonCollider` (`def_3_15`) and `IsBlockableNonCollider`
--   (`def_3_16`) are *both* indexed by `(p : Walk G u v) (k : ℕ)`,
--   the natural Lean shape lifts the `(π, k)` universal quantifier
--   to the theorem's binder list and leaves the conclusion as the
--   *per-position* implication.  This mirrors the per-walk-per-
--   position structure of `def_3_15` and `def_3_16` verbatim —
--   neither definition wraps its `(p, k)` indices in an explicit
--   `∀`, and neither does this claim.  An alternative
--   `∀ π k, π.IsNonCollider k → π.IsBlockableNonCollider k` form
--   pushed *inside* the conclusion would be logically equivalent
--   but break the chapter-wide binder-level convention and force
--   consumers to apply the explicit quantifier before reading off
--   the implication.
--
-- *`G : CDMG Node` and `hG : G.IsAcyclic` as explicit theorem
--   binders, in that order, before `π` and `k`.*  The LN's "Let
--   `G` be a CDMG and suppose `G` is acyclic" is the *standing*
--   hypothesis of the row; the walk `π` and position `k` then
--   range *under* it ("for every walk ... for every position ...").
--   Mirrors the binder convention of `claim_3_19`
--   (`MarginalizingOutThe.lean`) and matches the LN's layered
--   "let ... then for every ..." quantification.
--
-- *CDMG-hood structural (typed), acyclicity propositional —
--   intentional split, matching the addition's "ambient structure"
--   reading.*  The addition
--   `[acyclic_does_not_imply_directed_in_text]` reads: "in this
--   remark `G` is a CDMG, as fixed by the surrounding context; the
--   hypothesis '`G` is acyclic' is to be read as acyclicity in the
--   CDMG sense, so the edge orientations needed to define
--   (non-)colliders are already part of the ambient structure".
--   We encode the two halves asymmetrically: the CDMG-hood of `G`
--   is enforced *at the type level* by `G : CDMG Node` (no
--   separate hypothesis), which is the literal Lean rendering of
--   "ambient structure"; the acyclicity is carried by the
--   *propositional* hypothesis `hG : G.IsAcyclic`, using `def_3_6`'s
--   `Acyclicity` predicate verbatim (the only piece the LN actually
--   *names* as a hypothesis).  Bundling both into a typeclass
--   `[AcyclicCDMG Node G]` or a structured `CADMG`-style sub-type
--   was rejected: most of Section 3.3's per-position predicates
--   (`def_3_15`, `def_3_16`) and the surrounding claim infrastructure
--   take a CDMG-typed `G` without any acyclicity hypothesis at all,
--   so keeping acyclicity as an opt-in `Prop`-level binder maximally
--   aligns with how the LN composes hypotheses across the section.
--
-- *`{u v : Node}` implicit (synthesised from the walk).*  Mirrors
--   the binder shape of `def_3_16`'s `IsBlockableNonCollider`
--   (`{u v : Node} (p : Walk G u v) (k : ℕ)`): the endpoints are
--   determined by the walk's type and never need to be named at the
--   call site.  Reusing the exact same binder shape keeps the
--   theorem's signature ergonomically compatible with dot-notation
--   consumers like `π.IsNonCollider k`.
--
-- *Conclusion `π.IsNonCollider k → π.IsBlockableNonCollider k`,
--   implication-in-conclusion form (not double-conjunction).*
--   Transports the LN's literal "(non-collider) ⟹ (blockable
--   non-collider)" English phrasing word-for-word into Lean,
--   reusing the per-position predicates of `def_3_15` and
--   `def_3_16` character-for-character.  Note the *definitional
--   duplicate*: by `def_3_16`, `IsBlockableNonCollider :=
--   IsNonCollider ∧ ¬ IsUnblockableNonCollider`, so the conclusion
--   `π.IsBlockableNonCollider k` already contains the antecedent
--   `π.IsNonCollider k` as its first conjunct.  Two alternatives
--   were considered and rejected:
--     (i) the leaner form
--         `π.IsNonCollider k → ¬ π.IsUnblockableNonCollider k`,
--         which drops the redundant first conjunct on the right.
--         Rejected because it forces every downstream consumer to
--         re-assemble the `IsBlockableNonCollider` conjunction at
--         the call site before it can use the LN-named "blockable
--         non-collider" predicate; keeping the conclusion as
--         `IsBlockableNonCollider k` lets a consumer with
--         `π.IsNonCollider k` in scope obtain the LN-named
--         predicate in a single step, without first having to
--         unfold `def_3_16`'s definition.
--     (ii) hoisting the antecedent to a theorem hypothesis
--         `(hk : π.IsNonCollider k)`, which would be logically
--         equivalent but would drift from the LN's
--         implication-in-conclusion form ("all non-colliders are
--         blockable" is an *implication*, not a hypothesis-style
--         claim).
--
-- *No separate `k ≤ π.length` hypothesis on `k`.*  Out-of-range
--   positions `k > π.length` make `π.IsNonCollider k = False` (the
--   `k ≤ p.length` conjunct of `IsNonCollider` fails), so the
--   implication is vacuous and an explicit bound is redundant.
--   Matches the LN's "every position `k ∈ {0, …, n}`" scope, carried
--   implicitly by `IsNonCollider`'s own in-range conjunct.
--
-- *Theorem name `acyclic_non_colliders_blockable`.*  Reads directly
--   off the LN row title `AcyclicNonCollidersBlockable`, in
--   `snake_case` matching the chapter convention for top-level
--   `theorem`/`lemma` names.  Placed in `namespace Causality.CDMG`
--   so that the standing hypothesis `G : CDMG Node` aligns with the
--   namespace and the implementation can use dot-notation on `G`
--   freely without an extra `open` directive.
-- claim_3_20 -- start statement
theorem acyclic_non_colliders_blockable
    (G : CDMG Node) (hG : G.IsAcyclic)
    {u v : Node} (π : Walk G u v) (k : ℕ) :
    π.IsNonCollider k → π.IsBlockableNonCollider k
-- claim_3_20 -- end statement
:= by
  -- The proof translates the verified TeX proof at
  -- `tex/claim_3_20_proof_AcyclicNonCollidersBlockable.tex`.
  --
  -- Unfolding `IsBlockableNonCollider = IsNonCollider ∧
  -- ¬ IsUnblockableNonCollider`, the implication reduces to: assume
  -- the non-collider hypothesis (B1) and ¬ unblockable (B2).  Clause
  -- (B1) is the hypothesis; for (B2) we assume `hu : IsUnblockable…`
  -- and derive `False`.
  --
  -- Once `hu` is in scope, `IsUnblockableNonCollider`'s clauses force
  -- the position to be strictly interior (`1 ≤ k` from clause (ii)
  -- and `k + 1 ≤ π.length` from the `π.vertices[k + 1]? = some …`
  -- conjunct of clause (iii)).  So the end-position case of the TeX
  -- proof never arises: destructuring `hu` immediately places us in
  -- the interior case.  From there the TeX proof's Step 2.1–2.5
  -- cascade goes through:
  --
  --   * Step 2.1: from `IsNonCollider`'s `ah_π(k) ≤ 1` clause (= `¬
  --     IsCollider k`), one of `a_{k - 1}` / `a_k` is not into `v_k`.
  --   * Step 2.2: by the `WalkStep` relation at that slot, the
  --     "not-into" forces a directed walk-edge `(v_k, w) ∈ E` whose
  --     other endpoint `w` is on `π`.
  --   * Step 2.3: the unblockable implication at that slot gives
  --     `w ∈ Sc^G(v_k) ⊆ Anc^G(v_k)`, supplying a directed walk
  --     `ρ : Walk G w v_k`.
  --   * Step 2.4: prepending the single edge `(v_k, w)` to `ρ`
  --     yields a directed walk `v_k ⤳ v_k` of length `≥ 1`.
  --   * Step 2.5: contradicts `hG : G.IsAcyclic`.
  intro hk_nc
  refine ⟨hk_nc, ?_⟩
  intro hu
  obtain ⟨_, hk_pos, vkm1, vk, vkp1,
          hv_km1, hv_k, hv_kp1, h_km1_impl, h_k_impl⟩ := hu
  -- Extract the walk-edge at index `k` and the corresponding
  -- `WalkStep` relation, named in terms of `vk` and `vkp1`.
  obtain ⟨a_k, he_k, hWS_k⟩ := Walk.walkStep_at_vertices π hv_k hv_kp1
  -- Extract the walk-edge at index `k - 1` (and its `WalkStep`
  -- relation `G.WalkStep vkm1 a_km1 vk`).  We need the vertex
  -- Option-membership at position `(k - 1) + 1 = k`; rewrite `hv_k`.
  have hk_succ : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
  have hv_k' : π.vertices[k - 1 + 1]? = some vk := by rw [hk_succ]; exact hv_k
  obtain ⟨a_km1, he_km1, hWS_km1⟩ := Walk.walkStep_at_vertices π hv_km1 hv_k'
  -- Now `hWS_km1 : G.WalkStep vkm1 a_km1 vk` and
  --     `hWS_k   : G.WalkStep vk a_k vkp1`,
  -- with `he_km1 : π.edges[k - 1]? = some a_km1` and
  --     `he_k   : π.edges[k]? = some a_k`.
  -- Use `¬ IsCollider` to derive `¬ G.into vk a_km1 ∨ ¬ G.into vk a_k`.
  obtain ⟨_, h_notCol⟩ := hk_nc
  have h_notBothInto : ¬ (G.into vk a_km1 ∧ G.into vk a_k) := by
    rintro ⟨h1, h2⟩
    exact h_notCol ⟨hk_pos, vk, a_km1, a_k, hv_k, he_km1, he_k, h1, h2⟩
  -- Case-split on which walk-incident edge fails the "into" predicate.
  rcases not_and_or.mp h_notBothInto with hni_km1 | hni_k
  · -- ===== Case A: `¬ G.into vk a_km1`. =====
    -- The WalkStep at `k - 1` is `G.WalkStep vkm1 a_km1 vk`, with the
    -- forward writing `a_km1 = (vkm1, vk)` forcing `into` (via E or L
    -- clause).  Hence the only way for `¬ into` is the backward
    -- writing `a_km1 = (vk, vkm1) ∧ a_km1 ∈ E` — the desired outgoing
    -- walk-edge of `v_k`.
    rcases hWS_km1 with ⟨ha_eq, ha_EL⟩ | ⟨ha_eq, ha_E⟩
    · -- Forward writing: contradicts `¬ G.into vk a_km1`.
      exfalso; apply hni_km1
      rcases ha_EL with ha_E | ha_L
      · left
        refine ⟨ha_E, ?_⟩
        rw [ha_eq]
      · right
        refine ⟨ha_L, ?_⟩
        right; rw [ha_eq]
    · -- Backward writing: `a_km1 = (vk, vkm1) ∧ a_km1 ∈ G.E`.
      have h_edge_in_E : (vk, vkm1) ∈ G.E := ha_eq ▸ ha_E
      have he_km1_eq : π.edges[k - 1]? = some (vk, vkm1) := ha_eq ▸ he_km1
      have h_vkm1_Sc : vkm1 ∈ G.Sc vk := h_km1_impl ⟨he_km1_eq, h_edge_in_E⟩
      have h_vkm1_Anc : vkm1 ∈ G.Anc vk := h_vkm1_Sc.1
      obtain ⟨_, ρ, h_ρ_dir⟩ := h_vkm1_Anc
      -- Build the cycle by prepending the single edge `(vk, vkm1)` to ρ.
      have hstep : G.WalkStep vk (vk, vkm1) vkm1 := Or.inl ⟨rfl, Or.inl h_edge_in_E⟩
      let ρ_tilde : Walk G vk vk := Walk.cons vkm1 (vk, vkm1) hstep ρ
      have h_ρt_dir : ρ_tilde.IsDirectedWalk := ⟨rfl, h_edge_in_E, h_ρ_dir⟩
      have h_ρt_len : ρ_tilde.length ≥ 1 := by
        change ρ.length + 1 ≥ 1; omega
      have h_vk_in_G : vk ∈ G := (G.hE_subset h_edge_in_E).1
      exact hG vk h_vk_in_G ⟨ρ_tilde, h_ρt_dir, h_ρt_len⟩
  · -- ===== Case B: `¬ G.into vk a_k`. =====
    -- Symmetrically: the WalkStep at `k` has the backward writing
    -- `a_k = (vkp1, vk) ∈ E` forcing `into v_k` (via E-clause), so
    -- the only way for `¬ into` is the forward writing
    -- `a_k = (vk, vkp1)` with `a_k ∈ E` (taking `a_k ∈ L` would
    -- force `into` via the L-clause).
    rcases hWS_k with ⟨ha_eq, ha_EL⟩ | ⟨ha_eq, ha_E⟩
    · rcases ha_EL with ha_E | ha_L
      · -- `a_k = (vk, vkp1) ∧ a_k ∈ E`: desired outgoing walk-edge.
        have h_edge_in_E : (vk, vkp1) ∈ G.E := ha_eq ▸ ha_E
        have he_k_eq : π.edges[k]? = some (vk, vkp1) := ha_eq ▸ he_k
        have h_vkp1_Sc : vkp1 ∈ G.Sc vk := h_k_impl ⟨he_k_eq, h_edge_in_E⟩
        have h_vkp1_Anc : vkp1 ∈ G.Anc vk := h_vkp1_Sc.1
        obtain ⟨_, ρ, h_ρ_dir⟩ := h_vkp1_Anc
        have hstep : G.WalkStep vk (vk, vkp1) vkp1 := Or.inl ⟨rfl, Or.inl h_edge_in_E⟩
        let ρ_tilde : Walk G vk vk := Walk.cons vkp1 (vk, vkp1) hstep ρ
        have h_ρt_dir : ρ_tilde.IsDirectedWalk := ⟨rfl, h_edge_in_E, h_ρ_dir⟩
        have h_ρt_len : ρ_tilde.length ≥ 1 := by
          change ρ.length + 1 ≥ 1; omega
        have h_vk_in_G : vk ∈ G := (G.hE_subset h_edge_in_E).1
        exact hG vk h_vk_in_G ⟨ρ_tilde, h_ρt_dir, h_ρt_len⟩
      · -- `a_k = (vk, vkp1) ∈ L`: contradicts `¬ G.into vk a_k` via L-clause.
        exfalso; apply hni_k
        right
        refine ⟨ha_L, ?_⟩
        left; rw [ha_eq]
    · -- Backward writing `a_k = (vkp1, vk) ∈ E`: contradicts `¬ into` via E-clause.
      exfalso; apply hni_k
      left
      refine ⟨ha_E, ?_⟩
      rw [ha_eq]
-- REFACTOR-BLOCK-ORIGINAL-END: acyclic_non_colliders_blockable

-- ## Design choice — refactor block (`blockable_noncollider_first`)
--
-- *Why the conclusion is now `refactor_IsBlockableNonCollider`,
--   not the original `IsBlockableNonCollider`.*  The root refactor
--   `blockable_noncollider_first` swapped `def_3_16`'s
--   primary/derived split (see `BlockableAndUnblockable.lean`'s
--   REPLACEMENT block): blockable now reads off the LN's
--   elaboration disjunction directly (end-position OR outgoing
--   walk-edge of `v_k` to a node outside `G.Sc vk`), and unblockable
--   is the derived complement on the non-collider sub-class.  This
--   row's *LN statement* is unchanged — the
--   `[acyclic_does_not_imply_directed_in_text]` addition
--   (acyclicity read in the CDMG sense, via `def_3_6`) and the
--   binder shape `(G : CDMG Node) (hG : G.IsAcyclic) {u v} (π :
--   Walk G u v) (k : ℕ)` are inherited verbatim from the original
--   (see the design-choice block above the ORIGINAL marker for the
--   layered "let G ... then for every walk ..." rationale).  Only
--   the Lean encoding of "blockable" flipped from a double-negated
--   existential to a positive disjunction.  Accordingly the proof
--   is now *constructive* — exhibit a disjunction witness — rather
--   than the original negation-by-contradiction on
--   `IsUnblockableNonCollider`.
--
-- *High-level proof structure: case-split on `k`, mirroring the
--   tex twin's Cases A / B / C
--   (`tex/refactor_claim_3_20_proof_AcyclicNonCollidersBlockable.tex`).*
--   Cases A (`k = 0`) and B (`k = π.length`) pick the end-position
--   disjuncts of `refactor_IsBlockableNonCollider` directly via
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
--   `∃`-disjunct of `refactor_IsBlockableNonCollider` (Step C.3).
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
--   exactly the witness the refactored disjunction-form predicate
--   asks for at every interior non-collider position.  We re-
--   derive this contrapositive *pointwise* on the witness `w`
--   we already have, rather than factoring out a separate
--   `∀ v, G.Sc v = {v}` lemma and specialising — pointwise is
--   cheaper, stays close to the tex twin, and avoids committing
--   to a `Set` extensionality formulation that downstream refactor
--   rows do not depend on.
--
-- *Reuses file-level helpers, adds no new ones.*
--   `Walk.walkStep_at` and `Walk.walkStep_at_vertices` (above the
--   original theorem) are refactor-neutral structural
--   infrastructure on walk vertex/edge data; reused as-is.  Both
--   are `private`, matching the chapter convention of keeping
--   single-file proof support outside the public namespace.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: acyclic_non_colliders_blockable (was: refactor_acyclic_non_colliders_blockable)
-- ref: claim_3_20 (refactor twin)
-- Refactor twin of `acyclic_non_colliders_blockable`, targeting the
-- new `refactor_IsBlockableNonCollider` positive-disjunction
-- predicate (`def_3_16`'s replacement block).
-- claim_3_20 -- start statement
theorem refactor_acyclic_non_colliders_blockable
    (G : CDMG Node) (hG : G.IsAcyclic)
    {u v : Node} (π : Walk G u v) (k : ℕ) :
    π.IsNonCollider k → π.refactor_IsBlockableNonCollider k
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
-- REFACTOR-BLOCK-REPLACEMENT-END: acyclic_non_colliders_blockable

end CDMG

end Causality
