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

end Causality

namespace Causality

namespace CDMG

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Matches the
--   chapter convention used by every `CDMG`-opening file.
--
-- *Three-dash `--- start helper` / `--- end helper` markers.*  The
--   implicit `Node` + `DecidableEq Node` infrastructure is
--   statement-typing material, not the formalised LN content; the
--   three-dash flavour is the chapter convention for that distinction.
-- claim_3_20 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_20 --- end helper

-- Helper — packages the acyclicity-cycle argument once.  Given a
-- directed edge `(x, y) ∈ G.E` and `G.IsAcyclic`, the
-- target `y` cannot lie in the strongly connected component
-- `G.Sc x` — otherwise prepending `(x, y)` to a directed
-- walk `y → x` (witnessed by `y ∈ G.Anc x`) yields a
-- non-trivial directed walk `x → x`, contradicting acyclicity.
--
-- ## Design choice — outgoing_E_not_in_Sc
--
-- *Why factor out as a separate helper.*  The cycle-construction
--   argument fires at two slot branches inside
--   `blocking_interior_helper`; lifting it to its own lemma removes
--   the duplication and makes the load-bearing acyclicity-to-non-Sc
--   translation visible at the call site.
--
-- *Why prepend rather than append.*  The directed walk `ρ : y → x`
--   from `y ∈ Anc x` provides the right shape for prepending the
--   single step `(x, y) ∈ G.E` at the head: the resulting cons-cell
--   `.cons y (.forwardE hxy) ρ : Walk G x x` has source `x`,
--   middle vertex `y`, and target `x` — a non-trivial closed
--   directed walk based at `x`.
private lemma outgoing_E_not_in_Sc
    {G : CDMG Node} (hG : G.IsAcyclic)
    {x y : Node} (hxy : (x, y) ∈ G.E) : y ∉ G.Sc x := by
  intro h_in_Sc
  -- y ∈ Sc x → y ∈ Anc x → directed walk y → x.
  have h_y_Anc : y ∈ G.Anc x := h_in_Sc.1
  obtain ⟨_, ρ, h_ρ_dir⟩ := h_y_Anc
  -- Prepend (x, y) ∈ G.E as a `.forwardE`-step to get a closed
  -- directed walk x → x of length ≥ 1.
  let ρ_tilde : Walk G x x :=
    Walk.cons y (.forwardE hxy) ρ
  have h_ρt_dir : ρ_tilde.IsDirectedWalk := h_ρ_dir
  have h_ρt_len : ρ_tilde.length ≥ 1 := by
    change ρ.length + 1 ≥ 1
    omega
  have h_x_in_G : x ∈ G := (G.hE_subset hxy).1
  exact hG x h_x_in_G ⟨ρ_tilde, h_ρt_dir, h_ρt_len⟩


set_option linter.style.longLine false in
-- Helper — induction on the walk `π`, base-case `nil` discharged by
-- `Walk.length = 0`, inductive step pattern-matches the outer
-- cons-cons head, the substantive interior case `k = 1` reads `s₀`
-- and `s₁` off the head pair, and the inductive `k = m + 2` step
-- delegates to the IH on the tail walk.  The per-step "arrowhead at
-- v_k" reading uses the constructor-tag pair `s₀.HeadAtTarget` /
-- `s₁.HeadAtSource` from `def_3_15`.
--
-- ## Design choice — blocking_interior_helper
--
-- *Unfolding at the cons-cons-(k=1) pattern.*  At position 1 the
--   hypothesis `¬ π.IsCollider 1` unfolds to
--   `¬ (s₀.HeadAtTarget ∧ s₁.HeadAtSource)`.  `not_and_or` splits
--   the conjunction; each disjunct case-splits on the relevant
--   `WalkStep` constructor.
--
-- *Why the L-disjunct branches stay trivially dischargeable.*  At each
--   `cases s₀`/`cases s₁` constructor branch the matcher reduces
--   `HeadAtTarget` / `HeadAtSource` to one of two values:
--   - `True` on the "natural-side head" branches (`.forwardE _` for
--     target, `.backwardE _` for source, `.bidir _` for both);
--     `¬ True` is absurd, discharged via `absurd trivial h_n*`.
--   - The opposite-channel L-disjunct on the writing-mirror branches
--     (`.backwardE _` for target, `.forwardE _` for source) reduces
--     to `s(u, v) ∈ G.L`.  The proof does not need to inspect that
--     L-disjunct's truth value: the constructor parameter
--     `h : (vMid, _) ∈ G.E` (or `(_, vMid) ∈ G.E`, depending on side)
--     is the witness used here.  `outgoing_E_not_in_Sc hG h`
--     discharges the matching `HasBlockingLeftSlot 1` /
--     `HasBlockingRightSlot 1` goal directly.
private lemma blocking_interior_helper
    {G : CDMG Node} (hG : G.IsAcyclic) :
    ∀ {u v : Node} (π : Walk G u v) (k : ℕ),
      1 ≤ k → k < π.length → ¬ π.IsCollider k →
      π.HasBlockingLeftSlot k ∨ π.HasBlockingRightSlot k := by
  intro u v π
  induction π with
  | nil v hv =>
      intro k hk_pos hk_lt _
      -- length (.nil _ _) = 0, so k < 0 is impossible.
      simp [Walk.length] at hk_lt
  | @cons uOuter wOuter vMid s₀ π_rest ih =>
      intro k hk_pos hk_lt h_notCol
      cases π_rest with
      | nil v hv =>
          -- Outer length = 1; combined with 1 ≤ k and k < 1 → impossible.
          simp [Walk.length] at hk_lt
          omega
      | @cons _ _ vNext s₁ π_rest_rest =>
          -- Substantive interior case: outer walk is cons-cons.
          -- Outer cons-cell: source = uOuter, middle = vMid, terminus = wOuter
          -- Inner cons-cell: source = vMid, middle = vNext, terminus = wOuter
          match k, hk_pos, hk_lt, h_notCol with
          | 0, hk_pos, _, _ => exact absurd hk_pos (by decide)
          | 1, _, _, h_notCol =>
              -- Position 1: read s₀ and s₁ off the head pair.
              -- IsCollider at (cons vMid s₀ (cons _ s₁ _), 1)
              -- = s₀.HeadAtTarget ∧ s₁.HeadAtSource.
              have h_notBoth :
                  ¬ (s₀.HeadAtTarget ∧ s₁.HeadAtSource) :=
                h_notCol
              rcases not_and_or.mp h_notBoth with h_n0 | h_n1
              · -- ¬ s₀.HeadAtTarget → s₀ must be .backwardE.
                cases s₀ with
                | forwardE h =>
                    -- HeadAtTarget on .forwardE _ reduces to True.
                    exact absurd trivial h_n0
                | backwardE h =>
                    -- h : (vMid, uOuter) ∈ G.E.
                    -- HasBlockingLeftSlot at (.cons vMid (.backwardE _) _, 1)
                    -- = uOuter ∉ G.Sc vMid.
                    refine Or.inl ?_
                    change uOuter ∉ G.Sc vMid
                    exact outgoing_E_not_in_Sc hG h
                | bidir h =>
                    -- HeadAtTarget on .bidir _ reduces to True.
                    exact absurd trivial h_n0
              · -- ¬ s₁.HeadAtSource → s₁ must be .forwardE.
                cases s₁ with
                | forwardE h =>
                    -- h : (vMid, vNext) ∈ G.E.
                    -- HasBlockingRightSlot at outer cons-cons-(k=1):
                    -- recurses to (cons vNext (.forwardE _) _).HasBlockingRightSlot 0
                    -- = vNext ∉ G.Sc vMid.
                    refine Or.inr ?_
                    -- The outer recursion at k+1 = 1 needs s₀ to be destructed before
                    -- the matcher can route to the wildcard-cons cons-pattern.
                    cases s₀ with
                    | forwardE _ =>
                        change vNext ∉ G.Sc vMid
                        exact outgoing_E_not_in_Sc hG h
                    | backwardE _ =>
                        change vNext ∉ G.Sc vMid
                        exact outgoing_E_not_in_Sc hG h
                    | bidir _ =>
                        change vNext ∉ G.Sc vMid
                        exact outgoing_E_not_in_Sc hG h
                | backwardE h =>
                    -- HeadAtSource on .backwardE _ reduces to True.
                    exact absurd trivial h_n1
                | bidir h =>
                    -- HeadAtSource on .bidir _ reduces to True.
                    exact absurd trivial h_n1
          | m + 2, _, hk_lt, h_notCol =>
              -- Inductive step.  Outer walk is cons (vMid) s₀ tail
              -- where tail = cons vNext s₁ π_rest_rest.  The recursion
              -- equations:
              --   IsCollider (cons _ _ p) (m + 2)
              --     = p.IsCollider (m + 1)
              --   HasBlockingLeftSlot (cons _ _ p) (m + 2)
              --     = p.HasBlockingLeftSlot (m + 1)
              --   HasBlockingRightSlot (cons _ _ p) (m + 2)
              --     = p.HasBlockingRightSlot (m + 1)
              -- bring the goal into the form of the inner walk at m + 1.
              have h_notCol_inner :
                  ¬ (Walk.cons vNext s₁ π_rest_rest).IsCollider (m + 1) := by
                exact h_notCol
              have hk_lt_inner :
                  m + 1 < (Walk.cons vNext s₁ π_rest_rest).length := by
                have hlen :
                    (Walk.cons vMid s₀
                      (Walk.cons vNext s₁ π_rest_rest)).length
                       = (Walk.cons vNext s₁ π_rest_rest).length + 1 := rfl
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


set_option linter.style.longLine false in
-- ## Design choice — acyclic_non_colliders_blockable
--
-- *Three-case proof structure.*  The proof splits on the position `k`:
--   `Case A: k = 0` (left end), `Case B: k = π.length` (right end),
--   `Case C: 1 ≤ k < π.length` (interior).  The interior case is
--   delegated to `blocking_interior_helper`; the disjunct routing via
--   `Or.inl` / `Or.inr (Or.inl _)` / `Or.inr (Or.inr (Or.inl _))` /
--   `Or.inr (Or.inr (Or.inr _))` mirrors the four-disjunct shape of
--   `IsBlockableNonCollider`.
-- ref: claim_3_20
-- claim_3_20 -- start statement
theorem acyclic_non_colliders_blockable
    (G : CDMG Node) (hG : G.IsAcyclic)
    {u v : Node} (π : Walk G u v) (k : ℕ) :
    π.IsNonCollider k → π.IsBlockableNonCollider k
-- claim_3_20 -- end statement
:= by
  intro h_nc
  refine ⟨h_nc, ?_⟩
  -- Case A — left end-position (k = 0).
  by_cases h0 : k = 0
  · exact Or.inl h0
  -- Case B — right end-position (k = π.length).
  by_cases hn : k = π.length
  · exact Or.inr (Or.inl hn)
  -- Case C — interior position (1 ≤ k ∧ k < π.length).
  have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h0
  obtain ⟨hk_le, h_notCol⟩ := h_nc
  have hk_lt : k < π.length := lt_of_le_of_ne hk_le hn
  rcases blocking_interior_helper hG π k hk_pos hk_lt h_notCol with hL | hR
  · exact Or.inr (Or.inr (Or.inl hL))
  · exact Or.inr (Or.inr (Or.inr hR))

end CDMG

end Causality
