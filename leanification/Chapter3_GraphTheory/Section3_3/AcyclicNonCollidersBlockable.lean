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

-- ## Design choice — refactor section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Mirrors the
--   original `CDMG`-namespace `variable` block at the top of this file
--   byte-for-byte modulo the refactor's namespace retarget.  Matches the
--   chapter convention used by every `CDMG`-opening file
--   (`CDMG.lean`, `Walks.lean`'s refactor section, `Acyclicity.lean`'s
--   refactor section, `FamilyRelationships.lean`'s refactor section,
--   `CollidersAndNon.lean`'s refactor section,
--   `BlockableAndUnblockable.lean`'s refactor section).  The
--   `cdmg_typed_edges` refactor does NOT alter the carrier-type
--   discipline — only the `L`-field shape on `CDMG` and the
--   per-step walk-edge encoding inside `WalkStep` — so the
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

-- Helper — packages the acyclicity-cycle argument once.  Given a
-- directed edge `(x, y) ∈ G.E` and `G.IsAcyclic`, the
-- target `y` cannot lie in the strongly connected component
-- `G.Sc x` — otherwise prepending `(x, y)` to a directed
-- walk `y → x` (witnessed by `y ∈ G.Anc x`) yields a
-- non-trivial directed walk `x → x`, contradicting acyclicity.
--
-- ## Design choice — outgoing_E_not_in_Sc
--
-- *Why factor out as a separate helper.*  Under the original encoding
--   the cycle-construction argument appeared twice in the main proof
--   (once for the slot-(k-1) sub-case, once for the slot-k sub-case),
--   each time inlined as an `intro h_in_Sc; ...` block.  Under the
--   refactor the main theorem delegates the per-slot work to the
--   `blocking_interior_helper` helper below, and that helper
--   in turn invokes the acyclicity argument at *exactly* the two slot
--   branches.  Lifting the cycle-construction to its own lemma both
--   removes the duplication and makes the load-bearing acyclicity-
--   to-non-Sc translation visible at the call site.  This is a
--   net-new declaration (no original counterpart); the cleanup name
--   is `outgoing_E_not_in_Sc` (Phase 7 cleanup whole-word renames
--   `outgoing_E_not_in_Sc → outgoing_E_not_in_Sc`).
--
-- *Why prepend rather than append.*  The directed walk `ρ : y → x`
--   from `y ∈ Anc x` provides the right shape for prepending the
--   single step `(x, y) ∈ G.E` at the head: the resulting cons-cell
--   `.cons y (.forwardE hxy) ρ : Walk G x x` has source `x`,
--   middle vertex `y`, and target `x` — a non-trivial closed
--   directed walk based at `x`.  Appending would require a walk-
--   concatenation primitive that the refactor does not provide.
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

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: blocking_interior_helper
set_option linter.style.longLine false in
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
-- ## Design choice — blocking_interior_helper
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
--   `IsCollider` and `refactor_HasBlocking*Slot` byte-for-
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
-- *The `k = 1` substantive case.*  Unfold `¬ IsCollider 1`
--   at the cons-cons pattern to `¬ (s₀.IsInto vMid ∧
--   s₁.IsInto vMid)`; apply `not_and_or` to split.  Each
--   branch case-splits on the relevant WalkStep constructor:
--   * `¬ s₀.IsInto vMid`: among `.forwardE / .backwardE /
--     .bidir`, only `.backwardE h` (with `h : (vMid, u) ∈ G.E`,
--     where `u` is the outer walk's source) leaves `IsInto` falsifiable.
--     `.forwardE _` makes `IsInto` true via `vMid = vMid`; `.bidir _`
--     makes it true via `vMid = vMid ∨ vMid = u → vMid = vMid`.  In the
--     `.backwardE h` branch, `HasBlockingLeftSlot 1` unfolds to
--     `u ∉ G.Sc vMid`, discharged by `outgoing_E_not_in_Sc hG h`.
--   * `¬ s₁.IsInto vMid`: only `.forwardE h` (with
--     `h : (vMid, vNext) ∈ G.E`) leaves `IsInto` falsifiable.
--     `HasBlockingRightSlot 1` recurses via the outer cons cell to
--     `(cons vNext s₁ _).HasBlockingRightSlot 0`, which then
--     matches the `.forwardE _, 0` branch and unfolds to
--     `vNext ∉ G.Sc vMid` — discharged by
--     `outgoing_E_not_in_Sc hG h`.
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
              -- = s₀.IsInto vMid ∧ s₁.IsInto vMid.
              have h_notBoth :
                  ¬ (s₀.IsInto vMid ∧ s₁.IsInto vMid) := h_notCol
              rcases not_and_or.mp h_notBoth with h_n0 | h_n1
              · -- ¬ s₀.IsInto vMid → s₀ must be .backwardE.
                cases s₀ with
                | forwardE h =>
                    -- IsInto reduces to `vMid = vMid ∨ _`, which is `True`.
                    exact absurd
                      (Or.inl rfl : WalkStep.IsInto
                        (.forwardE h : WalkStep G uOuter vMid) vMid) h_n0
                | backwardE h =>
                    -- h : (vMid, uOuter) ∈ G.E.
                    -- HasBlockingLeftSlot at (.cons vMid (.backwardE _) _, 1)
                    -- = uOuter ∉ G.Sc vMid.
                    refine Or.inl ?_
                    change uOuter ∉ G.Sc vMid
                    exact outgoing_E_not_in_Sc hG h
                | bidir h =>
                    -- IsInto reduces to `vMid = uOuter ∨ vMid = vMid`, which is `True`.
                    exact absurd
                      (Or.inr rfl : WalkStep.IsInto
                        (.bidir h : WalkStep G uOuter vMid) vMid) h_n0
              · -- ¬ s₁.IsInto vMid → s₁ must be .forwardE.
                cases s₁ with
                | forwardE h =>
                    -- h : (vMid, vNext) ∈ G.E.
                    -- HasBlockingRightSlot at outer cons-cons-(k=1):
                    -- recurses to (cons vNext (.forwardE _) _).HasBlockingRightSlot 0
                    -- = vNext ∉ G.Sc vMid.
                    refine Or.inr ?_
                    -- Step the outer HasBlockingRightSlot 1 down to inner ...Slot 0,
                    -- which on .forwardE h unfolds to vNext ∉ G.Sc vMid.
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
                    -- IsInto reduces to `vMid = vMid ∨ _`, which is `True`.
                    exact absurd
                      (Or.inl rfl : WalkStep.IsInto
                        (.backwardE h : WalkStep G vMid vNext) vMid) h_n1
                | bidir h =>
                    -- IsInto on .bidir : WalkStep G vMid vNext at w = vMid:
                    -- (vMid = vMid ∨ vMid = vNext), the first disjunct is `True`.
                    exact absurd
                      (Or.inl rfl : WalkStep.IsInto
                        (.bidir h : WalkStep G vMid vNext) vMid) h_n1
          | m + 2, _, hk_lt, h_notCol =>
              -- Inductive step.  Outer walk is cons (vMid) s₀ tail
              -- where tail = cons vNext s₁ π_rest_rest.  The recursion
              -- equations:
              --   IsCollider (cons _ _ p) (m + 2) = p.IsCollider (m + 1)
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
-- REFACTOR-BLOCK-ORIGINAL-END: blocking_interior_helper

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: blocking_interior_helper (was: refactor_blocking_interior_helper)
set_option linter.style.longLine false in
-- Helper — side-aware port of `blocking_interior_helper` under the
-- `collider_side_aware` refactor.  Identical proof skeleton: induction
-- on the walk `π`, base-case `nil` discharged by `Walk.length = 0`,
-- inductive step pattern-matches the outer cons-cons head, the
-- substantive interior case `k = 1` reads `s₀` and `s₁` off the head
-- pair, and the inductive `k = m + 2` step delegates to the IH on the
-- tail walk.  Only the per-step "arrowhead at v_k" reading retargets
-- from the node-equality predicate `WalkStep.IsInto vMid` to the
-- side-aware constructor-tag pair `s₀.refactor_HeadAtTarget` /
-- `s₁.refactor_HeadAtSource` of def_3_15's refactor.
--
-- ## Design choice — refactor_blocking_interior_helper
--
-- *What changed under `collider_side_aware`.*  The hypothesis
--   `¬ π.IsCollider k` (with `IsCollider` reading per-step head-
--   contribution via the node-equality predicate `WalkStep.IsInto`)
--   becomes `¬ π.refactor_IsCollider k` (with `refactor_IsCollider`
--   reading per-step head-contribution via the constructor-tag-and-
--   type-index predicates `refactor_HeadAtTarget` /
--   `refactor_HeadAtSource`).  At the substantive cons-cons-(k=1)
--   pattern, the unfolding goes
--   `¬ refactor_IsCollider 1 = ¬ (s₀.refactor_HeadAtTarget ∧
--   s₁.refactor_HeadAtSource)`, identical in shape to the original's
--   `¬ (s₀.IsInto vMid ∧ s₁.IsInto vMid)`.  `not_and_or` splits the
--   conjunction; each disjunct case-splits on the relevant WalkStep
--   constructor.
--
-- *Why the L-disjunct branches of the side-aware helpers stay
--   trivially dischargeable here.*  At each `cases s₀`/`cases s₁`
--   constructor branch the matcher reduces `refactor_HeadAtTarget` /
--   `refactor_HeadAtSource` to one of two values:
--   - `True` on the "natural-side head" branches (`.forwardE _` for
--     target, `.backwardE _` for source, `.bidir _` for both);
--     `¬ True` is absurd, discharged via `absurd trivial h_n*`.
--   - The opposite-channel L-disjunct on the writing-mirror branches
--     (`.backwardE _` for target, `.forwardE _` for source) reduces
--     to `s(u, v) ∈ G.L`.  The proof does NOT need to inspect that
--     L-disjunct's truth value to discharge the goal: the constructor
--     parameter `h : (vMid, _) ∈ G.E` (or `(_, vMid) ∈ G.E`,
--     depending on side) is the witness this proof actually uses.
--     `outgoing_E_not_in_Sc hG h` discharges the matching
--     `HasBlockingLeftSlot 1` / `HasBlockingRightSlot 1` goal
--     directly — exactly as in the original proof.  The L-disjunct's
--     extra information about `G.L` membership is simply unused here.
--
-- *Why agreement-with-the-original on non-self-loop walks is
--   automatic, and the self-loop deviation does not break the proof.*
--   The side-aware refinement of `IsCollider` strictly refines the
--   original `IsCollider` only at positions adjacent to a directed
--   self-loop (the manager-accepted deviation
--   `collider_side_aware_at_self_loops`).  Both readings agree
--   pointwise on every walk that traverses no directed self-loop step,
--   so `¬ π.refactor_IsCollider k ↔ ¬ π.IsCollider k` on the non-self-
--   loop fragment of every walk — and on the self-loop fragment the
--   side-aware reading is *strictly weaker* on the non-collider side
--   (i.e. more positions classify as non-colliders).  Since this
--   helper's conclusion is `HasBlockingLeftSlot k ∨ HasBlockingRightSlot
--   k` (positive disjunction, monotone in the non-collider hypothesis),
--   the side-aware reading preserves the implication: every position
--   that the original classified as a non-collider stays a non-collider
--   under the side-aware reading too, and on those positions the
--   discharge via `outgoing_E_not_in_Sc hG _` carries over verbatim.
--   At positions newly-classified as non-colliders under the side-
--   aware reading (i.e. adjacent to a self-loop), the same discharge
--   structure fires: the non-collider hypothesis still forces at least
--   one walk-incident slot at v_k to host an outgoing directed edge
--   `(v_k, w) ∈ E` (the source-side L-disjunct's negation tells us
--   the `.forwardE _` slot encodes a real E-edge with v_k as tail,
--   and acyclicity rules out `w ∈ G.Sc v_k`).
private lemma refactor_blocking_interior_helper
    {G : CDMG Node} (hG : G.IsAcyclic) :
    ∀ {u v : Node} (π : Walk G u v) (k : ℕ),
      1 ≤ k → k < π.length → ¬ π.refactor_IsCollider k →
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
              -- refactor_IsCollider at (cons vMid s₀ (cons _ s₁ _), 1)
              -- = s₀.refactor_HeadAtTarget ∧ s₁.refactor_HeadAtSource.
              have h_notBoth :
                  ¬ (s₀.refactor_HeadAtTarget ∧ s₁.refactor_HeadAtSource) :=
                h_notCol
              rcases not_and_or.mp h_notBoth with h_n0 | h_n1
              · -- ¬ s₀.refactor_HeadAtTarget → s₀ must be .backwardE.
                cases s₀ with
                | forwardE h =>
                    -- refactor_HeadAtTarget on .forwardE _ reduces to True.
                    exact absurd trivial h_n0
                | backwardE h =>
                    -- h : (vMid, uOuter) ∈ G.E.
                    -- HasBlockingLeftSlot at (.cons vMid (.backwardE _) _, 1)
                    -- = uOuter ∉ G.Sc vMid.
                    refine Or.inl ?_
                    change uOuter ∉ G.Sc vMid
                    exact outgoing_E_not_in_Sc hG h
                | bidir h =>
                    -- refactor_HeadAtTarget on .bidir _ reduces to True.
                    exact absurd trivial h_n0
              · -- ¬ s₁.refactor_HeadAtSource → s₁ must be .forwardE.
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
                    -- refactor_HeadAtSource on .backwardE _ reduces to True.
                    exact absurd trivial h_n1
                | bidir h =>
                    -- refactor_HeadAtSource on .bidir _ reduces to True.
                    exact absurd trivial h_n1
          | m + 2, _, hk_lt, h_notCol =>
              -- Inductive step.  Outer walk is cons (vMid) s₀ tail
              -- where tail = cons vNext s₁ π_rest_rest.  The recursion
              -- equations:
              --   refactor_IsCollider (cons _ _ p) (m + 2)
              --     = p.refactor_IsCollider (m + 1)
              --   HasBlockingLeftSlot (cons _ _ p) (m + 2)
              --     = p.HasBlockingLeftSlot (m + 1)
              --   HasBlockingRightSlot (cons _ _ p) (m + 2)
              --     = p.HasBlockingRightSlot (m + 1)
              -- bring the goal into the form of the inner walk at m + 1.
              have h_notCol_inner :
                  ¬ (Walk.cons vNext s₁ π_rest_rest).refactor_IsCollider (m + 1) := by
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
-- REFACTOR-BLOCK-REPLACEMENT-END: blocking_interior_helper

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: acyclic_non_colliders_blockable
set_option linter.style.longLine false in
-- ## Design choice — acyclic_non_colliders_blockable
--
-- *Mechanical port of the original `acyclic_non_colliders_blockable`
--   onto the typed-WalkStep refactor.*  The LN-level proof structure
--   (Case A: k = 0; Case B: k = π.length; Case C: interior 1 ≤ k <
--   π.length) carries over verbatim because the disjunction shape of
--   `IsBlockableNonCollider` mirrors the original's:
--   end-position arms + two interior arms encoded via the new
--   `HasBlockingLeftSlot` / `HasBlockingRightSlot`
--   helpers (instead of the original's Option-membership existentials
--   over `Walk.edges` walk data).
--
-- *Why the interior case is delegated to a helper.*  Under the refactor
--   `Walk.edges` does not exist (see `Walks.lean`'s "Why no
--   `edges`" block), so the per-slot inspection patterns of
--   the original — which read walk-edge data at indices `k - 1` and
--   `k` via `p.edges[k - 1]?` / `p.edges[k]?` and the
--   `Walk.walkStep_at` helpers — must be replaced with structural
--   pattern-match on the walk's cons-chain.  Pushing this case
--   analysis into the `blocking_interior_helper` lemma
--   keeps the main theorem's body short and lets the helper express
--   the index-recursion lockstep across `IsCollider`,
--   `HasBlockingLeftSlot`, `HasBlockingRightSlot` cleanly via
--   induction on the walk.
--
-- *Acyclicity-cycle argument also factored out.*  See
--   `outgoing_E_not_in_Sc` above for the once-and-for-all
--   packaging of the original's Step C.2 cycle construction.  Under
--   the refactor that argument is invoked from inside
--   `blocking_interior_helper` at exactly the two slot
--   branches (`.backwardE _` at slot 1 → left-slot witness;
--   `.forwardE _` at the slot-k step → right-slot witness).
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
-- REFACTOR-BLOCK-ORIGINAL-END: acyclic_non_colliders_blockable

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: acyclic_non_colliders_blockable (was: refactor_acyclic_non_colliders_blockable)
set_option linter.style.longLine false in
-- ## Design choice — refactor_acyclic_non_colliders_blockable
--
-- *Mechanical port of `acyclic_non_colliders_blockable` onto the
--   `collider_side_aware` refactor.*  Statement signature retargets
--   `π.IsNonCollider k → π.IsBlockableNonCollider k` to
--   `π.refactor_IsNonCollider k → π.refactor_IsBlockableNonCollider k`.
--   Body retargets the interior-case discharge from
--   `blocking_interior_helper` to `refactor_blocking_interior_helper`
--   (and the destructure of `h_nc` unpacks `refactor_IsNonCollider`'s
--   `k ≤ π.length ∧ ¬ π.refactor_IsCollider k` shape).  All other
--   structure — the `Case A: k = 0` / `Case B: k = π.length` /
--   `Case C: interior` split, the disjunct routing via `Or.inl` /
--   `Or.inr` / `Or.inr (Or.inl _)` / `Or.inr (Or.inr (Or.inl _))` /
--   `Or.inr (Or.inr (Or.inr _))` — is byte-identical to the original.
--
-- *Why agreement-with-original on non-self-loop walks is automatic and
--   the self-loop deviation does not break the proof.*  The LN-level
--   mathematics of this claim (interior non-collider yields a blocking
--   slot via acyclicity) operates purely on the LN's literal stored-
--   pair / walk-constraint reading; neither leg of the argument
--   inspects the head/tail attribution at a self-loop step.  See the
--   design-choice block on `refactor_blocking_interior_helper` above
--   for the detailed monotonicity argument.  The four-disjunct
--   blockable conclusion is positive and monotone in the non-collider
--   precondition; the side-aware reading only refines the precondition
--   (more positions classify as non-colliders under the side-aware
--   reading than under the original), so the implication carries over
--   without modification at every position the side-aware reading
--   classifies as a non-collider — including the newly-non-collider
--   positions adjacent to a directed self-loop.
--
-- *Why `refactor_blocking_interior_helper` is invoked rather than the
--   original `blocking_interior_helper`.*  Both helpers coexist in
--   scope during the refactor window; the original takes a hypothesis
--   `¬ π.IsCollider k`, the refactor takes `¬ π.refactor_IsCollider k`.
--   The `h_notCol` extracted from the side-aware `refactor_IsNonCollider`
--   hypothesis has the latter type, so it routes to the refactor
--   helper directly.  After Phase 7 cleanup, the whole-word renames
--   `refactor_IsCollider → IsCollider`, `refactor_IsNonCollider →
--   IsNonCollider`, `refactor_IsBlockableNonCollider →
--   IsBlockableNonCollider`, and `refactor_blocking_interior_helper →
--   blocking_interior_helper` restore the body's surface form to its
--   pre-refactor reading.
-- ref: claim_3_20
-- claim_3_20 -- start statement
theorem refactor_acyclic_non_colliders_blockable
    (G : CDMG Node) (hG : G.IsAcyclic)
    {u v : Node} (π : Walk G u v) (k : ℕ) :
    π.refactor_IsNonCollider k → π.refactor_IsBlockableNonCollider k
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
  rcases refactor_blocking_interior_helper hG π k hk_pos hk_lt h_notCol with hL | hR
  · exact Or.inr (Or.inr (Or.inl hL))
  · exact Or.inr (Or.inr (Or.inr hR))
-- REFACTOR-BLOCK-REPLACEMENT-END: acyclic_non_colliders_blockable

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

end CDMG

end Causality
