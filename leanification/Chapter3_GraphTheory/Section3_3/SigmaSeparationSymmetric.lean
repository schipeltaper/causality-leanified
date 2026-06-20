import Chapter3_GraphTheory.Section3_3.ISigmaSeparation
import Chapter3_GraphTheory.Section3_2.MargPreservesAncestors

namespace Causality

/-!
# σ-separation is symmetric (`claim_3_22`)

This file formalises `claim_3_22`
(`\label{lem:sigma_separation_symmetric}`), the symmetry lemma embedded
in `def_3_18` item 4 of Section 3.3 of the lecture notes.

> Note that $\sigma$-separation is symmetric:
> $A \sPerp_G B \given C \iff B \sPerp_G A \given C$, since when
> $J = \emptyset$ the set of walks between $A$ and $B$ is the same
> regardless of direction, and the $\sigma$-blocking conditions are
> invariant under walk reversal.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/`
`claim_3_22_statement_SigmaSeparationSymmetric.tex`, verified
equivalent (both structurally and semantically) to the LN block
(`graphs.tex`, lines 1366–1369 sitting inside `def_3_18` item 4).  The
rewrite folded in only implicit-context hoists — no new content —
against the three working-phase LN-critic findings:

1. **`J = ∅` is the standing hypothesis, not a justification clause.**
   The LN's "since when $J = \emptyset$ …" prose is the justification
   for the claim; the rewrite hoists `J = ∅` into an explicit
   premise so the claim's hypothesis matches the σ-notation's scope.

2. **`\sPerp_G` is, per `def_3_18` item 4, defined only under
   `J = ∅`.**  Therefore the rewritten statement is fully general
   relative to the LN's scope of `\sPerp_G`: there is no
   "partial-proof gap" between the claim's apparent generality and the
   "$J = \emptyset$" justification.

3. **Walks are ordered sequences** (per `def_3_4` item i).  The LN's
   "the set of walks between $A$ and $B$ is the same regardless of
   direction" is loose prose — strictly, walk reversal induces an
   involution on `Walk G u v ↔ Walk G v u`, and the
   σ-blocking conditions are invariant under that involution.  This is
   a proof obligation for Manager B (the proof step), not part of the
   statement.

The conclusion is the biconditional
`A ⊥^σ_G B | C  ↔  B ⊥^σ_G A | C`, encoded against the existing
`IsSigmaSeparated` predicate from `def_3_18` item 4
(`ISigmaSeparation.lean`).  The hypothesis `hJ : G.J = ∅` is required
by `IsSigmaSeparated`'s signature; the three subset proofs
`hA, hB, hC` are required by the same signature and, under `hJ`,
reduce to the LN's "$A, B, C \ins V$" reading.

The proof body is `:= by sorry` and will be filled in by the
`prove_claim_in_lean` worker after the tex-proof phase
(`write_tex_proof` / `verify_tex_proof`) has produced and verified the
mathematical proof.  See `workspace_claim_3_22.md` for the
operator-supplied hint on the proof strategy (custom-local walk-
reversal helper or per-position structural argument; avoid heavy
generic walk-reversal infrastructure).
-/

end Causality

namespace Causality

namespace CDMG

-- ## Design choice — claim_3_22 section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Matches the
--   chapter-wide convention used by every `CDMG`-opening file in
--   Sections 3.1, 3.2 and 3.3 (`Section3_1/CDMG.lean`,
--   `Section3_1/Walks.lean`, `Section3_3/SigmaBlockedWalks.lean`,
--   `Section3_3/ISigmaSeparation.lean`, etc.).  The
--   `IsSigmaSeparated` predicate from `def_3_18` item 4 is itself
--   parameterised over this same implicit binder block, so the
--   theorem signature below auto-binds these binders into its type.
--
-- *Three-dash `--- start helper` / `--- end helper` markers.*  This
--   `variable` block is statement-typing infrastructure that the
--   wrapped theorem signature cannot compile without (the `G : CDMG
--   Node` premise pattern-matches against the implicit `Node`).
--   Chapter convention for that kind of declaration is the three-dash
--   helper flavour, distinct from the two-dash main-statement marker
--   used to wrap the theorem itself.
-- claim_3_22 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_22 --- end helper

/-! ### Proof helpers — walk reversal infrastructure

The helpers below build a *custom local* walk-reversal pipeline that
the theorem proof consumes.  These are proof helpers (see worker
contract): they support the tactic block, not the theorem signature,
so they carry no markers.

The shape mirrors the verified TeX proof's beats II and III:

* `WalkStep.reverse` — flip a single typed step's direction
  (`.forwardE ↔ .backwardE`; `.bidir` is fixed modulo the `Sym2`
  swap-equality).
* `Walk.reverse` — extend the per-step reversal to a full walk,
  via `comp`.
* Length / vertex-list / involution lemmas for `Walk.reverse`.
* `WalkStep.isInto_reverse` — the per-position arrowhead-presence
  predicate `IsInto` (def_3_15 helper) is invariant under
  per-step reversal.
* Position-correspondence lemmas for `IsCollider` /
  `HasBlockingLeftSlot` / `HasBlockingRightSlot` /
  `IsBlockableNonCollider` under reversal.
* `Walk.isSigmaBlockedGiven_reverse` — the σ-blocking witness
  transports across reversal.
-/

-- WalkStep reversal: flip the constructor tag and preserve the
-- underlying edge witness.  `.forwardE` ↔ `.backwardE` share the
-- *same* E-membership witness because for `WalkStep G v u`,
-- `.backwardE` takes `(u, v) ∈ G.E` — which is exactly the
-- witness `.forwardE` for `WalkStep G u v` was already carrying.
-- `.bidir` uses `Sym2.eq_swap : s(u, v) = s(v, u)` to retype the
-- swap-quotient witness.
def WalkStep.reverse {G : CDMG Node} :
    ∀ {u v : Node}, WalkStep G u v → WalkStep G v u
  | _, _, .forwardE h => .backwardE h
  | _, _, .backwardE h => .forwardE h
  | _, _, .bidir h => .bidir (Sym2.eq_swap ▸ h)

namespace WalkStep

lemma reverse_reverse {G : CDMG Node} :
    ∀ {u v : Node} (s : WalkStep G u v), s.reverse.reverse = s
  | _, _, .forwardE _ => rfl
  | _, _, .backwardE _ => rfl
  | _, _, .bidir _ => rfl

-- The per-position arrowhead-presence predicate `IsInto` (from
-- `def_3_15`'s helper) reads off node-equality on the WalkStep's
-- type indices plus an optional `Sym2`-membership disjunct.  Each
-- of those is invariant under reversal: index-swap is absorbed by
-- the `w = u ∨ w = v` Or-comm, and `s(u, v) = s(v, u)` in `Sym2`.
lemma isInto_reverse {G : CDMG Node} :
    ∀ {u v : Node} (s : WalkStep G u v) (w : Node),
      s.reverse.IsInto w ↔ s.IsInto w
  | _, _, .forwardE _, w => by
      change (w = _ ∨ (s(_, _) ∈ G.L ∧ (w = _ ∨ w = _))) ↔
           (w = _ ∨ (s(_, _) ∈ G.L ∧ (w = _ ∨ w = _)))
      rw [show (s(_, _) : Sym2 Node) = s(_, _) from Sym2.eq_swap]
      tauto
  | _, _, .backwardE _, w => by
      change (w = _ ∨ (s(_, _) ∈ G.L ∧ (w = _ ∨ w = _))) ↔
           (w = _ ∨ (s(_, _) ∈ G.L ∧ (w = _ ∨ w = _)))
      rw [show (s(_, _) : Sym2 Node) = s(_, _) from Sym2.eq_swap]
      tauto
  | _, _, .bidir _, _ => by
      change (_ = _ ∨ _ = _) ↔ (_ = _ ∨ _ = _)
      tauto

end WalkStep

-- Walk reversal: structural recursion via `Walk.comp`.  The
-- `cons mid s p'` case recurses on `p'` (whose reverse is a walk
-- from the target back to `mid`) and concatenates the single-step
-- walk `[s.reverse]` (from `mid` back to the original start
-- vertex).  Trivial walk reverses to itself.
def Walk.reverse {G : CDMG Node} :
    ∀ {u v : Node}, Walk G u v → Walk G v u
  | _, _, .nil w hw => .nil w hw
  | _, _, .cons _ s p =>
      p.reverse.comp (.cons _ s.reverse (.nil _ (WalkStep.source_mem s)))

namespace Walk

lemma length_reverse {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.reverse.length = p.length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p' => by
      simp only [Walk.reverse, Walk.length_comp, Walk.length_reverse p',
                 Walk.length, Nat.add_comm]

lemma vertices_reverse {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.reverse.vertices = p.vertices.reverse
  | _, _, .nil _ _ => rfl
  | u, _, .cons mid s p' => by
      -- p.reverse = p'.reverse.comp (cons u s.reverse (nil u _))
      -- (cons u s.reverse (nil u _)).vertices = [mid, u]
      -- vertices_comp gives p'.reverse.vertices.dropLast ++ [mid, u]
      -- By IH, p'.reverse.vertices = p'.vertices.reverse, which ends in mid
      -- (since p'.vertices starts with mid).  So
      --   p'.vertices.reverse.dropLast ++ [mid] = p'.vertices.reverse,
      -- and the goal collapses.
      change (p'.reverse.comp _).vertices = (u :: p'.vertices).reverse
      rw [Walk.vertices_comp, Walk.vertices_reverse p', List.reverse_cons]
      -- Show: p'.vertices.reverse.dropLast ++ [mid, u] = p'.vertices.reverse ++ [u]
      change p'.vertices.reverse.dropLast ++ [mid, u] = p'.vertices.reverse ++ [u]
      have h_head_eq : p'.vertices.head? = some mid := by
        cases p' with
        | nil _ _ => rfl
        | cons _ _ _ => rfl
      have hne : p'.vertices.reverse ≠ [] := by
        intro h
        have : p'.vertices = [] := by
          have := congrArg List.reverse h
          simpa using this
        exact Walk.vertices_ne_nil p' this
      have h_getLast :
          p'.vertices.reverse.getLast hne = mid := by
        rw [List.getLast_reverse]
        have hne' : p'.vertices ≠ [] := Walk.vertices_ne_nil p'
        have h_head' : p'.vertices.head hne' = mid := by
          have := h_head_eq
          rw [List.head?_eq_some_head (l := p'.vertices) hne'] at this
          exact Option.some.inj this
        exact h_head'
      conv_lhs =>
        rw [show ([mid, u] : List Node) = [mid] ++ [u] from rfl, ← List.append_assoc]
      conv_rhs =>
        rw [show p'.vertices.reverse = p'.vertices.reverse.dropLast ++ [mid] from by
              conv_lhs => rw [← List.dropLast_append_getLast hne]
              rw [h_getLast]]

-- A small helper: `Walk.comp` with `nil` on the right behaves
-- identically (modulo proof-irrelevance) to the original walk.
-- We need this to massage `(nil _ _).comp` and reverse-of-nil chains.
lemma nil_comp {G : CDMG Node} {u v : Node}
    (hv : u ∈ G) (q : Walk G u v) :
    (Walk.nil u hv).comp q = q := rfl

-- `q.comp nil = q` (modulo proof-irrelevance).  Used in the reverse_involution
-- proof to absorb trailing nil-extensions.
lemma comp_nil {G : CDMG Node} :
    ∀ {u v : Node} (q : Walk G u v) (hv : v ∈ G), q.comp (Walk.nil v hv) = q
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons mid s p', hv => by
      change Walk.cons mid s (p'.comp (Walk.nil _ hv)) = Walk.cons mid s p'
      rw [Walk.comp_nil p' hv]

-- Reverse distributes over comp: (q.comp r).reverse = r.reverse.comp q.reverse.
lemma comp_reverse {G : CDMG Node} :
    ∀ {u v w : Node} (q : Walk G u v) (r : Walk G v w),
      (q.comp r).reverse = r.reverse.comp q.reverse
  | _, _, _, .nil v hv, r => by
      -- q.comp r = r; q.reverse = nil v hv; r.reverse.comp (nil v hv) = r.reverse (by comp_nil)
      change r.reverse = r.reverse.comp (Walk.nil v hv)
      rw [Walk.comp_nil]
  | _, _, _, .cons mid s q', r => by
      change ((Walk.cons mid s q').comp r).reverse =
        r.reverse.comp ((Walk.cons mid s q').reverse)
      -- LHS: (cons mid s (q'.comp r)).reverse = (q'.comp r).reverse.comp (cons _ s.reverse (nil _ _))
      -- IH: (q'.comp r).reverse = r.reverse.comp q'.reverse
      -- So LHS = (r.reverse.comp q'.reverse).comp (cons _ s.reverse (nil _ _))
      --       = r.reverse.comp (q'.reverse.comp (cons _ s.reverse (nil _ _)))  by comp_assoc
      --       = r.reverse.comp (cons mid s q').reverse  by reverse def
      change ((q'.comp r).reverse).comp
        (Walk.cons _ s.reverse (Walk.nil _ (WalkStep.source_mem s))) =
        r.reverse.comp (q'.reverse.comp
          (Walk.cons _ s.reverse (Walk.nil _ (WalkStep.source_mem s))))
      rw [Walk.comp_reverse q' r]
      rw [Walk.comp_assoc]

-- Walk.reverse is involutive.
lemma reverse_involution {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.reverse.reverse = p
  | _, _, .nil _ _ => rfl
  | _, _, .cons mid s p' => by
      change (p'.reverse.comp
        (Walk.cons _ s.reverse (Walk.nil _ (WalkStep.source_mem s)))).reverse =
        Walk.cons mid s p'
      rw [Walk.comp_reverse]
      -- (cons _ s.reverse (nil _ _)).reverse = (nil _ _).reverse.comp (cons _ s.reverse.reverse (nil _ _))
      --                                    = (nil _ _).comp (cons _ s (nil _ _))
      --                                    = cons _ s (nil _ _)
      change (Walk.cons mid s.reverse.reverse (Walk.nil mid _)).comp p'.reverse.reverse =
        Walk.cons mid s p'
      rw [WalkStep.reverse_reverse, Walk.reverse_involution p']
      -- (cons _ s (nil _ _)).comp p' = cons _ s ((nil _ _).comp p') = cons _ s p'
      rfl

end Walk

-- REFACTOR-BLOCK-DELETE-BEGIN: isCollider_cons_zero
-- The two successor-shift equations of IsCollider, isolated as
-- definitional `rfl` lemmas so that subsequent simp/rw can fire
-- without re-running the equation compiler.

lemma Walk.isCollider_cons_zero {G : CDMG Node} {u w : Node} (mid : Node)
    (s : WalkStep G u mid) (p : Walk G mid w) :
    (Walk.cons mid s p).IsCollider 0 ↔
      match p with
      | .nil _ _ => False
      | .cons _ _ _ => False := by
  cases p <;> simp [Walk.IsCollider]
-- REFACTOR-BLOCK-DELETE-END: isCollider_cons_zero

-- REFACTOR-BLOCK-DELETE-BEGIN: isCollider_cons_nil_eq
-- Equational characterisation: `IsCollider` on a cons whose tail is
-- `nil` is always `False`.
lemma Walk.isCollider_cons_nil_eq {G : CDMG Node} {u : Node} (mid : Node)
    (s : WalkStep G u mid) (hw : mid ∈ G) (k : ℕ) :
    (Walk.cons mid s (Walk.nil mid hw)).IsCollider k = False := by
  cases k <;> rfl
-- REFACTOR-BLOCK-DELETE-END: isCollider_cons_nil_eq

-- REFACTOR-BLOCK-DELETE-BEGIN: isCollider_nil
-- IsCollider on the trivial walk is always False.
lemma Walk.isCollider_nil {G : CDMG Node} {v : Node} (hv : v ∈ G) (k : ℕ) :
    (Walk.nil v hv).IsCollider k = False := by
  cases k <;> rfl
-- REFACTOR-BLOCK-DELETE-END: isCollider_nil

-- REFACTOR-BLOCK-DELETE-BEGIN: isCollider_cons_cons_one
-- The collider check on a cons-cons walk at position 1 reads the two
-- head WalkSteps' arrowhead at the cons-cell's middle vertex.
lemma Walk.isCollider_cons_cons_one
    {G : CDMG Node} {u w : Node} (mid : Node)
    (s₀ : WalkStep G u mid) (mid₂ : Node) (s₁ : WalkStep G mid mid₂)
    (q : Walk G mid₂ w) :
    (Walk.cons mid s₀ (Walk.cons mid₂ s₁ q)).IsCollider 1 ↔
      (s₀.IsInto mid ∧ s₁.IsInto mid) := by
  rfl
-- REFACTOR-BLOCK-DELETE-END: isCollider_cons_cons_one

-- REFACTOR-BLOCK-DELETE-BEGIN: isCollider_cons_cons_succ_succ
-- Recursive shift: collider at position k+2 on a cons-cons walk
-- equals collider at position k+1 on the tail (which itself is a
-- cons-cons).  Note: this lemma only fires when the tail is a cons.
lemma Walk.isCollider_cons_cons_succ_succ
    {G : CDMG Node} {u w : Node} (mid : Node)
    (s₀ : WalkStep G u mid) (mid₂ : Node) (s₁ : WalkStep G mid mid₂)
    (q : Walk G mid₂ w) (k : ℕ) :
    (Walk.cons mid s₀ (Walk.cons mid₂ s₁ q)).IsCollider (k + 2) =
      (Walk.cons mid₂ s₁ q).IsCollider (k + 1) := by
  rfl
-- REFACTOR-BLOCK-DELETE-END: isCollider_cons_cons_succ_succ

-- REFACTOR-BLOCK-DELETE-BEGIN: isCollider_length_false
-- IsCollider at the boundary position k = p.length is `False` for any
-- walk.  Proof by induction on p.  The body of IsCollider only fires
-- a `True`-yielding branch when (i) the outer walk is a cons-cons and
-- (ii) the position is 1; the boundary position is never 1 unless the
-- walk has length 1 (a cons-nil), in which case the cons-nil branch
-- forces False.
lemma Walk.isCollider_length_false {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.IsCollider p.length = False
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ s (.nil _ hv) => by
      exact Walk.isCollider_cons_nil_eq _ s hv _
  | _, _, .cons mid s (.cons mid₂ s' p') => by
      -- length = p'.length + 2.  Use recursive IsCollider case to descend
      -- into the inner cons-cons walk, then invoke the IH on that walk
      -- (at position equal to its length).
      have h_len : (Walk.cons mid s (Walk.cons mid₂ s' p')).length = p'.length + 2 := by
        simp [Walk.length]
      rw [h_len]
      -- Goal: IsCollider at p'.length + 2, which by the recursive
      -- pattern equals (cons mid₂ s' p').IsCollider (p'.length + 1)
      change (Walk.cons mid₂ s' p').IsCollider (p'.length + 1) = False
      have ih := Walk.isCollider_length_false (Walk.cons mid₂ s' p')
      have h_tail_len : (Walk.cons mid₂ s' p').length = p'.length + 1 := by
        simp [Walk.length]
      rw [h_tail_len] at ih
      exact ih
-- REFACTOR-BLOCK-DELETE-END: isCollider_length_false

-- REFACTOR-BLOCK-DELETE-BEGIN: isCollider_out_of_range
-- IsCollider out of range (k > p.length) is also False.
lemma Walk.isCollider_out_of_range {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.length < k → p.IsCollider k = False
  | _, _, .nil _ _, k, _ => by cases k <;> rfl
  | _, _, .cons _ s (.nil _ hv), k, _ => Walk.isCollider_cons_nil_eq _ s hv _
  | _, _, .cons _ _ (.cons _ _ _), 0, h => by simp [Walk.length] at h
  | _, _, .cons _ _ (.cons _ _ _), 1, h => by
      simp [Walk.length] at h
  | _, _, .cons _ _ (.cons mid₂ s' p'), k + 2, h => by
      change (Walk.cons mid₂ s' p').IsCollider (k + 1) = False
      have h_tail_lt : (Walk.cons mid₂ s' p').length < k + 1 := by
        simp [Walk.length] at h ⊢
        omega
      exact Walk.isCollider_out_of_range (Walk.cons mid₂ s' p') (k+1) h_tail_lt
-- REFACTOR-BLOCK-DELETE-END: isCollider_out_of_range

-- REFACTOR-BLOCK-DELETE-BEGIN: isCollider_comp_eq_of_lt
-- Comp invariance for IsCollider at strictly-interior-of-`q` positions.
-- When `k < q.length`, both adjacent slots of position `k` are inside
-- the prefix `q`, so the extension by `r` is invisible to IsCollider.
lemma Walk.isCollider_comp_eq_of_lt {G : CDMG Node} :
    ∀ {u v w : Node} (q : Walk G u v) (r : Walk G v w) (k : ℕ),
      k < q.length →
      ((q.comp r).IsCollider k ↔ q.IsCollider k)
  | _, _, _, .nil _ _, _, _, h => by simp [Walk.length] at h
  | _, _, _, .cons mid s (.nil _ hv), r, k, h => by
      -- q = cons mid s (nil _ _) has length 1, so k < 1 means k = 0
      simp [Walk.length] at h
      subst h
      -- Goal: (cons mid s ((nil _ _).comp r)).IsCollider 0 ↔ (cons mid s (nil _ _)).IsCollider 0
      -- (nil _ _).comp r = r, so LHS = (cons mid s r).IsCollider 0 = False (regardless of r)
      -- RHS = False (cons-nil branch)
      change (Walk.cons mid s r).IsCollider 0 ↔ (Walk.cons mid s (Walk.nil _ hv)).IsCollider 0
      have h_rhs : (Walk.cons mid s (Walk.nil _ hv)).IsCollider 0 = False :=
        Walk.isCollider_cons_nil_eq mid s hv 0
      rw [h_rhs]
      constructor
      · intro h_c
        cases r with
        | nil _ _ => exact h_c
        | cons _ _ _ => exact h_c
      · intro h_c
        exact h_c.elim
  | _, _, _, .cons mid s (.cons mid₂ s' p''), r, 0, _ => by
      -- Both sides False
      change (Walk.cons mid s ((Walk.cons mid₂ s' p'').comp r)).IsCollider 0 ↔ _
      constructor <;> intro h <;> exact h.elim
  | _, _, _, .cons mid s (.cons mid₂ s' p''), r, 1, _ => by
      -- q.comp r at position 1 reads s and s' (same as q).
      change (Walk.cons mid s ((Walk.cons mid₂ s' p'').comp r)).IsCollider 1 ↔
             (Walk.cons mid s (Walk.cons mid₂ s' p'')).IsCollider 1
      -- LHS: q.comp r at position 1
      -- (cons mid₂ s' p'').comp r is some cons (since the head is mid₂)
      change ((Walk.cons mid s (Walk.cons mid₂ s' (p''.comp r))).IsCollider 1) ↔
             ((Walk.cons mid s (Walk.cons mid₂ s' p'')).IsCollider 1)
      rfl
  | _, _, _, .cons mid s (.cons mid₂ s' p''), r, k + 2, h => by
      have h' : k + 2 < (Walk.cons mid s (Walk.cons mid₂ s' p'')).length := h
      simp [Walk.length] at h'
      -- q.IsCollider (k+2) = (cons mid₂ s' p'').IsCollider (k+1)
      -- (q.comp r).IsCollider (k+2) = (cons mid₂ s' (p''.comp r)).IsCollider (k+1)
      -- By IH on cons mid₂ s' p'' (with q.length = (cons mid₂ s' p'').length + 1 - 1 = (cons mid₂ s' p'').length, no wait)
      have ih := Walk.isCollider_comp_eq_of_lt (Walk.cons mid₂ s' p'') r (k+1) (by
        simp [Walk.length]; omega)
      -- ih: ((cons mid₂ s' p'').comp r).IsCollider (k+1) ↔ (cons mid₂ s' p'').IsCollider (k+1)
      -- Goal: (cons mid s ((cons mid₂ s' p'').comp r)).IsCollider (k+2) ↔
      --       (cons mid s (cons mid₂ s' p'')).IsCollider (k+2)
      -- LHS: case on (cons mid₂ s' p'').comp r structure
      change (Walk.cons mid s ((Walk.cons mid₂ s' p'').comp r)).IsCollider (k+2) ↔
             (Walk.cons mid s (Walk.cons mid₂ s' p'')).IsCollider (k+2)
      -- (cons mid₂ s' p'').comp r = cons mid₂ s' (p''.comp r)
      change (Walk.cons mid s (Walk.cons mid₂ s' (p''.comp r))).IsCollider (k+2) ↔
             (Walk.cons mid s (Walk.cons mid₂ s' p'')).IsCollider (k+2)
      -- By isCollider_cons_cons_succ_succ:
      -- LHS = (cons mid₂ s' (p''.comp r)).IsCollider (k+1)
      -- RHS = (cons mid₂ s' p'').IsCollider (k+1)
      -- LHS = ((cons mid₂ s' p'').comp r).IsCollider (k+1)
      -- By IH, equal to (cons mid₂ s' p'').IsCollider (k+1) = RHS. ✓
      have eq1 : (Walk.cons mid s (Walk.cons mid₂ s' (p''.comp r))).IsCollider (k+2) =
                 (Walk.cons mid₂ s' (p''.comp r)).IsCollider (k+1) := rfl
      have eq2 : (Walk.cons mid s (Walk.cons mid₂ s' p'')).IsCollider (k+2) =
                 (Walk.cons mid₂ s' p'').IsCollider (k+1) := rfl
      rw [eq1, eq2]
      -- Now: (cons mid₂ s' (p''.comp r)).IsCollider (k+1) ↔ (cons mid₂ s' p'').IsCollider (k+1)
      -- The LHS is ((cons mid₂ s' p'').comp r).IsCollider (k+1) by comp def.
      change ((Walk.cons mid₂ s' p'').comp r).IsCollider (k+1) ↔
             (Walk.cons mid₂ s' p'').IsCollider (k+1)
      exact ih
-- REFACTOR-BLOCK-DELETE-END: isCollider_comp_eq_of_lt

-- REFACTOR-BLOCK-DELETE-BEGIN: isCollider_comp_succ_length_cons_cons
-- Junction lemma: when the suffix `Y` is cons-cons, IsCollider at the
-- "right after prefix" position of the composed walk reads the two head
-- steps of `Y`.  This is the structural content of "what happens at the
-- gluing point" and is what we need for the head case (k = 1 on the
-- original walk → position p.length - 1 on the reverse).
lemma Walk.isCollider_comp_succ_length_cons_cons {G : CDMG Node}
    {b c mid mid₂ : Node} (s : WalkStep G b mid) (s' : WalkStep G mid mid₂)
    (r : Walk G mid₂ c) :
    ∀ {a : Node} (q : Walk G a b),
      (q.comp (Walk.cons mid s (Walk.cons mid₂ s' r))).IsCollider (q.length + 1) ↔
        s.IsInto mid ∧ s'.IsInto mid
  | _, .nil _ _ => by
      -- q.comp Y = Y, q.length = 0
      change (Walk.cons mid s (Walk.cons mid₂ s' r)).IsCollider 1 ↔ _
      rfl
  | _, .cons _ _ (.nil _ _) => by
      -- q = cons mid₀ s₀ (nil _ _) with length 1.
      -- q.comp Y = cons mid₀ s₀ ((nil _ _).comp Y) = cons mid₀ s₀ Y
      --         = cons mid₀ s₀ (cons mid s (cons mid₂ s' r))
      -- IsCollider at q.length + 1 = 2:
      -- pattern: cons _ _ (cons _ _ _), k+2 with k = 0 → tail.IsCollider 1
      -- tail = cons mid s (cons mid₂ s' r), IsCollider 1 = s.IsInto mid ∧ s'.IsInto mid.
      rfl
  | _, .cons _ _ (.cons mid'' s'' q'') => by
      -- q = cons mid₀ s₀ (cons mid'' s'' q'')
      -- (q.comp Y).IsCollider (q.length + 1)
      -- q.length = (cons mid'' s'' q'').length + 1, so q.length + 1 = (cons mid'' s'' q'').length + 2
      -- The recursive case: cons _ _ (cons _ _ _), k+2 → tail.IsCollider (k+1)
      -- tail = (cons mid'' s'' q'').comp Y
      -- which reduces to: (cons mid'' s'' (q''.comp Y)).IsCollider ((cons mid'' s'' q'').length + 1)
      -- which by IH on (cons mid'' s'' q'') equals s.IsInto mid ∧ s'.IsInto mid.
      exact Walk.isCollider_comp_succ_length_cons_cons s s' r
        (Walk.cons mid'' s'' q'')
-- REFACTOR-BLOCK-DELETE-END: isCollider_comp_succ_length_cons_cons

-- REFACTOR-BLOCK-DELETE-BEGIN: isCollider_reverse
-- Main IsCollider invariance under walk reversal.  The position
-- correspondence is `k ↔ p.length - k`.
lemma Walk.isCollider_reverse {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.reverse.IsCollider (p.length - k) ↔ p.IsCollider k
  | _, _, .nil _ hv, k => by
      -- nil: both sides False
      have h_rhs : (Walk.nil _ hv).IsCollider k = False := Walk.isCollider_nil hv k
      have h_lhs : (Walk.nil _ hv).reverse.IsCollider ((Walk.nil _ hv).length - k) = False := by
        change (Walk.nil _ hv).IsCollider _ = False
        exact Walk.isCollider_nil hv _
      rw [h_lhs, h_rhs]
  | _, _, .cons _ s (.nil _ hv), k => by
      -- length 1 walk: IsCollider always False.
      -- p = cons _ s (nil _ _); p.reverse = (nil _ _).comp (cons _ s.reverse (nil _ _))
      --                              = cons _ s.reverse (nil _ _)
      -- Both p.IsCollider k and p.reverse.IsCollider (1 - k) are False.
      have h_rhs : (Walk.cons _ s (Walk.nil _ hv)).IsCollider k = False :=
        Walk.isCollider_cons_nil_eq _ s hv k
      have h_lhs : (Walk.cons _ s (Walk.nil _ hv)).reverse.IsCollider
            ((Walk.cons _ s (Walk.nil _ hv)).length - k) = False := by
        change (Walk.cons _ s.reverse (Walk.nil _ _)).IsCollider _ = False
        exact Walk.isCollider_cons_nil_eq _ s.reverse _ _
      rw [h_lhs, h_rhs]
  | _, _, .cons mid s (.cons mid₂ s' p''), k => by
      -- length ≥ 2 walk.  Case on k.
      cases k with
      | zero =>
          -- p.IsCollider 0 = False.  p.reverse.IsCollider p.length = False.
          have h_rhs : (Walk.cons mid s (Walk.cons mid₂ s' p'')).IsCollider 0 = False := rfl
          rw [h_rhs]
          have h_lhs : (Walk.cons mid s (Walk.cons mid₂ s' p'')).reverse.IsCollider
                ((Walk.cons mid s (Walk.cons mid₂ s' p'')).length - 0) = False := by
            rw [Nat.sub_zero,
                show (Walk.cons mid s (Walk.cons mid₂ s' p'')).length =
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).reverse.length from
                  (Walk.length_reverse _).symm]
            exact Walk.isCollider_length_false _
          rw [h_lhs]
      | succ k₀ =>
          cases k₀ with
          | zero =>
              -- k = 1: head case.
              have h_rhs_def : (Walk.cons mid s (Walk.cons mid₂ s' p'')).IsCollider 1 =
                  (s.IsInto mid ∧ s'.IsInto mid) := rfl
              rw [h_rhs_def]
              -- p.length - 1 = p''.length + 1.
              have h_len_sub :
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).length - 1 = p''.length + 1 := by
                simp [Walk.length]
              rw [h_len_sub]
              -- p.reverse decomposition.
              have h_rev_eq :
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).reverse =
                  p''.reverse.comp
                    (Walk.cons mid s'.reverse
                      (Walk.cons _ s.reverse
                        (Walk.nil _ (WalkStep.source_mem s)))) := by
                change (p''.reverse.comp
                          (Walk.cons mid s'.reverse
                            (Walk.nil _ (WalkStep.source_mem s')))).comp _ = _
                rw [Walk.comp_assoc]
                rfl
              rw [h_rev_eq]
              -- Position p''.length + 1 = p''.reverse.length + 1
              rw [show p''.length + 1 = p''.reverse.length + 1 from by rw [Walk.length_reverse]]
              rw [Walk.isCollider_comp_succ_length_cons_cons]
              rw [WalkStep.isInto_reverse, WalkStep.isInto_reverse]
              tauto
          | succ k₁ =>
              -- k = k₁ + 2 ≥ 2.  Use IH + comp invariance.
              have h_rhs_eq :
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).IsCollider (k₁ + 2) =
                  (Walk.cons mid₂ s' p'').IsCollider (k₁ + 1) := rfl
              rw [h_rhs_eq]
              have h_lhs_pos :
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).length - (k₁ + 2) =
                  (Walk.cons mid₂ s' p'').length - (k₁ + 1) := by
                simp [Walk.length]
              rw [h_lhs_pos]
              -- p.reverse = (cons mid₂ s' p'').reverse.comp X
              have h_rev :
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).reverse =
                  (Walk.cons mid₂ s' p'').reverse.comp
                    (Walk.cons _ s.reverse (Walk.nil _ (WalkStep.source_mem s))) := rfl
              rw [h_rev]
              -- comp invariance at strictly-interior position
              have h_lt : (Walk.cons mid₂ s' p'').length - (k₁ + 1) <
                  (Walk.cons mid₂ s' p'').reverse.length := by
                rw [Walk.length_reverse]
                have h_inner_len : (Walk.cons mid₂ s' p'').length = p''.length + 1 := by
                  simp [Walk.length]
                rw [h_inner_len]
                omega
              rw [Walk.isCollider_comp_eq_of_lt _ _ _ h_lt]
              exact Walk.isCollider_reverse (Walk.cons mid₂ s' p'') (k₁ + 1)
-- REFACTOR-BLOCK-DELETE-END: isCollider_reverse

namespace Walk

-- HasBlockingLeftSlot/RightSlot: helpers for nil and out-of-range cases.
lemma hasBlockingLeftSlot_nil {G : CDMG Node} {v : Node}
    (hv : v ∈ G) (k : ℕ) :
    (Walk.nil v hv).HasBlockingLeftSlot k = False := by
  cases k <;> rfl

lemma hasBlockingRightSlot_nil {G : CDMG Node} {v : Node}
    (hv : v ∈ G) (k : ℕ) :
    (Walk.nil v hv).HasBlockingRightSlot k = False := by
  cases k <;> rfl

-- Recursive reduction lemmas (definitional).
lemma hasBlockingRightSlot_cons_succ {G : CDMG Node}
    {u w : Node} (mid : Node) (s : WalkStep G u mid) (p : Walk G mid w) (k : ℕ) :
    (Walk.cons mid s p).HasBlockingRightSlot (k + 1) = p.HasBlockingRightSlot k := by
  cases s <;> rfl

lemma hasBlockingLeftSlot_cons_succ_succ {G : CDMG Node}
    {u w : Node} (mid : Node) (s : WalkStep G u mid) (p : Walk G mid w) (k : ℕ) :
    (Walk.cons mid s p).HasBlockingLeftSlot (k + 2) = p.HasBlockingLeftSlot (k + 1) := by
  cases s <;> rfl

-- HasBlockingLeftSlot at position 0 is always False.
lemma hasBlockingLeftSlot_zero_false {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.HasBlockingLeftSlot 0 = False
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ => rfl

-- HasBlockingRightSlot at the last slot (= p.length) of any walk:
-- slots are 0..p.length-1, so position p.length is one beyond the last
-- slot and HasBlockingRightSlot is False there.
lemma hasBlockingRightSlot_at_length_false {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.HasBlockingRightSlot p.length = False
  | _, _, .nil _ hv => Walk.hasBlockingRightSlot_nil hv 0
  | _, _, .cons _ s p' => by
      have h_len : (Walk.cons _ s p').length = p'.length + 1 := rfl
      rw [h_len, Walk.hasBlockingRightSlot_cons_succ]
      exact Walk.hasBlockingRightSlot_at_length_false p'

-- Out-of-range: HasBlockingRightSlot at k > p.length is False.
lemma hasBlockingRightSlot_out_of_range {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.length < k → p.HasBlockingRightSlot k = False
  | _, _, .nil _ hv, k, _ => Walk.hasBlockingRightSlot_nil hv k
  | _, _, .cons _ _ p', 0, h => by simp [Walk.length] at h
  | _, _, .cons _ s p', k + 1, h => by
      rw [Walk.hasBlockingRightSlot_cons_succ]
      have h_lt : p'.length < k := by simp [Walk.length] at h; omega
      exact Walk.hasBlockingRightSlot_out_of_range p' k h_lt

-- Comp invariance for HasBlockingRightSlot at strictly-interior-of-q
-- positions: j < q.length means the slot is inside q.
lemma hasBlockingRightSlot_comp_eq_of_lt {G : CDMG Node} :
    ∀ {u v w : Node} (q : Walk G u v) (r : Walk G v w) (j : ℕ),
      j < q.length →
      ((q.comp r).HasBlockingRightSlot j ↔ q.HasBlockingRightSlot j)
  | _, _, _, .nil _ _, _, _, h => by simp [Walk.length] at h
  | _, _, _, .cons _ s p', r, 0, _ => by
      -- comp produces cons _ s (p'.comp r); both at position 0
      change (Walk.cons _ s (p'.comp r)).HasBlockingRightSlot 0 ↔
             (Walk.cons _ s p').HasBlockingRightSlot 0
      cases s <;> rfl
  | _, _, _, .cons _ s p', r, k + 1, h => by
      change (Walk.cons _ s (p'.comp r)).HasBlockingRightSlot (k + 1) ↔
             (Walk.cons _ s p').HasBlockingRightSlot (k + 1)
      rw [Walk.hasBlockingRightSlot_cons_succ, Walk.hasBlockingRightSlot_cons_succ]
      have h_lt : k < p'.length := by simp [Walk.length] at h; omega
      exact Walk.hasBlockingRightSlot_comp_eq_of_lt p' r k h_lt

-- Junction lemma: HasBlockingRightSlot of q.comp r at position q.length
-- reads the first step of r (when r is non-trivial — here cons-cons).
lemma hasBlockingRightSlot_comp_eq_at_length {G : CDMG Node}
    {b c mid mid₂ : Node} (s : WalkStep G b mid) (s' : WalkStep G mid mid₂)
    (r' : Walk G mid₂ c) :
    ∀ {a' : Node} (q : Walk G a' b),
      (q.comp (Walk.cons mid s (Walk.cons mid₂ s' r'))).HasBlockingRightSlot q.length ↔
        (Walk.cons mid s (Walk.cons mid₂ s' r')).HasBlockingRightSlot 0
  | _, .nil _ _ => by
      change (Walk.cons mid s _).HasBlockingRightSlot 0 ↔ _
      rfl
  | _, .cons _ s₀ q' => by
      change (Walk.cons _ s₀ (q'.comp _)).HasBlockingRightSlot (q'.length + 1) ↔ _
      rw [Walk.hasBlockingRightSlot_cons_succ]
      exact Walk.hasBlockingRightSlot_comp_eq_at_length s s' r' q'

-- Same for r being a cons-nil (length-1 walk at the appended end).
lemma hasBlockingRightSlot_comp_eq_at_length_cons_nil {G : CDMG Node}
    {b c mid : Node} (s : WalkStep G b mid) (hv : c ∈ G) :
    -- here mid = c since nil's type Walk G mid mid forces mid = c
    -- we just need mid ∈ G; we get it from s.target_mem implicitly
    True := by trivial

lemma hasBlockingRightSlot_comp_eq_at_length_singleton {G : CDMG Node}
    {b mid : Node} (s : WalkStep G b mid) (hv : mid ∈ G) :
    ∀ {a' : Node} (q : Walk G a' b),
      (q.comp (Walk.cons mid s (Walk.nil mid hv))).HasBlockingRightSlot q.length ↔
        (Walk.cons mid s (Walk.nil mid hv)).HasBlockingRightSlot 0
  | _, .nil _ _ => by
      change (Walk.cons mid s (Walk.nil mid hv)).HasBlockingRightSlot 0 ↔ _
      rfl
  | _, .cons _ s₀ q' => by
      change (Walk.cons _ s₀ (q'.comp _)).HasBlockingRightSlot (q'.length + 1) ↔ _
      rw [Walk.hasBlockingRightSlot_cons_succ]
      exact Walk.hasBlockingRightSlot_comp_eq_at_length_singleton s hv q'

-- HasBlockingLeftSlot analogs.

-- Out-of-range: HasBlockingLeftSlot at k > p.length is False.
-- (Also p.length when p is non-trivial; needs slot k-1 < p.length, i.e., k ≤ p.length.)
lemma hasBlockingLeftSlot_out_of_range {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.length + 1 ≤ k → p.HasBlockingLeftSlot k = False
  | _, _, .nil _ hv, k, _ => Walk.hasBlockingLeftSlot_nil hv k
  | _, _, .cons _ _ _, 0, h => by simp [Walk.length] at h
  | _, _, .cons _ _ _, 1, h => by simp [Walk.length] at h
  | _, _, .cons _ s p', k + 2, h => by
      rw [Walk.hasBlockingLeftSlot_cons_succ_succ]
      have h_lt : p'.length + 1 ≤ k + 1 := by simp [Walk.length] at h; omega
      exact Walk.hasBlockingLeftSlot_out_of_range p' (k + 1) h_lt

-- Comp invariance for HasBlockingLeftSlot at strictly-interior positions.
lemma hasBlockingLeftSlot_comp_eq_of_lt {G : CDMG Node} :
    ∀ {u v w : Node} (q : Walk G u v) (r : Walk G v w) (k : ℕ),
      k ≤ q.length →
      ((q.comp r).HasBlockingLeftSlot k ↔ q.HasBlockingLeftSlot k)
  | _, _, _, .nil v hv, r, 0, _ => by
      -- nil.comp r = r; both r.HasBlockingLeftSlot 0 and nil.HasBlockingLeftSlot 0 are False
      have h_lhs : ((Walk.nil v hv).comp r).HasBlockingLeftSlot 0 = False := by
        change r.HasBlockingLeftSlot 0 = False
        exact Walk.hasBlockingLeftSlot_zero_false r
      have h_rhs : (Walk.nil v hv).HasBlockingLeftSlot 0 = False :=
        Walk.hasBlockingLeftSlot_zero_false _
      rw [h_lhs, h_rhs]
  | _, _, _, .nil _ _, _, _ + 1, h => by simp [Walk.length] at h
  | _, _, _, .cons _ s p', _, 0, _ => by
      change (Walk.cons _ s (p'.comp _)).HasBlockingLeftSlot 0 ↔
             (Walk.cons _ s p').HasBlockingLeftSlot 0
      cases s <;> rfl
  | _, _, _, .cons _ s p', r, 1, _ => by
      -- HasBlockingLeftSlot 1 depends on s (head step).
      change (Walk.cons _ s (p'.comp r)).HasBlockingLeftSlot 1 ↔
             (Walk.cons _ s p').HasBlockingLeftSlot 1
      cases s <;> rfl
  | _, _, _, .cons _ s p', r, k + 2, h => by
      change (Walk.cons _ s (p'.comp r)).HasBlockingLeftSlot (k + 2) ↔
             (Walk.cons _ s p').HasBlockingLeftSlot (k + 2)
      rw [Walk.hasBlockingLeftSlot_cons_succ_succ, Walk.hasBlockingLeftSlot_cons_succ_succ]
      have h_le : k + 1 ≤ p'.length := by simp [Walk.length] at h; omega
      exact Walk.hasBlockingLeftSlot_comp_eq_of_lt p' r (k + 1) h_le

-- Junction lemma for HasBlockingLeftSlot at q.length + 1 of q.comp r:
-- this reads the first step of r.
lemma hasBlockingLeftSlot_comp_eq_at_succ_length {G : CDMG Node}
    {b c mid : Node} (s : WalkStep G b mid) (r' : Walk G mid c) :
    ∀ {a' : Node} (q : Walk G a' b),
      (q.comp (Walk.cons mid s r')).HasBlockingLeftSlot (q.length + 1) ↔
        (Walk.cons mid s r').HasBlockingLeftSlot 1
  | _, .nil _ _ => by
      change (Walk.cons mid s r').HasBlockingLeftSlot 1 ↔ _
      rfl
  | _, .cons _ s₀ q' => by
      change (Walk.cons _ s₀ (q'.comp _)).HasBlockingLeftSlot (q'.length + 1 + 1) ↔ _
      rw [Walk.hasBlockingLeftSlot_cons_succ_succ]
      exact Walk.hasBlockingLeftSlot_comp_eq_at_succ_length s r' q'

-- Main reverse invariance: HasBlockingLeftSlot on p ↔ HasBlockingRightSlot on p.reverse.
-- Restricted to 1 ≤ k ≤ p.length (the meaningful range for HasBlockingLeftSlot).
-- Under reversal: slot k-1 of p corresponds to slot n-k of p.reverse (where n = p.length).
-- A `.backwardE` step on p (the firing pattern for HasBlockingLeftSlot at position k)
-- reverses to `.forwardE` on p.reverse (the firing pattern for HasBlockingRightSlot
-- at position n - k).  The vertex condition `u ∉ Sc v` transports verbatim.
lemma hasBlockingLeftSlot_reverse_eq_hasBlockingRightSlot {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ), k ≤ p.length →
      (p.reverse.HasBlockingRightSlot (p.length - k) ↔ p.HasBlockingLeftSlot k)
  | _, _, .nil _ hv, k, hk => by
      -- nil: p.length = 0, so k = 0.  Both sides False.
      have hk0 : k = 0 := by simp [Walk.length] at hk; omega
      subst hk0
      have h_lhs : (Walk.nil _ hv).reverse.HasBlockingRightSlot
          ((Walk.nil _ hv).length - 0) = False := by
        change (Walk.nil _ hv).HasBlockingRightSlot _ = False
        exact Walk.hasBlockingRightSlot_nil hv _
      have h_rhs : (Walk.nil _ hv).HasBlockingLeftSlot 0 = False :=
        Walk.hasBlockingLeftSlot_zero_false _
      rw [h_lhs, h_rhs]
  | _, _, .cons _ s (.nil _ hv), k, hk => by
      -- length-1 walk: k ∈ {0, 1}.
      cases k with
      | zero =>
          -- k = 0: both sides False
          have h_lhs :
              (Walk.cons _ s (Walk.nil _ hv)).reverse.HasBlockingRightSlot
                ((Walk.cons _ s (Walk.nil _ hv)).length - 0) = False := by
            change (Walk.cons _ s.reverse (Walk.nil _ _)).HasBlockingRightSlot _ = False
            simp only [Walk.length, Nat.sub_zero]
            rw [Walk.hasBlockingRightSlot_cons_succ]
            exact Walk.hasBlockingRightSlot_nil _ 0
          have h_rhs :
              (Walk.cons _ s (Walk.nil _ hv)).HasBlockingLeftSlot 0 = False :=
            Walk.hasBlockingLeftSlot_zero_false _
          rw [h_lhs, h_rhs]
      | succ k₀ =>
          cases k₀ with
          | zero =>
              -- k = 1: head case.
              change (Walk.cons _ s.reverse (Walk.nil _ _)).HasBlockingRightSlot 0 ↔
                     (Walk.cons _ s (Walk.nil _ hv)).HasBlockingLeftSlot 1
              cases s <;> rfl
          | succ k₁ =>
              -- k ≥ 2 contradicts hk : k ≤ 1
              simp [Walk.length] at hk
  | _, _, .cons mid s (.cons mid₂ s' p''), k, hk => by
      -- length ≥ 2 walk.
      cases k with
      | zero =>
          -- k = 0: both sides False
          have h_lhs : (Walk.cons mid s (Walk.cons mid₂ s' p'')).reverse.HasBlockingRightSlot
              ((Walk.cons mid s (Walk.cons mid₂ s' p'')).length - 0) = False := by
            rw [Nat.sub_zero,
                show (Walk.cons mid s (Walk.cons mid₂ s' p'')).length =
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).reverse.length from
                  (Walk.length_reverse _).symm]
            exact Walk.hasBlockingRightSlot_at_length_false _
          have h_rhs : (Walk.cons mid s (Walk.cons mid₂ s' p'')).HasBlockingLeftSlot 0 = False :=
            Walk.hasBlockingLeftSlot_zero_false _
          rw [h_lhs, h_rhs]
      | succ k₀ =>
          cases k₀ with
          | zero =>
              -- k = 1: head case.
              -- p.length - 1 = p''.length + 1.
              -- p.reverse = p''.reverse.comp (cons mid s'.reverse (cons u s.reverse (nil _ _)))
              -- At position p''.length + 1 = p''.reverse.length + 1 of this comp,
              -- the junction lemma applies: reads the first step of Y, which is s'.reverse.
              -- Wait actually we want HasBlockingRightSlot, not HasBlockingLeftSlot.
              -- At position p''.length + 1, HasBlockingRightSlot reads slot p''.length + 1.
              -- Slot p''.length + 1 of (p''.reverse.comp Y) where Y starts at slot p''.reverse.length = p''.length.
              -- So slot p''.length + 1 is INSIDE Y (specifically the second step of Y = s.reverse).
              -- Wait wait. Let me reread Y's structure: Y = cons mid s'.reverse (cons u s.reverse (nil u _)).
              -- Y has length 2. Steps at slots 0 and 1.
              -- Slot 0 of Y = s'.reverse. Slot 1 of Y = s.reverse.
              -- In the comp, slot j of p''.reverse.comp Y for j ≥ p''.length corresponds to slot (j - p''.length) of Y.
              -- So slot p''.length + 1 = slot 1 of Y = s.reverse.
              -- HasBlockingRightSlot at position p''.length + 1 reads slot p''.length + 1 = s.reverse.
              -- The check: s.reverse fires HasBlockingRightSlot 0 (when viewed as starting at its position) iff s.reverse = .forwardE with target ∉ Sc source.
              -- s.reverse : WalkStep G mid u, where u = original p's start.
              -- If s = .backwardE h (with h : (mid, u) ∈ E), then s.reverse = .forwardE h
              --   (with h : (mid, u) ∈ E, now as WalkStep G mid u).
              --   The check: target ∉ Sc source. target = u, source = mid. So u ∉ Sc mid.
              -- For RHS: p.HasBlockingLeftSlot 1. By pattern, depends on s.
              --   s = .backwardE h: u ∉ Sc mid (where u = source of s, mid = target).
              --   s = .forwardE / .bidir: False.
              -- So they match when s = .backwardE.
              -- For s = .forwardE: s.reverse = .backwardE, HasBlockingRightSlot fires only on .forwardE → False. RHS: also False.
              -- For s = .bidir: s.reverse = .bidir, HasBlockingRightSlot fires only on .forwardE → False. RHS: also False.
              -- Setup p.reverse:
              have h_len_sub :
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).length - 1 = p''.length + 1 := by
                simp [Walk.length]
              rw [h_len_sub]
              have h_rev_eq :
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).reverse =
                  p''.reverse.comp
                    (Walk.cons mid s'.reverse
                      (Walk.cons _ s.reverse
                        (Walk.nil _ (WalkStep.source_mem s)))) := by
                change (p''.reverse.comp
                          (Walk.cons mid s'.reverse
                            (Walk.nil _ (WalkStep.source_mem s')))).comp _ = _
                rw [Walk.comp_assoc]
                rfl
              rw [h_rev_eq]
              -- Use comp_eq_of_lt to push HasBlockingRightSlot inside? No, position p''.length + 1
              -- is NOT < p''.reverse.length = p''.length. It's exactly one more.
              -- So we need a different lemma — junction is at q.length, but we're at q.length + 1.
              -- Hmm. Let me think: q.length + 1 corresponds to the SECOND slot of the appended walk.
              -- So we want a "slot 1 of Y" lemma, which by the cons_succ pattern equals slot 0 of Y.tail.
              -- Y = cons mid s'.reverse (cons u s.reverse (nil _ _)). Y.tail = cons u s.reverse (nil _ _).
              -- HasBlockingRightSlot 1 of Y = HasBlockingRightSlot 0 of Y.tail = check on s.reverse.
              -- For q.comp Y at q.length + 1, after descending through all of q, we get to
              -- "Y at position q.length + 1 - q.length = 1". So we want to evaluate
              -- HasBlockingRightSlot 1 of Y at the junction.
              -- Use comp_eq_of_lt or comp_eq_at_length variant?
              -- Let me just compute.
              -- (q.comp Y).HasBlockingRightSlot (q.length + 1):
              --   For q nil: = Y.HasBlockingRightSlot 1 = check on s.reverse.
              --   For q cons mid₀ s₀ q': = (q'.comp Y).HasBlockingRightSlot q'.length + 1 (using cons_succ);
              --                          by IH recurses... this is similar to the junction lemma.
              -- Actually let me just use the at_length_singleton lemma but for the inner Y.tail.
              -- Y = cons mid s'.reverse (cons u s.reverse (nil u _)) = cons mid s'.reverse Y'
              -- where Y' = cons u s.reverse (nil u _).
              -- So q.comp Y = q.comp (cons mid s'.reverse Y') = q.snocCons... hmm
              -- Actually q.comp (cons mid s'.reverse Y') = (q.comp_with_first_step) ... not quite.
              -- Let me think directly.
              -- The walk q.comp Y, at position q.length + 1, reads slot q.length + 1.
              -- After q's slots (0..q.length-1), slot q.length is the FIRST slot of Y.
              -- Slot q.length + 1 is the SECOND slot of Y.
              -- For our Y (length 2), this is the second (last) slot = s.reverse.
              -- Hmm but the position q.length + 1 conceptually = "slot q.length + 1" is also = "junction + 1".
              -- We want to read what's at slot q.length + 1 = "first slot of Y.tail".
              -- (q.comp Y) = (q.snocStep) ... no, this is hard.
              -- Let me just use the comp_at_length_singleton lemma with Y' = cons u s.reverse (nil u _)
              -- AND noting that q.comp Y = (q.snoc s'.reverse).comp Y'.
              -- (q.snoc s'.reverse) has length q.length + 1.
              -- So we want HasBlockingRightSlot at (q.length + 1) on ((q.snoc s'.reverse).comp Y')
              -- = HasBlockingRightSlot at (q.snoc s'.reverse).length on (q.snoc s'.reverse.comp Y')
              -- By comp_eq_at_length_singleton on Y' = cons u s.reverse (nil _ _),
              --   this equals Y'.HasBlockingRightSlot 0 = check on s.reverse.
              -- Hmm but we don't have a snoc function...
              -- Let me just write the manipulation directly.
              have h_pos : p''.reverse.length + 1 = p''.length + 1 := by rw [Walk.length_reverse]
              -- Goal: (p''.reverse.comp Y).HasBlockingRightSlot (p''.length + 1) ↔ ...
              -- where Y = cons mid s'.reverse (cons _ s.reverse (nil _ _))
              -- = (p''.reverse.comp (cons mid s'.reverse (cons _ s.reverse (nil _ _))))
              --     .HasBlockingRightSlot (p''.length + 1)
              -- Rewrite p''.length = p''.reverse.length, then this is "position +1 of junction"
              rw [← h_pos]
              -- = position p''.reverse.length + 1 of comp
              -- Using comp = cons-cons structure of the right part, comp_at_length_singleton:
              -- Actually, the right part of comp is (cons mid s'.reverse (cons _ s.reverse (nil _ _)))
              -- which has length 2. So total length is p''.reverse.length + 2 = p''.length + 2 = p.length. ✓
              -- We want HasBlockingRightSlot at position p''.reverse.length + 1 (= p.length - 1).
              -- Let's use the recursive structure: comp = p''.reverse.comp X.
              -- For position k+1 on cons-headed walk: cons_succ reduces to position k on tail.
              -- Hmm but p''.reverse may not be cons (if p'' is nil).
              -- Let me case-split on p''.
              -- Actually, let me try a different approach: use the comp_at_length variant with the
              -- SHIFTED head.
              -- I.e., write (cons mid s'.reverse Y') = (nil mid _).snoc ??? hmm
              -- Or: regroup the comp. Since comp is associative, we can write:
              -- p''.reverse.comp (cons mid s'.reverse Y') = (p''.reverse.comp (cons mid s'.reverse (nil mid _))).comp Y'
              -- (where Y' = cons _ s.reverse (nil _ _))
              -- Then we have a new q' = p''.reverse.comp (cons mid s'.reverse (nil mid _))
              -- with q'.length = p''.length + 1.
              -- Position p''.reverse.length + 1 = p''.length + 1 = q'.length.
              -- HasBlockingRightSlot at q'.length of q'.comp Y' using comp_at_length_singleton gives:
              -- Y'.HasBlockingRightSlot 0 = check on s.reverse.
              -- This is what we want.
              have h_eq2 :
                  p''.reverse.comp (Walk.cons mid s'.reverse
                    (Walk.cons _ s.reverse (Walk.nil _ (WalkStep.source_mem s)))) =
                  (p''.reverse.comp (Walk.cons mid s'.reverse
                    (Walk.nil mid (WalkStep.source_mem s')))).comp
                    (Walk.cons _ s.reverse (Walk.nil _ (WalkStep.source_mem s))) := by
                rw [Walk.comp_assoc]
                rfl
              rw [h_eq2]
              -- Now position p''.reverse.length + 1 = (p''.reverse.comp (...)).length
              -- = p''.reverse.length + 1 ✓
              have h_q'_len : (p''.reverse.comp (Walk.cons mid s'.reverse
                  (Walk.nil mid (WalkStep.source_mem s')))).length = p''.reverse.length + 1 := by
                rw [Walk.length_comp]
                rfl
              rw [show p''.reverse.length + 1 =
                  (p''.reverse.comp (Walk.cons mid s'.reverse
                    (Walk.nil mid (WalkStep.source_mem s')))).length from h_q'_len.symm]
              rw [Walk.hasBlockingRightSlot_comp_eq_at_length_singleton s.reverse
                  (WalkStep.source_mem s)]
              -- Now: (cons _ s.reverse (nil _ _)).HasBlockingRightSlot 0 ↔ p.HasBlockingLeftSlot 1
              -- LHS depends on s.reverse; RHS depends on s.
              -- For s = .forwardE: s.reverse = .backwardE → LHS False; RHS False (forwardE at position 1).
              -- For s = .backwardE: s.reverse = .forwardE → LHS check; RHS check (same condition).
              -- For s = .bidir: s.reverse = .bidir → LHS False; RHS False.
              cases s <;> rfl
          | succ k₁ =>
              -- k = k₁ + 2 ≥ 2.  Use IH + comp invariance.
              have h_rhs_eq :
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).HasBlockingLeftSlot (k₁ + 2) =
                  (Walk.cons mid₂ s' p'').HasBlockingLeftSlot (k₁ + 1) :=
                Walk.hasBlockingLeftSlot_cons_succ_succ _ _ _ _
              rw [h_rhs_eq]
              have h_lhs_pos :
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).length - (k₁ + 2) =
                  (Walk.cons mid₂ s' p'').length - (k₁ + 1) := by
                simp [Walk.length]
              rw [h_lhs_pos]
              -- p.reverse = (cons mid₂ s' p'').reverse.comp (cons _ s.reverse (nil _ _))
              have h_rev :
                  (Walk.cons mid s (Walk.cons mid₂ s' p'')).reverse =
                  (Walk.cons mid₂ s' p'').reverse.comp
                    (Walk.cons _ s.reverse (Walk.nil _ (WalkStep.source_mem s))) := rfl
              rw [h_rev]
              -- comp invariance: position (cons mid₂ s' p'').length - (k₁ + 1) < (...) .length
              have h_lt : (Walk.cons mid₂ s' p'').length - (k₁ + 1) <
                  (Walk.cons mid₂ s' p'').reverse.length := by
                rw [Walk.length_reverse]
                have h_inner_len : (Walk.cons mid₂ s' p'').length = p''.length + 1 := by
                  simp [Walk.length]
                rw [h_inner_len]
                simp [Walk.length] at hk
                omega
              rw [Walk.hasBlockingRightSlot_comp_eq_of_lt _ _ _ h_lt]
              have hk' : k₁ + 1 ≤ (Walk.cons mid₂ s' p'').length := by
                simp [Walk.length] at hk ⊢; omega
              exact Walk.hasBlockingLeftSlot_reverse_eq_hasBlockingRightSlot
                (Walk.cons mid₂ s' p'') (k₁ + 1) hk'

-- The mirror invariance, derived from the above via `Walk.reverse_involution`.
lemma hasBlockingRightSlot_reverse_eq_hasBlockingLeftSlot {G : CDMG Node}
    {u v : Node} (p : Walk G u v) (k : ℕ) (hk : k ≤ p.length) :
    p.reverse.HasBlockingLeftSlot (p.length - k) ↔ p.HasBlockingRightSlot k := by
  -- Apply the LeftSlot invariance to p.reverse at position (p.length - k):
  -- p.reverse.reverse.HasBlockingRightSlot (p.reverse.length - (p.length - k))
  --   ↔ p.reverse.HasBlockingLeftSlot (p.length - k).
  -- LHS = p.HasBlockingRightSlot (p.length - (p.length - k)) = p.HasBlockingRightSlot k
  -- (using k ≤ p.length).
  have h_rev_len_eq : p.reverse.length = p.length := Walk.length_reverse p
  have h_sub_pos : p.length - k ≤ p.reverse.length := by rw [h_rev_len_eq]; omega
  have h_iff := Walk.hasBlockingLeftSlot_reverse_eq_hasBlockingRightSlot
    p.reverse (p.length - k) h_sub_pos
  -- h_iff: p.reverse.reverse.HasBlockingRightSlot (p.reverse.length - (p.length - k))
  --        ↔ p.reverse.HasBlockingLeftSlot (p.length - k)
  rw [Walk.reverse_involution, h_rev_len_eq] at h_iff
  -- h_iff: p.HasBlockingRightSlot (p.length - (p.length - k))
  --        ↔ p.reverse.HasBlockingLeftSlot (p.length - k)
  have h_arith : p.length - (p.length - k) = k := by omega
  rw [h_arith] at h_iff
  exact h_iff.symm

end Walk

-- REFACTOR-BLOCK-DELETE-BEGIN: isNonCollider_reverse
-- IsNonCollider invariance under reverse (follows from IsCollider invariance + length).
lemma Walk.isNonCollider_reverse {G : CDMG Node}
    {u v : Node} (p : Walk G u v) (k : ℕ) (hk : k ≤ p.length) :
    p.reverse.IsNonCollider (p.length - k) ↔ p.IsNonCollider k := by
  unfold Walk.IsNonCollider
  rw [Walk.length_reverse]
  constructor
  · rintro ⟨_h_le, h_not_coll⟩
    refine ⟨hk, ?_⟩
    intro h_coll
    exact h_not_coll ((Walk.isCollider_reverse p k).mpr h_coll)
  · rintro ⟨_h_le, h_not_coll⟩
    refine ⟨by omega, ?_⟩
    intro h_coll
    exact h_not_coll ((Walk.isCollider_reverse p k).mp h_coll)
-- REFACTOR-BLOCK-DELETE-END: isNonCollider_reverse

-- REFACTOR-BLOCK-DELETE-BEGIN: isBlockableNonCollider_reverse
-- IsBlockableNonCollider invariance under reverse.
lemma Walk.isBlockableNonCollider_reverse {G : CDMG Node}
    {u v : Node} (p : Walk G u v) (k : ℕ) (hk : k ≤ p.length) :
    p.reverse.IsBlockableNonCollider (p.length - k) ↔ p.IsBlockableNonCollider k := by
  unfold Walk.IsBlockableNonCollider
  rw [Walk.isNonCollider_reverse p k hk, Walk.length_reverse]
  -- Now: p.IsNonCollider k ∧
  --      ((p.length - k = 0 ∨ p.length - k = p.length ∨ p.reverse.HasBlockingLeftSlot (...)
  --        ∨ p.reverse.HasBlockingRightSlot (...)))
  -- ↔ p.IsNonCollider k ∧
  --   (k = 0 ∨ k = p.length ∨ p.HasBlockingLeftSlot k ∨ p.HasBlockingRightSlot k)
  rw [Walk.hasBlockingRightSlot_reverse_eq_hasBlockingLeftSlot p k hk,
      Walk.hasBlockingLeftSlot_reverse_eq_hasBlockingRightSlot p k hk]
  -- The remaining bit is just position arithmetic for the end-position disjuncts.
  constructor
  · rintro ⟨h_nc, h_disj⟩
    refine ⟨h_nc, ?_⟩
    rcases h_disj with h_eq | h_eq | h_left | h_right
    · -- p.length - k = 0 → k = p.length (since k ≤ p.length)
      have : k = p.length := by omega
      exact Or.inr (Or.inl this)
    · -- p.length - k = p.length → k = 0
      have : k = 0 := by omega
      exact Or.inl this
    · -- p.HasBlockingRightSlot k -- wait, the rw should have flipped it.
      -- Hmm let me retrace. After my rw, the disjunct order is:
      -- p.length - k = 0 ∨ p.length - k = p.length ∨ p.HasBlockingRightSlot k ∨ p.HasBlockingLeftSlot k
      -- because LeftSlot at (p.length - k) ↔ RightSlot at k by my second lemma applied directly.
      -- Wait no, the disjuncts on p.reverse are:
      --   p.length - k = 0
      --   p.length - k = p.length
      --   p.reverse.HasBlockingLeftSlot (p.length - k)
      --   p.reverse.HasBlockingRightSlot (p.length - k)
      -- After rw [hasBlockingRightSlot_reverse_eq_hasBlockingLeftSlot]:
      --   ... p.HasBlockingRightSlot k (this replaces the third)
      -- After rw [hasBlockingLeftSlot_reverse_eq_hasBlockingRightSlot]:
      --   ... p.HasBlockingLeftSlot k (this replaces the fourth)
      -- So disjuncts become: 0, length, RightSlot, LeftSlot.
      -- We want: 0, length, LeftSlot, RightSlot.
      -- They're equivalent by Or.comm.
      exact Or.inr (Or.inr (Or.inr h_left))
    · exact Or.inr (Or.inr (Or.inl h_right))
  · rintro ⟨h_nc, h_disj⟩
    refine ⟨h_nc, ?_⟩
    rcases h_disj with h_eq | h_eq | h_left | h_right
    · -- k = 0 → p.length - k = p.length
      have : p.length - k = p.length := by omega
      exact Or.inr (Or.inl this)
    · -- k = p.length → p.length - k = 0
      have : p.length - k = 0 := by omega
      exact Or.inl this
    · exact Or.inr (Or.inr (Or.inr h_left))
    · exact Or.inr (Or.inr (Or.inl h_right))
-- REFACTOR-BLOCK-DELETE-END: isBlockableNonCollider_reverse

namespace Walk

-- Walk.vertices has length equal to walk.length + 1.
lemma vertices_length {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.vertices.length = p.length + 1
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p' => by
      change (_ :: p'.vertices).length = _
      rw [List.length_cons, Walk.vertices_length p']
      rfl

-- Helper: if `p.vertices[k]? = some vk` and `k ≤ p.length`, then
-- `p.reverse.vertices[p.length - k]? = some vk`.
-- Uses `vertices_reverse` and standard List.reverse lemmas.
lemma vertices_reverse_getElem? {G : CDMG Node}
    {u v : Node} (p : Walk G u v) (k : ℕ) (vk : Node)
    (h_get : p.vertices[k]? = some vk) :
    p.reverse.vertices[p.length - k]? = some vk := by
  rw [Walk.vertices_reverse]
  have h_k_lt : k < p.vertices.length := by
    rw [List.getElem?_eq_some_iff] at h_get
    obtain ⟨h_lt, _⟩ := h_get
    exact h_lt
  rw [Walk.vertices_length] at h_k_lt
  rw [List.getElem?_reverse]
  · convert h_get using 2
    rw [Walk.vertices_length]
    omega
  · rw [Walk.vertices_length]
    omega

end Walk

-- REFACTOR-BLOCK-DELETE-BEGIN: isSigmaBlockedGiven_reverse_forward
-- σ-blocking invariance under walk reversal.
-- The forward direction maps a witness (k, vk) at position k on p to
-- a witness (p.length - k, vk) at position p.length - k on p.reverse,
-- using IsCollider and IsBlockableNonCollider invariance.
lemma Walk.isSigmaBlockedGiven_reverse_forward {G : CDMG Node} :
    ∀ {u v : Node} (q : Walk G u v) (C : Set Node) (hC : C ⊆ ↑G.J ∪ ↑G.V),
      q.IsSigmaBlockedGiven C hC → q.reverse.IsSigmaBlockedGiven C hC := by
  intro u v q C hC h
  unfold Walk.IsSigmaBlockedGiven at h ⊢
  rcases h with ⟨k, vk, h_get, h_coll, h_anc⟩ | ⟨k, vk, h_get, h_blk, h_inC⟩
  · have h_k_le : k ≤ q.length := by
      rw [List.getElem?_eq_some_iff] at h_get
      obtain ⟨h_lt, _⟩ := h_get
      rw [Walk.vertices_length] at h_lt
      omega
    refine Or.inl ⟨q.length - k, vk, ?_, ?_, h_anc⟩
    · exact Walk.vertices_reverse_getElem? q k vk h_get
    · exact (Walk.isCollider_reverse q k).mpr h_coll
  · have h_k_le : k ≤ q.length := by
      rw [List.getElem?_eq_some_iff] at h_get
      obtain ⟨h_lt, _⟩ := h_get
      rw [Walk.vertices_length] at h_lt
      omega
    refine Or.inr ⟨q.length - k, vk, ?_, ?_, h_inC⟩
    · exact Walk.vertices_reverse_getElem? q k vk h_get
    · exact (Walk.isBlockableNonCollider_reverse q k h_k_le).mpr h_blk
-- REFACTOR-BLOCK-DELETE-END: isSigmaBlockedGiven_reverse_forward

-- REFACTOR-BLOCK-DELETE-BEGIN: isSigmaBlockedGiven_reverse
lemma Walk.isSigmaBlockedGiven_reverse {G : CDMG Node}
    {u v : Node} (p : Walk G u v) (C : Set Node) (hC : C ⊆ ↑G.J ∪ ↑G.V) :
    p.IsSigmaBlockedGiven C hC ↔ p.reverse.IsSigmaBlockedGiven C hC := by
  constructor
  · exact Walk.isSigmaBlockedGiven_reverse_forward p C hC
  · intro h_rev
    have h_p : p.reverse.reverse.IsSigmaBlockedGiven C hC :=
      Walk.isSigmaBlockedGiven_reverse_forward p.reverse C hC h_rev
    rw [Walk.reverse_involution] at h_p
    exact h_p
-- REFACTOR-BLOCK-DELETE-END: isSigmaBlockedGiven_reverse

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: sigma_separation_symmetric
--
-- σ-separation is symmetric in its first two arguments: for every
-- CDMG `G` with empty input-node set `G.J = ∅` and every triple of
-- subsets `A, B, C ⊆ ↑G.J ∪ ↑G.V` (equivalently `A, B, C ⊆ ↑G.V`
-- under `hJ`),
--
--     `G.IsSigmaSeparated hJ A B C hA hB hC
--       ↔ G.IsSigmaSeparated hJ B A C hB hA hC`.
--
-- *Verbatim LN block* (`graphs.tex`, inside `def_3_18` item 4):
--
/-
\begin{claimmark}
Note that $\sigma$-separation is symmetric:
$A \sPerp_G B \given C \iff B \sPerp_G A \given C$, since when
$J = \emptyset$ the set of walks between $A$ and $B$ is the same
regardless of direction, and the $\sigma$-blocking conditions are
invariant under walk reversal.
\end{claimmark}
-/
--
-- ## Design choice — sigma_separation_symmetric
--
-- *Predicate name: `IsSigmaSeparated`, not `IsISigmaSeparated`.*  The
--   LN states the claim purely in σ-language: `A \sPerp_G B \given C`,
--   which per `def_3_18` item 4 is the renamed-under-`J = ∅` alias of
--   `\isPerp_G`.  The rewritten canonical tex makes `J = ∅` the
--   standing hypothesis, matching `\sPerp_G`'s scope.  Using
--   `IsSigmaSeparated` (not `IsISigmaSeparated`) at the signature
--   level keeps the LN-to-Lean correspondence one-to-one — the LN
--   never mentions iσ-separation in this claim, so the Lean statement
--   does not either.  A parallel iσ-version can be stated downstream
--   if needed; it is not part of *this* row.
--
-- *Explicit `hJ : G.J = ∅` as a propositional premise on the
--   theorem.*  Per `def_3_18` item 4, the `\sPerp_G` notation is
--   *defined* only under `J = ∅` — there is no σ-separation
--   predicate to speak of outside that regime.  Surfacing `hJ` as a
--   propositional hypothesis matches the LN's notational scope
--   exactly and lets `IsSigmaSeparated` (the `J=∅`-named alias)
--   appear on both sides of the biconditional with consistent
--   typing.  The wording-check item
--   `claim_unrestricted_but_proof_only_covers_J_empty` is resolved
--   as case (b): the LN's "when $J = \emptyset$" is the *scope of
--   the notation*, not a partial-justification qualifier on a
--   would-be-general claim.  Two alternatives were considered and
--   rejected:
--   - A `JEmpty`-restricted CDMG subtype (e.g.
--     `structure DMG extends CDMG Node where hJ : J = ∅`, or an
--     existing `def_3_7` `IsDMG` typeclass-style restriction)
--     would force every downstream consumer to package its CDMG +
--     `J = ∅` evidence into a fresh structure before invoking
--     symmetry, scrambling the LN's "let $G$ be a CDMG; suppose
--     $J = \emptyset$" reading and pulling in an upstream
--     dependency on `def_3_7` this row otherwise does not need.
--   - A side definition `IsSigmaSeparated' (G : CDMG Node) (A B C)
--     := G.J = ∅ ∧ G.IsSigmaSeparated …` baking `hJ` into a
--     standalone `Prop` was rejected: it would diverge from
--     `def_3_18` item 4's signature shape (which takes `hJ`
--     positionally) and break the one-to-one LN-to-Lean
--     correspondence on the σ-separation predicate at the call
--     site.
--   Taking `hJ` directly as a propositional theorem hypothesis
--   matches `def_3_18` item 4's positional binding byte-for-byte,
--   keeps the σ-vs-iσ symbolic distinction visible at goal
--   displays (no eager unfolding), and lets the downstream consumer
--   discharge `hJ` from its own ambient hypotheses without
--   restructuring its CDMG.
--
-- *`A B C : Set Node`, not `Finset Node`.*  Matches
--   `IsSigmaSeparated`'s carrier and the LN's "not necessarily
--   non-empty, not necessarily disjoint" permissiveness.  No
--   disjointness or non-emptiness assumption is taken on `A, B, C`,
--   matching the LN's rewritten "$A, B, C$ are not assumed to be
--   pairwise disjoint, nor non-empty" clause.
--
-- *Three subset hypotheses `(hA hB hC : … ⊆ ↑G.J ∪ ↑G.V)`, passed
--   through unmodified to `IsSigmaSeparated`.*  These are the typing
--   premises `IsSigmaSeparated` takes by signature (which closes the
--   silent-admission leak the predicate would otherwise exhibit if
--   `A`/`B`/`C` contained out-of-graph nodes); we pass them through
--   verbatim — on the LHS as `(hA, hB, hC)`, on the RHS as
--   `(hB, hA, hC)` — so the theorem composes mechanically with the
--   upstream predicate and downstream consumers can invoke it
--   without re-deriving any typing premises.  An alternative shape
--   that reconciles `hA, hB, hC : … ⊆ ↑G.J ∪ ↑G.V` to the simpler
--   `… ⊆ ↑G.V` reading (since `hJ` makes the two equivalent: under
--   `G.J = ∅`, `↑G.J ∪ ↑G.V = ∅ ∪ ↑G.V = ↑G.V`) was considered and
--   rejected: any such reformulation would force the theorem to
--   re-derive the equivalence at every invocation site (or push
--   that obligation onto the consumer), whereas pulling the typing
--   premises through verbatim keeps the Lean signature faithful to
--   the upstream predicate's contract and lets the consumer run the
--   reconciliation `… ⊆ ↑G.V ↔ … ⊆ ↑G.J ∪ ↑G.V` derivation
--   downstream when it actually has the simpler hypothesis on hand.
--   The LN-equivalence is recorded in the rewritten canonical tex's
--   parenthetical "equivalently $A, B, C \ins J \cup V$, since
--   $J = \emptyset$" so future readers can match the two phrasings.
--
-- *Biconditional `↔`, exactly as the LN spells it.*  The LN block is
--   "$A \sPerp_G B \given C \iff B \sPerp_G A \given C$"; the Lean
--   conclusion uses `↔` against the same predicate, swapping the
--   first two `Set` arguments and the corresponding subset proofs
--   `hA ↔ hB` on the right-hand side to match the predicate's
--   positional binding `(A, B, C, hA, hB, hC)`.  No reformulation
--   into a one-direction implication + symmetry remark — the LN
--   states the biconditional directly, so the Lean statement does
--   too.  A `Symmetric` typeclass / `Symmetric`-relation encoding
--   (i.e. `Symmetric (fun A B => G.IsSigmaSeparated hJ A B C hA hB hC)`)
--   was considered and rejected: `IsSigmaSeparated` is a 3-ary
--   relation in the relevant slots `(A, B, C)` (with `G, hJ, C, hC`
--   fixed parameters and `hA, hB` carried as positional typing
--   evidence that has to swap alongside `(A, B)`), not a 2-ary
--   `Set Node → Set Node → Prop` relation; folding it into
--   `Symmetric` would force consumers to either curry away `C, hC`
--   at every use site or rely on a partially-applied form that
--   obscures the LN-grep correspondence on `A \sPerp_G B \given C`.
--   Two separate one-direction theorems (`forward` and `backward`)
--   were also rejected: the LN's `\iff` is the single rw-friendly
--   shape downstream consumers will reach for (most uses transport
--   the predicate across the swap, not extract one direction),
--   splitting into two would double the lemma count without buying
--   anything beyond what `Iff.mp` / `Iff.mpr` already provide.
--
-- *Argument order `(G, hJ, A, B, C, hA, hB, hC)` mirrors the
--   upstream `IsSigmaSeparated` signature byte-for-byte.*  On the
--   RHS the transposition `(B, A, C, hB, hA, hC)` is the *unique*
--   well-typed swap that spells `B \sPerp_G A \given C`: `C` and
--   `hC` stay put because the conditioning set is symmetric in the
--   LN and `hC` types against the unchanged `C`; the typing
--   evidence `hA, hB` has to swap alongside its `A, B` because
--   `IsSigmaSeparated`'s second positional set-slot takes the
--   subset proof for *whatever set sits there*, not a fixed name.
--   This makes both sides of the `↔` visually a single-token swap
--   of the first two `Set` arguments (with their typing evidence
--   following), and downstream consumers can `rw
--   [sigma_separation_symmetric hJ A B C hA hB hC]` without
--   re-deriving the typing premises — they already have
--   `(hA, hB, hC)` from the LHS occurrence and the rewrite reuses
--   them on the RHS occurrence.  Any other rebinding (e.g.
--   permuting `C` into the first or second slot, or naming the
--   typing-evidence binders `hA', hB'` to flag that they typed
--   different sets on the LHS than on the RHS) would break this
--   mechanical-rewrite property and force the consumer to invoke
--   the symmetry as a two-step `mp`/`mpr` extraction.
--
-- *Theorem name `sigma_separation_symmetric` (snake_case).*  Matches
--   the chapter convention used by `acyclic_non_colliders_blockable`
--   in this very section (`AcyclicNonCollidersBlockable.lean`), and
--   by every other top-level theorem in the chapter.  The row's
--   `title` field is `SigmaSeparationSymmetric` (PascalCase, used for
--   the file name); the Lean identifier is the snake_case
--   transliteration.
--
-- *Body is exactly `:= by sorry`.*  This file is the Manager A
--   statement step; the proof obligation will be discharged by the
--   `prove_claim_in_lean` worker after `write_tex_proof` /
--   `verify_tex_proof` have produced and verified the mathematical
--   proof.  The workspace scratchpad (`workspace_claim_3_22.md`)
--   carries an operator hint on the proof strategy that is for
--   Manager B, not for this row.
--
-- *Paper-trail signpost for Manager B (proof phase).*  See
--   `workspace_claim_3_22.md` for the carried-over operator hint:
--   build a *custom local* walk-reversal helper that preserves
--   channel information (or prove the per-position
--   `IsBlockableNonCollider` equivalence directly without
--   constructing the reversed `Walk` object) — do NOT touch
--   `def_3_1` / `def_3_4` / `def_3_16`.  Under `J = ∅` the
--   symmetry is mathematically trivial because per-vertex
--   blockability depends only on incident-edge geometry at the
--   vertex, not on traversal direction; a > 500-line generic
--   reversal-infrastructure detour is a signal the proof has
--   wandered off the right path.
-- claim_3_22 -- start statement
theorem sigma_separation_symmetric
    (G : CDMG Node) (hJ : G.J = ∅) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V)
    (hC : C ⊆ ↑G.J ∪ ↑G.V) :
    G.IsSigmaSeparated hJ A B C hA hB hC ↔
      G.IsSigmaSeparated hJ B A C hB hA hC
-- claim_3_22 -- end statement
:= by
  -- Unfold IsSigmaSeparated = IsISigmaSeparated.
  unfold CDMG.IsSigmaSeparated CDMG.IsISigmaSeparated
  -- The universal-over-walks statement.  Under hJ : G.J = ∅, (G.J : Set Node) ∪ X = X.
  have h_J_empty : (↑G.J : Set Node) = ∅ := by
    rw [hJ]; simp
  -- It suffices to prove one direction (by symmetry of A and B).
  -- Forward direction: assume A σ⊥ B | C; show B σ⊥ A | C.
  -- Given π : Walk G u v with u ∈ B and v ∈ J ∪ A = A,
  --   consider π.reverse : Walk G v u with v ∈ A and u ∈ B = J ∪ B.
  --   By hypothesis applied to π.reverse, π.reverse is σ-blocked.
  --   By σ-blocking invariance under reverse, π is σ-blocked.
  have one_direction :
      ∀ {X Y : Set Node} {hX : X ⊆ ↑G.J ∪ ↑G.V} {hY : Y ⊆ ↑G.J ∪ ↑G.V},
        (∀ {u v : Node} (π : Walk G u v), u ∈ X → v ∈ (↑G.J : Set Node) ∪ Y →
            π.IsSigmaBlockedGiven C hC) →
        ∀ {u v : Node} (π : Walk G u v), u ∈ Y → v ∈ (↑G.J : Set Node) ∪ X →
            π.IsSigmaBlockedGiven C hC := by
    intro X Y _ _ h u v π h_start h_end
    -- π : Walk G u v with u ∈ Y, v ∈ J ∪ X.
    -- Under hJ, v ∈ X.  But hypothesis h takes "u ∈ X, v ∈ J ∪ Y".
    -- Apply h to π.reverse : Walk G v u with v ∈ X, u ∈ J ∪ Y (since u ∈ Y).
    have h_end' : v ∈ X := by
      rw [h_J_empty, Set.empty_union] at h_end
      exact h_end
    have h_start' : u ∈ (↑G.J : Set Node) ∪ Y := by
      rw [h_J_empty, Set.empty_union]
      exact h_start
    have h_rev_blocked : π.reverse.IsSigmaBlockedGiven C hC :=
      h π.reverse h_end' h_start'
    exact (Walk.isSigmaBlockedGiven_reverse π C hC).mpr h_rev_blocked
  constructor
  · exact fun h => one_direction (X := A) (Y := B) (hX := hA) (hY := hB) h
  · exact fun h => one_direction (X := B) (Y := A) (hX := hB) (hY := hA) h
-- REFACTOR-BLOCK-ORIGINAL-END: sigma_separation_symmetric

-- ---------- Refactor reversal infrastructure (side-aware) ------------------
-- The lemmas below are the side-aware analogues of the pre-refactor
-- reversal helpers above (`WalkStep.isInto_reverse`,
-- `Walk.isCollider_reverse`, `Walk.isNonCollider_reverse`,
-- `Walk.isBlockableNonCollider_reverse`,
-- `Walk.isSigmaBlockedGiven_reverse_forward`,
-- `Walk.isSigmaBlockedGiven_reverse`).  Each is wrapped in its own
-- REPLACEMENT marker block so Phase 7 cleanup drops the `refactor_`
-- prefix uniformly across helpers and theorem.  The walk-reversal
-- primitive `WalkStep.reverse` / `Walk.reverse`, the
-- `Walk.HasBlockingLeftSlot` / `Walk.HasBlockingRightSlot` reversal-
-- invariance lemmas, the `vertices_reverse_getElem?` transport lemma,
-- and the walk-comp infrastructure are reused unchanged — those
-- helpers do not depend on the collider classifier and so survive the
-- refactor mechanically.

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: headAtTarget_reverse (was: refactor_headAtTarget_reverse)
namespace WalkStep
-- Per-step side-aware reversal lemma.  The `WalkStep.reverse`
-- swap-quotient identity on `.bidir` plus `Sym2.eq_swap` on the
-- writing-mirror L-disjunct of `.forwardE` / `.backwardE` makes
-- "head at the reversed step's TARGET" equivalent to
-- "head at the original step's SOURCE".  Mirror of
-- `WalkStep.isInto_reverse` (pre-refactor scaffold above) but reading
-- the side off the constructor tag rather than via node-equality.
lemma refactor_headAtTarget_reverse {G : CDMG Node} :
    ∀ {u v : Node} (s : WalkStep G u v),
      s.reverse.refactor_HeadAtTarget ↔ s.refactor_HeadAtSource
  | _, _, .forwardE _ => by
      change (s(_, _) : Sym2 Node) ∈ G.L ↔ s(_, _) ∈ G.L
      rw [show (s(_, _) : Sym2 Node) = s(_, _) from Sym2.eq_swap]
  | _, _, .backwardE _ => Iff.rfl
  | _, _, .bidir _ => Iff.rfl
end WalkStep
-- REFACTOR-BLOCK-REPLACEMENT-END: headAtTarget_reverse

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: headAtSource_reverse (was: refactor_headAtSource_reverse)
namespace WalkStep
-- Mirror of `refactor_headAtTarget_reverse`: head at the reversed
-- step's SOURCE iff head at the original step's TARGET.
lemma refactor_headAtSource_reverse {G : CDMG Node} :
    ∀ {u v : Node} (s : WalkStep G u v),
      s.reverse.refactor_HeadAtSource ↔ s.refactor_HeadAtTarget
  | _, _, .forwardE _ => Iff.rfl
  | _, _, .backwardE _ => by
      change (s(_, _) : Sym2 Node) ∈ G.L ↔ s(_, _) ∈ G.L
      rw [show (s(_, _) : Sym2 Node) = s(_, _) from Sym2.eq_swap]
  | _, _, .bidir _ => Iff.rfl
end WalkStep
-- REFACTOR-BLOCK-REPLACEMENT-END: headAtSource_reverse

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isCollider_nil_sa (was: refactor_isCollider_nil_sa)
namespace Walk
-- refactor_IsCollider on the trivial walk is False at every position.
lemma refactor_isCollider_nil_sa {G : CDMG Node} {v : Node}
    (hv : v ∈ G) (k : ℕ) :
    (Walk.nil v hv).refactor_IsCollider k = False := by
  cases k <;> rfl
end Walk
-- REFACTOR-BLOCK-REPLACEMENT-END: isCollider_nil_sa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isCollider_cons_nil_eq_sa (was: refactor_isCollider_cons_nil_eq_sa)
namespace Walk
-- refactor_IsCollider on a length-1 walk (cons-nil) is False at every
-- position (the position-1 case requires two walk-incident steps).
lemma refactor_isCollider_cons_nil_eq_sa {G : CDMG Node}
    {u : Node} (mid : Node) (s : WalkStep G u mid) (hw : mid ∈ G) (k : ℕ) :
    (Walk.cons mid s (Walk.nil mid hw)).refactor_IsCollider k = False := by
  cases k <;> rfl
end Walk
-- REFACTOR-BLOCK-REPLACEMENT-END: isCollider_cons_nil_eq_sa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isCollider_length_false_sa (was: refactor_isCollider_length_false_sa)
namespace Walk
-- The end-position `k = p.length` is never a collider; mirrors
-- pre-refactor `Walk.isCollider_length_false`.
lemma refactor_isCollider_length_false_sa {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v), p.refactor_IsCollider p.length = False
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ s (.nil _ hv) => by
      exact Walk.refactor_isCollider_cons_nil_eq_sa _ s hv _
  | _, _, .cons mid s (.cons mid₂ s' p') => by
      have h_len :
          (Walk.cons mid s (Walk.cons mid₂ s' p')).length = p'.length + 2 := by
        simp [Walk.length]
      rw [h_len]
      change (Walk.cons mid₂ s' p').refactor_IsCollider (p'.length + 1) = False
      have ih := Walk.refactor_isCollider_length_false_sa
        (Walk.cons mid₂ s' p')
      have h_tail_len :
          (Walk.cons mid₂ s' p').length = p'.length + 1 := by
        simp [Walk.length]
      rw [h_tail_len] at ih
      exact ih
end Walk
-- REFACTOR-BLOCK-REPLACEMENT-END: isCollider_length_false_sa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isCollider_comp_eq_of_lt_sa (was: refactor_isCollider_comp_eq_of_lt_sa)
namespace Walk
-- Comp invariance for refactor_IsCollider at strictly-interior-of-`q`
-- positions; mirrors pre-refactor `Walk.isCollider_comp_eq_of_lt`.
lemma refactor_isCollider_comp_eq_of_lt_sa {G : CDMG Node} :
    ∀ {u v w : Node} (q : Walk G u v) (r : Walk G v w) (k : ℕ),
      k < q.length →
      ((q.comp r).refactor_IsCollider k ↔ q.refactor_IsCollider k)
  | _, _, _, .nil _ _, _, _, h => by simp [Walk.length] at h
  | _, _, _, .cons mid s (.nil _ hv), r, k, h => by
      simp [Walk.length] at h
      subst h
      change (Walk.cons mid s r).refactor_IsCollider 0 ↔
             (Walk.cons mid s (Walk.nil _ hv)).refactor_IsCollider 0
      have h_rhs :
          (Walk.cons mid s (Walk.nil _ hv)).refactor_IsCollider 0 = False :=
        Walk.refactor_isCollider_cons_nil_eq_sa mid s hv 0
      rw [h_rhs]
      constructor
      · intro h_c
        cases r with
        | nil _ _ => exact h_c
        | cons _ _ _ => exact h_c
      · intro h_c
        exact h_c.elim
  | _, _, _, .cons mid s (.cons mid₂ s' p''), r, 0, _ => by
      change (Walk.cons mid s
              ((Walk.cons mid₂ s' p'').comp r)).refactor_IsCollider 0 ↔ _
      constructor <;> intro h <;> exact h.elim
  | _, _, _, .cons mid s (.cons mid₂ s' p''), r, 1, _ => by
      change (Walk.cons mid s
              ((Walk.cons mid₂ s' p'').comp r)).refactor_IsCollider 1 ↔
             (Walk.cons mid s
              (Walk.cons mid₂ s' p'')).refactor_IsCollider 1
      change ((Walk.cons mid s
              (Walk.cons mid₂ s' (p''.comp r))).refactor_IsCollider 1) ↔
             ((Walk.cons mid s
              (Walk.cons mid₂ s' p'')).refactor_IsCollider 1)
      rfl
  | _, _, _, .cons mid s (.cons mid₂ s' p''), r, k + 2, h => by
      have h' :
          k + 2 < (Walk.cons mid s (Walk.cons mid₂ s' p'')).length := h
      simp [Walk.length] at h'
      have ih := Walk.refactor_isCollider_comp_eq_of_lt_sa
        (Walk.cons mid₂ s' p'') r (k+1) (by simp [Walk.length]; omega)
      change (Walk.cons mid s
              ((Walk.cons mid₂ s' p'').comp r)).refactor_IsCollider (k+2) ↔
             (Walk.cons mid s
              (Walk.cons mid₂ s' p'')).refactor_IsCollider (k+2)
      change (Walk.cons mid s
              (Walk.cons mid₂ s' (p''.comp r))).refactor_IsCollider (k+2) ↔
             (Walk.cons mid s
              (Walk.cons mid₂ s' p'')).refactor_IsCollider (k+2)
      have eq1 : (Walk.cons mid s
                  (Walk.cons mid₂ s'
                  (p''.comp r))).refactor_IsCollider (k+2) =
                 (Walk.cons mid₂ s'
                  (p''.comp r)).refactor_IsCollider (k+1) := rfl
      have eq2 : (Walk.cons mid s
                  (Walk.cons mid₂ s' p'')).refactor_IsCollider (k+2) =
                 (Walk.cons mid₂ s'
                  p'').refactor_IsCollider (k+1) := rfl
      rw [eq1, eq2]
      change ((Walk.cons mid₂ s' p'').comp r).refactor_IsCollider (k+1) ↔
             (Walk.cons mid₂ s' p'').refactor_IsCollider (k+1)
      exact ih
end Walk
-- REFACTOR-BLOCK-REPLACEMENT-END: isCollider_comp_eq_of_lt_sa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isCollider_comp_succ_length_cons_cons_sa (was: refactor_isCollider_comp_succ_length_cons_cons_sa)
namespace Walk
-- Junction lemma: refactor_IsCollider of `q.comp Y` at `q.length + 1`
-- reads the first two steps of `Y`.  Mirrors pre-refactor
-- `Walk.isCollider_comp_succ_length_cons_cons`.
lemma refactor_isCollider_comp_succ_length_cons_cons_sa
    {G : CDMG Node} {b c mid mid₂ : Node} (s : WalkStep G b mid)
    (s' : WalkStep G mid mid₂) (r : Walk G mid₂ c) :
    ∀ {a : Node} (q : Walk G a b),
      (q.comp (Walk.cons mid s
        (Walk.cons mid₂ s' r))).refactor_IsCollider (q.length + 1) ↔
        s.refactor_HeadAtTarget ∧ s'.refactor_HeadAtSource
  | _, .nil _ _ => by
      change (Walk.cons mid s
        (Walk.cons mid₂ s' r)).refactor_IsCollider 1 ↔ _
      rfl
  | _, .cons _ _ (.nil _ _) => by
      rfl
  | _, .cons _ _ (.cons mid'' s'' q'') => by
      exact Walk.refactor_isCollider_comp_succ_length_cons_cons_sa s s' r
        (Walk.cons mid'' s'' q'')
end Walk
-- REFACTOR-BLOCK-REPLACEMENT-END: isCollider_comp_succ_length_cons_cons_sa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isCollider_reverse_sa (was: refactor_isCollider_reverse_sa)
namespace Walk
-- Main refactor_IsCollider invariance under walk reversal.  The
-- position correspondence is `k ↔ p.length - k`.  Mirrors pre-refactor
-- `Walk.isCollider_reverse` but uses the side-aware per-step
-- reversal lemmas `refactor_headAtTarget_reverse` /
-- `refactor_headAtSource_reverse` (constructor-tag-flip via
-- `WalkStep.reverse` + `Sym2.eq_swap`) instead of
-- `WalkStep.isInto_reverse`.  The constructor-tag-flip closes the
-- per-step equivalence without consulting the stored ordered pair, so
-- the writing-mirror artifact warned about in
-- `workspace_claim_3_22.md` is structurally precluded.
lemma refactor_isCollider_reverse_sa {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v) (k : ℕ),
      p.reverse.refactor_IsCollider (p.length - k) ↔ p.refactor_IsCollider k
  | _, _, .nil _ hv, k => by
      have h_rhs : (Walk.nil _ hv).refactor_IsCollider k = False :=
        Walk.refactor_isCollider_nil_sa hv k
      have h_lhs : (Walk.nil _ hv).reverse.refactor_IsCollider
            ((Walk.nil _ hv).length - k) = False := by
        change (Walk.nil _ hv).refactor_IsCollider _ = False
        exact Walk.refactor_isCollider_nil_sa hv _
      rw [h_lhs, h_rhs]
  | _, _, .cons _ s (.nil _ hv), k => by
      have h_rhs :
          (Walk.cons _ s (Walk.nil _ hv)).refactor_IsCollider k = False :=
        Walk.refactor_isCollider_cons_nil_eq_sa _ s hv k
      have h_lhs : (Walk.cons _ s (Walk.nil _ hv)).reverse.refactor_IsCollider
            ((Walk.cons _ s (Walk.nil _ hv)).length - k) = False := by
        change (Walk.cons _ s.reverse (Walk.nil _ _)).refactor_IsCollider _ =
          False
        exact Walk.refactor_isCollider_cons_nil_eq_sa _ s.reverse _ _
      rw [h_lhs, h_rhs]
  | _, _, .cons mid s (.cons mid₂ s' p''), k => by
      cases k with
      | zero =>
          have h_rhs :
              (Walk.cons mid s
                (Walk.cons mid₂ s' p'')).refactor_IsCollider 0 = False := rfl
          rw [h_rhs]
          have h_lhs :
              (Walk.cons mid s
                (Walk.cons mid₂ s' p'')).reverse.refactor_IsCollider
                ((Walk.cons mid s (Walk.cons mid₂ s' p'')).length - 0) =
                False := by
            rw [Nat.sub_zero,
                show (Walk.cons mid s (Walk.cons mid₂ s' p'')).length =
                  (Walk.cons mid s
                    (Walk.cons mid₂ s' p'')).reverse.length from
                  (Walk.length_reverse _).symm]
            exact Walk.refactor_isCollider_length_false_sa _
          rw [h_lhs]
      | succ k₀ =>
          cases k₀ with
          | zero =>
              have h_rhs_def :
                  (Walk.cons mid s
                    (Walk.cons mid₂ s' p'')).refactor_IsCollider 1 =
                  (s.refactor_HeadAtTarget ∧ s'.refactor_HeadAtSource) := rfl
              rw [h_rhs_def]
              have h_len_sub :
                  (Walk.cons mid s
                    (Walk.cons mid₂ s' p'')).length - 1 = p''.length + 1 := by
                simp [Walk.length]
              rw [h_len_sub]
              have h_rev_eq :
                  (Walk.cons mid s
                    (Walk.cons mid₂ s' p'')).reverse =
                  p''.reverse.comp
                    (Walk.cons mid s'.reverse
                      (Walk.cons _ s.reverse
                        (Walk.nil _ (WalkStep.source_mem s)))) := by
                change (p''.reverse.comp
                          (Walk.cons mid s'.reverse
                            (Walk.nil _
                              (WalkStep.source_mem s')))).comp _ = _
                rw [Walk.comp_assoc]
                rfl
              rw [h_rev_eq]
              rw [show p''.length + 1 = p''.reverse.length + 1 from by
                    rw [Walk.length_reverse]]
              rw [Walk.refactor_isCollider_comp_succ_length_cons_cons_sa]
              rw [WalkStep.refactor_headAtTarget_reverse,
                  WalkStep.refactor_headAtSource_reverse]
              tauto
          | succ k₁ =>
              have h_rhs_eq :
                  (Walk.cons mid s
                    (Walk.cons mid₂ s' p'')).refactor_IsCollider (k₁ + 2) =
                  (Walk.cons mid₂ s' p'').refactor_IsCollider (k₁ + 1) := rfl
              rw [h_rhs_eq]
              have h_lhs_pos :
                  (Walk.cons mid s
                    (Walk.cons mid₂ s' p'')).length - (k₁ + 2) =
                  (Walk.cons mid₂ s' p'').length - (k₁ + 1) := by
                simp [Walk.length]
              rw [h_lhs_pos]
              have h_rev :
                  (Walk.cons mid s
                    (Walk.cons mid₂ s' p'')).reverse =
                  (Walk.cons mid₂ s' p'').reverse.comp
                    (Walk.cons _ s.reverse
                      (Walk.nil _ (WalkStep.source_mem s))) := rfl
              rw [h_rev]
              have h_lt :
                  (Walk.cons mid₂ s' p'').length - (k₁ + 1) <
                  (Walk.cons mid₂ s' p'').reverse.length := by
                rw [Walk.length_reverse]
                have h_inner_len :
                    (Walk.cons mid₂ s' p'').length = p''.length + 1 := by
                  simp [Walk.length]
                rw [h_inner_len]
                omega
              rw [Walk.refactor_isCollider_comp_eq_of_lt_sa _ _ _ h_lt]
              exact Walk.refactor_isCollider_reverse_sa
                (Walk.cons mid₂ s' p'') (k₁ + 1)
end Walk
-- REFACTOR-BLOCK-REPLACEMENT-END: isCollider_reverse_sa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isNonCollider_reverse_sa (was: refactor_isNonCollider_reverse_sa)
namespace Walk
-- refactor_IsNonCollider invariance under walk reversal.  Mirror of
-- pre-refactor `Walk.isNonCollider_reverse`.
lemma refactor_isNonCollider_reverse_sa {G : CDMG Node}
    {u v : Node} (p : Walk G u v) (k : ℕ) (hk : k ≤ p.length) :
    p.reverse.refactor_IsNonCollider (p.length - k) ↔
      p.refactor_IsNonCollider k := by
  unfold Walk.refactor_IsNonCollider
  rw [Walk.length_reverse]
  constructor
  · rintro ⟨_h_le, h_not_coll⟩
    refine ⟨hk, ?_⟩
    intro h_coll
    exact h_not_coll
      ((Walk.refactor_isCollider_reverse_sa p k).mpr h_coll)
  · rintro ⟨_h_le, h_not_coll⟩
    refine ⟨by omega, ?_⟩
    intro h_coll
    exact h_not_coll
      ((Walk.refactor_isCollider_reverse_sa p k).mp h_coll)
end Walk
-- REFACTOR-BLOCK-REPLACEMENT-END: isNonCollider_reverse_sa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isBlockableNonCollider_reverse_sa (was: refactor_isBlockableNonCollider_reverse_sa)
namespace Walk
-- refactor_IsBlockableNonCollider invariance under walk reversal.
-- Reuses the unchanged `HasBlockingLeftSlot` / `HasBlockingRightSlot`
-- reversal-invariance lemmas defined above (those helpers are net-
-- zero under the side-aware refactor).  Mirror of pre-refactor
-- `Walk.isBlockableNonCollider_reverse`.
lemma refactor_isBlockableNonCollider_reverse_sa {G : CDMG Node}
    {u v : Node} (p : Walk G u v) (k : ℕ) (hk : k ≤ p.length) :
    p.reverse.refactor_IsBlockableNonCollider (p.length - k) ↔
      p.refactor_IsBlockableNonCollider k := by
  unfold Walk.refactor_IsBlockableNonCollider
  rw [Walk.refactor_isNonCollider_reverse_sa p k hk, Walk.length_reverse]
  rw [Walk.hasBlockingRightSlot_reverse_eq_hasBlockingLeftSlot p k hk,
      Walk.hasBlockingLeftSlot_reverse_eq_hasBlockingRightSlot p k hk]
  constructor
  · rintro ⟨h_nc, h_disj⟩
    refine ⟨h_nc, ?_⟩
    rcases h_disj with h_eq | h_eq | h_left | h_right
    · have : k = p.length := by omega
      exact Or.inr (Or.inl this)
    · have : k = 0 := by omega
      exact Or.inl this
    · exact Or.inr (Or.inr (Or.inr h_left))
    · exact Or.inr (Or.inr (Or.inl h_right))
  · rintro ⟨h_nc, h_disj⟩
    refine ⟨h_nc, ?_⟩
    rcases h_disj with h_eq | h_eq | h_left | h_right
    · have : p.length - k = p.length := by omega
      exact Or.inr (Or.inl this)
    · have : p.length - k = 0 := by omega
      exact Or.inl this
    · exact Or.inr (Or.inr (Or.inr h_left))
    · exact Or.inr (Or.inr (Or.inl h_right))
end Walk
-- REFACTOR-BLOCK-REPLACEMENT-END: isBlockableNonCollider_reverse_sa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isSigmaBlockedGiven_reverse_forward_sa (was: refactor_isSigmaBlockedGiven_reverse_forward_sa)
namespace Walk
-- Forward direction of the σ-blocked reversal-invariance.  Mirror of
-- pre-refactor `Walk.isSigmaBlockedGiven_reverse_forward`; references
-- `refactor_IsCollider` / `refactor_IsBlockableNonCollider` through
-- `refactor_IsSigmaBlockedGiven`.
lemma refactor_isSigmaBlockedGiven_reverse_forward_sa
    {G : CDMG Node} :
    ∀ {u v : Node} (q : Walk G u v) (C : Set Node) (hC : C ⊆ ↑G.J ∪ ↑G.V),
      q.refactor_IsSigmaBlockedGiven C hC →
        q.reverse.refactor_IsSigmaBlockedGiven C hC := by
  intro u v q C hC h
  unfold Walk.refactor_IsSigmaBlockedGiven at h ⊢
  rcases h with ⟨k, vk, h_get, h_coll, h_anc⟩ | ⟨k, vk, h_get, h_blk, h_inC⟩
  · have h_k_le : k ≤ q.length := by
      rw [List.getElem?_eq_some_iff] at h_get
      obtain ⟨h_lt, _⟩ := h_get
      rw [Walk.vertices_length] at h_lt
      omega
    refine Or.inl ⟨q.length - k, vk, ?_, ?_, h_anc⟩
    · exact Walk.vertices_reverse_getElem? q k vk h_get
    · exact (Walk.refactor_isCollider_reverse_sa q k).mpr h_coll
  · have h_k_le : k ≤ q.length := by
      rw [List.getElem?_eq_some_iff] at h_get
      obtain ⟨h_lt, _⟩ := h_get
      rw [Walk.vertices_length] at h_lt
      omega
    refine Or.inr ⟨q.length - k, vk, ?_, ?_, h_inC⟩
    · exact Walk.vertices_reverse_getElem? q k vk h_get
    · exact (Walk.refactor_isBlockableNonCollider_reverse_sa q k
        h_k_le).mpr h_blk
end Walk
-- REFACTOR-BLOCK-REPLACEMENT-END: isSigmaBlockedGiven_reverse_forward_sa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isSigmaBlockedGiven_reverse_sa (was: refactor_isSigmaBlockedGiven_reverse_sa)
namespace Walk
-- Biconditional σ-blocked reversal-invariance.  Mirror of pre-
-- refactor `Walk.isSigmaBlockedGiven_reverse`.
lemma refactor_isSigmaBlockedGiven_reverse_sa {G : CDMG Node}
    {u v : Node} (p : Walk G u v) (C : Set Node) (hC : C ⊆ ↑G.J ∪ ↑G.V) :
    p.refactor_IsSigmaBlockedGiven C hC ↔
      p.reverse.refactor_IsSigmaBlockedGiven C hC := by
  constructor
  · exact Walk.refactor_isSigmaBlockedGiven_reverse_forward_sa p C hC
  · intro h_rev
    have h_p : p.reverse.reverse.refactor_IsSigmaBlockedGiven C hC :=
      Walk.refactor_isSigmaBlockedGiven_reverse_forward_sa
        p.reverse C hC h_rev
    rw [Walk.reverse_involution] at h_p
    exact h_p
end Walk
-- REFACTOR-BLOCK-REPLACEMENT-END: isSigmaBlockedGiven_reverse_sa

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: sigma_separation_symmetric (was: refactor_sigma_separation_symmetric)
--
-- σ-separation is symmetric in its first two arguments — side-aware
-- refactor port (`collider_side_aware`).  Same LN claim and same
-- biconditional shape as the ORIGINAL block above; the only delta is
-- a single mechanical upstream retarget
-- `IsSigmaSeparated → refactor_IsSigmaSeparated`.
--
-- ## Design choice — refactor_sigma_separation_symmetric
--
-- *DEPENDENT row, not a root.*  The side-aware reading is implemented
--   upstream at `def_3_15`'s helpers `refactor_HeadAtSource` /
--   `refactor_HeadAtTarget` (`CollidersAndNon.lean`); this row
--   inherits it transparently via the predicate chain
--   `refactor_IsCollider` → `refactor_IsBlockableNonCollider` →
--   `refactor_IsSigmaBlockedGiven` → `refactor_IsISigmaSeparated` →
--   `refactor_IsSigmaSeparated`.  The symmetry statement itself does
--   NOT commit to any per-step arrowhead-contribution reading — it is
--   a pure surface assertion on the σ-separation predicate.  The
--   refactor only touches the *referenced predicate*, not the shape
--   of the symmetry assertion.
--
-- *Mechanical port; same signature shape as ORIGINAL.*  The single
--   delta versus the ORIGINAL `sigma_separation_symmetric` is
--   `IsSigmaSeparated` → `refactor_IsSigmaSeparated` on both sides of
--   the biconditional.  Every other binder (`G hJ A B C hA hB hC`),
--   every other shape choice — `Set Node` not `Finset`; subset
--   hypotheses `⊆ ↑G.J ∪ ↑G.V`; biconditional `↔`; RHS argument
--   transposition `(B, A, C, hB, hA, hC)` — carries through from the
--   ORIGINAL byte-for-byte.  The OLD design-choice rationale in the
--   ORIGINAL block above applies verbatim to every binder and shape
--   choice that did not change; the points worth re-emphasising under
--   the refactor are collected in this block.  After Phase 7 cleanup
--   the whole-word rename `refactor_sigma_separation_symmetric →
--   sigma_separation_symmetric` and
--   `refactor_IsSigmaSeparated → IsSigmaSeparated` restores the
--   surface form to its pre-refactor reading, now resolving against
--   the unique (post-rename) side-aware defs.
--
-- *Wording-check subtleties carried through from ORIGINAL — explicit.*
--   The three working-phase LN-critic findings flagged for this row
--   resolve as follows under the refactor port:
--   - `undefined_J_in_symmetry_justification`: the LN's "$J = \emptyset$"
--     clause references the ambient CDMG's input-node set `G.J`, which
--     this REPLACEMENT signature surfaces explicitly as
--     `hJ : G.J = ∅` (binder lifted verbatim from ORIGINAL).  The
--     rewritten canonical tex statement makes `J = ∅` the standing
--     premise, so the dangling-`J` ambiguity in the LN prose is
--     resolved at the statement level and does not propagate into
--     the proof obligation.
--   - `claim_unrestricted_but_proof_only_covers_J_empty`: resolved as
--     case (b) -- `\sPerp_G` is, per `def_3_18` item 4, *defined* only
--     under `J = ∅`, so the rewritten statement is fully general
--     relative to the σ-notation's scope.  Resolution analysis lives
--     in the ORIGINAL block above (around the "Explicit `hJ` as a
--     propositional premise" bullet); the REPLACEMENT inherits the
--     same signature shape and therefore the same resolution
--     byte-for-byte.
--   - `walks_same_regardless_of_direction_ambiguous`: walks are
--     *ordered* sequences (per `def_3_4` item i), so the LN prose's
--     "the set of walks between $A$ and $B$ is the same regardless
--     of direction" is loose -- strictly, walk reversal induces an
--     *involution* `Walk G u v ↔ Walk G v u` (`Walk.reverse_involution`
--     in this file), and the proof goes through bijection-by-
--     reversal plus per-step blocking-invariance, not literal
--     set-equality.  Under the side-aware refactor, the per-step
--     invariance becomes a *structural* consequence of the
--     constructor-tag flip plus `Sym2.eq_swap` -- see the bullets
--     on `Sym2.eq_swap`, operator-hint strategies, and the
--     manager-accepted self-loop deviation below.
--
-- *Why the retarget to `refactor_IsSigmaSeparated` is required during
--   the refactor window.*  Both `CDMG.IsSigmaSeparated` (ORIGINAL
--   block in `ISigmaSeparation.lean`) and
--   `CDMG.refactor_IsSigmaSeparated` (REPLACEMENT block in the same
--   file) coexist in scope while the refactor is in flight.  An
--   unqualified `G.IsSigmaSeparated` in this REPLACEMENT theorem's
--   body would resolve via literal-name match to the ORIGINAL non-
--   side-aware def, pairing the symmetry theorem with the wrong
--   upstream predicate.  In `claim_3_22`'s specific case this
--   mismatch would re-introduce the spurious-collider-at-self-loop
--   divergence the side-aware refactor is designed to eliminate —
--   exactly the scenario the operator hint in
--   `workspace_claim_3_22.md` warned about (the previous attempt's
--   "writing-mirror artifact" at a `(u, v) ∈ G.L` + `(v, u) ∈ G.E`
--   coincidence).  The REPLACEMENT theorem's body explicitly
--   references `G.refactor_IsSigmaSeparated`, so the symmetry
--   statement composes with the side-aware predicate throughout the
--   refactor window.  After Phase 7's whole-word rename
--   `refactor_IsSigmaSeparated → IsSigmaSeparated` (with the ORIGINAL
--   `IsSigmaSeparated` block deleted by the same cleanup pass), the
--   body's surface form `G.IsSigmaSeparated` resolves to the unique
--   (post-rename) side-aware def — the pre-refactor surface form is
--   restored with the side-aware semantics throughout.
--
-- *Why the proof closes under the refactor: structural reversal-
--   invariance.*  Under the side-aware encoding, `refactor_HeadAtSource`
--   and `refactor_HeadAtTarget` read arrowhead-presence off the
--   `WalkStep`'s *constructor tag* alone, plus an explicit
--   `s(u, v) ∈ G.L` disjunct on the opposite-channel branch (the
--   writing-mirror re-firing required by clause~(c) of the
--   `collider_side_aware` addition tag).  The constructor tag flips
--   cleanly under `WalkStep.reverse` (`.forwardE ↔ .backwardE`,
--   `.bidir ↔ .bidir`); the `Sym2`-typed L-disjunct is invariant
--   under `Sym2`-swap.  Hence the per-step equivalences
--   `s.reverse.refactor_HeadAtTarget ↔ s.refactor_HeadAtSource` and
--   `s.reverse.refactor_HeadAtSource ↔ s.refactor_HeadAtTarget` are
--   *structural* consequences of the helper defs (no edge-set
--   inference, no `IsInto`-style node-equality test), and the
--   position-1 collider definition's asymmetric
--   `s₀.refactor_HeadAtTarget ∧ s₁.refactor_HeadAtSource` shape
--   composes cleanly through walk reversal via `And.comm`.  The
--   symmetry proof's heavy lifting was always the reversal-invariance
--   of `IsCollider` / `IsBlockableNonCollider` /
--   `IsSigmaBlockedGiven`; under the refactor these lemmas re-prove
--   cleanly using the constructor-tag swap, *eliminating* the
--   "writing-mirror artifact" issue the previous (pre-refactor)
--   attempt hit when the `IsInto`-based reading inferred the
--   channel from the stored ordered pair (see `workspace_claim_3_22.md`
--   for the operator hint detailing that failure mode).  The refactor
--   makes the proof closure cleaner, not harder.
--
-- *`Sym2.eq_swap` is the load-bearing mathlib lemma for the
--   L-disjunct's reversal-invariance.*  The `s(u, v) ∈ G.L` disjunct
--   appearing in `refactor_HeadAtSource`'s `.forwardE` branch and in
--   `refactor_HeadAtTarget`'s `.backwardE` branch is typed
--   `Sym2 Node`, the swap-quotient of `Node × Node`.  After
--   `WalkStep.reverse` (this file's `def WalkStep.reverse`) swaps
--   the type indices `(u, v) → (v, u)`, the L-disjunct's `Sym2`
--   term `s(u, v)` is re-elaborated as `s(v, u)`, and
--   `Sym2.eq_swap : s(u, v) = s(v, u)` is the propositional
--   equality that identifies the two as the same element of
--   `Sym2 Node`.  Concretely, `WalkStep.reverse`'s `.bidir` branch
--   *already* invokes `Sym2.eq_swap ▸ h` to retype the swap-quotient
--   membership witness, and the same rewrite is what makes the
--   `.forwardE` ↔ `.backwardE` reversal preserve the L-disjunct's
--   evaluation pointwise.  An equivalent encoding using
--   `Node × Node` (ordered pairs) plus an explicit `Or` over both
--   orientations would force the proof to carry a four-case
--   (forward/backward × original/reversed) disjunction-elimination
--   at every walk-step; the `Sym2`-quotient collapses those four
--   cases to one.  This is the architectural payoff of `def_3_1`'s
--   choice to type `L` against `Set (Sym2 Node)` rather than
--   `Set (Node × Node)` -- the symmetry proof's per-step reversal
--   lemma reduces to a one-line constructor case-split with
--   `Sym2.eq_swap` as the only rewrite, no explicit
--   orientation-disjunction needed.
--
-- *Connection to the carried-over operator hint's two suggested
--   strategies.*  `workspace_claim_3_22.md` records the previous
--   solve attempt's failure mode (a "writing-mirror artifact"
--   triggered by the `IsInto`-based reading inferring channel from
--   the stored ordered pair, then misclassifying the swapped pair
--   at writing-mirror coincidences `(u, v) ∈ G.L` ∧ `(v, u) ∈ G.E`)
--   and suggests two local strategies for the proof: (i) a *tagged*
--   reversed-walk type that carries explicit channel tags through
--   reversal, and (ii) a per-position case-analysis that proves the
--   `IsBlockableNonCollider`-equivalence directly without
--   constructing the full reversed `Walk` object.  The side-aware
--   refactor subsumes (i) at the type-theoretic level: `WalkStep`'s
--   three constructors `.forwardE` / `.backwardE` / `.bidir` *are*
--   the channel tags strategy (i) proposed, carried natively by the
--   existing typed-walk-step API rather than bolted on by a
--   parallel data type.  And the refactor's per-step structural
--   lemmas `s.reverse.refactor_HeadAtTarget ↔
--   s.refactor_HeadAtSource` (and its mirror) realise strategy (ii)
--   directly: each is a constructor case-split that discharges by
--   `Sym2.eq_swap` plus reflexivity on the constant-`True`
--   branches, with no walk-level construction at all.  Net effect:
--   the heavy-infrastructure failure mode the operator hint warned
--   about (>500 lines of generic walk-reversal plumbing crashing
--   on the writing-mirror artifact) is *structurally precluded* by
--   the refactor -- the side-aware predicates do not consult the
--   stored ordered pair to infer the channel, so there is no
--   pair-swap-induced misclassification to work around in the
--   proof.
--
-- *Manager-accepted deviation `collider_side_aware_at_self_loops`
--   is the enabler of the clean reversal-invariance argument.*
--   The deviation (recorded in `leanification/deviations.json`)
--   commits the side-aware encoding to placing the arrowhead at a
--   directed self-loop `(v, v) ∈ G.E` on the walk-traversal
--   *target* side only -- the side identified by the `.forwardE` /
--   `.backwardE` constructor tag -- rather than at both sides as
--   the literal-LN "edge into $v_k$" test admits.  This is what
--   makes per-step reversal-invariance a structural consequence of
--   the constructor-tag flip alone: at a self-loop step encoded as
--   `.forwardE _ : WalkStep G v v`, the source-side
--   `refactor_HeadAtSource` reduces to `s(v, v) ∈ G.L`, vacuously
--   `False` by `def_3_1`'s `hL_irrefl` (no diagonal pair in
--   `G.L`); after reversal, the same self-loop step is
--   `.backwardE _ : WalkStep G v v`, with source-side `True` and
--   target-side `s(v, v) ∈ G.L = False`.  Source and target swap
--   correctly under reversal at self-loops, with no special-casing
--   in the reversal-invariance lemma.  Under the pre-refactor
--   `IsInto` reading a self-loop's source and target indices were
--   the same node, so the node-equality test fired `True` on both
--   sides and a walk `a → b → b` was spuriously classified as
--   colliding at `b` -- the reversal-invariance argument then had
--   to absorb that artifact, which is precisely the failure mode
--   the previous proof attempt hit.  The deviation eliminates the
--   artifact at its source.  Note that the deviation is a STRICT
--   refinement of the literal-LN reading: on walks that traverse
--   no directed self-loop step the side-aware predicates classify
--   every position the same as the literal stored-pair test (per
--   `def_3_15`'s "intended deviation at directed self-loops;
--   agreement elsewhere" bullet in `CollidersAndNon.lean`), so the
--   symmetry claim's σ-blocking semantics agree with the LN on
--   every non-self-loop walk while remaining well-defined and
--   reversal-invariant on self-loop walks.
--
-- *Statement-level `:= by sorry` is intentional.*  This file is the
--   Manager A statement step for the REPLACEMENT theorem; the proof
--   obligation will be discharged by the `prove_claim_in_lean`
--   worker (Manager B) after `write_tex_proof` / `verify_tex_proof`
--   have produced and verified the mathematical proof (with the tex
--   proof written to the *twin* file
--   `tex/refactor_claim_3_22_proof_SigmaSeparationSymmetric.tex`,
--   not the un-prefixed original, per the refactor row briefing).
--   Filling the proof body here is explicitly NOT this worker's
--   scope — only the statement port is.
-- claim_3_22 -- start statement
theorem refactor_sigma_separation_symmetric
    (G : CDMG Node) (hJ : G.J = ∅) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V)
    (hC : C ⊆ ↑G.J ∪ ↑G.V) :
    G.refactor_IsSigmaSeparated hJ A B C hA hB hC ↔
      G.refactor_IsSigmaSeparated hJ B A C hB hA hC
-- claim_3_22 -- end statement
:= by
  -- (I) Unfold refactor_IsSigmaSeparated = refactor_IsISigmaSeparated.
  unfold CDMG.refactor_IsSigmaSeparated CDMG.refactor_IsISigmaSeparated
  -- Under hJ : G.J = ∅, (G.J : Set Node) ∪ X = X for any set X.
  have h_J_empty : (↑G.J : Set Node) = ∅ := by
    rw [hJ]; simp
  -- One-direction lemma: covers either implication by symmetry in X, Y.
  -- (II) + (III) folded into the per-side application: for each walk
  -- with the swapped endpoints, reverse it and invoke the hypothesis
  -- on the reversed walk; then transport σ-blocking back via
  -- `refactor_isSigmaBlockedGiven_reverse_sa`.
  have one_direction :
      ∀ {X Y : Set Node} {hX : X ⊆ ↑G.J ∪ ↑G.V} {hY : Y ⊆ ↑G.J ∪ ↑G.V},
        (∀ {u v : Node} (π : Walk G u v), u ∈ X →
            v ∈ (↑G.J : Set Node) ∪ Y →
            π.refactor_IsSigmaBlockedGiven C hC) →
        ∀ {u v : Node} (π : Walk G u v), u ∈ Y →
            v ∈ (↑G.J : Set Node) ∪ X →
            π.refactor_IsSigmaBlockedGiven C hC := by
    intro X Y _ _ h u v π h_start h_end
    have h_end' : v ∈ X := by
      rw [h_J_empty, Set.empty_union] at h_end
      exact h_end
    have h_start' : u ∈ (↑G.J : Set Node) ∪ Y := by
      rw [h_J_empty, Set.empty_union]
      exact h_start
    have h_rev_blocked : π.reverse.refactor_IsSigmaBlockedGiven C hC :=
      h π.reverse h_end' h_start'
    exact (Walk.refactor_isSigmaBlockedGiven_reverse_sa π C hC).mpr
      h_rev_blocked
  constructor
  · exact fun h => one_direction (X := A) (Y := B) (hX := hA) (hY := hB) h
  · exact fun h => one_direction (X := B) (Y := A) (hX := hB) (hY := hA) h
-- REFACTOR-BLOCK-REPLACEMENT-END: sigma_separation_symmetric

end CDMG

end Causality
