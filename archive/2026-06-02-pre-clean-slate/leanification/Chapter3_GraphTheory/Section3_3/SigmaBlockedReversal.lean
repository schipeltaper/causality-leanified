import Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks

/-!
# Walk-reversal-invariance of σ-blocking (claim_3_22 infrastructure)

This file introduces the position-level walk-reversal-invariance
lemmas needed to prove claim_3_22 (`SigmaSeparationSymmetric`).
The lemmas live in the `Causality.Walk` / `Causality.WalkStep`
namespaces and decompose the "$\sigma$-blocking is invariant
under walk reversal" sub-lemma of the TeX proof
`claim_3_22_proof_SigmaSeparationSymmetric.tex` into the three
position-level invariances enumerated in Step 3 of that proof:

* `Walk.isColliderAt_reverse_iff` — the collider predicate
  transports under the involution `k ↔ π.length - k`.
* `Walk.isUnblockableNonColliderAt_reverse_iff` — the
  unblockable-non-collider predicate transports under the same
  involution (with the SCC outgoing-arrow condition staying
  intrinsic to the edges).
* `Walk.isBlockableNonColliderAt_reverse_iff` — corollary of the
  above two via the `IsBlockableNonColliderAt := IsNonColliderAt ∧
  ¬ IsUnblockableNonColliderAt` definition.

These combine to:

* `Walk.isSigmaBlocked_reverse_iff` — `π.IsSigmaBlocked C ↔
  π.reverse.IsSigmaBlocked C`. The set $\Anc^G(C)$ is intrinsic
  to `G` and `C`, so the two existential clauses of
  `IsSigmaBlocked` are transported point-wise via the involution.

The file also adds foundational walk helpers (`nodeAt_append_*`,
`nodeAt_reverse`, `append_assoc`, `isColliderAt_append_lt_length`,
etc.) needed by the position-level proofs. Per-step reversal lemmas
in `WalkStep` (e.g. `reverse_hasArrowheadAtTarget`) handle the
"arrowhead status of each edge endpoint is independent of the
walk's direction of traversal" observation in the TeX proof.

The infrastructure lives in `Section3_3` (not `Section3_1`) because
it is introduced specifically for the σ-blocking-reversal pivot
in claim_3_22; the walk-data-level reversal primitives
(`Walk.reverse`, `WalkStep.reverse`, `length_reverse`, the three
`reverse_forward` / `reverse_backward` / `reverse_bidir` `@[simp]`
lemmas) already exist in `Section3_1/Walks.lean` and are
re-used here.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace WalkStep

variable {G : CDMG α}

/-! ### Per-step reversal-invariance of arrowhead / direction predicates -/

/-- Reversing a step swaps `HasArrowheadAtTarget` and
`HasArrowheadAtSource` (in both forward/backward cases the arrowhead
literally moves sides; in the bidir case both stay True). -/
@[simp] theorem reverse_hasArrowheadAtTarget {v w : α} (s : WalkStep G v w) :
    s.reverse.HasArrowheadAtTarget ↔ s.HasArrowheadAtSource := by
  cases s <;> simp

/-- Reversing a step swaps `HasArrowheadAtSource` and
`HasArrowheadAtTarget`. -/
@[simp] theorem reverse_hasArrowheadAtSource {v w : α} (s : WalkStep G v w) :
    s.reverse.HasArrowheadAtSource ↔ s.HasArrowheadAtTarget := by
  cases s <;> simp

/-- Reversing a step swaps `IsForward` and `IsBackward`: `forward`
becomes `backward` and vice versa; `bidir` stays non-forward and
non-backward on both sides. -/
@[simp] theorem reverse_isForward {v w : α} (s : WalkStep G v w) :
    s.reverse.IsForward ↔ s.IsBackward := by
  cases s <;> simp

/-- Reversing a step swaps `IsBackward` and `IsForward`. -/
@[simp] theorem reverse_isBackward {v w : α} (s : WalkStep G v w) :
    s.reverse.IsBackward ↔ s.IsForward := by
  cases s <;> simp

/-- Reversing a step preserves `IsBidir`. -/
@[simp] theorem reverse_isBidir {v w : α} (s : WalkStep G v w) :
    s.reverse.IsBidir ↔ s.IsBidir := by
  cases s <;> simp

/-- Reversing both steps of a joint and swapping their order preserves
the unblockable-joint predicate: this is the TeX proof's "the local
triple $(v_{k-1}, v_k, v_{k+1})$ on $\pi$ becomes
$(v_{k+1}, v_k, v_{k-1})$ at position $n-k$ on $\pi^{-1}$" observation
combined with the arrowhead-status invariance above. The forward /
backward outgoing arrows from the joint swap roles (since reversing a
step swaps `IsForward` and `IsBackward`); the SCC condition
`a ∈ G.Sc b` only mentions the joint vertex `b` and the neighbour
vertex, both of which are unchanged. -/
theorem reverse_isUnblockableJoint {a b c : α}
    (s : WalkStep G a b) (s' : WalkStep G b c) :
    s'.reverse.IsUnblockableJoint s.reverse ↔ s.IsUnblockableJoint s' := by
  unfold IsUnblockableJoint
  simp only [reverse_hasArrowheadAtTarget, reverse_hasArrowheadAtSource,
    reverse_isForward, reverse_isBackward]
  constructor
  · rintro ⟨hCol, hBack, hFwd⟩
    exact ⟨fun ⟨h1, h2⟩ => hCol ⟨h2, h1⟩, hFwd, hBack⟩
  · rintro ⟨hCol, hBack, hFwd⟩
    exact ⟨fun ⟨h1, h2⟩ => hCol ⟨h2, h1⟩, hFwd, hBack⟩

end WalkStep

namespace Walk

variable {G : CDMG α}

/-! ### Walk-level `append` associativity -/

/-- Walk `append` is associative. Used in the joint-position case of
the walk-reversal-invariance proofs below. -/
theorem append_assoc : ∀ {u v w x : α} (p₁ : Walk G u v) (p₂ : Walk G v w)
    (p₃ : Walk G w x), (p₁.append p₂).append p₃ = p₁.append (p₂.append p₃)
  | _, _, _, _, .nil _, _, _ => by rw [Walk.nil_append, Walk.nil_append]
  | _, _, _, _, .cons _ p₁', p₂, p₃ => by
      rw [Walk.cons_append, Walk.cons_append, Walk.cons_append]
      congr 1
      exact append_assoc p₁' p₂ p₃

/-! ### Foundational `append` / `reverse` helpers for `nodeAt` -/

/-- `nodeAt` of an appended walk agrees with `nodeAt` of the left
walk on positions in the left walk's range. -/
theorem nodeAt_append_le : ∀ {u v w : α} (p₁ : Walk G u v) (p₂ : Walk G v w)
    {k : ℕ}, k ≤ p₁.length → (p₁.append p₂).nodeAt k = p₁.nodeAt k
  | _, _, _, .nil _, _, 0, _ => by
      rw [Walk.nil_append, Walk.nodeAt_nil, Walk.nodeAt_zero]
  | _, _, _, .nil _, _, _+1, hk => by simp at hk
  | _, _, _, .cons _ _, _, 0, _ => rfl
  | _, _, _, .cons _ p₁', p₂, k+1, hk => by
      have hk' : k ≤ p₁'.length := by
        simp [Walk.length_cons] at hk; omega
      rw [Walk.cons_append, Walk.nodeAt_cons_succ, Walk.nodeAt_cons_succ]
      exact nodeAt_append_le p₁' p₂ hk'

/-- `nodeAt` of an appended walk at a position past the left walk
reduces to `nodeAt` of the right walk at the shifted position. -/
theorem nodeAt_append_add_left : ∀ {u v w : α} (p₁ : Walk G u v) (p₂ : Walk G v w)
    (k : ℕ), (p₁.append p₂).nodeAt (p₁.length + k) = p₂.nodeAt k
  | _, _, _, .nil _, p₂, k => by
      rw [Walk.nil_append, Walk.length_nil, Nat.zero_add]
  | _, _, _, .cons _ p₁', p₂, k => by
      rw [Walk.cons_append, Walk.length_cons]
      have hRw : p₁'.length + 1 + k = (p₁'.length + k) + 1 := by omega
      rw [hRw, Walk.nodeAt_cons_succ]
      exact nodeAt_append_add_left p₁' p₂ k

/-- `nodeAt` of a reversed walk at position `k ≤ π.length` equals
`nodeAt` of the original walk at the swapped position `π.length - k`. -/
theorem nodeAt_reverse : ∀ {v w : α} (π : Walk G v w) {k : ℕ},
    k ≤ π.length → π.reverse.nodeAt k = π.nodeAt (π.length - k)
  | _, _, .nil _, k, hk => by
      simp only [Walk.length_nil, Nat.le_zero] at hk
      subst hk
      rfl
  | v, _, .cons s p, k, hk => by
      simp only [Walk.length_cons] at hk
      rw [Walk.reverse_cons]
      rcases Nat.lt_or_ge k (p.length + 1) with hkb | hkb
      · have hkp : k ≤ p.reverse.length := by
          rw [Walk.length_reverse]; omega
        rw [nodeAt_append_le _ _ hkp]
        rw [Walk.length_reverse] at hkp
        rw [nodeAt_reverse p hkp]
        have step : (Walk.cons s p).length - k = (p.length - k) + 1 := by
          rw [Walk.length_cons]; omega
        rw [step, Walk.nodeAt_cons_succ]
      · have hk_eq : k = p.length + 1 := by omega
        subst hk_eq
        have hRHS : (Walk.cons s p).nodeAt
            ((Walk.cons s p).length - (p.length + 1)) = v := by
          rw [Walk.length_cons, Nat.sub_self, Walk.nodeAt_cons_zero]
        rw [hRHS]
        have hRw : (p.length + 1 : ℕ) = p.reverse.length + 1 := by
          rw [Walk.length_reverse]
        rw [hRw, nodeAt_append_add_left p.reverse (Walk.cons s.reverse (Walk.nil v)) 1]
        rw [Walk.nodeAt_cons_succ, Walk.nodeAt_nil]

/-! ### `IsColliderAt` position bounds -/

/-- A collider position lies strictly inside the walk: an
`IsColliderAt k` witness forces `k < π.length`. Used to justify
`π.length - k` reindexing in the reversal proofs (so that the
involution `k ↔ π.length - k` makes sense on collider witnesses). -/
theorem isColliderAt_lt_length : ∀ {v w : α} (π : Walk G v w) {k : ℕ},
    π.IsColliderAt k → k < π.length
  | _, _, .nil _, _, h => h.elim
  | _, _, .cons _ (.nil _), _, h => h.elim
  | _, _, .cons _ (.cons _ _), 0, h => h.elim
  | _, _, .cons _ (.cons _ _), 1, _ => by
      simp [Walk.length_cons]
  | _, _, .cons _ (.cons s' p), k+2, h => by
      have h' : (Walk.cons s' p).IsColliderAt (k + 1) := by
        rw [Walk.isColliderAt_cons_cons_succ_succ] at h
        exact h
      have ih := isColliderAt_lt_length (Walk.cons s' p) h'
      simp [Walk.length_cons] at ih ⊢
      omega

/-- A position at or past the walk's length is not a collider. -/
theorem not_isColliderAt_of_length_le {v w : α} (π : Walk G v w) {k : ℕ}
    (hk : π.length ≤ k) : ¬ π.IsColliderAt k := fun h =>
  absurd (isColliderAt_lt_length π h) (Nat.not_lt.mpr hk)

/-! ### Append-locality of `IsColliderAt` (interior of left walk) -/

/-- On an appended walk `p₁.append p₂`, the `IsColliderAt`
predicate at any position strictly inside the left walk agrees with
`IsColliderAt` of the left walk alone. -/
theorem isColliderAt_append_lt_length : ∀ {u v w : α} (p₁ : Walk G u v)
    (p₂ : Walk G v w) {k : ℕ}, k < p₁.length →
    ((p₁.append p₂).IsColliderAt k ↔ p₁.IsColliderAt k)
  | _, _, _, .nil _, _, _, hk => by simp at hk
  | _, _, _, .cons _ (.nil _), _, _+1, hk => by
      simp [Walk.length_cons, Walk.length_nil] at hk
  | _, _, _, .cons _ (.nil _), p₂, 0, _ => by
      rw [Walk.cons_append, Walk.nil_append]
      cases p₂ with
      | nil _ => simp
      | cons _ _ => simp
  | _, _, _, .cons _ (.cons _ _), _, 0, _ => by
      rw [Walk.cons_append, Walk.cons_append]
      simp
  | _, _, _, .cons _ (.cons _ _), _, 1, _ => by
      rw [Walk.cons_append, Walk.cons_append]
      simp
  | _, _, _, .cons s (.cons s' p₁'), p₂, k+2, hk => by
      rw [Walk.cons_append, Walk.cons_append]
      simp only [Walk.isColliderAt_cons_cons_succ_succ]
      rw [← Walk.cons_append]
      have hk' : k + 1 < (Walk.cons s' p₁').length := by
        simp [Walk.length_cons] at hk ⊢; omega
      exact isColliderAt_append_lt_length (Walk.cons s' p₁') p₂ hk'

/-! ### Append-locality of `IsColliderAt` at the joint position -/

/-- The `IsColliderAt` predicate at the joint position
`p₁.length + 1` of `p₁.append (cons s (cons s' p₂))` is exactly the
joint condition at the head of `cons s (cons s' p₂)`. The structural
recursion on `p₁` shifts the index down by `p₁.length`, leaving the
fresh joint between `s` and `s'` exposed. -/
theorem isColliderAt_append_cons_cons_one : ∀ {u v w x y : α}
    (p₁ : Walk G u v) (s : WalkStep G v w) (s' : WalkStep G w x)
    (p₂ : Walk G x y),
    ((p₁.append (Walk.cons s (Walk.cons s' p₂))).IsColliderAt
      (p₁.length + 1) ↔ s.HasArrowheadAtTarget ∧ s'.HasArrowheadAtSource)
  | _, _, _, _, _, .nil _, _, _, _ => by
      simp [Walk.nil_append, Walk.length_nil]
  | _, _, _, _, _, .cons _ (.nil _), _, _, _ => by
      -- p₁ = cons _ (nil _), p₁.length = 1.
      -- After unfolding append + length, both sides reduce to the joint condition.
      simp [Walk.cons_append, Walk.nil_append, Walk.length_cons, Walk.length_nil]
  | _, _, _, _, _, .cons _ (.cons s''' p₁''), s, s', p₂ => by
      -- p₁ = cons _ (cons s''' p₁''), p₁.length = p₁''.length + 2.
      -- After unfolding append twice + length_cons, position becomes p₁''.length + 3
      -- and the walk has shape `cons _ (cons s''' (p₁''.append ...))`.
      -- Apply cons_cons_succ_succ once to peel off the outer cons, then fold back
      -- to (cons s''' p₁'').append form to apply IH.
      simp only [Walk.cons_append, Walk.length_cons,
        Walk.isColliderAt_cons_cons_succ_succ]
      rw [← Walk.cons_append]
      exact isColliderAt_append_cons_cons_one (Walk.cons s''' p₁'') s s' p₂

/-! ### Reversal-invariance of `IsColliderAt` -/

/-- The `IsColliderAt` predicate is invariant under walk reversal,
modulo the involution `k ↔ π.length - k`. This is the TeX proof's
"collider pattern $v_{k-1} \suh v_k \hus v_{k+1}$ becomes
$v_{k+1} \suh v_k \hus v_{k-1}$ at position $n-k$" step. -/
theorem isColliderAt_reverse_iff {v w : α} (π : Walk G v w) (k : ℕ) :
    π.reverse.IsColliderAt k ↔ π.IsColliderAt (π.length - k) := by
  induction π generalizing k with
  | nil v => simp [Walk.reverse_nil, Walk.length_nil]
  | cons s p ih =>
    cases p with
    | nil w =>
      -- single-step walk: both sides False for any k
      rw [Walk.reverse_cons, Walk.reverse_nil, Walk.nil_append,
        Walk.length_cons, Walk.length_nil]
      cases k with
      | zero => simp
      | succ k' => cases k' <;> simp
    | cons s' p' =>
      -- π = cons s (cons s' p'), length p'.length + 2
      have hlen : (Walk.cons s (Walk.cons s' p')).length = p'.length + 2 := by
        simp [Walk.length_cons]
      have hlenRev : (Walk.cons s (Walk.cons s' p')).reverse.length = p'.length + 2 := by
        rw [Walk.length_reverse, hlen]
      rcases Nat.lt_or_ge k (p'.length + 2) with hk | hk
      · rcases Nat.lt_or_ge k (p'.length + 1) with hkb | hkb
        · -- 0 ≤ k ≤ p'.length: interior of (cons s' p').reverse
          rw [Walk.reverse_cons]
          have hkp : k < (Walk.cons s' p').reverse.length := by
            rw [Walk.length_reverse, Walk.length_cons]; omega
          rw [isColliderAt_append_lt_length _ _ hkp]
          rw [ih k]
          simp only [Walk.length_cons]
          -- Goal: (cons s' p').IsColliderAt (p'.length + 1 - k) ↔
          --       (cons s (cons s' p')).IsColliderAt (p'.length + 1 + 1 - k)
          have h1 : p'.length + 1 - k = (p'.length - k) + 1 := by omega
          have h2 : p'.length + 1 + 1 - k = (p'.length - k) + 2 := by omega
          rw [h1, h2, Walk.isColliderAt_cons_cons_succ_succ]
        · -- k = p'.length + 1: joint case
          have hk_eq : k = p'.length + 1 := by omega
          subst hk_eq
          rw [Walk.reverse_cons, Walk.reverse_cons]
          rw [append_assoc, Walk.cons_append, Walk.nil_append]
          rw [show (p'.length + 1 : ℕ) = p'.reverse.length + 1 from by
            rw [Walk.length_reverse]]
          rw [isColliderAt_append_cons_cons_one p'.reverse s'.reverse s.reverse _]
          rw [WalkStep.reverse_hasArrowheadAtTarget,
            WalkStep.reverse_hasArrowheadAtSource]
          simp only [Walk.length_cons]
          rw [show p'.length + 1 + 1 - (p'.reverse.length + 1) = 1 from by
            rw [Walk.length_reverse]; omega]
          rw [Walk.isColliderAt_cons_cons_one]
          exact And.comm
      · -- k ≥ p'.length + 2 = length: out of range
        have hLHS : ¬ (Walk.cons s (Walk.cons s' p')).reverse.IsColliderAt k :=
          not_isColliderAt_of_length_le _ (by rw [hlenRev]; exact hk)
        have hsub : (Walk.cons s (Walk.cons s' p')).length - k = 0 := by
          rw [hlen]; omega
        rw [hsub, Walk.isColliderAt_cons_cons_zero]
        exact iff_false_intro hLHS

/-! ### Reversal-invariance of `IsUnblockableNonColliderAt` -/

/-- An unblockable-non-collider position past the walk's length is impossible. -/
theorem not_isUnblockableNonColliderAt_of_length_le {v w : α} (π : Walk G v w) {k : ℕ}
    (hk : π.length ≤ k) : ¬ π.IsUnblockableNonColliderAt k := fun h =>
  absurd (zero_lt_and_lt_length_of_isUnblockableNonColliderAt π k h).2
    (Nat.not_lt.mpr hk)

/-- Like `isColliderAt_append_lt_length`, but for the unblockable
non-collider predicate. -/
theorem isUnblockableNonColliderAt_append_lt_length : ∀ {u v w : α} (p₁ : Walk G u v)
    (p₂ : Walk G v w) {k : ℕ}, k < p₁.length →
    ((p₁.append p₂).IsUnblockableNonColliderAt k ↔ p₁.IsUnblockableNonColliderAt k)
  | _, _, _, .nil _, _, _, hk => by simp at hk
  | _, _, _, .cons _ (.nil _), _, _+1, hk => by
      simp [Walk.length_cons, Walk.length_nil] at hk
  | _, _, _, .cons _ (.nil _), p₂, 0, _ => by
      rw [Walk.cons_append, Walk.nil_append]
      cases p₂ with
      | nil _ => simp
      | cons _ _ => simp
  | _, _, _, .cons _ (.cons _ _), _, 0, _ => by
      rw [Walk.cons_append, Walk.cons_append]
      simp
  | _, _, _, .cons _ (.cons _ _), _, 1, _ => by
      rw [Walk.cons_append, Walk.cons_append]
      simp
  | _, _, _, .cons s (.cons s' p₁'), p₂, k+2, hk => by
      rw [Walk.cons_append, Walk.cons_append]
      simp only [Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]
      rw [← Walk.cons_append]
      have hk' : k + 1 < (Walk.cons s' p₁').length := by
        simp [Walk.length_cons] at hk ⊢; omega
      exact isUnblockableNonColliderAt_append_lt_length (Walk.cons s' p₁') p₂ hk'

/-- Like `isColliderAt_append_cons_cons_one`, but for the unblockable
non-collider predicate. -/
theorem isUnblockableNonColliderAt_append_cons_cons_one : ∀ {u v w x y : α}
    (p₁ : Walk G u v) (s : WalkStep G v w) (s' : WalkStep G w x)
    (p₂ : Walk G x y),
    ((p₁.append (Walk.cons s (Walk.cons s' p₂))).IsUnblockableNonColliderAt
      (p₁.length + 1) ↔ s.IsUnblockableJoint s')
  | _, _, _, _, _, .nil _, _, _, _ => by
      simp [Walk.nil_append, Walk.length_nil]
  | _, _, _, _, _, .cons _ (.nil _), _, _, _ => by
      simp [Walk.cons_append, Walk.nil_append, Walk.length_cons, Walk.length_nil]
  | _, _, _, _, _, .cons _ (.cons s''' p₁''), s, s', p₂ => by
      simp only [Walk.cons_append, Walk.length_cons,
        Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]
      rw [← Walk.cons_append]
      exact isUnblockableNonColliderAt_append_cons_cons_one
        (Walk.cons s''' p₁'') s s' p₂

/-- The `IsUnblockableNonColliderAt` predicate is invariant under
walk reversal, modulo the involution `k ↔ π.length - k`. The TeX
proof's "unblockability condition … is preserved: the endpoint
condition transports …, the set of outgoing arrows from $v_k$ on
the walk is intrinsic to the two incident edges …, and
$\Sc^G(v_k)$ depends on $G$ and $v_k$ alone" decomposes (via the
`IsUnblockableJoint` joint condition) exactly into the per-step
`reverse_isUnblockableJoint` lemma in `WalkStep`. -/
theorem isUnblockableNonColliderAt_reverse_iff {v w : α} (π : Walk G v w) (k : ℕ) :
    π.reverse.IsUnblockableNonColliderAt k ↔
      π.IsUnblockableNonColliderAt (π.length - k) := by
  induction π generalizing k with
  | nil v => simp [Walk.reverse_nil, Walk.length_nil]
  | cons s p ih =>
    cases p with
    | nil w =>
      rw [Walk.reverse_cons, Walk.reverse_nil, Walk.nil_append,
        Walk.length_cons, Walk.length_nil]
      cases k with
      | zero => simp
      | succ k' => cases k' <;> simp
    | cons s' p' =>
      have hlen : (Walk.cons s (Walk.cons s' p')).length = p'.length + 2 := by
        simp [Walk.length_cons]
      have hlenRev : (Walk.cons s (Walk.cons s' p')).reverse.length = p'.length + 2 := by
        rw [Walk.length_reverse, hlen]
      rcases Nat.lt_or_ge k (p'.length + 2) with hk | hk
      · rcases Nat.lt_or_ge k (p'.length + 1) with hkb | hkb
        · -- interior of (cons s' p').reverse
          rw [Walk.reverse_cons]
          have hkp : k < (Walk.cons s' p').reverse.length := by
            rw [Walk.length_reverse, Walk.length_cons]; omega
          rw [isUnblockableNonColliderAt_append_lt_length _ _ hkp]
          rw [ih k]
          simp only [Walk.length_cons]
          have h1 : p'.length + 1 - k = (p'.length - k) + 1 := by omega
          have h2 : p'.length + 1 + 1 - k = (p'.length - k) + 2 := by omega
          rw [h1, h2, Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]
        · -- joint case
          have hk_eq : k = p'.length + 1 := by omega
          subst hk_eq
          rw [Walk.reverse_cons, Walk.reverse_cons]
          rw [append_assoc, Walk.cons_append, Walk.nil_append]
          rw [show (p'.length + 1 : ℕ) = p'.reverse.length + 1 from by
            rw [Walk.length_reverse]]
          rw [isUnblockableNonColliderAt_append_cons_cons_one p'.reverse
            s'.reverse s.reverse _]
          rw [WalkStep.reverse_isUnblockableJoint]
          simp only [Walk.length_cons]
          rw [show p'.length + 1 + 1 - (p'.reverse.length + 1) = 1 from by
            rw [Walk.length_reverse]; omega]
          rw [Walk.isUnblockableNonColliderAt_cons_cons_one]
      · -- k ≥ length: out of range
        have hLHS : ¬ (Walk.cons s (Walk.cons s' p')).reverse.IsUnblockableNonColliderAt k :=
          not_isUnblockableNonColliderAt_of_length_le _
            (by rw [hlenRev]; exact hk)
        have hsub : (Walk.cons s (Walk.cons s' p')).length - k = 0 := by
          rw [hlen]; omega
        rw [hsub, Walk.isUnblockableNonColliderAt_cons_cons_zero]
        exact iff_false_intro hLHS

/-! ### Reversal-invariance of `IsNonColliderAt` and
`IsBlockableNonColliderAt` -/

/-- The `IsNonColliderAt` predicate is invariant under walk
reversal, modulo `k ↔ π.length - k`. Requires `k ≤ π.length`
since `IsNonColliderAt` has a `k ≤ length` conjunct that would
otherwise spuriously transport. -/
theorem isNonColliderAt_reverse_iff {v w : α} (π : Walk G v w) {k : ℕ}
    (hk : k ≤ π.length) :
    π.reverse.IsNonColliderAt k ↔ π.IsNonColliderAt (π.length - k) := by
  unfold Walk.IsNonColliderAt
  rw [Walk.length_reverse, isColliderAt_reverse_iff]
  refine ⟨fun ⟨_, h⟩ => ⟨by omega, h⟩, fun ⟨_, h⟩ => ⟨hk, h⟩⟩

/-- The `IsBlockableNonColliderAt` predicate is invariant under
walk reversal, modulo `k ↔ π.length - k`. The TeX proof's
"combining the second and third bullets, this predicate too
transports under $k \leftrightarrow n-k$" step. -/
theorem isBlockableNonColliderAt_reverse_iff {v w : α} (π : Walk G v w) {k : ℕ}
    (hk : k ≤ π.length) :
    π.reverse.IsBlockableNonColliderAt k ↔
      π.IsBlockableNonColliderAt (π.length - k) := by
  unfold Walk.IsBlockableNonColliderAt
  rw [isNonColliderAt_reverse_iff π hk,
    isUnblockableNonColliderAt_reverse_iff π k]

/-! ### Reversal-invariance of `IsSigmaBlocked` (the main lemma) -/

/-- σ-blocking is invariant under walk reversal: `π.IsSigmaBlocked C
↔ π.reverse.IsSigmaBlocked C`. This is the sub-lemma of the TeX
proof's Step 3 that drives the symmetry of σ-separation. Each of
the two `IsSigmaBlocked` clauses transports via the involution
`k ↔ π.length - k`, using `isColliderAt_reverse_iff` (resp.
`isBlockableNonColliderAt_reverse_iff`) for the predicate and
`nodeAt_reverse` for the vertex; `G.AncSet C` is intrinsic to
`G` and `C` and so unchanged. -/
theorem isSigmaBlocked_reverse_iff {v w : α} (π : Walk G v w) (C : Set α) :
    π.reverse.IsSigmaBlocked C ↔ π.IsSigmaBlocked C := by
  -- Forward and backward use the same construction: extract witness, map index k ↔ length - k.
  constructor
  · rintro (⟨k, hcoll, hOut⟩ | ⟨k, hblock, hIn⟩)
    · -- collider witness k on π.reverse
      have hk : k < π.reverse.length := isColliderAt_lt_length _ hcoll
      rw [Walk.length_reverse] at hk
      have hkLe : k ≤ π.length := le_of_lt hk
      refine Or.inl ⟨π.length - k, ?_, ?_⟩
      · rw [isColliderAt_reverse_iff] at hcoll; exact hcoll
      · rw [nodeAt_reverse π hkLe] at hOut; exact hOut
    · -- blockable non-collider witness k on π.reverse
      have hkRevLe : k ≤ π.reverse.length := hblock.1.1
      have hkLe : k ≤ π.length := by
        rw [Walk.length_reverse] at hkRevLe; exact hkRevLe
      refine Or.inr ⟨π.length - k, ?_, ?_⟩
      · rw [isBlockableNonColliderAt_reverse_iff π hkLe] at hblock; exact hblock
      · rw [nodeAt_reverse π hkLe] at hIn; exact hIn
  · rintro (⟨k, hcoll, hOut⟩ | ⟨k, hblock, hIn⟩)
    · -- collider witness k on π
      have hk : k < π.length := isColliderAt_lt_length _ hcoll
      have hkLe : k ≤ π.length := le_of_lt hk
      have hkSub : π.length - k ≤ π.length := Nat.sub_le _ _
      refine Or.inl ⟨π.length - k, ?_, ?_⟩
      · rw [isColliderAt_reverse_iff]
        rw [show π.length - (π.length - k) = k from by omega]
        exact hcoll
      · rw [nodeAt_reverse π hkSub]
        rw [show π.length - (π.length - k) = k from by omega]
        exact hOut
    · -- blockable non-collider witness k on π
      have hkLe : k ≤ π.length := hblock.1.1
      have hkSub : π.length - k ≤ π.length := Nat.sub_le _ _
      refine Or.inr ⟨π.length - k, ?_, ?_⟩
      · rw [isBlockableNonColliderAt_reverse_iff π hkSub]
        rw [show π.length - (π.length - k) = k from by omega]
        exact hblock
      · rw [nodeAt_reverse π hkSub]
        rw [show π.length - (π.length - k) = k from by omega]
        exact hIn

end Walk

end Causality
