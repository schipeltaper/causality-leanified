import Chapter3_GraphTheory.Section3_2.MarginalizationsCommute
import Chapter3_GraphTheory.Section3_2.MarginalizationPreserves
import Chapter3_GraphTheory.Section3_3.ISigmaSeparation
import Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks
import Chapter3_GraphTheory.Section3_3.SigmaSeparationEquivalences
import Chapter3_GraphTheory.Section3_3.SigmaOpenPathWalk
import Chapter3_GraphTheory.Section3_3.SigmaBlockedReversal
import Chapter3_GraphTheory.Section3_3.LabelRomanHelpers

-- TeX proof reference:
-- leanification/Chapter3_GraphTheory/Section3_3/tex/claim_3_25_proof_ISigmaSeparation.tex
-- specifically lines 41 -- 105 (the (⇒) lift direction, single-vertex case).

/-!
# σ-open-walk marginalization layer for claim_3_25

This file is the **σ-open-walk marginalization layer** sitting
between `Section3_3/SigmaSeparationEquivalences.lean` and
`Section3_3/ISigmaSeparationMarginalization.lean` (the row-level
file for claim_3_25). It exposes the single-vertex (`D = {u}`)
walk-translation primitives that the row-level
`isISigmaSeparated_marginalize_iff` proof will compose:

1. **`lift_sigmaOpen_walk_through_single_vertex`** -- the (⇒)
   direction. Every $C$-σ-open walk in `G.marginalize {u}` whose
   colliders all lie in `C` lifts to a $C$-σ-open walk in `G`
   with colliders still in `C`. Mirrors the LN's proof.tex
   lines 41 -- 105.

2. **`contract_sigmaOpen_walk_at_single_vertex`** -- the (⇐)
   direction (stubbed, see Sub-task 3). Every $C$-σ-open walk
   in `G` contracts to a $C$-σ-open walk in `G.marginalize {u}`.

3. **`isISigmaSeparated_marginalize_singleton_iff`** -- the
   single-vertex iff (stubbed, see Sub-task 4). Wraps the two
   directions into a predicate-level equivalence.

## Provenance and dependencies

The mathematical content traces directly to the LN's lift
table (`claim_3_25_proof_ISigmaSeparation.tex` lines 57 -- 70):
"every edge in $G^{\sm u}$ lifts to a short walk through $u$
in $G$", with four enumerated lift patterns for bifurcation
edges and the directed-walk-with-interior-in-$\{u\}$ pattern
for directed edges.

Sub-task 1 (the leanification diagnostic at
`Section3_3/workspace_claim_3_25.md` §D.1 -- D.2) already
completed the upstream API additions and visibility promotions:

* `MarginalizationsCommute.lean` -- public access to
  `lift_directed_walk` (line 145), `shrink_directed_walk`
  (line 302), `directed_walk_iff` (503),
  `directed_walk_iff_no_length` (543), `lift_bifurcation_walk`
  (610), `shrink_bifurcation_walk` (710),
  `bifurcation_walk_iff_no_length` (808).
* `MarginalizationPreserves.lean` -- new set-level helpers
  `marginalize_desc_iff` (3986), `marginalize_Sc_iff` (4040),
  `marginalize_AncSet_subset` (4093),
  `marginalize_AncSet_eq_on_complement` (4142).

The lift direction proven here uses the directed-walk and
bifurcation lift primitives plus `marginalize_AncSet_subset`
for the AncSet-membership transport at colliders, plus
`marginalize_Sc_iff` together with the LN's "outgoing-edge
through $u$ is in $\Sc^G(b_j)$" SCC argument for the
unblockability-preservation step at boundary non-colliders.

## Position-indexing convention

Mirrors `Section3_3/SigmaBlockedWalks.lean`:

* Positions are indexed by `ℕ` over `{0, …, π.length}`.
* `nodeAt` is junk-on-out-of-range; the junk is never
  semantically observed by `IsSigmaOpen` /
  `IsColliderAt` / `IsBlockableNonColliderAt`.
* End-nodes are always blockable non-colliders;
  interior non-colliders may be blockable or unblockable;
  unblockable positions are strictly interior
  (`0 < k < π.length`).

## Style precedents

* `Section3_3/LabelRomanHelpers.lean` -- module-docstring
  style and use of `Walk.prefix` / `Walk.suffix` /
  `Walk.append` as the structural sub-walk primitives.
* `Section3_3/SigmaOpenPathWalk.lean` -- the σ-open-walk
  manipulation paradigm at the row-level: induct on the walk,
  splice via `prefix.append (middle.append suffix)`, use
  `marginalize_AncSet_subset` (or its set-level analogues) to
  transport σ-open clauses across walk transformations.
* `Section3_2/MarginalizationsCommute.lean` -- the structural
  recursion pattern over a `Walk (G.marginalize W) v w`,
  case-splitting on the head step's constructor (forward /
  backward / bidir) and unfolding `mem_marginalize_E` /
  `mem_marginalize_L` to extract the lift segment.

## Sub-task ownership

* **Sub-task 2 (this file)**: owns the **lift direction only**.
  The lift theorem is fully proven; the two follow-up
  declarations carry `by sorry` bodies with explicit
  `TODO(Sub-task N): ...` decorations citing the row-level
  workspace at `Section3_3/workspace_claim_3_25.md`.
* **Sub-task 3**: owns the contract direction. The LN's
  "longer runs through self-loops are handled analogously"
  hand-wave (proof.tex lines 129 -- 130, Blocker B in the
  diagnostic §B.2) is expected to bite there; the worker
  should escalate via `expand_proof` on the LN's
  `\Claude{...}` if it does.
* **Sub-task 4**: owns the singleton iff. The proof should
  be ~2 -- 5 lines, combining the two directions above with
  `isISigmaSeparated_TFAE` / `isNotISigmaSeparated_TFAE` to
  bridge between "no σ-open walk" and the `IsISigmaSeparated`
  predicate.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace CDMG

/-! ### Bifurcation walks have no collider at any position -/

-- claim_3_25 helper (Sub-task 2a)
-- title: SigmaOpenWalkMarginalization -- bifurcations are collider-free
--
-- A `BifurcationWitness` decomposes a walk as
-- `v_0 \hut v_1 \hut \cdots \hut v_{k-1} \hus v_k \tuh \cdots \tuh v_n`
-- with the left arm all `backward` (LN's `\hut`), the hinge being
-- `backward` or `bidir` (LN's `\hus`), and the right arm all
-- `forward` (LN's `\tuh`). At every interior joint, at least one of
-- the two adjacent steps lacks the relevant arrowhead at the joint
-- vertex:
--
-- * Inside the left arm (two adjacent `backward` steps), the LEFT
--   step has `HasArrowheadAtTarget = False`.
-- * At the boundary between the last left-arm step and the hinge,
--   the LEFT step is `backward` so `HasArrowheadAtTarget = False`.
-- * At the boundary between the hinge and the first right-arm step,
--   the RIGHT step is `forward` so `HasArrowheadAtSource = False`.
-- * Inside the right arm (two adjacent `forward` steps), the RIGHT
--   step has `HasArrowheadAtSource = False`.
--
-- Either failure mode falsifies the collider joint condition
-- `s.HasArrowheadAtTarget ∧ s'.HasArrowheadAtSource`. The end-point
-- and out-of-range positions are non-colliders by definition of
-- `IsColliderAt` (which returns `False` on `nil`, `cons _ nil`, and
-- on `cons _ (cons _ _)` at position 0; the `not_isColliderAt_of_length_le`
-- lemma covers `k ≥ length`).
--
-- This helper is consumed by `lift_aux` (the auxiliary lift body of
-- `lift_sigmaOpen_walk_through_single_vertex`) in the
-- bifurcation-lift case: when an edge of `G^{\sm u}` lifts to a
-- bifurcation walk in `G`, the collider verification at the
-- bifurcation's interior `u`-positions is fully discharged by this
-- lemma — since the bifurcation is collider-free at every position,
-- the σ-open clause 1 (colliders in `Anc^G(C)`) is vacuously true on
-- the lift segment, and only the clause-2 (blockable non-colliders
-- not in `C`) check at the inserted `u`-vertices remains, which is
-- discharged by the `huC : u ∉ C` precondition.
--
-- ## Design choice
--
-- * **Universal in `k`, not just interior.** The manager's refined
--   TODO at `Section3_3/workspace_claim_3_25.md` Manager B turn 6
--   noted that stating the universal version (no collider at *any*
--   position, including endpoints and out-of-range) is strictly
--   stronger than the "interior only" version and avoids the
--   downstream boundary bookkeeping. Endpoint and out-of-range
--   positions are non-colliders by `IsColliderAt`'s definition and
--   by `not_isColliderAt_of_length_le` respectively — neither needs
--   to be re-asserted at the caller.
--
-- * **Inner `suffices` generalises over the left arm.** The
--   structural induction is naturally on the left arm of the
--   bifurcation, but the bifurcation predicate itself does not admit
--   a useful direct induction principle. We restate the goal as a
--   universally-quantified statement over an abstract walk
--   `la.append (.cons hi ra)`, then induct on `la : Walk G a m`. The
--   hinge `hi` and right arm `ra` stay constant through the
--   recursion. Per the manager's note in
--   `SigmaOpenWalkMarginalization.lean:280--592`, helper (1) is the
--   "only genuinely new content" of the lift; the structural
--   induction is straightforward once `la` is exposed.
--
-- * **`hingeIntoSource` is not consumed.** The bifurcation witness's
--   `hingeIntoSource` field (the hinge has an arrowhead at its
--   source) is irrelevant to the no-collider argument: the collider
--   failures at positions `leftArm.length` (left-side) and
--   `leftArm.length + 1` (right-side) come from the *left* last step
--   (backward) and the *right* first step (forward) respectively,
--   never from the hinge's source-arrowhead. The proof consumes only
--   `leftBackward` (left arm all-backward) and `rightDirected`
--   (right arm all-forward) from the witness.
--
-- * **Style mirrors `LabelRomanHelpers.not_isColliderAt_of_isDirected`.**
--   The case-split structure (`cases s` → `cases j` → `cases j`)
--   parallels the existing template at `LabelRomanHelpers.lean:103`,
--   keeping the proof readable for anyone already familiar with the
--   existing collider-freeness lemmas in this layer.
/-- A bifurcation walk has no collider at any position. The shape
$v_0 \hut v_1 \hut \cdots \hut v_{k-1} \hus v_k \tuh \cdots \tuh v_n$
puts at least one no-arrowhead side at every interior joint:
inside the left arm both steps are `backward` (no target-arrowhead
on the left); at the left-arm / hinge boundary the left step is
`backward`; at the hinge / right-arm boundary the right step is
`forward` (no source-arrowhead on the right); inside the right arm
both steps are `forward`. Endpoint and out-of-range positions are
non-colliders by definition. -/
private lemma not_isColliderAt_of_isBifurcation {v w : α} {G : CDMG α}
    {π : Walk G v w} (hπ : π.IsBifurcation) (k : ℕ) :
    ¬ π.IsColliderAt k := by
  obtain ⟨bw⟩ := hπ.2.2.2
  rw [bw.decompose]
  -- Generalise the statement over an arbitrary all-backward left arm
  -- `la`, an arbitrary step `hi` (no constraint needed -- the
  -- bifurcation's `hingeIntoSource` is unused), and an arbitrary
  -- directed right arm `ra`. Then induct on `la`.
  suffices h : ∀ {a m m' b : α} (la : Walk G a m) (hi : WalkStep G m m')
                  (ra : Walk G m' b),
                  la.IsAllBackward → ra.IsDirected →
                  ∀ j, ¬ (la.append (Walk.cons hi ra)).IsColliderAt j from
    h bw.leftArm bw.hinge bw.rightArm bw.leftBackward bw.rightDirected k
  intro a m m' b la
  induction la with
  | nil m =>
    -- `la = nil m`, so the walk is `cons hi ra`. Case on `ra` and `j`
    -- to push the collider check to either an end-node (False by
    -- definition), the joint between `hi` and `ra`'s first forward
    -- step (failed by `ra` being directed → first step is forward →
    -- `HasArrowheadAtSource = False`), or strictly inside `ra` (no
    -- collider on a directed walk by `not_isColliderAt_of_isDirected`).
    intro hi ra _ hrd j hcol
    rw [Walk.nil_append] at hcol
    cases ra with
    | nil _ => exact (Walk.isColliderAt_cons_nil _ _).mp hcol
    | @cons _ _ _ s' p' =>
      cases j with
      | zero => exact (Walk.isColliderAt_cons_cons_zero _ _ _).mp hcol
      | succ j =>
        cases j with
        | zero =>
          rw [Walk.isColliderAt_cons_cons_one] at hcol
          -- `hcol : hi.HasArrowheadAtTarget ∧ s'.HasArrowheadAtSource`.
          -- `s'` is the first step of the directed `ra`, so `forward`.
          cases s' with
          | forward _ => exact hcol.2
          | backward _ => simp at hrd
          | bidir _ => simp at hrd
        | succ j =>
          simp only [Walk.isColliderAt_cons_cons_succ_succ] at hcol
          exact Walk.not_isColliderAt_of_isDirected _ (j+1) hrd hcol
  | @cons _ _ _ s p ih =>
    -- `la = cons s p`. From `la.IsAllBackward`, `s` is `backward`
    -- (the other two constructor cases close immediately via `simp`).
    -- After `Walk.cons_append`, the walk reads
    -- `cons (backward h_e) (p.append (cons hi ra))`. The tail
    -- `p.append (cons hi ra)` has length ≥ 1, so by `walk_pos_eq_cons`
    -- it equals `cons s'' rest` for some head step `s''`; rewriting
    -- via that equation puts the goal in `cons _ (cons _ _)` form
    -- and the usual three-way case-split on `j` works:
    --   * j = 0 → False by `isColliderAt_cons_cons_zero`.
    --   * j = 1 → joint condition reduces to
    --     `(backward h_e).HasArrowheadAtTarget ∧ _`, whose left
    --     conjunct unfolds to `False` (backward steps have no
    --     target-arrowhead).
    --   * j = j' + 2 → reduces to `(cons s'' rest).IsColliderAt (j'+1)`;
    --     rewriting back via `← h_tail_eq` exposes
    --     `(p.append (cons hi ra)).IsColliderAt (j'+1)` for the IH.
    intro hi ra hlb hrd j hcol
    cases s with
    | forward _ => simp at hlb
    | bidir _ => simp at hlb
    | backward h_e =>
      simp only [Walk.isAllBackward_cons_backward] at hlb
      rw [Walk.cons_append] at hcol
      have h_tail_pos : 1 ≤ (p.append (Walk.cons hi ra)).length := by
        rw [Walk.length_append, Walk.length_cons]; omega
      obtain ⟨_, s'', rest, h_tail_eq⟩ := Walk.walk_pos_eq_cons _ h_tail_pos
      rw [h_tail_eq] at hcol
      cases j with
      | zero => exact (Walk.isColliderAt_cons_cons_zero _ _ _).mp hcol
      | succ j =>
        cases j with
        | zero =>
          rw [Walk.isColliderAt_cons_cons_one] at hcol
          exact hcol.1
        | succ j =>
          simp only [Walk.isColliderAt_cons_cons_succ_succ] at hcol
          rw [← h_tail_eq] at hcol
          exact ih hi ra hlb hrd (j+1) hcol

/-! ### Step-lift and append-shift helpers (Sub-task 2b) -/

-- claim_3_25 helpers (Sub-task 2b)
--
-- Five mechanical helpers (plus one tiny auxiliary `interiorIn_reverse_iff`)
-- needed by the (⇒) lift theorem `lift_sigmaOpen_walk_through_single_vertex`.
-- Each is a thin composition of upstream API from
-- `Section3_2/Marginalization.lean`,
-- `Section3_2/MarginalizationPreserves.lean`, and
-- `Section3_3/LabelRomanHelpers.lean`. The set:
--
--   * (aux) `interiorIn_reverse_iff` -- interior preserved by reverse.
--   * (2)   `isBlockableNonColliderAt_append_shift_pos` -- append-shift.
--   * (3)   `isAllBackward_reverse_of_isDirected_local` -- local copy
--           of `Section3_2/BifurcationAlternative.lean:136`.
--   * (4)   `forward_step_to_walk_in_G` -- per-step `forward` lift.
--   * (5)   `backward_step_to_walk_in_G` -- per-step `backward` lift.
--   * (6)   `bidir_step_to_walk_in_G` -- per-step `bidir` lift.

-- ## Design choice (auxiliary `interiorIn_reverse_iff`)
--
-- Not one of the five spec'd helpers, but invoked by (5) and (6) to
-- transport `InteriorIn` across `Walk.reverse`. The proof is a single
-- `simp only` chain through `Walk.support_reverse` plus the standard
-- list lemmas (`List.tail_reverse`, `List.dropLast_reverse`,
-- `List.mem_reverse`, `List.tail_dropLast`). Placed first so (5) and
-- (6) can call it.
/-- Interior membership is preserved by walk reversal: the set of
interior vertices of `π.reverse` is set-theoretically the same as
the set of interior vertices of `π` (only the traversal order
changes). -/
private lemma interiorIn_reverse_iff {G : CDMG α} {v w : α}
    (π : Walk G v w) (W : Set α) :
    π.reverse.InteriorIn W ↔ π.InteriorIn W := by
  simp only [Walk.interiorIn_def, Walk.support_reverse, List.tail_reverse,
    List.dropLast_reverse, List.mem_reverse, List.tail_dropLast]

-- ## Design choice (helper 2)
--
-- Mirrors `Walk.isUnblockableNonColliderAt_append_shift_pos`
-- (`Section3_3/LabelRomanHelpers.lean:785`) but for the blockable
-- variant. `Walk.IsBlockableNonColliderAt k` unfolds (per
-- `Section3_3/BlockableAndUnblockable.lean:549`) to
-- `IsNonColliderAt k ∧ ¬ IsUnblockableNonColliderAt k`, and
-- `IsNonColliderAt k` further unfolds (per
-- `Section3_3/CollidersAndNon.lean:314`) to
-- `(k ≤ length) ∧ ¬ IsColliderAt k`. The three pieces transport
-- independently via `length_append`, `isColliderAt_append_shift_pos`,
-- and `isUnblockableNonColliderAt_append_shift_pos`. The length
-- piece is the only non-trivial step (needs an `omega` to push
-- `p₁.length + k' ≤ p₁.length + p₂.length ↔ k' ≤ p₂.length`).
/-- Append-shift transport for `IsBlockableNonColliderAt`: for
positions strictly inside the right factor, the predicate transports
unchanged from the appended walk to the right factor. -/
private theorem isBlockableNonColliderAt_append_shift_pos
    {G : CDMG α} {u v w : α} (p₁ : Walk G u v) (p₂ : Walk G v w) (k' : ℕ)
    (hk : 0 < k') :
    (p₁.append p₂).IsBlockableNonColliderAt (p₁.length + k') ↔
      p₂.IsBlockableNonColliderAt k' := by
  rw [Walk.isBlockableNonColliderAt_iff, Walk.isBlockableNonColliderAt_iff,
      Walk.isNonColliderAt_iff, Walk.isNonColliderAt_iff,
      Walk.isColliderAt_append_shift_pos p₁ p₂ k' hk,
      Walk.isUnblockableNonColliderAt_append_shift_pos p₁ p₂ k' hk,
      Walk.length_append]
  constructor
  · rintro ⟨⟨_, hcol⟩, hunb⟩
    exact ⟨⟨by omega, hcol⟩, hunb⟩
  · rintro ⟨⟨_, hcol⟩, hunb⟩
    exact ⟨⟨by omega, hcol⟩, hunb⟩

-- ## Design choice (helper 3)
--
-- Direct re-derivation of the private lemma at
-- `Section3_2/BifurcationAlternative.lean:136`. Lean's privacy is
-- file-local, so the private declaration there is invisible here;
-- the `_local` suffix makes the relationship explicit to future
-- readers (as suggested by the manager's spec). We substitute the
-- public `Walk.marg_isAllBackward_append`
-- (`Section3_2/MarginalizationPreserves.lean:183`) for the private
-- `isAllBackward_append` referenced in the original body -- both
-- prove the same fact, and the public form is reachable from this
-- module via the existing `MarginalizationsCommute` import.
/-- A `forward` step reverses to a `backward` step, so an all-forward
(`IsDirected`) walk reverses to an all-backward walk. Local copy of
the private lemma at `Section3_2/BifurcationAlternative.lean:136`. -/
private lemma isAllBackward_reverse_of_isDirected_local {G : CDMG α}
    {v w : α} {p : Walk G v w} (hp : p.IsDirected) :
    p.reverse.IsAllBackward := by
  induction p with
  | nil _ => simp
  | cons s p' ih =>
    cases s with
    | forward h =>
      simp only [Walk.isDirected_cons_forward] at hp
      simp only [Walk.reverse_cons, WalkStep.reverse_forward]
      rw [Walk.marg_isAllBackward_append]
      exact ⟨ih hp, by simp⟩
    | backward _ => simp at hp
    | bidir _ => simp at hp

-- ## Design choice (helper 4)
--
-- Thin wrapper around `CDMG.mem_marginalize_E`
-- (`Section3_2/Marginalization.lean:575`). Unfolds the
-- directed-edge-membership iff and extracts the witness directed
-- walk, discarding the two boundary-membership conjuncts (the
-- caller already has them via `hvu` / `hmu`). The `hvu` and `hmu`
-- hypotheses are documentary -- they pin down which
-- marginalization-of-edge case we're in -- but the proof body
-- does not consume them.
/-- Per-step lift for a `forward` step in `G.marginalize {u}`: the
underlying `mem_marginalize_E` witness gives a directed walk in `G`
with interior in `{u}` of length ≥ 1. -/
private lemma forward_step_to_walk_in_G {G : CDMG α} {u v m : α}
    (h_E : (v, m) ∈ (G.marginalize {u}).E)
    (hvu : v ≠ u) (hmu : m ≠ u) :
    ∃ σ : Walk G v m, σ.IsDirected ∧ σ.InteriorIn {u} ∧ 1 ≤ σ.length := by
  rw [CDMG.mem_marginalize_E] at h_E
  obtain ⟨_, _, π, hπ_dir, hπ_int, hπ_pos⟩ := h_E
  exact ⟨π, hπ_dir, hπ_int, hπ_pos⟩

-- ## Design choice (helper 5)
--
-- Symmetric to (4) but for `backward` steps: a backward step
-- `(m, v) ∈ E^{\sm \{u\}}` unfolds (via `mem_marginalize_E` on the
-- swapped pair) to a directed walk `π : Walk G m v` with interior
-- in `{u}`. Reverse to obtain `σ := π.reverse : Walk G v m`, which
-- is all-backward (helper 3), retains interior in `{u}`
-- (`interiorIn_reverse_iff`), and has the same length
-- (`Walk.length_reverse`).
/-- Per-step lift for a `backward` step in `G.marginalize {u}`: the
reverse of the underlying `mem_marginalize_E` witness is an
all-backward walk in `G` with interior in `{u}` of length ≥ 1. -/
private lemma backward_step_to_walk_in_G {G : CDMG α} {u v m : α}
    (h_E : (m, v) ∈ (G.marginalize {u}).E)
    (hvu : v ≠ u) (hmu : m ≠ u) :
    ∃ σ : Walk G v m, σ.IsAllBackward ∧ σ.InteriorIn {u} ∧ 1 ≤ σ.length := by
  rw [CDMG.mem_marginalize_E] at h_E
  obtain ⟨_, _, π, hπ_dir, hπ_int, hπ_pos⟩ := h_E
  refine ⟨π.reverse, isAllBackward_reverse_of_isDirected_local hπ_dir,
    (interiorIn_reverse_iff π {u}).mpr hπ_int, ?_⟩
  rwa [Walk.length_reverse]

-- ## Design choice (helper 6 -- softened, no `IsBifurcation`)
--
-- `mem_marginalize_L` (`Section3_2/Marginalization.lean:597`)
-- exposes the bifurcation existential in *either* walk direction
-- (`v → m` or `m → v`). Manager B's call (turn 7): **drop the
-- `IsBifurcation` conjunct from the conclusion**. Rationale: in
-- the consumer (the lift theorem's bidir-case branch), the
-- joint-condition matching at the boundary is vacuously satisfied
-- regardless of σ's internal structure -- because a `bidir` step
-- has arrowheads at both endpoints, the implication
-- `σ.last.HasArrowheadAtTarget → step.HasArrowheadAtTarget`
-- collapses to `True → True` (see the refined TODO observation at
-- `:498--501`). Therefore the consumer only needs a walk in `G`
-- with the right interior and length ≥ 1 -- not strictly a
-- bifurcation. Dropping the `IsBifurcation` conjunct sidesteps
-- the bifurcation-reversal subtlety at
-- `Section3_2/Marginalization.lean:369--371` (where reversal of
-- a single-step backward bifurcation does *not* preserve
-- `IsBifurcation`). If a future caller does need the
-- bifurcation, see the TODO note inline.
--
-- `huV : u ∈ G.V` is preserved in the signature as documentary
-- context (matches the upstream lift theorem's precondition), but
-- the proof body does not consume it.
/-- Per-step lift for a `bidir` step in `G.marginalize {u}`: the
underlying `mem_marginalize_L` witness (in either direction) gives
a walk in `G` from `v` to `m` with interior in `{u}` and length
≥ 1. The `IsBifurcation` conjunct is dropped from the conclusion;
see the design block for the rationale. -/
private lemma bidir_step_to_walk_in_G {G : CDMG α} {u v m : α}
    (h_L : (v, m) ∈ (G.marginalize {u}).L)
    (hvu : v ≠ u) (hmu : m ≠ u) (huV : u ∈ G.V) :
    ∃ σ : Walk G v m, σ.InteriorIn {u} ∧ 1 ≤ σ.length := by
  rw [CDMG.mem_marginalize_L] at h_L
  -- TODO: caller may need `IsBifurcation`; if so, case-analyse on
  -- direction here and apply `Walk.reverse`, attending to the
  -- bifurcation-reversal warning at
  -- `Section3_2/Marginalization.lean:369--371`.
  obtain ⟨_, _, _, _, _, h_bif⟩ := h_L
  rcases h_bif with ⟨π, hπ_bif, hπ_int⟩ | ⟨π, hπ_bif, hπ_int⟩
  · -- Bifurcation in v → m direction: use π directly.
    exact ⟨π, hπ_int, π.length_pos_of_isBifurcation hπ_bif⟩
  · -- Bifurcation in m → v direction: reverse.
    refine ⟨π.reverse, (interiorIn_reverse_iff π {u}).mpr hπ_int, ?_⟩
    rw [Walk.length_reverse]
    exact π.length_pos_of_isBifurcation hπ_bif

/-! ### Strong bidir-step lift and SCC argument (Sub-task 2c locals) -/

-- claim_3_25 helper (Sub-task 2c, strong bidir lift)
--
-- The `bidir_step_to_walk_in_G` (helper 6) softened the conclusion to
-- just `σ.InteriorIn {u} ∧ 1 ≤ σ.length`. For the boundary verification
-- in `lift_aux`, we need stronger guarantees on σ:
--
--   * **No collider on σ at any position** -- so the σ-open verification
--     at positions inside σ has no collider obligation to discharge.
--   * **σ's first step has a source-arrowhead** -- matching the outer
--     `.bidir` step's `HasArrowheadAtSource = True`, needed for the
--     first-step source-arrowhead iff invariant.
--   * **σ's last step has a target-arrowhead** -- matching the outer
--     `.bidir` step's `HasArrowheadAtTarget = True`, needed for the
--     boundary joint condition.
--
-- The proof unfolds `mem_marginalize_L` and case-analyses on the
-- direction of the bifurcation witness (v → m, or m → v reversed):
--
-- * **Case (i)** (bifurcation v → m): take σ := π. No collider by
--   helper 1. The first step is the first step of the bifurcation's
--   left arm (backward) or, if the left arm is `nil`, the hinge (backward
--   or bidir) -- either way, source-arrowhead True. The last step is the
--   last step of the right arm (forward, since right arm is all-forward)
--   or, if the right arm is `nil`, the hinge. For hinge = bidir: target
--   arrowhead True. For hinge = backward with empty right arm: π is
--   all-backward, so π.reverse is directed m → v with interior in {u},
--   contradicting `mem_marginalize_L`'s 4th conjunct.
--
-- * **Case (ii)** (bifurcation m → v, reversed): take σ := π.reverse.
--   No collider by `isColliderAt_reverse_iff` combined with helper 1
--   on π. Analogous arrowhead analysis after applying the reverse
--   operation, with the impossible sub-case (rightArm = nil, hinge =
--   backward) contradicting `mem_marginalize_L`'s 3rd conjunct via
--   π.reverse being directed v → m.

/-- A `bidir` step in `G.marginalize {u}` lifts to a walk `σ` in `G` of
length ≥ 1 with interior in `{u}`, no collider at any position, and
where σ's first step has a source-arrowhead and σ's last step has a
target-arrowhead. This strengthens `bidir_step_to_walk_in_G`'s
conclusion with the structural witnesses needed for the boundary joint
condition in `lift_aux`. -/
private lemma bidir_step_to_walk_in_G_arrows {G : CDMG α} {u v m : α}
    (h_L : (v, m) ∈ (G.marginalize {u}).L)
    (hvu : v ≠ u) (hmu : m ≠ u) (huV : u ∈ G.V) :
    ∃ σ : Walk G v m,
      σ.InteriorIn {u} ∧ 1 ≤ σ.length ∧
      (∀ k, ¬ σ.IsColliderAt k) ∧
      (∃ (m₁ : α) (s_first : WalkStep G v m₁) (rest : Walk G m₁ m),
         σ = Walk.cons s_first rest ∧ s_first.HasArrowheadAtSource) ∧
      (∃ (m₂ : α) (pre : Walk G v m₂) (s_last : WalkStep G m₂ m),
         σ = pre.append (Walk.cons s_last (Walk.nil m)) ∧
           s_last.HasArrowheadAtTarget) := by
  -- Unfold `mem_marginalize_L` with type-ascription so Lean reduces `(v, m).1 = v`
  -- and `(v, m).2 = m` immediately, avoiding the Prod-literal headache downstream.
  rw [CDMG.mem_marginalize_L] at h_L
  have h_L' : v ∈ G.V \ {u} ∧ m ∈ G.V \ {u} ∧ v ≠ m ∧
      (¬ ∃ π : Walk G v m, π.IsDirected ∧ π.InteriorIn {u}) ∧
      (¬ ∃ π : Walk G m v, π.IsDirected ∧ π.InteriorIn {u}) ∧
      ((∃ π : Walk G v m, π.IsBifurcation ∧ π.InteriorIn {u}) ∨
       (∃ π : Walk G m v, π.IsBifurcation ∧ π.InteriorIn {u})) := h_L
  obtain ⟨_, _, _, h_no_dir_vm, h_no_dir_mv, h_bif⟩ := h_L'
  rcases h_bif with ⟨π, hπ_bif, hπ_int⟩ | ⟨π, hπ_bif, hπ_int⟩
  · -- Case (i): bifurcation v → m. Take σ := π.
    obtain ⟨⟨m_l, m_r, la, hi, ra, hpi_eq, hlb, his, hrd⟩⟩ := hπ_bif.2.2.2
    have hπ_pos : 1 ≤ π.length := π.length_pos_of_isBifurcation hπ_bif
    refine ⟨π, hπ_int, hπ_pos, not_isColliderAt_of_isBifurcation hπ_bif, ?_, ?_⟩
    · -- First step has source-arrowhead.
      cases la with
      | nil _ =>
        refine ⟨_, hi, ra, ?_, his⟩
        rw [hpi_eq, Walk.nil_append]
      | @cons _ w₂ _ s_l la_tail =>
        refine ⟨w₂, s_l, la_tail.append (Walk.cons hi ra), ?_, ?_⟩
        · rw [hpi_eq, Walk.cons_append]
        · cases s_l with
          | forward _ => simp at hlb
          | backward _ => simp
          | bidir _ => simp at hlb
    · -- Last step has target-arrowhead.
      cases ra with
      | @cons _ w₃ _ s_r ra_tail =>
        have hra_pos : 1 ≤ (Walk.cons s_r ra_tail).length := by simp [Walk.length_cons]
        obtain ⟨w_last, ra_pre, s_last, h_ra_eq⟩ :=
          Walk.walk_pos_eq_append_last (Walk.cons s_r ra_tail) hra_pos
        refine ⟨w_last, la.append (Walk.cons hi ra_pre), s_last, ?_, ?_⟩
        · rw [hpi_eq, h_ra_eq]
          rw [show (Walk.cons hi (ra_pre.append (Walk.cons s_last (Walk.nil m)))) =
            (Walk.cons hi ra_pre).append (Walk.cons s_last (Walk.nil m)) from
            by rw [Walk.cons_append]]
          rw [Walk.append_assoc]
        · rw [h_ra_eq] at hrd
          have hra_pre_dir := Walk.isDirected_split_append ra_pre _ hrd
          cases s_last with
          | forward _ => simp
          | backward _ => simp at hra_pre_dir
          | bidir _ => simp at hra_pre_dir
      | nil _ =>
        cases hi with
        | forward _ => simp at his
        | backward h_e =>
          -- π is all-backward; π.reverse directed m → v contradicts h_no_dir_mv.
          exfalso
          apply h_no_dir_mv
          refine ⟨π.reverse, ?_, (interiorIn_reverse_iff π {u}).mpr hπ_int⟩
          rw [hpi_eq, Walk.reverse_append, Walk.reverse_cons, Walk.reverse_nil,
              Walk.nil_append, WalkStep.reverse_backward,
              Walk.cons_append, Walk.nil_append, Walk.isDirected_cons_forward]
          exact Walk.marg_isDirected_reverse_of_isAllBackward hlb
        | bidir h_b =>
          refine ⟨_, la, WalkStep.bidir h_b, ?_, by simp⟩
          rw [hpi_eq]
  · -- Case (ii): bifurcation m → v, reversed. Take σ := π.reverse.
    obtain ⟨⟨m_l, m_r, la, hi, ra, hpi_eq, hlb, his, hrd⟩⟩ := hπ_bif.2.2.2
    have hπ_pos : 1 ≤ π.length := π.length_pos_of_isBifurcation hπ_bif
    refine ⟨π.reverse, (interiorIn_reverse_iff π {u}).mpr hπ_int, ?_, ?_, ?_, ?_⟩
    · rw [Walk.length_reverse]; exact hπ_pos
    · intro k h_coll
      rw [Walk.isColliderAt_reverse_iff] at h_coll
      exact not_isColliderAt_of_isBifurcation hπ_bif (π.length - k) h_coll
    · -- First step of π.reverse has source-arrowhead.
      cases ra with
      | @cons _ w₃ _ s_r ra_tail =>
        have hra_pos : 1 ≤ (Walk.cons s_r ra_tail).length := by simp [Walk.length_cons]
        obtain ⟨w_ra_last, ra_pre, s_ra_last, h_ra_eq⟩ :=
          Walk.walk_pos_eq_append_last (Walk.cons s_r ra_tail) hra_pos
        rw [h_ra_eq] at hrd
        have hra_pre_dir := Walk.isDirected_split_append ra_pre _ hrd
        cases s_ra_last with
        | forward h_e =>
          refine ⟨w_ra_last, WalkStep.backward h_e,
            (la.append (Walk.cons hi ra_pre)).reverse, ?_, by simp⟩
          rw [hpi_eq, h_ra_eq]
          rw [show (Walk.cons hi (ra_pre.append (Walk.cons (WalkStep.forward h_e) (Walk.nil v)))) =
            (Walk.cons hi ra_pre).append (Walk.cons (WalkStep.forward h_e) (Walk.nil v)) from
            by rw [Walk.cons_append]]
          rw [← Walk.append_assoc]
          rw [Walk.reverse_append, Walk.reverse_cons, Walk.reverse_nil, Walk.nil_append,
              WalkStep.reverse_forward, Walk.cons_append, Walk.nil_append]
        | backward _ => simp at hra_pre_dir
        | bidir _ => simp at hra_pre_dir
      | nil _ =>
        cases hi with
        | forward _ => simp at his
        | backward h_e =>
          exfalso
          apply h_no_dir_vm
          refine ⟨π.reverse, ?_, (interiorIn_reverse_iff π {u}).mpr hπ_int⟩
          rw [hpi_eq, Walk.reverse_append, Walk.reverse_cons, Walk.reverse_nil,
              Walk.nil_append, WalkStep.reverse_backward,
              Walk.cons_append, Walk.nil_append, Walk.isDirected_cons_forward]
          exact Walk.marg_isDirected_reverse_of_isAllBackward hlb
        | bidir h_b =>
          -- σ.first = (bidir h_b).reverse = bidir (G.L_symm h_b) : WalkStep G v m_l.
          refine ⟨_, WalkStep.bidir (G.L_symm h_b), la.reverse, ?_, by simp⟩
          rw [hpi_eq, Walk.reverse_append, Walk.reverse_cons, Walk.reverse_nil,
              Walk.nil_append, WalkStep.reverse_bidir,
              Walk.cons_append, Walk.nil_append]
    · -- Last step of π.reverse has target-arrowhead.
      cases la with
      | nil _ =>
        cases hi with
        | forward _ => simp at his
        | backward h_e =>
          refine ⟨_, ra.reverse, WalkStep.forward h_e, ?_, by simp⟩
          rw [hpi_eq, Walk.nil_append, Walk.reverse_cons, WalkStep.reverse_backward]
        | bidir h_b =>
          -- σ.last = (bidir h_b).reverse = bidir (G.L_symm h_b) : WalkStep G m_r m.
          refine ⟨_, ra.reverse, WalkStep.bidir (G.L_symm h_b), ?_, by simp⟩
          rw [hpi_eq, Walk.nil_append, Walk.reverse_cons, WalkStep.reverse_bidir]
      | @cons _ w₂ _ s_l la_tail =>
        cases s_l with
        | forward _ => simp at hlb
        | backward h_e =>
          refine ⟨w₂, (la_tail.append (Walk.cons hi ra)).reverse,
            WalkStep.forward h_e, ?_, by simp⟩
          rw [hpi_eq, Walk.cons_append, Walk.reverse_cons, WalkStep.reverse_backward]
        | bidir _ => simp at hlb

-- claim_3_25 helper (Sub-task 2c, SCC argument)
--
-- The LN's SCC argument for unblockable non-colliders (proof.tex
-- lines 94 -- 100): when an outgoing edge from `m` on `π'`
-- (which lives in `(G.marg {u}).Sc m`) lifts to a multi-step walk
-- through `u` in `G`, that lift gives `u ∈ G.Sc m`. Specifically,
-- a directed walk τ : Walk G m anchor of length ≥ 2 with interior
-- in `{u}` exposes `m → u` (forward first step) and `u → … → anchor`
-- (suffix), and combined with `anchor ∈ G.Anc m` (coming from
-- `anchor ∈ (G.marg {u}).Sc m \ {u} ⊆ G.Sc m`), produces a directed
-- walk `u → anchor → m` for `u ∈ G.Anc m`.
--
-- ## Design choice
--
-- * **`huV : u ∈ G.V` precondition.** Needed to put `u ∈ G` (so that
--   `u ∈ G.Anc m` and `u ∈ G.Desc m` are well-typed at the `mem_Anc`
--   / `mem_Desc` level), since `Anc`/`Desc` membership requires
--   `_ ∈ G`. Comes for free at the call site (`lift_aux` passes its
--   own `huV` through).
--
-- * **`anchor ∈ G.Anc m` precondition, not `anchor ∈ G.Sc m`.** We
--   only need ancestry of `anchor` in `G` (to derive `u → anchor → m`);
--   the descent side is irrelevant for the SCC conclusion. The call
--   site provides `anchor ∈ G.Sc m` (via `marginalize_Sc_iff` applied
--   to `(G.marg {u}).Sc m \ {u}`), and `Sc ⊆ Anc` lets the caller
--   project.

/-- LN's SCC argument (proof.tex lines 94--100): if a directed walk
`τ : Walk G m anchor` of length ≥ 2 passes through `u` (interior in
`{u}`) and `anchor ∈ G.Anc m`, then `u ∈ G.Sc m`. -/
private lemma u_in_Sc_via_directed_lift {G : CDMG α} {u m anchor : α}
    (τ : Walk G m anchor) (hτ_dir : τ.IsDirected) (hτ_pos : 2 ≤ τ.length)
    (hτ_int : τ.InteriorIn {u}) (huV : u ∈ G.V)
    (hAnchor : anchor ∈ G.Anc m) :
    u ∈ G.Sc m := by
  have hu_in_G : u ∈ G := by rw [CDMG.mem_iff]; exact Or.inr huV
  -- Decompose τ as cons. The intermediate vertex must equal u (via interior).
  have hτ_pos1 : 1 ≤ τ.length := by omega
  obtain ⟨m', τ_first, τ_tail, hτ_eq⟩ := Walk.walk_pos_eq_cons τ hτ_pos1
  have hτ_tail_pos : 1 ≤ τ_tail.length := by
    rw [hτ_eq, Walk.length_cons] at hτ_pos; omega
  -- m' is in τ_tail.support.dropLast (since τ_tail.support starts with m' and has length ≥ 2).
  have hm'_in_int : m' ∈ τ.support.tail.dropLast := by
    rw [hτ_eq, Walk.support_cons, List.tail_cons]
    -- Goal: m' ∈ τ_tail.support.dropLast.
    obtain ⟨m₂, s₂, p₂, h_tail_eq⟩ := Walk.walk_pos_eq_cons τ_tail hτ_tail_pos
    rw [h_tail_eq, Walk.support_cons]
    -- (m' :: p₂.support).dropLast = m' :: p₂.support.dropLast (since p₂.support ≠ []).
    have h_p₂_supp_ne : p₂.support ≠ [] := by
      intro h
      have := Walk.support_length p₂
      rw [h] at this
      simp at this
    rw [List.dropLast_cons_of_ne_nil h_p₂_supp_ne]
    exact List.mem_cons_self
  have hm'_in_u : m' ∈ ({u} : Set α) := hτ_int _ hm'_in_int
  have hm'_eq : m' = u := Set.mem_singleton_iff.mp hm'_in_u
  -- Substitute m' = u (force m' direction since m' is the bound variable from obtain).
  subst m'
  have hτ_dir' : (Walk.cons τ_first τ_tail).IsDirected := hτ_eq ▸ hτ_dir
  cases τ_first with
  | forward h_E =>
    rw [Walk.isDirected_cons_forward] at hτ_dir'
    refine ⟨?_, ?_⟩
    · -- u ∈ Anc m via u → anchor (τ_tail) + anchor → m.
      exact CDMG.anc_trans ⟨hu_in_G, τ_tail, hτ_dir'⟩ hAnchor
    · -- u ∈ Desc m via the single-step walk m → u.
      refine ⟨hu_in_G, Walk.cons (WalkStep.forward h_E) (Walk.nil u), ?_⟩
      simp
  | backward _ => simp at hτ_dir'
  | bidir _ => simp at hτ_dir'

-- claim_3_25 helper (Sub-task 2e, support-position-membership of interior nodeAt)
--
-- For a walk `π` and an interior position `0 < k < π.length`, the vertex
-- `π.nodeAt k` is one of the strict-interior vertices on `π.support.tail.dropLast`.
-- Combined with `π.InteriorIn W`, this gives `π.nodeAt k ∈ W` for interior `k`.
-- Proof is by induction on `π` with a sub-case on the "next-to-first" position.
/-- The vertex at an interior position of a walk lies in
`π.support.tail.dropLast` (the strict interior of the support list). -/
private theorem nodeAt_mem_interior_support {G : CDMG α} :
    ∀ {a b : α} (π : Walk G a b) {k : ℕ}, 0 < k → k < π.length →
      π.nodeAt k ∈ π.support.tail.dropLast := by
  intro a b π
  induction π with
  | nil _ =>
    intro k _ h
    simp [Walk.length_nil] at h
  | @cons a' m b' s p ih =>
    intro k hk_pos hk_lt
    rw [Walk.length_cons] at hk_lt
    rw [Walk.support_cons, List.tail_cons]
    cases k with
    | zero => omega
    | succ k' =>
      rw [Walk.nodeAt_cons_succ]
      -- Goal: `p.nodeAt k' ∈ p.support.dropLast`.
      have hk'_lt : k' < p.length := by omega
      have hp_pos : 1 ≤ p.length := by omega
      obtain ⟨m₂, s', p'', hp_eq⟩ := Walk.walk_pos_eq_cons p hp_pos
      have h_p''_supp_ne : p''.support ≠ [] := by
        intro h
        have := Walk.support_length p''
        rw [h] at this; simp at this
      cases k' with
      | zero =>
        -- `p.nodeAt 0 = m`, and `m ∈ p.support.dropLast` since `p.support = m :: ...`.
        rw [Walk.nodeAt_zero, hp_eq, Walk.support_cons,
            List.dropLast_cons_of_ne_nil h_p''_supp_ne]
        exact List.mem_cons_self
      | succ k'' =>
        -- Apply IH on `p` at position `k'' + 1` (interior of `p`), then promote
        -- `p.support.tail.dropLast` membership to `p.support.dropLast` membership
        -- via the inclusion `p.support.tail.dropLast ⊆ p.support.dropLast`.
        have h_ih := ih (k := k'' + 1) (Nat.succ_pos _) (by omega)
        have h_tail_drop_sub : p.support.tail.dropLast ⊆ p.support.dropLast := by
          rw [hp_eq, Walk.support_cons, List.tail_cons,
              List.dropLast_cons_of_ne_nil h_p''_supp_ne]
          intro x hx
          exact List.mem_cons.mpr (Or.inr hx)
        exact h_tail_drop_sub h_ih

/-- Strengthened version of `lift_aux` with two additional conjuncts:
    `C5`: length preservation — if `π'` is trivial (length 0), so is `ρ`;
    `C4-strong`: the iff invariant on the outer-cons-decomposition is
    extended with `sρ.IsForward → mρ ∈ G.Anc mπ`. Both extra conjuncts
    are required for the boundary unblockable verification in the
    recursive cons-case (see Sub-task 2d escalation at workspace
    lines 1209 -- 1457 for the precise gap).

    `lift_aux` (immediately below) is derived from this in 7 lines. -/
private lemma lift_aux_strong {G : CDMG α} {u : α} (huV : u ∈ G.V)
    {C : Set α} (huC : u ∉ C) :
    ∀ {a b : α} (π' : Walk (G.marginalize {u}) a b),
      a ≠ u → b ≠ u →
      (∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ (G.marginalize {u}).AncSet C) →
      (∀ k, 0 < k → π'.IsBlockableNonColliderAt k → π'.nodeAt k ∉ C) →
      (∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ C) →
    ∃ ρ : Walk G a b,
      (∀ k, ρ.IsColliderAt k → ρ.nodeAt k ∈ G.AncSet C) ∧
      (∀ k, 0 < k → ρ.IsBlockableNonColliderAt k → ρ.nodeAt k ∉ C) ∧
      (∀ k, ρ.IsColliderAt k → ρ.nodeAt k ∈ C) ∧
      (π'.length = 0 → ρ.length = 0) ∧
      (∀ {mπ : α} (sπ : WalkStep (G.marginalize {u}) a mπ)
         (pπ : Walk (G.marginalize {u}) mπ b),
         π' = Walk.cons sπ pπ →
         ∃ (mρ : α) (sρ : WalkStep G a mρ) (pρ : Walk G mρ b),
           ρ = Walk.cons sρ pρ ∧
           (sρ.HasArrowheadAtSource ↔ sπ.HasArrowheadAtSource) ∧
           (sρ.IsForward → mρ ∈ G.Anc mπ)) := by
  intro a b π'
  induction π' with
  | nil v =>
    -- Nil case: ρ := nil v. All conjuncts trivial.
    intro _ _ _ _ _
    refine ⟨Walk.nil v, ?_, ?_, ?_, ?_, ?_⟩
    · intro k h; simp at h
    · intro k hk h
      -- (nil v).IsBlockableNonColliderAt requires k ≤ 0, contradicting hk.
      have : k ≤ (Walk.nil v : Walk G v v).length := h.1.1
      simp at this; omega
    · intro k h; simp at h
    · intro _; simp
    · intro mπ sπ pπ h_eq; cases h_eq
  | @cons aπ mπ bπ stepπ p' ih =>
    intro ha hb h1 h2 h3
    cases stepπ with
    | forward h_E =>
      -- Extract σ : Walk G aπ mπ via mem_marginalize_E.
      have h_E_unf : (aπ, mπ) ∈ (G.marginalize {u}).E := h_E
      rw [CDMG.mem_marginalize_E] at h_E_unf
      obtain ⟨_, h_mπ_VnotU, σ, hσ_dir, hσ_int, hσ_pos⟩ := h_E_unf
      have hmπ_ne_u : mπ ≠ u := h_mπ_VnotU.2
      have hmπ_V : mπ ∈ G.V := h_mπ_VnotU.1
      have hmπ_in_G : mπ ∈ G := CDMG.mem_iff.mpr (Or.inr hmπ_V)
      -- Decompose σ as cons σ_first σ_rest.
      obtain ⟨mσ, σ_first, σ_rest, hσ_eq⟩ := Walk.walk_pos_eq_cons σ hσ_pos
      have hσ_dir' : (Walk.cons σ_first σ_rest).IsDirected := hσ_eq ▸ hσ_dir
      have ⟨h_e_first, h_σ_first_eq⟩ :
          ∃ h : aπ ⟶[G] mσ, σ_first = WalkStep.forward h := by
        cases σ_first with
        | forward h => exact ⟨h, rfl⟩
        | backward _ => simp at hσ_dir'
        | bidir _ => simp at hσ_dir'
      have hσ_rest_dir : σ_rest.IsDirected := by
        rw [h_σ_first_eq] at hσ_dir'; simpa using hσ_dir'
      have hmσ_in_V : mσ ∈ G.V := (G.E_subset h_e_first).2
      have hmσ_in_G : mσ ∈ G := CDMG.mem_iff.mpr (Or.inr hmσ_in_V)
      have hmσ_anc_mπ : mσ ∈ G.Anc mπ := ⟨hmσ_in_G, σ_rest, hσ_rest_dir⟩
      cases p' with
      | nil _ =>
        -- p' = nil mπ, bπ = mπ. Build ρ := σ.
        refine ⟨σ, ?_, ?_, ?_, ?_, ?_⟩
        · -- C1: σ directed has no collider.
          intro k h_coll
          exact absurd h_coll (Walk.not_isColliderAt_of_isDirected σ k hσ_dir)
        · -- C2: blockable non-colliders not in C.
          intro k hk h_blk
          by_cases hk_lt : k < σ.length
          · have h_in_int : σ.nodeAt k ∈ σ.support.tail.dropLast :=
              nodeAt_mem_interior_support σ hk hk_lt
            have h_node_u : σ.nodeAt k = u :=
              Set.mem_singleton_iff.mp (hσ_int (σ.nodeAt k) h_in_int)
            rw [h_node_u]; exact huC
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · subst hk_eq
              rw [Walk.nodeAt_length]
              -- π' has length 1, position 1 is endpoint, blockable.
              have h_pi_len :
                  (Walk.cons (WalkStep.forward h_E) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).length = 1 := by
                simp [Walk.length_cons]
              have h_pi_blk :
                  (Walk.cons (WalkStep.forward h_E) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).IsBlockableNonColliderAt 1 := by
                rw [show (1 : ℕ) =
                  (Walk.cons (WalkStep.forward h_E) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).length from h_pi_len.symm]
                exact Walk.isBlockableNonColliderAt_length _
              have h_pi_node :
                  (Walk.cons (WalkStep.forward h_E) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).nodeAt 1 = mπ := by
                simp
              have h_res := h2 1 Nat.one_pos h_pi_blk
              rw [h_pi_node] at h_res
              exact h_res
            · exfalso
              have := h_blk.1.1
              omega
        · -- C3: σ directed has no collider.
          intro k h_coll
          exact absurd h_coll (Walk.not_isColliderAt_of_isDirected σ k hσ_dir)
        · -- C5: π'.length = 1 ≠ 0.
          intro h_len
          simp [Walk.length_cons, Walk.length_nil] at h_len
        · -- C4-strong.
          intro mπ_out sπ_out pπ_out h_eq
          refine ⟨mσ, σ_first, σ_rest, hσ_eq, ?_, ?_⟩
          · -- iff.
            cases h_eq
            rw [h_σ_first_eq]
            simp
          · -- IsForward → mσ ∈ G.Anc mπ_out.
            cases h_eq
            intro _
            exact hmσ_anc_mπ
      | @cons _ mπ_p _ s' p'' =>
        -- p' = cons s' p''. Apply IH on p' to get ρ_p'.
        -- Step 1: Derive mπ_p ≠ u.
        have hmπ_p_ne_u : mπ_p ≠ u := by
          cases s' with
          | forward h_E' =>
            have h_unf : (mπ, mπ_p) ∈ (G.marginalize {u}).E := h_E'
            rw [CDMG.mem_marginalize_E] at h_unf
            exact h_unf.2.1.2
          | backward h_E' =>
            have h_unf : (mπ_p, mπ) ∈ (G.marginalize {u}).E := h_E'
            rw [CDMG.mem_marginalize_E] at h_unf
            rcases h_unf.1 with hJ | hV
            · intro h_eq; subst h_eq
              exact (Set.disjoint_left.mp G.disjoint_JV) hJ huV
            · exact hV.2
          | bidir h_L' =>
            have h_unf : (mπ, mπ_p) ∈ (G.marginalize {u}).L := h_L'
            rw [CDMG.mem_marginalize_L] at h_unf
            exact h_unf.2.1.2
        -- Step 2: Derive p'-shifted σ-open clauses.
        have hp'_1 : ∀ k, (Walk.cons s' p'').IsColliderAt k →
            (Walk.cons s' p'').nodeAt k ∈ (G.marginalize {u}).AncSet C := by
          intro k h_coll
          cases k with
          | zero =>
            cases p'' with
            | nil _ => exact absurd h_coll (by simp)
            | @cons _ _ _ _ _ => exact absurd h_coll (by simp)
          | succ k' =>
            have h_π_coll :
                (Walk.cons (WalkStep.forward h_E) (Walk.cons s' p'')).IsColliderAt (k'+2) := by
              rw [Walk.isColliderAt_cons_cons_succ_succ]; exact h_coll
            have h_res := h1 (k'+2) h_π_coll
            simp only [Walk.nodeAt_cons_succ] at h_res
            exact h_res
        have hp'_2 : ∀ k, 0 < k → (Walk.cons s' p'').IsBlockableNonColliderAt k →
            (Walk.cons s' p'').nodeAt k ∉ C := by
          intro k hk h_blk
          cases k with
          | zero => omega
          | succ k' =>
            have h_π_blk :
                (Walk.cons (WalkStep.forward h_E) (Walk.cons s' p'')).IsBlockableNonColliderAt (k'+2) := by
              have h_blk_unf := h_blk
              rw [Walk.isBlockableNonColliderAt_iff, Walk.isNonColliderAt_iff] at h_blk_unf
              obtain ⟨⟨h_le, h_nc⟩, h_nu⟩ := h_blk_unf
              rw [Walk.isBlockableNonColliderAt_iff, Walk.isNonColliderAt_iff]
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · rw [Walk.length_cons]; omega
              · rw [Walk.isColliderAt_cons_cons_succ_succ]; exact h_nc
              · rw [Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]; exact h_nu
            have h_res := h2 (k'+2) (by omega) h_π_blk
            simp only [Walk.nodeAt_cons_succ] at h_res
            exact h_res
        have hp'_3 : ∀ k, (Walk.cons s' p'').IsColliderAt k →
            (Walk.cons s' p'').nodeAt k ∈ C := by
          intro k h_coll
          cases k with
          | zero =>
            cases p'' with
            | nil _ => exact absurd h_coll (by simp)
            | @cons _ _ _ _ _ => exact absurd h_coll (by simp)
          | succ k' =>
            have h_π_coll :
                (Walk.cons (WalkStep.forward h_E) (Walk.cons s' p'')).IsColliderAt (k'+2) := by
              rw [Walk.isColliderAt_cons_cons_succ_succ]; exact h_coll
            have h_res := h3 (k'+2) h_π_coll
            simp only [Walk.nodeAt_cons_succ] at h_res
            exact h_res
        -- Step 3: Apply IH on p'.
        obtain ⟨ρ_p', hρ_p'_c1, hρ_p'_c2, hρ_p'_c3, _hρ_p'_len, hρ_p'_c4⟩ :=
          ih hmπ_ne_u hb hp'_1 hp'_2 hp'_3
        -- Step 4: Extract ρ_p' = cons sρ' pρ' via C4-strong of IH.
        obtain ⟨mρ', sρ', pρ', hρ_p'_eq, hρ_p'_arrow, hρ_p'_anc⟩ :=
          hρ_p'_c4 s' p'' rfl
        -- Step 5: Decompose σ as σ_pre.append (cons σ_last (nil mπ)) for boundary analysis.
        obtain ⟨mσ_pre, σ_pre, σ_last, hσ_eq_last⟩ :=
          Walk.walk_pos_eq_append_last σ hσ_pos
        -- σ_last is forward (from σ.IsDirected).
        have hσ_last_dir : σ.IsDirected := hσ_dir
        rw [hσ_eq_last] at hσ_last_dir
        have hσ_pre_dir : σ_pre.IsDirected :=
          (Walk.isDirected_split_append _ _ hσ_last_dir).1
        have hσ_last_step_dir : (Walk.cons σ_last (Walk.nil mπ)).IsDirected :=
          (Walk.isDirected_split_append _ _ hσ_last_dir).2
        have ⟨h_e_last, h_σ_last_eq⟩ :
            ∃ h : mσ_pre ⟶[G] mπ, σ_last = WalkStep.forward h := by
          cases σ_last with
          | forward h => exact ⟨h, rfl⟩
          | backward _ => simp at hσ_last_step_dir
          | bidir _ => simp at hσ_last_step_dir
        have hσ_last_arrow_tgt : σ_last.HasArrowheadAtTarget := by
          rw [h_σ_last_eq]; simp
        -- σ_pre.length = σ.length - 1.
        have hσ_pre_len : σ_pre.length + 1 = σ.length := by
          rw [hσ_eq_last, Walk.length_append, Walk.length_cons, Walk.length_nil]
        -- ρ = σ.append ρ_p'.
        -- After Step 4, ρ_p' = cons sρ' pρ'. So ρ = σ.append (cons sρ' pρ').
        -- For boundary analysis, ρ rewrites as σ_pre.append (cons σ_last (cons sρ' pρ')).
        have h_ρ_eq : σ.append ρ_p' =
            σ_pre.append (Walk.cons σ_last (Walk.cons sρ' pρ')) := by
          rw [hρ_p'_eq, hσ_eq_last]
          rw [Walk.append_assoc]
          rw [show (Walk.cons σ_last (Walk.nil mπ)).append (Walk.cons sρ' pρ') =
            Walk.cons σ_last (Walk.cons sρ' pρ') from by
            rw [Walk.cons_append, Walk.nil_append]]
        -- Step 6: Build ρ := σ.append ρ_p' and verify the five conjuncts.
        refine ⟨σ.append ρ_p', ?_, ?_, ?_, ?_, ?_⟩
        · -- C1: ρ.IsColliderAt k → ρ.nodeAt k ∈ G.AncSet C.
          intro k h_coll
          by_cases hk_lt : k < σ.length
          · -- Inside σ: σ.IsDirected so no collider.
            rw [Walk.isColliderAt_append_lt_length _ _ hk_lt] at h_coll
            exact absurd h_coll (Walk.not_isColliderAt_of_isDirected σ k hσ_dir)
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · -- Boundary k = σ.length.
              subst hk_eq
              -- ρ.nodeAt σ.length = σ.nodeAt σ.length = mπ via nodeAt_append_le.
              have h_node_eq : (σ.append ρ_p').nodeAt σ.length = mπ := by
                rw [Walk.nodeAt_append_le _ _ (le_refl _), Walk.nodeAt_length]
              rw [h_node_eq]
              -- Show: mπ ∈ G.AncSet C. Use h1 1 + non-collider analysis.
              -- ρ collider at σ.length: rewrite ρ via h_ρ_eq.
              rw [h_ρ_eq] at h_coll
              rw [show σ.length = σ_pre.length + 1 from hσ_pre_len.symm] at h_coll
              rw [Walk.isColliderAt_append_cons_cons_one] at h_coll
              obtain ⟨_, hsρ'_arrow⟩ := h_coll
              -- sρ'.HasArrowheadAtSource = True → s'.HasArrowheadAtSource = True (via iff).
              have hs'_arrow : s'.HasArrowheadAtSource := hρ_p'_arrow.mp hsρ'_arrow
              -- π'.IsColliderAt 1 holds.
              have h_π_coll : (Walk.cons (WalkStep.forward h_E)
                  (Walk.cons s' p'')).IsColliderAt 1 := by
                rw [Walk.isColliderAt_cons_cons_one]
                exact ⟨by simp, hs'_arrow⟩
              have h_res := h1 1 h_π_coll
              -- π'.nodeAt 1 = (cons s' p'').nodeAt 0 = mπ.
              simp only [Walk.nodeAt_cons_succ, Walk.nodeAt_cons_zero] at h_res
              -- Now lift via marginalize_AncSet_subset.
              exact marginalize_AncSet_subset G {u} C h_res
            · -- k > σ.length: shift to ρ_p'.
              have h_gt : σ.length < k := lt_of_le_of_ne hk_lt (Ne.symm hk_eq)
              have h_eq_k : k = σ.length + (k - σ.length) := by omega
              rw [h_eq_k] at h_coll
              rw [Walk.isColliderAt_append_shift_pos _ _ _ (by omega : 0 < k - σ.length)] at h_coll
              have h_res := hρ_p'_c1 (k - σ.length) h_coll
              rw [h_eq_k, Walk.nodeAt_append_add_left]
              exact h_res
        · -- C2: blockable non-colliders not in C.
          intro k hk h_blk
          by_cases hk_lt : k < σ.length
          · -- Inside σ. nodeAt = u (interior) so ∉ C.
            have h_node_eq : (σ.append ρ_p').nodeAt k = σ.nodeAt k := by
              rw [Walk.nodeAt_append_le _ _ (le_of_lt hk_lt)]
            rw [h_node_eq]
            have h_in_int : σ.nodeAt k ∈ σ.support.tail.dropLast :=
              nodeAt_mem_interior_support σ hk hk_lt
            have h_node_u : σ.nodeAt k = u :=
              Set.mem_singleton_iff.mp (hσ_int (σ.nodeAt k) h_in_int)
            rw [h_node_u]; exact huC
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · -- Boundary k = σ.length.
              subst hk_eq
              have h_node_eq : (σ.append ρ_p').nodeAt σ.length = mπ := by
                rw [Walk.nodeAt_append_le _ _ (le_refl _), Walk.nodeAt_length]
              rw [h_node_eq]
              -- Derive: sρ' = forward (from non-collider).
              -- Show: ρ blockable → π' blockable at 1 (via SCC contradiction if needed).
              have h_blk' := h_blk
              rw [h_ρ_eq] at h_blk'
              rw [show σ.length = σ_pre.length + 1 from hσ_pre_len.symm] at h_blk'
              -- ρ.IsBlockableNonColliderAt = non-collider ∧ NOT unblockable.
              obtain ⟨h_nc, h_nb⟩ := h_blk'
              -- Non-collider at σ_pre.length + 1: NOT (σ_last arrow ∧ sρ' arrow).
              rw [Walk.isNonColliderAt_iff] at h_nc
              rw [Walk.isColliderAt_append_cons_cons_one] at h_nc
              have h_not_coll : ¬ (σ_last.HasArrowheadAtTarget ∧ sρ'.HasArrowheadAtSource) :=
                h_nc.2
              -- σ_last.HasArrowheadAtTarget = True. So sρ'.HasArrowheadAtSource = False.
              have hsρ'_not_arrow : ¬ sρ'.HasArrowheadAtSource := fun h =>
                h_not_coll ⟨hσ_last_arrow_tgt, h⟩
              -- sρ' is forward (since HasArrowheadAtSource = False).
              have ⟨h_e_sρ', h_sρ'_eq⟩ :
                  ∃ h : mπ ⟶[G] mρ', sρ' = WalkStep.forward h := by
                cases sρ' with
                | forward h => exact ⟨h, rfl⟩
                | backward _ => exact absurd (by simp : (WalkStep.backward _).HasArrowheadAtSource) hsρ'_not_arrow
                | bidir _ => exact absurd (by simp : (WalkStep.bidir _).HasArrowheadAtSource) hsρ'_not_arrow
              -- s' is forward (via iff).
              have hs'_not_arrow : ¬ s'.HasArrowheadAtSource :=
                fun h => hsρ'_not_arrow (hρ_p'_arrow.mpr h)
              have ⟨h_e_s', h_s'_eq⟩ :
                  ∃ h : mπ ⟶[G.marginalize {u}] mπ_p, s' = WalkStep.forward h := by
                cases s' with
                | forward h => exact ⟨h, rfl⟩
                | backward _ => exact absurd (by simp : (WalkStep.backward _).HasArrowheadAtSource) hs'_not_arrow
                | bidir _ => exact absurd (by simp : (WalkStep.bidir _).HasArrowheadAtSource) hs'_not_arrow
              -- NOT unblockable.
              rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_nb
              -- h_nb : ¬ σ_last.IsUnblockableJoint sρ'.
              -- IsUnblockableJoint = (¬ coll) ∧ (σ_last.IsBackward → ...) ∧ (sρ'.IsForward → mρ' ∈ G.Sc mπ).
              -- σ_last forward (h_σ_last_eq) → σ_last.IsBackward = False, second clause vacuous.
              -- sρ' forward (h_sρ'_eq) → sρ'.IsForward = True, third clause: mρ' ∈ G.Sc mπ.
              -- So unblockable iff (¬ coll) ∧ mρ' ∈ G.Sc mπ.
              -- Not unblockable: mρ' ∉ G.Sc mπ (since non-collider holds, NOT (and-of-three) reduces to NOT third).
              have h_mρ'_not_in_Sc : mρ' ∉ G.Sc mπ := by
                intro h_in
                apply h_nb
                refine ⟨?_, ?_, ?_⟩
                · -- ¬ collider
                  rw [h_σ_last_eq, h_sρ'_eq]; simp
                · -- σ_last.IsBackward = False → vacuous
                  rw [h_σ_last_eq]; simp
                · -- sρ'.IsForward → mρ' ∈ G.Sc mπ
                  intro _; exact h_in
              -- Show: π' blockable at 1 → mπ ∉ C.
              have h_π_blk : (Walk.cons (WalkStep.forward h_E)
                  (Walk.cons s' p'')).IsBlockableNonColliderAt 1 := by
                rw [Walk.isBlockableNonColliderAt_iff, Walk.isNonColliderAt_iff,
                    Walk.length_cons, Walk.isColliderAt_cons_cons_one,
                    Walk.isUnblockableNonColliderAt_cons_cons_one]
                refine ⟨⟨by omega, ?_⟩, ?_⟩
                · -- ¬ ((forward h_E).HasArrowheadAtTarget ∧ s'.HasArrowheadAtSource)
                  intro ⟨_, h⟩; exact hs'_not_arrow h
                · -- ¬ IsUnblockableJoint (forward h_E) s'.
                  intro h_unb
                  obtain ⟨_, _, h_forward_clause⟩ := h_unb
                  -- s'.IsForward = True (from h_s'_eq), so h_forward_clause : mπ_p ∈ (G.marg {u}).Sc mπ.
                  have hs'_fwd : s'.IsForward := by rw [h_s'_eq]; simp
                  have h_mπ_p_in_marg_Sc : mπ_p ∈ (G.marginalize {u}).Sc mπ := h_forward_clause hs'_fwd
                  -- Use marginalize_Sc_iff to convert.
                  have hmπ_not_in_u : mπ ∉ ({u} : Set α) := by
                    rw [Set.mem_singleton_iff]; exact hmπ_ne_u
                  rw [CDMG.marginalize_Sc_iff G {u} hmπ_not_in_u] at h_mπ_p_in_marg_Sc
                  -- h_mπ_p_in_marg_Sc : mπ_p ∈ G.Sc mπ \ {u}.
                  have hmπ_p_in_Sc : mπ_p ∈ G.Sc mπ := h_mπ_p_in_marg_Sc.1
                  have hmπ_p_in_Anc : mπ_p ∈ G.Anc mπ := hmπ_p_in_Sc.1
                  -- mρ' ∈ G.Anc mπ_p (from C4-strong of IH).
                  have hsρ'_fwd : sρ'.IsForward := by rw [h_sρ'_eq]; simp
                  have hmρ'_in_Anc : mρ' ∈ G.Anc mπ_p := hρ_p'_anc hsρ'_fwd
                  -- anc_trans: mρ' ∈ G.Anc mπ.
                  have hmρ'_in_Anc_mπ : mρ' ∈ G.Anc mπ :=
                    CDMG.anc_trans hmρ'_in_Anc hmπ_p_in_Anc
                  -- mρ' ∈ G.Desc mπ via single-edge mπ → mρ'.
                  have hmρ'_in_V : mρ' ∈ G.V := (G.E_subset h_e_sρ').2
                  have hmρ'_in_G : mρ' ∈ G := CDMG.mem_iff.mpr (Or.inr hmρ'_in_V)
                  have hmρ'_in_Desc : mρ' ∈ G.Desc mπ := by
                    rw [CDMG.mem_Desc]
                    refine ⟨hmρ'_in_G,
                      Walk.cons (WalkStep.forward h_e_sρ') (Walk.nil mρ'), ?_⟩
                    simp
                  -- mρ' ∈ G.Sc mπ.
                  have hmρ'_in_Sc : mρ' ∈ G.Sc mπ :=
                    ⟨hmρ'_in_Anc_mπ, hmρ'_in_Desc⟩
                  exact h_mρ'_not_in_Sc hmρ'_in_Sc
              have h_res := h2 1 Nat.one_pos h_π_blk
              simp only [Walk.nodeAt_cons_succ, Walk.nodeAt_cons_zero] at h_res
              exact h_res
            · -- k > σ.length: shift to ρ_p'.
              have h_gt : σ.length < k := lt_of_le_of_ne hk_lt (Ne.symm hk_eq)
              have h_eq_k : k = σ.length + (k - σ.length) := by omega
              rw [h_eq_k] at h_blk
              rw [isBlockableNonColliderAt_append_shift_pos σ ρ_p' (k - σ.length)
                  (by omega : 0 < k - σ.length)] at h_blk
              have h_res := hρ_p'_c2 (k - σ.length) (by omega) h_blk
              rw [h_eq_k, Walk.nodeAt_append_add_left]
              exact h_res
        · -- C3: ρ.IsColliderAt k → ρ.nodeAt k ∈ C.
          intro k h_coll
          by_cases hk_lt : k < σ.length
          · rw [Walk.isColliderAt_append_lt_length _ _ hk_lt] at h_coll
            exact absurd h_coll (Walk.not_isColliderAt_of_isDirected σ k hσ_dir)
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · subst hk_eq
              have h_node_eq : (σ.append ρ_p').nodeAt σ.length = mπ := by
                rw [Walk.nodeAt_append_le _ _ (le_refl _), Walk.nodeAt_length]
              rw [h_node_eq]
              -- Same as C1 boundary, but use h3 instead of h1.
              rw [h_ρ_eq] at h_coll
              rw [show σ.length = σ_pre.length + 1 from hσ_pre_len.symm] at h_coll
              rw [Walk.isColliderAt_append_cons_cons_one] at h_coll
              obtain ⟨_, hsρ'_arrow⟩ := h_coll
              have hs'_arrow : s'.HasArrowheadAtSource := hρ_p'_arrow.mp hsρ'_arrow
              have h_π_coll : (Walk.cons (WalkStep.forward h_E)
                  (Walk.cons s' p'')).IsColliderAt 1 := by
                rw [Walk.isColliderAt_cons_cons_one]
                exact ⟨by simp, hs'_arrow⟩
              have h_res := h3 1 h_π_coll
              simp only [Walk.nodeAt_cons_succ, Walk.nodeAt_cons_zero] at h_res
              exact h_res
            · have h_gt : σ.length < k := lt_of_le_of_ne hk_lt (Ne.symm hk_eq)
              have h_eq_k : k = σ.length + (k - σ.length) := by omega
              rw [h_eq_k] at h_coll
              rw [Walk.isColliderAt_append_shift_pos _ _ _ (by omega : 0 < k - σ.length)] at h_coll
              have h_res := hρ_p'_c3 (k - σ.length) h_coll
              rw [h_eq_k, Walk.nodeAt_append_add_left]
              exact h_res
        · -- C5: π'.length ≥ 1, vacuous.
          intro h_len
          simp [Walk.length_cons] at h_len
        · -- C4-strong: decompose σ.append ρ_p' as cons.
          intro mπ_out sπ_out pπ_out h_eq
          refine ⟨mσ, σ_first, σ_rest.append ρ_p', ?_, ?_, ?_⟩
          · -- ρ = σ.append ρ_p' = cons σ_first (σ_rest.append ρ_p').
            rw [hσ_eq, Walk.cons_append]
          · cases h_eq
            rw [h_σ_first_eq]; simp
          · cases h_eq
            intro _; exact hmσ_anc_mπ
    | backward h_E =>
      -- Backward outer case. Extract a directed walk π_orig : Walk G mπ aπ
      -- via mem_marginalize_E on the backward step's reversed pair.
      have h_E_unf : (mπ, aπ) ∈ (G.marginalize {u}).E := h_E
      rw [CDMG.mem_marginalize_E] at h_E_unf
      obtain ⟨h_mπ_mem, h_aπ_VnotU, π_orig, hπ_orig_dir, hπ_orig_int, hπ_orig_pos⟩ :=
        h_E_unf
      -- Derive mπ ≠ u.
      have hmπ_ne_u : mπ ≠ u := by
        rcases h_mπ_mem with hJ | hV
        · intro heq; subst heq
          exact (Set.disjoint_left.mp G.disjoint_JV) hJ huV
        · exact hV.2
      -- Build σ := π_orig.reverse : Walk G aπ mπ explicitly.
      obtain ⟨σ, hσ_def⟩ : ∃ σ : Walk G aπ mπ, σ = π_orig.reverse :=
        ⟨π_orig.reverse, rfl⟩
      have hσ_back : σ.IsAllBackward := by
        rw [hσ_def]; exact isAllBackward_reverse_of_isDirected_local hπ_orig_dir
      have hσ_pos : 1 ≤ σ.length := by
        rw [hσ_def, Walk.length_reverse]; exact hπ_orig_pos
      have hσ_int : σ.InteriorIn {u} := by
        rw [hσ_def]; exact (interiorIn_reverse_iff π_orig {u}).mpr hπ_orig_int
      -- σ.reverse = π_orig (via reverse_reverse).
      have hσ_rev_eq : σ.reverse = π_orig := by
        rw [hσ_def, Walk.reverse_reverse]
      have hσ_rev_dir : σ.reverse.IsDirected := by
        rw [hσ_rev_eq]; exact hπ_orig_dir
      -- σ has no collider at any position.
      have hσ_no_coll : ∀ k, ¬ σ.IsColliderAt k := by
        intro k hcoll
        have hk_lt : k < σ.length := Walk.isColliderAt_lt_length _ hcoll
        have h_in_rev : σ.reverse.IsColliderAt (σ.length - k) := by
          rw [Walk.isColliderAt_reverse_iff]
          rw [show σ.length - (σ.length - k) = k from by omega]
          exact hcoll
        exact Walk.not_isColliderAt_of_isDirected σ.reverse (σ.length - k)
          hσ_rev_dir h_in_rev
      -- Decompose σ as cons σ_first σ_rest. σ_first is backward.
      obtain ⟨mσ, σ_first, σ_rest, hσ_eq⟩ := Walk.walk_pos_eq_cons σ hσ_pos
      have hσ_back' : (Walk.cons σ_first σ_rest).IsAllBackward := hσ_eq ▸ hσ_back
      have ⟨h_e_first, h_σ_first_eq⟩ :
          ∃ h : aπ ⟵[G] mσ, σ_first = WalkStep.backward h := by
        cases σ_first with
        | forward _ => simp at hσ_back'
        | backward h => exact ⟨h, rfl⟩
        | bidir _ => simp at hσ_back'
      cases p' with
      | nil _ =>
        -- p' = nil mπ, bπ = mπ. Build ρ := σ.
        refine ⟨σ, ?_, ?_, ?_, ?_, ?_⟩
        · intro k h_coll
          exact absurd h_coll (hσ_no_coll k)
        · -- C2: blockable non-collider → ∉ C.
          intro k hk h_blk
          by_cases hk_lt : k < σ.length
          · have h_in_int : σ.nodeAt k ∈ σ.support.tail.dropLast :=
              nodeAt_mem_interior_support σ hk hk_lt
            have h_node_u : σ.nodeAt k = u :=
              Set.mem_singleton_iff.mp (hσ_int (σ.nodeAt k) h_in_int)
            rw [h_node_u]; exact huC
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · subst hk_eq
              rw [Walk.nodeAt_length]
              -- π' has length 1 (cons (backward h_E) (nil mπ)), endpoint.
              have h_pi_len :
                  (Walk.cons (WalkStep.backward h_E) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).length = 1 := by
                simp [Walk.length_cons]
              have h_pi_blk :
                  (Walk.cons (WalkStep.backward h_E) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).IsBlockableNonColliderAt 1 := by
                rw [show (1 : ℕ) =
                  (Walk.cons (WalkStep.backward h_E) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).length from h_pi_len.symm]
                exact Walk.isBlockableNonColliderAt_length _
              have h_pi_node :
                  (Walk.cons (WalkStep.backward h_E) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).nodeAt 1 = mπ := by simp
              have h_res := h2 1 Nat.one_pos h_pi_blk
              rw [h_pi_node] at h_res
              exact h_res
            · exfalso
              have := h_blk.1.1
              omega
        · intro k h_coll
          exact absurd h_coll (hσ_no_coll k)
        · intro h_len
          simp [Walk.length_cons, Walk.length_nil] at h_len
        · -- C4-strong.
          intro mπ_out sπ_out pπ_out h_eq
          refine ⟨mσ, σ_first, σ_rest, hσ_eq, ?_, ?_⟩
          · cases h_eq
            rw [h_σ_first_eq]; simp
          · -- IsForward → mσ ∈ G.Anc. σ_first backward, vacuous.
            cases h_eq
            rw [h_σ_first_eq]
            intro h_fwd
            simp at h_fwd
      | @cons _ mπ_p _ s' p'' =>
        -- p' = cons s' p''. Apply IH on p'.
        have hmπ_p_ne_u : mπ_p ≠ u := by
          cases s' with
          | forward h_E' =>
            have h_unf : (mπ, mπ_p) ∈ (G.marginalize {u}).E := h_E'
            rw [CDMG.mem_marginalize_E] at h_unf
            exact h_unf.2.1.2
          | backward h_E' =>
            have h_unf : (mπ_p, mπ) ∈ (G.marginalize {u}).E := h_E'
            rw [CDMG.mem_marginalize_E] at h_unf
            rcases h_unf.1 with hJ | hV
            · intro h_eq; subst h_eq
              exact (Set.disjoint_left.mp G.disjoint_JV) hJ huV
            · exact hV.2
          | bidir h_L' =>
            have h_unf : (mπ, mπ_p) ∈ (G.marginalize {u}).L := h_L'
            rw [CDMG.mem_marginalize_L] at h_unf
            exact h_unf.2.1.2
        -- Derive p'-shifted clauses (same as forward case).
        have hp'_1 : ∀ k, (Walk.cons s' p'').IsColliderAt k →
            (Walk.cons s' p'').nodeAt k ∈ (G.marginalize {u}).AncSet C := by
          intro k h_coll
          cases k with
          | zero =>
            cases p'' with
            | nil _ => exact absurd h_coll (by simp)
            | @cons _ _ _ _ _ => exact absurd h_coll (by simp)
          | succ k' =>
            have h_π_coll :
                (Walk.cons (WalkStep.backward h_E)
                  (Walk.cons s' p'')).IsColliderAt (k'+2) := by
              rw [Walk.isColliderAt_cons_cons_succ_succ]; exact h_coll
            have h_res := h1 (k'+2) h_π_coll
            simp only [Walk.nodeAt_cons_succ] at h_res
            exact h_res
        have hp'_2 : ∀ k, 0 < k → (Walk.cons s' p'').IsBlockableNonColliderAt k →
            (Walk.cons s' p'').nodeAt k ∉ C := by
          intro k hk h_blk
          cases k with
          | zero => omega
          | succ k' =>
            have h_π_blk :
                (Walk.cons (WalkStep.backward h_E)
                  (Walk.cons s' p'')).IsBlockableNonColliderAt (k'+2) := by
              have h_blk_unf := h_blk
              rw [Walk.isBlockableNonColliderAt_iff, Walk.isNonColliderAt_iff] at h_blk_unf
              obtain ⟨⟨h_le, h_nc⟩, h_nu⟩ := h_blk_unf
              rw [Walk.isBlockableNonColliderAt_iff, Walk.isNonColliderAt_iff]
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · rw [Walk.length_cons]; omega
              · rw [Walk.isColliderAt_cons_cons_succ_succ]; exact h_nc
              · rw [Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]; exact h_nu
            have h_res := h2 (k'+2) (by omega) h_π_blk
            simp only [Walk.nodeAt_cons_succ] at h_res
            exact h_res
        have hp'_3 : ∀ k, (Walk.cons s' p'').IsColliderAt k →
            (Walk.cons s' p'').nodeAt k ∈ C := by
          intro k h_coll
          cases k with
          | zero =>
            cases p'' with
            | nil _ => exact absurd h_coll (by simp)
            | @cons _ _ _ _ _ => exact absurd h_coll (by simp)
          | succ k' =>
            have h_π_coll :
                (Walk.cons (WalkStep.backward h_E)
                  (Walk.cons s' p'')).IsColliderAt (k'+2) := by
              rw [Walk.isColliderAt_cons_cons_succ_succ]; exact h_coll
            have h_res := h3 (k'+2) h_π_coll
            simp only [Walk.nodeAt_cons_succ] at h_res
            exact h_res
        -- Apply IH and extract ρ_p' = cons sρ' pρ'.
        obtain ⟨ρ_p', hρ_p'_c1, hρ_p'_c2, hρ_p'_c3, _hρ_p'_len, hρ_p'_c4⟩ :=
          ih hmπ_ne_u hb hp'_1 hp'_2 hp'_3
        obtain ⟨mρ', sρ', pρ', hρ_p'_eq, hρ_p'_arrow, hρ_p'_anc⟩ :=
          hρ_p'_c4 s' p'' rfl
        -- Decompose σ as σ_pre.append (cons σ_last (nil mπ)).
        obtain ⟨mσ_pre, σ_pre, σ_last, hσ_eq_last⟩ :=
          Walk.walk_pos_eq_append_last σ hσ_pos
        have hσ_back_l : σ.IsAllBackward := hσ_back
        rw [hσ_eq_last] at hσ_back_l
        -- σ_last is backward. Extract via marg_isAllBackward_append iff.
        have h_σ_last_back : (Walk.cons σ_last (Walk.nil mπ)).IsAllBackward :=
          ((Walk.marg_isAllBackward_append _ _).mp hσ_back_l).2
        have ⟨h_e_last, h_σ_last_eq⟩ :
            ∃ h : mσ_pre ⟵[G] mπ, σ_last = WalkStep.backward h := by
          cases σ_last with
          | forward _ => simp at h_σ_last_back
          | backward h => exact ⟨h, rfl⟩
          | bidir _ => simp at h_σ_last_back
        have hσ_last_not_arrow_tgt : ¬ σ_last.HasArrowheadAtTarget := by
          rw [h_σ_last_eq]; simp
        have hσ_pre_len : σ_pre.length + 1 = σ.length := by
          rw [hσ_eq_last, Walk.length_append, Walk.length_cons, Walk.length_nil]
        -- Build h_ρ_eq.
        have h_ρ_eq : σ.append ρ_p' =
            σ_pre.append (Walk.cons σ_last (Walk.cons sρ' pρ')) := by
          rw [hρ_p'_eq, hσ_eq_last]
          rw [Walk.append_assoc]
          rw [show (Walk.cons σ_last (Walk.nil mπ)).append (Walk.cons sρ' pρ') =
            Walk.cons σ_last (Walk.cons sρ' pρ') from by
            rw [Walk.cons_append, Walk.nil_append]]
        refine ⟨σ.append ρ_p', ?_, ?_, ?_, ?_, ?_⟩
        · -- C1.
          intro k h_coll
          by_cases hk_lt : k < σ.length
          · rw [Walk.isColliderAt_append_lt_length _ _ hk_lt] at h_coll
            exact absurd h_coll (hσ_no_coll k)
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · subst hk_eq
              -- Boundary at σ.length: σ_last backward, HasArrowheadAtTarget = False.
              -- So joint is non-collider. Contradiction.
              exfalso
              rw [h_ρ_eq] at h_coll
              rw [show σ.length = σ_pre.length + 1 from hσ_pre_len.symm] at h_coll
              rw [Walk.isColliderAt_append_cons_cons_one] at h_coll
              exact hσ_last_not_arrow_tgt h_coll.1
            · have h_gt : σ.length < k := lt_of_le_of_ne hk_lt (Ne.symm hk_eq)
              have h_eq_k : k = σ.length + (k - σ.length) := by omega
              rw [h_eq_k] at h_coll
              rw [Walk.isColliderAt_append_shift_pos _ _ _
                  (by omega : 0 < k - σ.length)] at h_coll
              have h_res := hρ_p'_c1 (k - σ.length) h_coll
              rw [h_eq_k, Walk.nodeAt_append_add_left]
              exact h_res
        · -- C2: blockable non-collider → ∉ C.
          intro k hk h_blk
          by_cases hk_lt : k < σ.length
          · have h_node_eq : (σ.append ρ_p').nodeAt k = σ.nodeAt k :=
              Walk.nodeAt_append_le _ _ (le_of_lt hk_lt)
            rw [h_node_eq]
            have h_in_int : σ.nodeAt k ∈ σ.support.tail.dropLast :=
              nodeAt_mem_interior_support σ hk hk_lt
            have h_node_u : σ.nodeAt k = u :=
              Set.mem_singleton_iff.mp (hσ_int (σ.nodeAt k) h_in_int)
            rw [h_node_u]; exact huC
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · subst hk_eq
              have h_node_eq : (σ.append ρ_p').nodeAt σ.length = mπ := by
                rw [Walk.nodeAt_append_le _ _ (le_refl _), Walk.nodeAt_length]
              rw [h_node_eq]
              -- π' is non-collider at 1 (always, in backward outer).
              have h_π_non_coll : ¬ (Walk.cons (WalkStep.backward h_E)
                  (Walk.cons s' p'')).IsColliderAt 1 := by
                rw [Walk.isColliderAt_cons_cons_one]
                intro h_and; exact (by simp : ¬ (WalkStep.backward h_E).HasArrowheadAtTarget) h_and.1
              -- Show NOT π' unblockable at 1, by contradiction.
              have h_π_not_unb : ¬ (Walk.cons (WalkStep.backward h_E)
                  (Walk.cons s' p'')).IsUnblockableNonColliderAt 1 := by
                intro h_π_unb
                rw [Walk.isUnblockableNonColliderAt_cons_cons_one] at h_π_unb
                -- h_π_unb : (backward h_E).IsUnblockableJoint s'.
                obtain ⟨_, h_back_clause, h_fwd_clause⟩ := h_π_unb
                have h_back_clause' : aπ ∈ (G.marginalize {u}).Sc mπ :=
                  h_back_clause (by simp : (WalkStep.backward h_E).IsBackward)
                -- Derive ρ unblockable at σ.length, contradicting h_blk.
                apply h_blk.2
                rw [h_ρ_eq]
                rw [show σ.length = σ_pre.length + 1 from hσ_pre_len.symm]
                rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one]
                refine ⟨?_, ?_, ?_⟩
                · -- ¬ collider
                  rw [h_σ_last_eq]; simp
                · -- σ_last.IsBackward = True → σ_last.source = mσ_pre ∈ G.Sc mπ.
                  intro _
                  -- Need: mσ_pre ∈ G.Sc mπ.
                  -- Case on σ.length.
                  by_cases hσ_len2 : 2 ≤ σ.length
                  · -- σ.length ≥ 2: mσ_pre = u (interior of σ).
                    -- Use u_in_Sc_via_directed_lift on σ.reverse.
                    -- σ.reverse : Walk G mπ aπ, directed, length ≥ 2, interior {u}.
                    have hσ_rev_int : σ.reverse.InteriorIn {u} :=
                      (interiorIn_reverse_iff σ {u}).mpr hσ_int
                    have hσ_rev_pos : 2 ≤ σ.reverse.length := by
                      rw [Walk.length_reverse]; exact hσ_len2
                    -- aπ ∈ G.Anc mπ (from h_back_clause').
                    have hmπ_not_in_u : mπ ∉ ({u} : Set α) := by
                      rw [Set.mem_singleton_iff]; exact hmπ_ne_u
                    rw [CDMG.marginalize_Sc_iff G {u} hmπ_not_in_u] at h_back_clause'
                    have haπ_Anc_mπ : aπ ∈ G.Anc mπ := h_back_clause'.1.1
                    -- Apply SCC helper.
                    have hu_in_Sc : u ∈ G.Sc mπ :=
                      u_in_Sc_via_directed_lift σ.reverse hσ_rev_dir hσ_rev_pos
                        hσ_rev_int huV haπ_Anc_mπ
                    -- mσ_pre = u (from hσ_eq_last + σ.length ≥ 2).
                    -- More precisely: σ_pre.length = σ.length - 1 ≥ 1.
                    -- σ_pre : Walk G aπ mσ_pre. The end of σ_pre is the interior of σ at position σ.length - 1.
                    -- nodeAt of σ_pre at its length = mσ_pre.
                    -- For σ.length ≥ 2: σ.nodeAt (σ.length - 1) = u (interior).
                    -- And σ.nodeAt (σ.length - 1) = σ_pre.nodeAt (σ.length - 1) (by nodeAt_append_le, since σ.length - 1 ≤ σ_pre.length).
                    -- σ_pre.length = σ.length - 1 = σ.length - 1.
                    -- σ_pre.nodeAt σ_pre.length = mσ_pre (by nodeAt_length).
                    -- So mσ_pre = σ.nodeAt (σ.length - 1) = u.
                    have hσ_pre_pos : 1 ≤ σ_pre.length := by omega
                    have h_node_pre_last : σ_pre.nodeAt σ_pre.length = mσ_pre :=
                      Walk.nodeAt_length _
                    have h_eq_pos : σ.length - 1 = σ_pre.length := by omega
                    have h_node_σ_at_pre_len : σ.nodeAt σ_pre.length = mσ_pre := by
                      rw [hσ_eq_last, Walk.nodeAt_append_le _ _ (le_refl _)]
                      exact h_node_pre_last
                    have h_node_σ_eq_u : σ.nodeAt σ_pre.length = u := by
                      have h_int : σ.nodeAt σ_pre.length ∈ σ.support.tail.dropLast :=
                        nodeAt_mem_interior_support σ (by omega : 0 < σ_pre.length)
                          (by omega : σ_pre.length < σ.length)
                      exact Set.mem_singleton_iff.mp (hσ_int (σ.nodeAt σ_pre.length) h_int)
                    have h_mσ_pre_eq_u : mσ_pre = u := by
                      rw [← h_node_σ_at_pre_len, h_node_σ_eq_u]
                    rw [h_mσ_pre_eq_u]
                    exact hu_in_Sc
                  · -- σ.length = 1: mσ_pre = aπ.
                    push_neg at hσ_len2
                    have hσ_len1 : σ.length = 1 := by omega
                    -- σ.length = 1, so σ_pre.length = 0, so σ_pre = nil aπ, so mσ_pre = aπ.
                    have hσ_pre_len_0 : σ_pre.length = 0 := by omega
                    have h_mσ_pre_eq_aπ : mσ_pre = aπ := by
                      cases σ_pre with
                      | nil _ => rfl
                      | @cons _ _ _ _ _ => simp [Walk.length_cons] at hσ_pre_len_0
                    rw [h_mσ_pre_eq_aπ]
                    -- aπ ∈ G.Sc mπ from h_back_clause'.
                    have hmπ_not_in_u : mπ ∉ ({u} : Set α) := by
                      rw [Set.mem_singleton_iff]; exact hmπ_ne_u
                    rw [CDMG.marginalize_Sc_iff G {u} hmπ_not_in_u] at h_back_clause'
                    exact h_back_clause'.1
                · -- sρ'.IsForward → mρ' ∈ G.Sc mπ.
                  intro hsρ'_fwd
                  -- sρ' forward → s' forward (via iff).
                  have hsρ'_no_arrow_src : ¬ sρ'.HasArrowheadAtSource := by
                    have ⟨h_e_sρ'_temp, h_sρ'_eq_temp⟩ :
                        ∃ h : mπ ⟶[G] mρ', sρ' = WalkStep.forward h := by
                      cases sρ' with
                      | forward h => exact ⟨h, rfl⟩
                      | backward _ => simp at hsρ'_fwd
                      | bidir _ => simp at hsρ'_fwd
                    rw [h_sρ'_eq_temp]; simp
                  have hs'_no_arrow_src : ¬ s'.HasArrowheadAtSource :=
                    fun h => hsρ'_no_arrow_src (hρ_p'_arrow.mpr h)
                  have hs'_fwd : s'.IsForward := by
                    cases s' with
                    | forward _ => simp
                    | backward _ => exact absurd (by simp) hs'_no_arrow_src
                    | bidir _ => exact absurd (by simp) hs'_no_arrow_src
                  -- mπ_p ∈ (G.marg {u}).Sc mπ from h_fwd_clause.
                  have hmπ_p_in_marg_Sc : mπ_p ∈ (G.marginalize {u}).Sc mπ :=
                    h_fwd_clause hs'_fwd
                  -- Convert via marginalize_Sc_iff.
                  have hmπ_not_in_u : mπ ∉ ({u} : Set α) := by
                    rw [Set.mem_singleton_iff]; exact hmπ_ne_u
                  rw [CDMG.marginalize_Sc_iff G {u} hmπ_not_in_u] at hmπ_p_in_marg_Sc
                  have hmπ_p_in_Anc : mπ_p ∈ G.Anc mπ := hmπ_p_in_marg_Sc.1.1
                  -- mρ' ∈ G.Anc mπ_p via C4-strong of IH.
                  have hmρ'_in_Anc_p : mρ' ∈ G.Anc mπ_p := hρ_p'_anc hsρ'_fwd
                  -- anc_trans.
                  have hmρ'_in_Anc_mπ : mρ' ∈ G.Anc mπ :=
                    CDMG.anc_trans hmρ'_in_Anc_p hmπ_p_in_Anc
                  -- mρ' ∈ G.Desc mπ via single forward edge.
                  have ⟨h_e_sρ', h_sρ'_eq⟩ :
                      ∃ h : mπ ⟶[G] mρ', sρ' = WalkStep.forward h := by
                    cases sρ' with
                    | forward h => exact ⟨h, rfl⟩
                    | backward _ => simp at hsρ'_fwd
                    | bidir _ => simp at hsρ'_fwd
                  have hmρ'_in_V : mρ' ∈ G.V := (G.E_subset h_e_sρ').2
                  have hmρ'_in_G : mρ' ∈ G := CDMG.mem_iff.mpr (Or.inr hmρ'_in_V)
                  have hmρ'_in_Desc : mρ' ∈ G.Desc mπ := by
                    rw [CDMG.mem_Desc]
                    refine ⟨hmρ'_in_G,
                      Walk.cons (WalkStep.forward h_e_sρ') (Walk.nil mρ'), ?_⟩
                    simp
                  exact ⟨hmρ'_in_Anc_mπ, hmρ'_in_Desc⟩
              -- Now π' blockable at 1.
              have h_π_blk : (Walk.cons (WalkStep.backward h_E)
                  (Walk.cons s' p'')).IsBlockableNonColliderAt 1 := by
                rw [Walk.isBlockableNonColliderAt_iff, Walk.isNonColliderAt_iff]
                refine ⟨⟨?_, h_π_non_coll⟩, h_π_not_unb⟩
                simp [Walk.length_cons]
              have h_res := h2 1 Nat.one_pos h_π_blk
              simp only [Walk.nodeAt_cons_succ, Walk.nodeAt_cons_zero] at h_res
              exact h_res
            · have h_gt : σ.length < k := lt_of_le_of_ne hk_lt (Ne.symm hk_eq)
              have h_eq_k : k = σ.length + (k - σ.length) := by omega
              rw [h_eq_k] at h_blk
              rw [isBlockableNonColliderAt_append_shift_pos σ ρ_p'
                  (k - σ.length) (by omega : 0 < k - σ.length)] at h_blk
              have h_res := hρ_p'_c2 (k - σ.length) (by omega) h_blk
              rw [h_eq_k, Walk.nodeAt_append_add_left]
              exact h_res
        · -- C3.
          intro k h_coll
          by_cases hk_lt : k < σ.length
          · rw [Walk.isColliderAt_append_lt_length _ _ hk_lt] at h_coll
            exact absurd h_coll (hσ_no_coll k)
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · subst hk_eq
              exfalso
              rw [h_ρ_eq] at h_coll
              rw [show σ.length = σ_pre.length + 1 from hσ_pre_len.symm] at h_coll
              rw [Walk.isColliderAt_append_cons_cons_one] at h_coll
              exact hσ_last_not_arrow_tgt h_coll.1
            · have h_gt : σ.length < k := lt_of_le_of_ne hk_lt (Ne.symm hk_eq)
              have h_eq_k : k = σ.length + (k - σ.length) := by omega
              rw [h_eq_k] at h_coll
              rw [Walk.isColliderAt_append_shift_pos _ _ _
                  (by omega : 0 < k - σ.length)] at h_coll
              have h_res := hρ_p'_c3 (k - σ.length) h_coll
              rw [h_eq_k, Walk.nodeAt_append_add_left]
              exact h_res
        · -- C5.
          intro h_len
          simp [Walk.length_cons] at h_len
        · -- C4-strong.
          intro mπ_out sπ_out pπ_out h_eq
          refine ⟨mσ, σ_first, σ_rest.append ρ_p', ?_, ?_, ?_⟩
          · rw [hσ_eq, Walk.cons_append]
          · cases h_eq
            rw [h_σ_first_eq]; simp
          · cases h_eq
            rw [h_σ_first_eq]
            intro h_fwd; simp at h_fwd
    | bidir h_L =>
      -- Bidir outer case. Extract σ via bidir_step_to_walk_in_G_arrows,
      -- which already provides σ with no colliders, first-step source-arrowhead,
      -- and last-step target-arrowhead.
      have h_L_unf : (aπ, mπ) ∈ (G.marginalize {u}).L := h_L
      rw [CDMG.mem_marginalize_L] at h_L_unf
      have hmπ_ne_u : mπ ≠ u := h_L_unf.2.1.2
      have hmπ_V : mπ ∈ G.V := h_L_unf.2.1.1
      have hmπ_in_G : mπ ∈ G := CDMG.mem_iff.mpr (Or.inr hmπ_V)
      -- For bidir_step_to_walk_in_G_arrows, we need aπ ≠ u, mπ ≠ u, huV.
      obtain ⟨σ, hσ_int, hσ_pos, hσ_no_coll, hσ_first_ex, hσ_last_ex⟩ :=
        bidir_step_to_walk_in_G_arrows h_L ha hmπ_ne_u huV
      obtain ⟨mσ, σ_first, σ_rest, hσ_eq, hσ_first_arrow⟩ := hσ_first_ex
      obtain ⟨mσ_pre, σ_pre, σ_last, hσ_eq_last, hσ_last_arrow⟩ := hσ_last_ex
      have hσ_pre_len : σ_pre.length + 1 = σ.length := by
        rw [hσ_eq_last, Walk.length_append, Walk.length_cons, Walk.length_nil]
      cases p' with
      | nil _ =>
        -- p' = nil mπ. Build ρ := σ.
        refine ⟨σ, ?_, ?_, ?_, ?_, ?_⟩
        · intro k h_coll; exact absurd h_coll (hσ_no_coll k)
        · -- C2.
          intro k hk h_blk
          by_cases hk_lt : k < σ.length
          · have h_in_int : σ.nodeAt k ∈ σ.support.tail.dropLast :=
              nodeAt_mem_interior_support σ hk hk_lt
            have h_node_u : σ.nodeAt k = u :=
              Set.mem_singleton_iff.mp (hσ_int (σ.nodeAt k) h_in_int)
            rw [h_node_u]; exact huC
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · subst hk_eq
              rw [Walk.nodeAt_length]
              have h_pi_len :
                  (Walk.cons (WalkStep.bidir h_L) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).length = 1 := by
                simp [Walk.length_cons]
              have h_pi_blk :
                  (Walk.cons (WalkStep.bidir h_L) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).IsBlockableNonColliderAt 1 := by
                rw [show (1 : ℕ) =
                  (Walk.cons (WalkStep.bidir h_L) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).length from h_pi_len.symm]
                exact Walk.isBlockableNonColliderAt_length _
              have h_pi_node :
                  (Walk.cons (WalkStep.bidir h_L) (Walk.nil mπ) :
                    Walk (G.marginalize {u}) aπ mπ).nodeAt 1 = mπ := by simp
              have h_res := h2 1 Nat.one_pos h_pi_blk
              rw [h_pi_node] at h_res
              exact h_res
            · exfalso
              have := h_blk.1.1; omega
        · intro k h_coll; exact absurd h_coll (hσ_no_coll k)
        · intro h_len; simp [Walk.length_cons, Walk.length_nil] at h_len
        · -- C4-strong.
          intro mπ_out sπ_out pπ_out h_eq
          refine ⟨mσ, σ_first, σ_rest, hσ_eq, ?_, ?_⟩
          · -- iff.
            cases h_eq
            constructor
            · intro _; simp
            · intro _; exact hσ_first_arrow
          · -- IsForward → mσ ∈ G.Anc. σ_first has HasArrowheadAtSource = True,
            -- so it's not forward (forward has HasArrowheadAtSource = False). Vacuous.
            intro h_fwd
            exfalso
            cases σ_first with
            | forward _ => simp at hσ_first_arrow
            | backward _ => simp at h_fwd
            | bidir _ => simp at h_fwd
      | @cons _ mπ_p _ s' p'' =>
        -- p' = cons s' p''. Apply IH on p'.
        have hmπ_p_ne_u : mπ_p ≠ u := by
          cases s' with
          | forward h_E' =>
            have h_unf : (mπ, mπ_p) ∈ (G.marginalize {u}).E := h_E'
            rw [CDMG.mem_marginalize_E] at h_unf
            exact h_unf.2.1.2
          | backward h_E' =>
            have h_unf : (mπ_p, mπ) ∈ (G.marginalize {u}).E := h_E'
            rw [CDMG.mem_marginalize_E] at h_unf
            rcases h_unf.1 with hJ | hV
            · intro h_eq; subst h_eq
              exact (Set.disjoint_left.mp G.disjoint_JV) hJ huV
            · exact hV.2
          | bidir h_L' =>
            have h_unf : (mπ, mπ_p) ∈ (G.marginalize {u}).L := h_L'
            rw [CDMG.mem_marginalize_L] at h_unf
            exact h_unf.2.1.2
        have hp'_1 : ∀ k, (Walk.cons s' p'').IsColliderAt k →
            (Walk.cons s' p'').nodeAt k ∈ (G.marginalize {u}).AncSet C := by
          intro k h_coll
          cases k with
          | zero =>
            cases p'' with
            | nil _ => exact absurd h_coll (by simp)
            | @cons _ _ _ _ _ => exact absurd h_coll (by simp)
          | succ k' =>
            have h_π_coll :
                (Walk.cons (WalkStep.bidir h_L)
                  (Walk.cons s' p'')).IsColliderAt (k'+2) := by
              rw [Walk.isColliderAt_cons_cons_succ_succ]; exact h_coll
            have h_res := h1 (k'+2) h_π_coll
            simp only [Walk.nodeAt_cons_succ] at h_res
            exact h_res
        have hp'_2 : ∀ k, 0 < k → (Walk.cons s' p'').IsBlockableNonColliderAt k →
            (Walk.cons s' p'').nodeAt k ∉ C := by
          intro k hk h_blk
          cases k with
          | zero => omega
          | succ k' =>
            have h_π_blk :
                (Walk.cons (WalkStep.bidir h_L)
                  (Walk.cons s' p'')).IsBlockableNonColliderAt (k'+2) := by
              have h_blk_unf := h_blk
              rw [Walk.isBlockableNonColliderAt_iff, Walk.isNonColliderAt_iff] at h_blk_unf
              obtain ⟨⟨h_le, h_nc⟩, h_nu⟩ := h_blk_unf
              rw [Walk.isBlockableNonColliderAt_iff, Walk.isNonColliderAt_iff]
              refine ⟨⟨?_, ?_⟩, ?_⟩
              · rw [Walk.length_cons]; omega
              · rw [Walk.isColliderAt_cons_cons_succ_succ]; exact h_nc
              · rw [Walk.isUnblockableNonColliderAt_cons_cons_succ_succ]; exact h_nu
            have h_res := h2 (k'+2) (by omega) h_π_blk
            simp only [Walk.nodeAt_cons_succ] at h_res
            exact h_res
        have hp'_3 : ∀ k, (Walk.cons s' p'').IsColliderAt k →
            (Walk.cons s' p'').nodeAt k ∈ C := by
          intro k h_coll
          cases k with
          | zero =>
            cases p'' with
            | nil _ => exact absurd h_coll (by simp)
            | @cons _ _ _ _ _ => exact absurd h_coll (by simp)
          | succ k' =>
            have h_π_coll :
                (Walk.cons (WalkStep.bidir h_L)
                  (Walk.cons s' p'')).IsColliderAt (k'+2) := by
              rw [Walk.isColliderAt_cons_cons_succ_succ]; exact h_coll
            have h_res := h3 (k'+2) h_π_coll
            simp only [Walk.nodeAt_cons_succ] at h_res
            exact h_res
        obtain ⟨ρ_p', hρ_p'_c1, hρ_p'_c2, hρ_p'_c3, _hρ_p'_len, hρ_p'_c4⟩ :=
          ih hmπ_ne_u hb hp'_1 hp'_2 hp'_3
        obtain ⟨mρ', sρ', pρ', hρ_p'_eq, hρ_p'_arrow, hρ_p'_anc⟩ :=
          hρ_p'_c4 s' p'' rfl
        -- Build h_ρ_eq.
        have h_ρ_eq : σ.append ρ_p' =
            σ_pre.append (Walk.cons σ_last (Walk.cons sρ' pρ')) := by
          rw [hρ_p'_eq, hσ_eq_last]
          rw [Walk.append_assoc]
          rw [show (Walk.cons σ_last (Walk.nil mπ)).append (Walk.cons sρ' pρ') =
            Walk.cons σ_last (Walk.cons sρ' pρ') from by
            rw [Walk.cons_append, Walk.nil_append]]
        refine ⟨σ.append ρ_p', ?_, ?_, ?_, ?_, ?_⟩
        · -- C1.
          intro k h_coll
          by_cases hk_lt : k < σ.length
          · rw [Walk.isColliderAt_append_lt_length _ _ hk_lt] at h_coll
            exact absurd h_coll (hσ_no_coll k)
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · subst hk_eq
              have h_node_eq : (σ.append ρ_p').nodeAt σ.length = mπ := by
                rw [Walk.nodeAt_append_le _ _ (le_refl _), Walk.nodeAt_length]
              rw [h_node_eq]
              rw [h_ρ_eq] at h_coll
              rw [show σ.length = σ_pre.length + 1 from hσ_pre_len.symm] at h_coll
              rw [Walk.isColliderAt_append_cons_cons_one] at h_coll
              obtain ⟨_, hsρ'_arrow⟩ := h_coll
              have hs'_arrow : s'.HasArrowheadAtSource := hρ_p'_arrow.mp hsρ'_arrow
              have h_π_coll : (Walk.cons (WalkStep.bidir h_L)
                  (Walk.cons s' p'')).IsColliderAt 1 := by
                rw [Walk.isColliderAt_cons_cons_one]
                exact ⟨by simp, hs'_arrow⟩
              have h_res := h1 1 h_π_coll
              simp only [Walk.nodeAt_cons_succ, Walk.nodeAt_cons_zero] at h_res
              exact marginalize_AncSet_subset G {u} C h_res
            · have h_gt : σ.length < k := lt_of_le_of_ne hk_lt (Ne.symm hk_eq)
              have h_eq_k : k = σ.length + (k - σ.length) := by omega
              rw [h_eq_k] at h_coll
              rw [Walk.isColliderAt_append_shift_pos _ _ _
                  (by omega : 0 < k - σ.length)] at h_coll
              have h_res := hρ_p'_c1 (k - σ.length) h_coll
              rw [h_eq_k, Walk.nodeAt_append_add_left]
              exact h_res
        · -- C2.
          intro k hk h_blk
          by_cases hk_lt : k < σ.length
          · have h_node_eq : (σ.append ρ_p').nodeAt k = σ.nodeAt k :=
              Walk.nodeAt_append_le _ _ (le_of_lt hk_lt)
            rw [h_node_eq]
            have h_in_int : σ.nodeAt k ∈ σ.support.tail.dropLast :=
              nodeAt_mem_interior_support σ hk hk_lt
            have h_node_u : σ.nodeAt k = u :=
              Set.mem_singleton_iff.mp (hσ_int (σ.nodeAt k) h_in_int)
            rw [h_node_u]; exact huC
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · subst hk_eq
              have h_node_eq : (σ.append ρ_p').nodeAt σ.length = mπ := by
                rw [Walk.nodeAt_append_le _ _ (le_refl _), Walk.nodeAt_length]
              rw [h_node_eq]
              -- Same SCC structure as forward case (σ.last has HasArrowheadAtTarget = True).
              have h_blk' := h_blk
              rw [h_ρ_eq] at h_blk'
              rw [show σ.length = σ_pre.length + 1 from hσ_pre_len.symm] at h_blk'
              obtain ⟨h_nc, h_nb⟩ := h_blk'
              rw [Walk.isNonColliderAt_iff] at h_nc
              rw [Walk.isColliderAt_append_cons_cons_one] at h_nc
              have h_not_coll : ¬ (σ_last.HasArrowheadAtTarget ∧ sρ'.HasArrowheadAtSource) :=
                h_nc.2
              have hsρ'_not_arrow : ¬ sρ'.HasArrowheadAtSource := fun h =>
                h_not_coll ⟨hσ_last_arrow, h⟩
              have ⟨h_e_sρ', h_sρ'_eq⟩ :
                  ∃ h : mπ ⟶[G] mρ', sρ' = WalkStep.forward h := by
                cases sρ' with
                | forward h => exact ⟨h, rfl⟩
                | backward _ =>
                  exact absurd (by simp : (WalkStep.backward _).HasArrowheadAtSource)
                    hsρ'_not_arrow
                | bidir _ =>
                  exact absurd (by simp : (WalkStep.bidir _).HasArrowheadAtSource)
                    hsρ'_not_arrow
              have hs'_not_arrow : ¬ s'.HasArrowheadAtSource :=
                fun h => hsρ'_not_arrow (hρ_p'_arrow.mpr h)
              have ⟨h_e_s', h_s'_eq⟩ :
                  ∃ h : mπ ⟶[G.marginalize {u}] mπ_p, s' = WalkStep.forward h := by
                cases s' with
                | forward h => exact ⟨h, rfl⟩
                | backward _ =>
                  exact absurd (by simp : (WalkStep.backward _).HasArrowheadAtSource)
                    hs'_not_arrow
                | bidir _ =>
                  exact absurd (by simp : (WalkStep.bidir _).HasArrowheadAtSource)
                    hs'_not_arrow
              rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_nb
              -- σ_last has HasArrowheadAtTarget. We need its IsBackward = False to know first → vacuous.
              -- σ_last could be forward or bidir (both have HasArrowheadAtTarget). Check both cases.
              have hσ_last_not_back : ¬ σ_last.IsBackward := by
                cases σ_last with
                | forward _ => simp
                | backward _ => simp at hσ_last_arrow
                | bidir _ => simp
              have h_mρ'_not_in_Sc : mρ' ∉ G.Sc mπ := by
                intro h_in
                apply h_nb
                refine ⟨?_, ?_, ?_⟩
                · intro ⟨_, h⟩; exact hsρ'_not_arrow h
                · intro h_back; exact absurd h_back hσ_last_not_back
                · intro _; exact h_in
              have h_π_blk : (Walk.cons (WalkStep.bidir h_L)
                  (Walk.cons s' p'')).IsBlockableNonColliderAt 1 := by
                rw [Walk.isBlockableNonColliderAt_iff, Walk.isNonColliderAt_iff,
                    Walk.length_cons, Walk.isColliderAt_cons_cons_one,
                    Walk.isUnblockableNonColliderAt_cons_cons_one]
                refine ⟨⟨by omega, ?_⟩, ?_⟩
                · intro ⟨_, h⟩; exact hs'_not_arrow h
                · intro h_unb
                  obtain ⟨_, _, h_fwd_clause⟩ := h_unb
                  have hs'_fwd : s'.IsForward := by rw [h_s'_eq]; simp
                  have h_mπ_p_in_marg_Sc : mπ_p ∈ (G.marginalize {u}).Sc mπ :=
                    h_fwd_clause hs'_fwd
                  have hmπ_not_in_u : mπ ∉ ({u} : Set α) := by
                    rw [Set.mem_singleton_iff]; exact hmπ_ne_u
                  rw [CDMG.marginalize_Sc_iff G {u} hmπ_not_in_u] at h_mπ_p_in_marg_Sc
                  have hmπ_p_in_Anc : mπ_p ∈ G.Anc mπ := h_mπ_p_in_marg_Sc.1.1
                  have hsρ'_fwd : sρ'.IsForward := by rw [h_sρ'_eq]; simp
                  have hmρ'_in_Anc_p : mρ' ∈ G.Anc mπ_p := hρ_p'_anc hsρ'_fwd
                  have hmρ'_in_Anc_mπ : mρ' ∈ G.Anc mπ :=
                    CDMG.anc_trans hmρ'_in_Anc_p hmπ_p_in_Anc
                  have hmρ'_in_V : mρ' ∈ G.V := (G.E_subset h_e_sρ').2
                  have hmρ'_in_G : mρ' ∈ G := CDMG.mem_iff.mpr (Or.inr hmρ'_in_V)
                  have hmρ'_in_Desc : mρ' ∈ G.Desc mπ := by
                    rw [CDMG.mem_Desc]
                    refine ⟨hmρ'_in_G,
                      Walk.cons (WalkStep.forward h_e_sρ') (Walk.nil mρ'), ?_⟩
                    simp
                  exact h_mρ'_not_in_Sc ⟨hmρ'_in_Anc_mπ, hmρ'_in_Desc⟩
              have h_res := h2 1 Nat.one_pos h_π_blk
              simp only [Walk.nodeAt_cons_succ, Walk.nodeAt_cons_zero] at h_res
              exact h_res
            · have h_gt : σ.length < k := lt_of_le_of_ne hk_lt (Ne.symm hk_eq)
              have h_eq_k : k = σ.length + (k - σ.length) := by omega
              rw [h_eq_k] at h_blk
              rw [isBlockableNonColliderAt_append_shift_pos σ ρ_p' (k - σ.length)
                  (by omega : 0 < k - σ.length)] at h_blk
              have h_res := hρ_p'_c2 (k - σ.length) (by omega) h_blk
              rw [h_eq_k, Walk.nodeAt_append_add_left]
              exact h_res
        · -- C3.
          intro k h_coll
          by_cases hk_lt : k < σ.length
          · rw [Walk.isColliderAt_append_lt_length _ _ hk_lt] at h_coll
            exact absurd h_coll (hσ_no_coll k)
          · push_neg at hk_lt
            by_cases hk_eq : k = σ.length
            · subst hk_eq
              have h_node_eq : (σ.append ρ_p').nodeAt σ.length = mπ := by
                rw [Walk.nodeAt_append_le _ _ (le_refl _), Walk.nodeAt_length]
              rw [h_node_eq]
              rw [h_ρ_eq] at h_coll
              rw [show σ.length = σ_pre.length + 1 from hσ_pre_len.symm] at h_coll
              rw [Walk.isColliderAt_append_cons_cons_one] at h_coll
              obtain ⟨_, hsρ'_arrow⟩ := h_coll
              have hs'_arrow : s'.HasArrowheadAtSource := hρ_p'_arrow.mp hsρ'_arrow
              have h_π_coll : (Walk.cons (WalkStep.bidir h_L)
                  (Walk.cons s' p'')).IsColliderAt 1 := by
                rw [Walk.isColliderAt_cons_cons_one]
                exact ⟨by simp, hs'_arrow⟩
              have h_res := h3 1 h_π_coll
              simp only [Walk.nodeAt_cons_succ, Walk.nodeAt_cons_zero] at h_res
              exact h_res
            · have h_gt : σ.length < k := lt_of_le_of_ne hk_lt (Ne.symm hk_eq)
              have h_eq_k : k = σ.length + (k - σ.length) := by omega
              rw [h_eq_k] at h_coll
              rw [Walk.isColliderAt_append_shift_pos _ _ _
                  (by omega : 0 < k - σ.length)] at h_coll
              have h_res := hρ_p'_c3 (k - σ.length) h_coll
              rw [h_eq_k, Walk.nodeAt_append_add_left]
              exact h_res
        · intro h_len; simp [Walk.length_cons] at h_len
        · -- C4-strong.
          intro mπ_out sπ_out pπ_out h_eq
          refine ⟨mσ, σ_first, σ_rest.append ρ_p', ?_, ?_, ?_⟩
          · rw [hσ_eq, Walk.cons_append]
          · cases h_eq
            constructor
            · intro _; simp
            · intro _; exact hσ_first_arrow
          · -- IsForward → mσ ∈ G.Anc. σ_first has source-arrowhead, not forward, vacuous.
            intro h_fwd
            exfalso
            cases σ_first with
            | forward _ => simp at hσ_first_arrow
            | backward _ => simp at h_fwd
            | bidir _ => simp at h_fwd

-- claim_3_25 helper (Sub-task 2c, auxiliary lift with strengthened IH)
--
-- The structural-recursion auxiliary for `lift_sigmaOpen_walk_through_single_vertex`.
-- Compared to the public theorem, this auxiliary uses a **weakened σ-open
-- formulation** that skips the `k = 0` clause-2 obligation (the
-- endpoint-vertex-not-in-`C` constraint at the start of the walk). The
-- weakening is essential because in the recursive cons-case, the head
-- step's target vertex `m` (= start of `p'`) may or may not be in `C`,
-- depending on `π'`'s status at position 1 -- and `m ∈ C` is consistent
-- with `π'` being a collider or unblockable at 1. With the weakened
-- formulation, `m ∈ C` doesn't break the recursion.
--
-- The auxiliary also exposes the **first-step source-arrowhead iff
-- invariant**: when both `π'` and `ρ` have a first step (i.e., π' is
-- non-trivial), the first step's source-arrowhead is preserved between
-- `π'` and `ρ`. This is what enables the boundary verification at
-- position `σ.length` on `ρ` in the recursive cons-case: the joint
-- condition collider/non-collider/unblockable status transports between
-- the two walks via the arrowhead match.
--
-- ## Proof structure
--
-- Induction on `π'`. Base case (`π' = nil v`): take `ρ = nil v`; the
-- iff invariant is vacuous (no cons decomposition). Cons case:
-- case-split on the head step `step`:
--
-- * **forward `step = .forward h_E`** (h_E : (a, m) ∈ (G.marg {u}).E):
--   apply `forward_step_to_walk_in_G` to get a directed walk
--   `σ : Walk G a m` with interior in `{u}`. Apply IH on `p'` to
--   get `ρ_p'`. Build `ρ = σ.append ρ_p'`. For boundary verification at
--   position `σ.length` on `ρ`: σ.last is forward (HasArrowheadAtTarget
--   = True); the joint condition becomes `ρ_p'.first.HasArrowheadAtSource`,
--   which matches `p'.first.HasArrowheadAtSource` via the IH iff.
--
-- * **backward `step = .backward h_E`** (h_E : (m, a) ∈ (G.marg {u}).E):
--   apply `backward_step_to_walk_in_G` to get an all-backward walk
--   `σ : Walk G a m`. σ.last is backward (HasArrowheadAtTarget = False);
--   no collider possible at position `σ.length` on ρ. For unblockable
--   verification: if σ.length ≥ 2, σ.last.source = u, apply
--   `u_in_Sc_via_directed_lift` (SCC helper) to get u ∈ G.Sc m.
--
-- * **bidir `step = .bidir h_L`**: apply `bidir_step_to_walk_in_G_arrows`
--   to get σ with no colliders, source/target arrowheads at first/last
--   matching the bidir step's True/True. Same boundary verification
--   pattern as forward.
--
-- The σ-open verification on `ρ = σ.append ρ_p'` partitions positions
-- as: (a) `0 ≤ k < σ.length` (inside σ — nodeAt = u via interior or
-- = a at position 0); (b) `k = σ.length` (boundary at m — use π's
-- status at 1 + IH iff + SCC where needed); (c) `k > σ.length`
-- (inside ρ_p' — shift via `isColliderAt_append_shift_pos` and
-- `isBlockableNonColliderAt_append_shift_pos`).
private lemma lift_aux {G : CDMG α} {u : α} (huV : u ∈ G.V)
    {C : Set α} (huC : u ∉ C) :
    ∀ {a b : α} (π' : Walk (G.marginalize {u}) a b),
      a ≠ u → b ≠ u →
      (∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ (G.marginalize {u}).AncSet C) →
      (∀ k, 0 < k → π'.IsBlockableNonColliderAt k → π'.nodeAt k ∉ C) →
      (∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ C) →
    ∃ ρ : Walk G a b,
      (∀ k, ρ.IsColliderAt k → ρ.nodeAt k ∈ G.AncSet C) ∧
      (∀ k, 0 < k → ρ.IsBlockableNonColliderAt k → ρ.nodeAt k ∉ C) ∧
      (∀ k, ρ.IsColliderAt k → ρ.nodeAt k ∈ C) ∧
      (∀ {mπ : α} (sπ : WalkStep (G.marginalize {u}) a mπ)
         (pπ : Walk (G.marginalize {u}) mπ b),
         π' = Walk.cons sπ pπ →
         ∃ (mρ : α) (sρ : WalkStep G a mρ) (pρ : Walk G mρ b),
           ρ = Walk.cons sρ pρ ∧
           (sρ.HasArrowheadAtSource ↔ sπ.HasArrowheadAtSource)) := by
  -- Derive `lift_aux` from `lift_aux_strong` by discarding the two extra
  -- conjuncts (C5 length-preservation and the IsForward-Anc clause of
  -- C4-strong). The signature here is the public one used by
  -- `lift_sigmaOpen_walk_through_single_vertex`; `lift_aux_strong`'s
  -- proof of the structural recursion lives above this lemma.
  intro a b π' ha hb h1 h2 h3
  obtain ⟨ρ, hc1, hc2, hc3, _h_len, h_c4_strong⟩ :=
    lift_aux_strong huV huC π' ha hb h1 h2 h3
  refine ⟨ρ, hc1, hc2, hc3, ?_⟩
  intros mπ sπ pπ h_eq
  obtain ⟨mρ, sρ, pρ, hρ_eq, hρ_arrow, _h_anc⟩ := h_c4_strong sπ pπ h_eq
  exact ⟨mρ, sρ, pρ, hρ_eq, hρ_arrow⟩

-- claim_3_25 (Sub-task 2 deliverable)
-- title: SigmaOpenWalkMarginalization -- single-vertex lift of σ-open walks
--
-- This is the (⇒) direction of `isISigmaSeparated_marginalize_iff`
-- specialized to `D = {u}`: a σ-open walk in the marginalization
-- `G.marginalize {u}` lifts, edge by edge, to a σ-open walk in `G`.
-- The LN's argument (proof.tex lines 41 -- 105) decomposes into:
--
--   1. **Lift table** (proof.tex lines 57 -- 70). Every edge in
--      `G^{\sm u}` lifts to a short walk through `u` in `G`:
--      * Directed edge `v \tuh w` comes from `v \tuh w` (length 1)
--        or `v \tuh u \tuh w` (length 2, more generally a directed
--        walk with interior in `{u}`).
--      * Bidirected edge `v \huh w` comes from one of four
--        bifurcation patterns: just-bidir `v \huh w`, fork
--        `v \hut u \tuh w`, left-hinge `v \huh u \tuh w`, or
--        right-hinge `v \hut u \huh w`.
--      In all bifurcation cases, `u` appears as a non-collider
--      with at most one arrowhead towards `u`.
--
--   2. **Arrowhead preservation at non-`u` nodes** (proof.tex
--      lines 78 -- 84). For each boundary vertex `b_j` of the
--      lift, the arrowhead patterns at `b_j` from each adjacent
--      edge are preserved between `π` (in `G^{\sm u}`) and the
--      lifted walk `ρ` (in `G`). So collider / non-collider
--      status at each `b_j` is preserved.
--
--   3. **Colliders remain σ-open** (proof.tex line 86 -- 88).
--      A collider `b_j` in `ρ` was a collider in `π` (by step 2);
--      `π`'s σ-open clause 1 gives `b_j ∈ Anc^{G^{\sm u}}(C)`,
--      which by `marginalize_AncSet_subset` lifts to
--      `b_j ∈ Anc^G(C)`.
--
--   4. **Blockable non-colliders remain σ-open** (proof.tex
--      lines 90 -- 92). A blockable non-collider `b_j` in `π`
--      satisfies `b_j ∉ C` (`π`'s σ-open clause 2); the same
--      `b_j` is a non-collider in `ρ` (by step 2), and whether
--      `b_j` becomes unblockable in `ρ` (a possibility, since
--      `Sc^G(b_j) \supseteq Sc^{G^{\sm u}}(b_j)`) or stays
--      blockable, `b_j ∉ C` is enough.
--
--   5. **Unblockable non-colliders remain σ-open** (proof.tex
--      lines 94 -- 100). An unblockable non-collider `b_j` in
--      `π` remains unblockable in `ρ`: any outgoing edge that
--      was preserved through the lift stays in `Sc^G(b_j)`
--      (`Sc^{G^{\sm u}}(b_j) \subseteq Sc^G(b_j)`); any outgoing
--      edge that *was* expanded through `u` (the LN's "$b_j
--      \tuh u \tuh b_{j\pm 1}$" pattern, with `b_{j\pm 1} \in
--      \Sc^{G^{\sm u}}(b_j)`) has its new target `u` in
--      `\Sc^G(b_j)` -- because `b_j \tuh u \in E` gives
--      `u \in Desc^G(b_j)`, and `u \tuh b_{j\pm 1} \to b_j`
--      (the directed-walk-from-$u$-to-$b_j$ through the SCC of
--      $b_{j\pm 1}$) gives `u \in Anc^G(b_j)`.
--
--   6. **Inserted `u`-nodes are σ-open** (proof.tex lines
--      102 -- 104). Each `u`-vertex interior to a lift segment
--      is a non-collider (at most one arrowhead pointing to it),
--      and `u \notin C` (the lemma's precondition `huC`), so
--      the σ-open clause 2 holds regardless of whether the
--      `u`-position is blockable or unblockable.
--
-- The LN's footnote on longer bifurcation lifts through repeated
-- `u`-self-loops (proof.tex line 66) does NOT bite in the lift
-- direction: the `lift_bifurcation_walk` primitive
-- (`Section3_2/MarginalizationsCommute.lean:610`) already returns
-- a bifurcation in `G` with arbitrary `u`-interior, and the
-- σ-open verification at the `u`-interior vertices uses
-- `huC : u ∉ C` directly (independent of how many `u`-vertices
-- appear). Blocker B in the diagnostic (`workspace_claim_3_25.md`
-- §B.2) applies only to the (⇐) contract direction.
--
-- ## Design choice
--
-- * **Strong induction on `π'`** (structural). The LN's
--   "edge by edge" lift table directly suggests structural
--   recursion: for each `WalkStep` of `π'`, extract a lift
--   segment via `mem_marginalize_E` / `mem_marginalize_L`,
--   then concatenate via `Walk.append`. The `induction π' with`
--   tactic plus `Walk.append`-based composition matches this
--   one-to-one.
--
-- * **`hvu : v ≠ u` and `hwu : w ≠ u` as explicit
--   preconditions.** Every vertex on a `Walk (G.marginalize
--   {u})` walk of length ≥ 1 is forced into `(G.marginalize
--   {u}).J ∪ (G.marginalize {u}).V = G.J ∪ (G.V \ {u})`, which
--   excludes `u`. The endpoints `v` and `w` need this
--   explicitly because the trivial walk `nil v` doesn't carry
--   the constraint. Without `hvu, hwu`, the lift would
--   degenerate at trivial walks with endpoint equal to `u`
--   (vacuous existential, but cluttered statement).
--
-- * **`huC : u ∉ C` precondition.** Mirrors the LN's source
--   block precondition `D ∩ (A ∪ B ∪ C) = ∅` (specialized to
--   `D = {u}`, restricted to the `C`-conjunct). The `huA` /
--   `huB` halves are not needed for the lift: the lift
--   constructs walks between arbitrary endpoints `v, w`, not
--   between `A` and `B`-endpoints; the `A` / `B`-side enters
--   only at the wrapper level (sub-task 4's
--   `isISigmaSeparated_marginalize_singleton_iff`).
--
-- * **`huV : u ∈ G.V` precondition.** Mirrors the LN's "$u \in
--   V$" (where the lemma takes "$u \in V \sm (A \cup B \cup C)$").
--   The lift segment lemmas (`lift_directed_walk`,
--   `lift_bifurcation_walk`) don't strictly need this -- they
--   work for any `W : Set α` -- but the σ-openness preservation
--   at `u`-positions and the LN's SCC argument at boundary
--   non-colliders both rely on `u` being a graph vertex (so
--   that walks through `u` are well-formed).
--
-- * **Existential conclusion `∃ ρ`, not a function `lift_walk`.**
--   Mirrors the LN's "obtaining a walk $\pi$ in $G$" prose
--   (proof.tex line 75): we extract some lift, not a specific
--   one. A function `lift_walk : Walk (G.marg {u}) v w →
--   Walk G v w` would need `Classical.choice` to pick a
--   specific witness from each `mem_marginalize_E` /
--   `mem_marginalize_L` existential, and the additional
--   noncomputability would clutter downstream consumers (who
--   only need the existence). The single-vertex iff
--   (sub-task 4) likewise consumes the existential, not a
--   specific function.
--
-- * **Conclusion's "colliders in `C`" conjunct.** The LN's
--   stronger property "all colliders in `C`" (not just "in
--   `Anc^G(C)`") is preserved through the lift by the same
--   argument as the σ-open clause 1: a collider in `ρ` was a
--   collider in `π'` (step 2), and `π'`'s `hCol'` puts it in
--   `C`. We carry the conjunct through the conclusion so that
--   the single-vertex iff (sub-task 4) and the row-level
--   wrapper can both consume it via
--   `((G.sigmaOpens_TFAE C v w).out 0 2).mpr` to bridge
--   between the "walk with colliders in `C`" surface and the
--   "σ-open path" surface of `isNotISigmaSeparated_TFAE`.

/-- LN proof.tex:41 -- 105 (the (⇒) lift direction, single-vertex
case): every $C$-σ-open walk in `G.marginalize {u}` whose colliders
all lie in `C` lifts, edge by edge through the LN's bifurcation /
directed-edge lift table, to a $C$-σ-open walk in `G` with
colliders still in `C`.

This is the **single-vertex specialization** of the (⇒) direction
of `isISigmaSeparated_marginalize_iff`'s contrapositive. Composing
with the (⇐) direction (`contract_sigmaOpen_walk_at_single_vertex`,
sub-task 3) and using `isISigmaSeparated_TFAE` /
`isNotISigmaSeparated_TFAE` bridges to the row-level wrapper. -/
theorem lift_sigmaOpen_walk_through_single_vertex
    (G : CDMG α) {u : α} (huV : u ∈ G.V) (C : Set α) (huC : u ∉ C)
    {v w : α} (hvu : v ≠ u) (hwu : w ≠ u)
    (π' : Walk (G.marginalize {u}) v w)
    (hOpen' : π'.IsSigmaOpen C)
    (hCol' : ∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ C) :
    ∃ ρ : Walk G v w, ρ.IsSigmaOpen C ∧
      (∀ k, ρ.IsColliderAt k → ρ.nodeAt k ∈ C) := by
  -- Derive the public theorem from `lift_aux` (the strengthened-IH auxiliary
  -- with weakened clause 2 skipping k = 0). We supply the weakened clause 2
  -- (trivially follows from the full one) and recover the k = 0 obligation
  -- on `ρ` via the start-vertex `v ∉ C` (from `hOpen'.2 0` on π').
  obtain ⟨h_c1, h_c2_full⟩ := hOpen'
  have h_c2_weak : ∀ k, 0 < k → π'.IsBlockableNonColliderAt k → π'.nodeAt k ∉ C :=
    fun k _ => h_c2_full k
  obtain ⟨ρ, h_ρ_c1, h_ρ_c2_w, h_ρ_col, _⟩ :=
    lift_aux huV huC π' hvu hwu h_c1 h_c2_weak hCol'
  refine ⟨ρ, ⟨h_ρ_c1, ?_⟩, h_ρ_col⟩
  intro k h_blk
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · -- k = 0: ρ.nodeAt 0 = v, need v ∉ C.
    have h_v_notin_C : π'.nodeAt 0 ∉ C := h_c2_full 0 (Walk.isBlockableNonColliderAt_zero π')
    rw [Walk.nodeAt_zero] at h_v_notin_C ⊢
    exact h_v_notin_C
  · -- k > 0: use the weakened conclusion from lift_aux.
    exact h_ρ_c2_w k hk_pos h_blk

-- NOTE: The previous worker's escalation TODO (~300 lines documenting the
-- need for a strengthened-IH design, the SCC argument, and the helper
-- decomposition) has been removed in favor of the lift_aux + helper
-- design above. The relevant pieces are now distributed across:
--   * `bidir_step_to_walk_in_G_arrows` (the strong bidir lift, replacing
--     the manager's spec helper 6's softened conclusion with the
--     stronger arrowhead-witness form),
--   * `u_in_Sc_via_directed_lift` (the SCC argument formalized as a
--     standalone helper, matching the LN's proof.tex lines 94--100),
--   * `lift_aux` (the strengthened-IH structural recursion -- still has
--     a `sorry` for the ~500-700 LoC structural-recursion body itself,
--     which is the specific subgoal the next worker should pick up).
--
-- The original 300-line TODO is preserved in the workspace
-- (`workspace_claim_3_25.md`, Manager B turn 8 + earlier diagnostic
-- entries) for future reference.

/-! ### Private helpers for the (⇐) contract direction (Sub-task 3) -/

-- claim_3_25 helper (Sub-task 3)
-- title: split walk into "u-run prefix" + "non-u suffix"
--
-- Given a walk `p : Walk G u b` with `b ≠ u`, extract the maximal prefix
-- of `p` that goes through `u`-only vertices (its `support.dropLast` lies
-- in `{u}`) and ends at the first non-`u` vertex `m` encountered. The
-- length of the prefix is ≥ 1.
--
-- ## Design choice
--
-- * Structural recursion on `p`. At each step, case on the target `w` of
--   the head: if `w = u`, recurse on the tail (extending the buffer); if
--   `w ≠ u`, the first non-`u` vertex is `w` and the prefix is the head
--   step alone.
private lemma split_until_next_non_u {G : CDMG α} {u : α} :
    ∀ (n : ℕ), ∀ {b : α} (p : Walk G u b), p.length ≤ n → b ≠ u →
      ∃ (m : α) (τ : Walk G u m) (ρ : Walk G m b),
        m ≠ u ∧ p = τ.append ρ ∧ 1 ≤ τ.length ∧
        (∀ x ∈ τ.support.dropLast, x = u) := by
  intro n
  induction n with
  | zero =>
    intro b p hlen hb
    cases p with
    | nil _ => exact absurd rfl hb
    | @cons _ _ _ _ _ => rw [Walk.length_cons] at hlen; omega
  | succ k ih =>
    intro b p hlen hb
    cases p with
    | nil _ => exact absurd rfl hb
    | @cons _ w _ step p' =>
      have hp'_len : p'.length ≤ k := by rw [Walk.length_cons] at hlen; omega
      by_cases hw : w = u
      · subst hw
        obtain ⟨m, τ', ρ, hm_ne, hp'_eq, hτ'_pos, hτ'_supp⟩ := ih p' hp'_len hb
        refine ⟨m, Walk.cons step τ', ρ, hm_ne, ?_, ?_, ?_⟩
        · rw [Walk.cons_append, hp'_eq]
        · simp [Walk.length_cons]
        · intro x hx
          rw [Walk.support_cons, List.dropLast_cons_of_ne_nil τ'.marg_support_ne_nil] at hx
          rcases List.mem_cons.mp hx with rfl | hxr
          · rfl
          · exact hτ'_supp x hxr
      · refine ⟨w, Walk.cons step (Walk.nil w), p', hw, ?_, ?_, ?_⟩
        · rw [Walk.cons_append, Walk.nil_append]
        · simp [Walk.length_cons]
        · intro x hx
          rw [Walk.support_cons, Walk.support_nil] at hx
          simp at hx
          exact hx

-- claim_3_25 helper (Sub-task 3)
-- title: single-edge step in G between non-u vertices lifts to a marg step
--
-- Given a single edge `(v, m) ∈ G.E` with `v, m ≠ u`, the directed
-- walk `cons (forward h) nil` has empty interior ⊆ {u}, so
-- `(v, m) ∈ (G.marginalize {u}).E` via `mem_marginalize_E`.
private lemma single_forward_to_marg_E {G : CDMG α} {u v m : α}
    (h : v ⟶[G] m) (hvu : v ≠ u) (hmu : m ≠ u) :
    (v, m) ∈ (G.marginalize {u}).E := by
  rw [CDMG.mem_marginalize_E]
  have hm_V : m ∈ G.V := (Set.mem_prod.mp (G.E_subset h)).2
  have hv_in_JV : v ∈ G.J ∪ G.V := (Set.mem_prod.mp (G.E_subset h)).1
  refine ⟨?_, ⟨hm_V, ?_⟩, Walk.cons (WalkStep.forward h) (Walk.nil m), ?_, ?_, ?_⟩
  · rcases hv_in_JV with hJ | hV
    · exact Or.inl hJ
    · refine Or.inr ⟨hV, ?_⟩
      intro h_eq
      exact hvu (Set.mem_singleton_iff.mp h_eq)
  · intro h_eq
    exact hmu (Set.mem_singleton_iff.mp h_eq)
  · simp
  · intro x hx
    rw [Walk.support_cons, Walk.support_nil] at hx
    simp at hx
  · simp [Walk.length_cons]

/-! ### The (⇐) direction: σ-open walks contract at a single vertex (stub) -/

-- claim_3_25 (Sub-task 3 deliverable, stubbed here)
-- title: SigmaOpenWalkMarginalization -- single-vertex contract of σ-open walks
--
-- This is the (⇐) direction of `isISigmaSeparated_marginalize_iff`
-- specialized to `D = {u}`: a σ-open walk in `G` whose endpoints
-- are not `u` contracts, by collapsing each maximal run of `u`'s
-- into a single edge in `G.marginalize {u}`, to a σ-open walk in
-- the marginalized graph. The proof body is left as a `sorry`
-- because this is the LN's harder direction and is the explicit
-- scope of sub-task 3, not sub-task 2. The LN's "longer runs
-- through self-loop traversals of `u` are handled analogously"
-- hand-wave (proof.tex lines 129 -- 130, Blocker B in the
-- diagnostic §B.2) is expected to bite during the contract
-- proof; the sub-task 3 worker should escalate via `expand_proof`
-- on the LN's `\Claude{...}` if necessary.

/-- LN proof.tex:106 -- 190 (the (⇐) contract direction, single-vertex
case). Every $C$-σ-open walk in `G` whose colliders all lie in `C`
contracts, by collapsing each maximal run of `u`'s into a single
edge, to a $C$-σ-open walk in `G.marginalize {u}` with colliders
still in `C`. The preconditions `u ∉ A`, `u ∉ B`, `u ∉ C` mirror
the LN's `D ∩ (A ∪ B ∪ C) = ∅` clause specialized to `D = {u}`.

TODO(Sub-task 3): discharge `sorry`. The proof is the LN's
contraction case-table (proof.tex lines 131 -- 138) plus the
unblockable-non-collider rerouting through a fresh hinge vertex
(proof.tex lines 159 -- 189). Blocker B
(`workspace_claim_3_25.md` §B.2 -- the self-loop hand-wave at
proof.tex lines 129 -- 130) is expected to bite; escalate via
`expand_proof` on the LN's `\Claude{...}` if it does. The
infrastructure of `shrink_directed_walk` (`MarginalizationsCommute.lean`
line 302), `shrink_bifurcation_walk` (line 710), and the
σ-open / collider preservation lemmas in
`Section3_3/SigmaBlockedReversal.lean` cover the structural
case-analysis; the σ-openness verification at boundary positions
mirrors the lift theorem above but in the dual direction.

The `A`, `B` parameters are carried in the signature (rather than
collapsed into the single `C`-conjunct that the lift theorem
uses) because the sub-task-3 / sub-task-4 wrapper level wants to
state the precondition exactly as the LN does
(`D ∩ (A ∪ B ∪ C) = ∅`, with `D = {u}`). The body will likely
only consume `huC : u ∉ C` and `hvu : v ≠ u` /
`hwu : w ≠ u`; the sub-task 3 worker may simplify the binder
shape if `huA` / `huB` turn out to be unused. -/
theorem contract_sigmaOpen_walk_at_single_vertex
    (G : CDMG α) {u : α} (huV : u ∈ G.V) (A B C : Set α)
    (huA : u ∉ A) (huB : u ∉ B) (huC : u ∉ C)
    {v w : α} (hvu : v ≠ u) (hwu : w ≠ u)
    (π : Walk G v w)
    (hOpen : π.IsSigmaOpen C)
    (hCol : ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C) :
    ∃ π' : Walk (G.marginalize {u}) v w, π'.IsSigmaOpen C ∧
      (∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ C) := by
  -- TODO(Sub-task 3): see the docstring above. The contract
  -- direction is the explicit scope of sub-task 3, not sub-task 2.
  sorry

/-! ### Combined single-vertex iff (stub) -/

-- claim_3_25 (Sub-task 4 deliverable, stubbed here)
-- title: SigmaOpenWalkMarginalization -- single-vertex iff
--
-- The `D = {u}` specialization of `isISigmaSeparated_marginalize_iff`:
-- `G.IsISigmaSeparated A B C ↔ (G.marginalize {u}).IsISigmaSeparated A B C`
-- whenever `u ∈ G.V` and `u ∉ A ∪ B ∪ C`. The proof body is left as
-- a `sorry` because it depends on both lift and contract directions
-- being proven (sub-task 2 + sub-task 3); sub-task 4 will combine
-- them via `isISigmaSeparated_TFAE` / `isNotISigmaSeparated_TFAE`.

/-- LN proof.tex:34 -- 40 (the single-vertex iff): the `D = {u}`
specialization of `isISigmaSeparated_marginalize_iff`. Together
with the LN's `marginalize_marginalize`-driven induction on
`#D` (proof.tex line 38 -- 39), this discharges the outer
reduction in the row-level wrapper.

TODO(Sub-task 4): discharge `sorry`. Should be a ~2 -- 5 line
proof:
```
constructor
· -- (⇒) direction: contrapose, use `isNotISigmaSeparated_TFAE`
  -- to extract a $C$-σ-open walk-with-colliders-in-`C` from
  -- `¬ G.IsISigmaSeparated A B C`, then apply
  -- `contract_sigmaOpen_walk_at_single_vertex`.
· -- (⇐) direction: contrapose, extract a witness from
  -- `¬ (G.marginalize {u}).IsISigmaSeparated A B C` via the same
  -- TFAE, then apply `lift_sigmaOpen_walk_through_single_vertex`.
```
The endpoints `v ∈ A`, `w ∈ G.J ∪ B` of the extracted walk satisfy
`v ≠ u` (since `u ∉ A`) and `w ≠ u` (since `u ∉ B` and
`u ∉ G.J` -- the latter follows from `u ∈ G.V` and
`G.disjoint_JV`), discharging the `hvu` / `hwu` preconditions of
the two single-vertex helpers. -/
theorem isISigmaSeparated_marginalize_singleton_iff
    (G : CDMG α) {u : α} (huV : u ∈ G.V) (A B C : Set α)
    (huA : u ∉ A) (huB : u ∉ B) (huC : u ∉ C) :
    G.IsISigmaSeparated A B C ↔
      (G.marginalize {u}).IsISigmaSeparated A B C := by
  -- TODO(Sub-task 4): see the docstring above. Should be a short
  -- proof combining `lift_sigmaOpen_walk_through_single_vertex`,
  -- `contract_sigmaOpen_walk_at_single_vertex`, and
  -- `isNotISigmaSeparated_TFAE`.
  sorry

end CDMG

end Causality
