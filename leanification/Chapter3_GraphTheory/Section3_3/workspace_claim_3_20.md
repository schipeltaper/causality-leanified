# Workspace for claim_3_20 — AcyclicNonCollidersBlockable

## Refactor context

This row is a **DEPENDENT** in the `collider_side_aware` refactor.  Roots: `def_3_15`.
Root structural change: in `CollidersAndNon.lean`, the per-step arrowhead-contribution
predicate `WalkStep.IsInto : … → Node → Prop` (a node-equality reading on the WalkStep's
type indices) is replaced by the side-aware pair
`refactor_HeadAtTarget` / `refactor_HeadAtSource` (zero-arg, constructor-tag reading with
opposite-channel L-disjuncts for writing-mirror coverage).  Downstream
`refactor_IsCollider` /  `refactor_IsNonCollider` change accordingly:
  * `IsCollider` clause-1 body: `s₀.IsInto vk ∧ s₁.IsInto vk`
    → `refactor_IsCollider` clause-1 body:
    `s₀.refactor_HeadAtTarget ∧ s₁.refactor_HeadAtSource`
  * `IsNonCollider` body: `k ≤ p.length ∧ ¬ p.IsCollider k`
    → `refactor_IsNonCollider` body: `k ≤ p.length ∧ ¬ p.refactor_IsCollider k`

`def_3_16` (`BlockableAndUnblockable.lean`) was already ported under this same refactor:
`refactor_IsBlockableNonCollider` retargets the first conjunct
`p.IsNonCollider k` → `p.refactor_IsNonCollider k`; the four-disjunct
`(k = 0 ∨ k = p.length ∨ HasBlockingLeftSlot k ∨ HasBlockingRightSlot k)` is unchanged
(`HasBlockingLeftSlot` / `HasBlockingRightSlot` are NOT refactored — they pattern-match on
WalkStep constructor tags and query `G.Sc`, neither touched by this refactor).

## Mathematical content of the proof — UNCHANGED by the refactor

The LN-level proof (canonical tex `tex/claim_3_20_proof_AcyclicNonCollidersBlockable.tex`)
splits on the position `k` along π: end-positions are trivial; interior positions extract
an outgoing E-walk-edge of `v_k` from the non-collider hypothesis, then use acyclicity to
show its other endpoint lies outside `Sc^G(v_k)`.  This LN argument does NOT depend on any
Lean-side encoding choice for "arrowhead at v_k" -- it operates on the LN's literal
stored-pair / walk-constraint reading directly.

The Lean-side mechanical port:

  * Wrap existing `blocking_interior_helper` in `REFACTOR-BLOCK-ORIGINAL` markers.
  * Write `refactor_blocking_interior_helper`: same body, except:
    - hypothesis `¬ π.IsCollider k` → `¬ π.refactor_IsCollider k`;
    - substantive `k = 1` case: unfold `¬ refactor_IsCollider 1` at the cons-cons pattern
      to `¬ (s₀.refactor_HeadAtTarget ∧ s₁.refactor_HeadAtSource)`; `not_and_or` split.
      Each branch case-splits on the relevant WalkStep constructor:
       - `¬ s₀.refactor_HeadAtTarget`: `.forwardE _` → True (impossible),
         `.bidir _` → True (impossible), `.backwardE h` → `s(u,v) ∈ G.L` (possible).
         In the `.backwardE h` branch, `h : (vMid, uOuter) ∈ G.E`, and
         `HasBlockingLeftSlot 1 = uOuter ∉ G.Sc vMid` is discharged by
         `outgoing_E_not_in_Sc hG h`.
       - `¬ s₁.refactor_HeadAtSource`: `.backwardE _` → True (impossible),
         `.bidir _` → True (impossible), `.forwardE h` → `s(u,v) ∈ G.L` (possible).
         In the `.forwardE h` branch, `h : (vMid, vNext) ∈ G.E`, and the outer
         `HasBlockingRightSlot 1` reduces (via the cons-cell descent + .forwardE branch)
         to `vNext ∉ G.Sc vMid`, discharged by `outgoing_E_not_in_Sc hG h`.
    - inductive `k + 2` step: same shape, just retarget the predicate names.
  * Wrap existing `acyclic_non_colliders_blockable` in `REFACTOR-BLOCK-ORIGINAL` markers.
  * Write `refactor_acyclic_non_colliders_blockable`: same signature, except
    `π.IsNonCollider k → π.IsBlockableNonCollider k`
    → `π.refactor_IsNonCollider k → π.refactor_IsBlockableNonCollider k`,
    and the body delegates to `refactor_blocking_interior_helper` instead.
  * `outgoing_E_not_in_Sc` is NOT touched -- references only `G.IsAcyclic`, `G.E`,
    `G.Sc`, `G.Anc`, `Walk.cons` / `Walk.IsDirectedWalk` / `WalkStep.forwardE`, none of
    which are refactored.  It stays outside any REFACTOR-BLOCK markers.

## Tex twin

Existing `tex/claim_3_20_proof_AcyclicNonCollidersBlockable.tex` is itself a twin from
the previous `cdmg_typed_edges` refactor.  For `collider_side_aware`, the LN-level proof is
again unchanged -- only the Lean encoding's per-step head-contribution reading changes,
which is INVISIBLE in the tex.  The twin file
`tex/refactor_claim_3_20_proof_AcyclicNonCollidersBlockable.tex` will hold a copy of the
proof body verbatim, updated only in its top-comment header to credit the new refactor.

## Plan

1. Dispatch `write_tex_proof.md` (claim row, refactor twin mode) to write the twin tex
   at `tex/refactor_claim_3_20_proof_AcyclicNonCollidersBlockable.tex`.
2. `verify_tex_statement_plus_proof` (structural) on the twin.
3. `verify_tex_proof` (mathematical) on the twin.
4. Dispatch `prove_claim_in_lean.md` (refactor mode) to add the REPLACEMENT blocks
   in `AcyclicNonCollidersBlockable.lean`.
5. `review_design` on the REPLACEMENT.
6. `verify_equivalence` on the REPLACEMENT statement vs LN.
7. `add_design_choice_comments` to enrich the comment block.
8. `solved`.

## History

(none yet)
