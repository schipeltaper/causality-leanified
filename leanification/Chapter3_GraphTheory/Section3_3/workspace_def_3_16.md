# Workspace for def_3_16 — BlockableAndUnblockable (refactor: collider_side_aware)

## Refactor goal (this row)

DEPENDENT row. Root `def_3_15` is changing the semantics of
`IsCollider` / `IsNonCollider` to a SIDE-AWARE reading via the new
helpers `refactor_HeadAtTarget` / `refactor_HeadAtSource`. The current
declarations in this file reference `p.IsNonCollider k` — during the
refactor window this resolves to the ORIGINAL (non-side-aware) version
by literal-name match, exactly the failure mode the def_3_15 workspace
documented and fixed (see its third strict-gate FAIL fix). To keep the
side-aware partition pointwise during the refactor window, this row's
predicates must reference `refactor_IsNonCollider` (and
`refactor_IsBlockableNonCollider`) in the REPLACEMENT bodies.

**Scope: this row's file only.** Other dependent rows
(`AcyclicNonCollidersBlockable`, `SigmaBlockedWalks`, …) have their
own refactor entries and will be ported by their own managers.

## What changes vs what does NOT

| Declaration                  | Touched by refactor? | Marker treatment |
|------------------------------|----------------------|------------------|
| `variable {Node}` section block | no (already helper-marked) | unchanged |
| `variable {G : CDMG Node}`   | no (already helper-marked) | unchanged |
| `Walk.HasBlockingLeftSlot`   | no (no reference to IsCollider/IsNonCollider; pattern-matches on `.backwardE`/`.forwardE`/`.bidir` which are unchanged; uses `G.Sc` which is unchanged) | unchanged, no REFACTOR markers |
| `Walk.HasBlockingRightSlot`  | no (same rationale)  | unchanged, no REFACTOR markers |
| `Walk.IsBlockableNonCollider` | YES — body cites `p.IsNonCollider k` | `REFACTOR-BLOCK-ORIGINAL` wraps existing def; `REFACTOR-BLOCK-REPLACEMENT` adds `refactor_IsBlockableNonCollider` retargeting onto `p.refactor_IsNonCollider` |
| `Walk.IsUnblockableNonCollider` | YES — body cites both `p.IsNonCollider k` and `p.IsBlockableNonCollider k` | `REFACTOR-BLOCK-ORIGINAL` wraps existing def; `REFACTOR-BLOCK-REPLACEMENT` adds `refactor_IsUnblockableNonCollider` retargeting onto `p.refactor_IsNonCollider` and `p.refactor_IsBlockableNonCollider` |

## Why `HasBlockingLeftSlot` / `HasBlockingRightSlot` correctly handle the self-loop case under BOTH readings

At a directed self-loop at slot `k-1` (or slot `k`), the cons-cell's
source `u` and target `v` are bound to the same node `w` (the loop
vertex). The helper checks `u ∉ G.Sc v` (resp. `v ∉ G.Sc u`), which
reduces to `w ∉ G.Sc w`. By `def_3_5`'s trivial-walk witness
(`Walk.nil`), `w ∈ G.Sc w` always, so `w ∉ G.Sc w` is False — the
self-loop slot is never "blocking". This was already correct under
the OLD reading and stays correct under the NEW reading; the SC
self-membership absorbs the self-loop convention through the
SC-component test, no constructor-tag dispatch needed.

The semantic shift introduced by the refactor lands at the
non-collider classification level (positions that were colliders
under the old `IsInto` reading and are now non-colliders under the
side-aware reading); on those newly-non-collider positions the four
disjuncts of `IsBlockableNonCollider` evaluate to False (interior +
SC self-membership), so the position ends up `IsUnblockable` — exactly
the LN's "a self-loop alone never disqualifies an interior position
from being unblockable" reading in the canonical tex's "Treatment of
directed self-loops" paragraph.

## Tex (canonical statement)

`tex/def_3_16_BlockableAndUnblockable.tex` already commits to the
walk-edge-based reading (which IS the side-aware reading at the LN
level — the LN has always read the walk graph-theoretically; the Lean
encoding is catching up). The tex's "Treatment of directed self-loops"
paragraph already reads "a self-loop alone never disqualifies an
interior position from being unblockable". No tex changes needed.

`addition_to_the_LN` for this row should stay empty for now — the
side-aware encoding is documented at the def_3_15 level (where the
encoding choice is made), and def_3_16's encoding is purely a
mechanical retarget onto the new partner predicates.

## Plan

1. **(this turn)** Workspace written; dispatch
   `formalize_definition_in_lean` worker to write the REPLACEMENT
   blocks for `IsBlockableNonCollider` and `IsUnblockableNonCollider`.
2. `review_design` — full-LN-context check that the refactored predicates
   are a natural shape.
3. `verify_equivalence` — friendly check of the refactored predicates
   vs LN block + addition.
4. (Optional but recommended) `verify_equivalence_strict` — catches
   any deviation early; the strict gate will run on `solved` anyway.
5. `add_design_choice_comments` — refresh the design-choice prose
   above each REPLACEMENT block to explain the `refactor_IsNonCollider`
   / `refactor_IsBlockableNonCollider` retarget and why it matters
   during the refactor window (mirrors def_3_15's `IsNonCollider`
   REPLACEMENT block's rationale).
6. `solved` → orchestrator runs verify_row_solved + sorry-check +
   strict-gate.

## Marker layout (mirrors def_3_15's `IsCollider` / `IsNonCollider` pair)

For each of `IsBlockableNonCollider` / `IsUnblockableNonCollider`:

```
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: <Name>
-- <existing design-choice comment block>
-- def_3_16 -- start statement
def <Name> ... := ... -- existing body, unchanged
-- def_3_16 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: <Name>

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: <Name> (was: refactor_<Name>)
-- <NEW design-choice comment block tailored to the side-aware port>
-- def_3_16 -- start statement
def refactor_<Name> ... := ... -- retargeted body
-- def_3_16 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: <Name>
```

The inner `-- def_3_16 -- start/end statement` markers are
website-extraction tags (untouched by Phase 7 cleanup's whole-word
rename, since they are documentation comments not declaration names).

## Run summary log
_(append per-run summaries if the row is paused and resumed)_
