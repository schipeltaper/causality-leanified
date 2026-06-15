# Workspace for def_3_17 — SigmaBlockedWalks (refactor: blockable_noncollider_first)

This file is the manager's scratchpad for this row. Use it for:

- The plan
- A running list of what has been tried and why it didn't work
- Notes for the next manager (if you `new_manager`-handoff or
  the run ends and a future invocation picks this row up again)

## Refactor situation (manager run starting 2026-06-15)

**Role:** DEPENDENT in refactor `blockable_noncollider_first`.
**Cause:** root `def_3_16` swapped its primary/derived split — `refactor_IsBlockableNonCollider` (positive disjunction form) is now primary; `refactor_IsUnblockableNonCollider` (negation form) is derived. Cleanup-script global rename will collapse `refactor_<Name>` → `<Name>` across every affected file.

### Key observation: this row needs no Lean change

`SigmaBlockedWalks.lean` references `p.IsBlockableNonCollider k` as a black-box predicate — never inspects its internal shape. Concretely:

- `IsSigmaOpenGiven` uses `p.IsBlockableNonCollider k → vk ∉ C` (universal-implication form).
- `IsSigmaBlockedGiven` uses `… ∧ p.IsBlockableNonCollider k ∧ vk ∈ C` (existential-conjunction form).

After Phase 7 cleanup deletes the ORIGINAL block in `BlockableAndUnblockable.lean` and renames `refactor_IsBlockableNonCollider` → `IsBlockableNonCollider` globally:

- The name `IsBlockableNonCollider` will resolve to the new disjunction-form primary.
- The two predicates of `def_3_17` will continue to compile because their black-box use of `IsBlockableNonCollider` doesn't depend on its internal shape.
- Extensional meaning is preserved because the refactor design proves the new and old shapes agree on the `IsNonCollider` sub-class case-by-case (see `BlockableAndUnblockable.lean` lines 493–523).

So no REPLACEMENT marker block is needed in `SigmaBlockedWalks.lean`. The cleanup script's refusal check (refuses if it finds top-level `refactor_*` declarations outside REPLACEMENT markers) won't trigger because there will be no `refactor_*` declarations in this file at all.

### Existing artefacts stay as-is

- **Canonical tex statement** (`tex/def_3_17_SigmaBlockedWalks.tex`): already integrates the `[claim_type_mismatch_vertex_vs_walk]` addition and is verified equivalent to LN+addition from the original solve. No edit needed.
- **Lean file** (`SigmaBlockedWalks.lean`): already has rich design comments and statement markers (`-- def_3_17 -- start/end statement`). Design rationale references `IsBlockableNonCollider`'s "walk-edge reading" inherited from `def_3_16`; that walk-edge reading is preserved by the refactor (per `verify_with_examples` instance 4 on `def_3_16`'s refactor), so all design comments remain accurate.

### Plan

1. **verify_equivalence** — friendly check that the existing Lean still matches LN+addition under the refactored shape. (Quick sanity check before relying on the strict gate.)
2. **add_design_choice_comments** — orchestrator-required pre-`solved` step. Confirm the existing comment block adequately documents the refactor's no-op effect on this row, or update if anything has gone stale.
3. **solved** — auto-runs `verify_row_solved` + hard sorry check + strict-equivalence gate. With no Lean change, all three should pass.

## Run log
