# Workspace for claim_3_22 — SigmaSeparationSymmetric

This file is the manager's scratchpad for this row. Use it for:

- The plan (output of `make_plan` worker)
- A running list of what has been tried and why it didn't work
- Notes for the next manager (if you `new_manager`-handoff or
  the run ends and a future invocation picks this row up again)

It is YAML-untyped markdown — feel free to add sections.

## 2026-06-21 — Manager turn 1 survey

State on entry:
- `formalized=yes proven=no solved=no`, `actions_tracking` all-zero
  (i.e. this is the first manager-tracked action sequence for the
  refactor row).
- A prior run (pre-this-manager) appears to have completed the entire
  port. Concretely:
  - `SigmaSeparationSymmetric.lean` (2068 lines): contains
    walk-reversal infrastructure (pre-marker; lines 91-279), a long
    string of `REFACTOR-BLOCK-DELETE-BEGIN/END` blocks for the
    pre-refactor `Walk.isCollider_*` / `isBlockableNonCollider_*` /
    `isSigmaBlockedGiven_*` helpers (lines 281-1162), an
    `REFACTOR-BLOCK-ORIGINAL` block holding the pre-refactor
    `sigma_separation_symmetric` theorem with FULL proof body (lines
    1164-1381 — body is not `:= by sorry` despite the comment claim;
    references the to-be-deleted `Walk.isSigmaBlockedGiven_reverse`),
    and `REFACTOR-BLOCK-REPLACEMENT` blocks for every side-aware
    helper plus the side-aware theorem `refactor_sigma_separation_symmetric`
    (lines 1399-2064; also a complete proof body, threading
    `refactor_HeadAtTarget` / `refactor_HeadAtSource` /
    `refactor_IsCollider` / `refactor_IsBlockableNonCollider` /
    `refactor_IsSigmaBlockedGiven` through the same beat structure).
  - `tex/refactor_claim_3_22_proof_SigmaSeparationSymmetric.tex` (292
    lines): complete refactor-twin proof, ends with `\end{proof}` then
    `\end{document}`; no `sorry` / `TODO` / `FIXME`.
- `lake build` from repo root: clean (no errors; only style-warning
  long-line / `simp`-flexibility notes).
- No actual `sorry` tokens anywhere in the Lean file (only in
  comments documenting an earlier Manager A intent that was later
  superseded by the proof being filled in).

Strategy for this manager: the work is genuinely done. The
side-aware refactor of `def_3_15` (constructor-tag-only
`refactor_HeadAtSource` / `refactor_HeadAtTarget`) made the
writing-mirror artefact described in the carried-over operator tip
(2026-06-16) structurally impossible at the predicate level, which
in turn unblocks the per-step reversal-invariance lemmas
(`refactor_headAtTarget_reverse` / `refactor_headAtSource_reverse` —
each provable by `Iff.rfl` on every WalkStep constructor). The
remaining heavy lifting — the `HasBlockingLeftSlot` /
`HasBlockingRightSlot` reversal-equivalence lemmas, the
`refactor_isCollider_reverse_sa` chain, etc. — was performed by the
prior run and survives unchanged.

Dispatching `solved` next: triggers `verify_row_solved` + hard
sorry-check + strict-equivalence gate. Expect PASS on all three.
