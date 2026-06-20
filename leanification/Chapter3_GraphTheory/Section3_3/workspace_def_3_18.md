# Workspace for def_3_18 — ISigmaSeparation

This file is the manager's scratchpad for this row. Use it for:

- The plan (output of `make_plan` worker)
- A running list of what has been tried and why it didn't work
- Notes for the next manager (if you `new_manager`-handoff or
  the run ends and a future invocation picks this row up again)

It is YAML-untyped markdown — feel free to add sections.

## Refactor: `collider_side_aware` — DEPENDENT port plan (manager turn 1)

This row is a DEPENDENT in `collider_side_aware`; the only root that affects
it is `def_3_15` (`CollidersAndNon.lean`), but the dependency propagates
through `def_3_17` (`SigmaBlockedWalks.lean`), which is already solved as
part of this refactor table.

### What changed upstream

- `CollidersAndNon.lean`: `IsCollider` / `IsNonCollider` retargeted to use
  the new side-aware `HeadAtTarget` / `HeadAtSource` helpers (constructor-
  tag reading rather than `IsInto` node-equality). Solved.
- `SigmaBlockedWalks.lean`: `IsSigmaBlockedGiven` body retargeted to call
  the side-aware `refactor_IsCollider` / `refactor_IsBlockableNonCollider`
  partners. **Signature byte-identical** to the ORIGINAL. Solved.
- `BlockableAndUnblockable.lean`: `IsBlockableNonCollider` /
  `IsUnblockableNonCollider` similarly retargeted. Solved.

### What this row needs

This row carries **no head-contribution logic of its own**. The five
declarations all forward to `IsSigmaBlockedGiven` directly or transitively
through `IsISigmaSeparated`. The signature of `refactor_IsSigmaBlockedGiven`
is byte-identical to the ORIGINAL, so the port is purely mechanical:

| Decl | Body change |
| --- | --- |
| `IsISigmaSeparated` | `π.IsSigmaBlockedGiven C hC` → `π.refactor_IsSigmaBlockedGiven C hC` |
| `IsNotISigmaSeparated` | `¬ G.IsISigmaSeparated …` → `¬ G.refactor_IsISigmaSeparated …` |
| `IsISigmaSeparatedEmpty` | `G.IsISigmaSeparated A B ∅ …` → `G.refactor_IsISigmaSeparated A B ∅ …` |
| `IsSigmaSeparated` | `G.IsISigmaSeparated A B C …` → `G.refactor_IsISigmaSeparated A B C …` |
| `IsNotSigmaSeparated` | `G.IsNotISigmaSeparated A B C …` → `G.refactor_IsNotISigmaSeparated A B C …` |

Five `REFACTOR-BLOCK-ORIGINAL-BEGIN/END` + five `REFACTOR-BLOCK-REPLACEMENT-BEGIN/END`
pairs. No new helpers expected — the existing `variable` block is reused.

### Pattern precedent

Closest template: `SigmaBlockedWalks.lean` (the sibling DEPENDENT row,
`def_3_17`) — two `REFACTOR-BLOCK` pairs wrapping `IsSigmaOpenGiven` /
`IsSigmaBlockedGiven` with full design-block docstrings (~150 lines each).
Multi-decl example: `BlockableAndUnblockable.lean`.

### Pending verifiers after the port

1. `verify_tex_statement_only` (structural, on the existing canonical tex)
   — but the tex hasn't changed for a refactor; check that prior verification
   carries.
2. `verify_tex_statement_equivalence` — same as above.
3. `review_design` (full LN context).
4. `verify_equivalence` (vs LN + `addition_to_the_LN`).
5. `add_design_choice_comments` already done in the existing file;
   verify the REPLACEMENT block docstrings carry the refactor-specific
   rationale comparable to `SigmaBlockedWalks.lean`'s precedent.
6. `solved` → triggers strict-equivalence gate.
