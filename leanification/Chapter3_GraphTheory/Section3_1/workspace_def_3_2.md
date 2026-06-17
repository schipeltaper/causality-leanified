# Workspace for def_3_2 — CDMGNotation (refactor DEPENDENT in `cdmg_typed_edges`)

## Refactor context

This is a DEPENDENT row in refactor `cdmg_typed_edges`. The root
`def_3_1` (`CDMG.lean`) flipped `L` from `Finset (Node × Node)` +
`hL_symm` to `Finset (Sym2 Node)` (symmetry definitional via the
quotient). The root has been completed and lives at
`leanification/Chapter3_GraphTheory/Section3_1/CDMG.lean` with both
the original `structure CDMG` (in ORIGINAL markers, lines 174–187)
and the replacement `structure refactor_CDMG` (in REPLACEMENT
markers, lines 189–393).

## Declarations affected, decision per declaration

`CDMGNotation.lean` has 7 declarations, all inside `namespace CDMG`:

| # | name | body uses | needs body change? | needs refactor block? |
|---|------|-----------|-------------------|----------------------|
| 1 | `instMembership` | `G.J ∪ G.V` | no | yes (target type changes) |
| 2 | `tuh` | `(v1,v2) ∈ G.E` | no | yes (target type changes) |
| 3 | `hut` | `(v2,v1) ∈ G.E` | no | yes (target type changes) |
| 4 | `huh` | `(v1,v2) ∈ G.L` | **YES — `s(v1,v2) ∈ G.L`** | yes |
| 5 | `suh` | `G.tuh v1 v2 ∨ G.huh v1 v2` | no | yes (target type changes; dot-notation resolves in `refactor_CDMG` namespace) |
| 6 | `hus` | `G.hut v1 v2 ∨ G.huh v1 v2` | no | yes |
| 7 | `sus` | `G.tuh v1 v2 ∨ G.hut v1 v2 ∨ G.huh v1 v2` | no | yes |

All 7 need `refactor_*` versions because downstream refactor rows
need to use `v ∈ G`, `G.tuh`, `G.huh`, etc., for `G : refactor_CDMG Node`.
Dot-notation on `G : refactor_CDMG Node` looks in the
`refactor_CDMG` namespace (not `CDMG`), so the refactor declarations
must live in `namespace refactor_CDMG`.

## File-structure plan

Open a new `namespace refactor_CDMG ... end refactor_CDMG` block
after the existing `end CDMG` (inside `namespace Causality`). Inside
the new namespace:

- One helper-marker-wrapped `variable {Node : Type*} [DecidableEq Node]` line.
- 7 `refactor_*` declarations, each in its own
  `REFACTOR-BLOCK-REPLACEMENT-BEGIN: <Name> (was: refactor_<Name>)`
  block with statement markers and forward-looking design comments.

Each of the 7 original declarations gets wrapped in
`REFACTOR-BLOCK-ORIGINAL-BEGIN/END: <Name>` markers (around the
statement-marker block, NOT the design comments above it — mirror
the def_3_1 example).

After Phase 7 cleanup, the file has two `namespace CDMG ... end CDMG`
blocks (one empty shell, one with the refactor declarations
renamed). The polish step is comment-only and won't merge them; a
follow-up tidy could, but it's harmless.

## Plan

1. **Single `spawn_agent_sub_task` to write all markers + refactor_* declarations**, with explicit naming for each declaration and `lake build` verification at the end.
2. `review_design` on the replacement block (full LN context).
3. `verify_equivalence` against LN + addition_to_the_LN.
4. `verify_equivalence_strict` (recommended — `huh` introduces the `Sym2`-based encoding into this row's surface).
5. `add_design_choice_comments` (if review_design surfaces gaps).
6. `solved` → strict-equivalence solved-gate → mark solved.

## Notes / history

_(first turn — dispatching the porting worker now)_
