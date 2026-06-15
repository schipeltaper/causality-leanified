# Workspace for def_3_18 — ISigmaSeparation (refactor row)

## Refactor context

This is a DEPENDENT row in refactor `blockable_noncollider_first`
(roots: `def_3_16`).  The upstream root swapped the primary/derived
split of `IsBlockableNonCollider` / `IsUnblockableNonCollider`:
- old: positive `IsUnblockableNonCollider`, derived
  `IsBlockableNonCollider := IsNonCollider ∧ ¬IsUnblockableNonCollider`
- new: positive `refactor_IsBlockableNonCollider` (disjunction over
  end-positions + outgoing walk-edges leaving `G.Sc vk`), derived
  `refactor_IsUnblockableNonCollider := IsNonCollider ∧ ¬refactor_IsBlockableNonCollider`

The two pairs agree extensionally on the `p.IsNonCollider k` sub-class
(case-by-case proof in def_3_16's design-choice block, lines ~493-523
of `BlockableAndUnblockable.lean`).

## Analysis: no shape change needed in this file

`ISigmaSeparation.lean` references `IsSigmaBlockedGiven` (from
`def_3_17`, `SigmaBlockedWalks.lean`) as a *black-box predicate* —
it never destructures the predicate nor reaches into its internal
existentials.  Grep confirms zero direct references to
`IsBlockableNonCollider` / `IsUnblockableNonCollider` /
`refactor_*` in the Lean code path of `ISigmaSeparation.lean` (the
single match is inside a design-choice comment).

Upstream `SigmaBlockedWalks.lean` (the `def_3_17` row of this refactor)
made the same determination — black-box treatment — and added a
"Refactor compatibility" paragraph to its top-level docstring without
adding any `REFACTOR-BLOCK-ORIGINAL` / `REFACTOR-BLOCK-REPLACEMENT`
marker pair.

This row inherits that pattern at one further remove: `IsISigmaSeparated`
is a black box over `IsSigmaBlockedGiven`, which is a black box over
`IsBlockableNonCollider`; the chain preserves extensional content.

## Planned action sequence (mirrors def_3_17's path)

1. `verify_equivalence` — confirm existing Lean predicate still matches
   LN block + `addition_to_the_LN` after the upstream swap.
2. `add_design_choice_comments` — add a "Refactor compatibility
   (`blockable_noncollider_first`)" paragraph to the top-level
   docstring of `ISigmaSeparation.lean`, mirroring the parallel
   paragraph in `SigmaBlockedWalks.lean` lines ~112-135.
3. `solved` → strict-gate auto-runs; should PASS since no shape change.

## Notes for future managers / fallback

- If `verify_equivalence` FAILs unexpectedly, the strict checker may
  have spotted a regression I missed; re-dispatch the formalizer with
  the feedback.
- If the strict gate inside `solved` returns `EXAMPLE_GENERATION` and
  `verify_with_examples` fails, the discrepancy is almost certainly
  in def_3_17 / def_3_16 (upstream), not here — consider
  `refactor` on the affected upstream root or `accept_deviation` only
  as last resort.
