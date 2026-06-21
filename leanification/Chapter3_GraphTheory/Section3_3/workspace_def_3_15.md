# Workspace for def_3_15 — CollidersAndNon (refactor: collider_side_aware)

## State at fresh pickup (2026-06-21)

Row was previously `solved=yes` but has been **reset to `solved=no`** by an
out-of-band change. The uncommitted diff shows:

- `refactor_HeadAtTarget.backwardE _` flipped from `s(u, v) ∈ G.L` → `False`.
- `refactor_HeadAtSource.forwardE _` flipped from `s(u, v) ∈ G.L` → `False`.
- Workspace wiped to its empty stub.
- `refactor_data.json` rolled back to `solved=no`, counters cleared.

This brings the Lean code into agreement with `addition_to_the_LN`'s
clause (b), which says explicitly: "the contribution of $a_i$ to
$\mathrm{ah}_\pi(k)$ is determined **solely** by the recorded channel
$c_i$, **never consulting whether the underlying stored pair also sits
in the opposite channel**". The previously-committed L-disjunct
(writing-mirror OR-of-channels) was an over-cautious patch that does
NOT match the addition.

Consequence: the addition's clause (c) explicitly enumerates the
divergence from the literal stored-pair test at BOTH directed
self-loop steps AND writing-mirror walk-steps. The earlier deviation
register entry `collider_side_aware_at_self_loops` was scoped only to
self-loops; with the OR-of-channels fix removed, the writing-mirror
divergence is now also a real one.

`lake build` is clean (8288 jobs; only pre-existing lint warnings in
`SigmaSeparationSymmetric.lean`).

## What needs updating

1. **Canonical tex** `tex/def_3_15_CollidersAndNon.tex` — its
   "Encoding note" paragraph (lines 47-49) currently asserts an
   OR-of-channels convention that "coincides pointwise with the literal
   stored-pair test at every non-self-loop walk-step". This is now
   wrong (per addition clause (c) writing-mirror walk-steps also
   diverge). The "Treatment of directed self-loops" paragraph and the
   "Classification" paragraph stay structurally OK.

2. **Design-choice comments in `CollidersAndNon.lean`** above
   `refactor_HeadAtTarget`, `refactor_HeadAtSource`, `refactor_IsCollider`
   — currently describe the OR-of-channels writing-mirror union
   semantics with the L-disjunct as load-bearing. With the L-disjunct
   gone, these comments are stale; need rewrite to motivate the
   constructor-tag-only reading + the addition's clause (c) deviation
   scope at both self-loops and writing-mirror walk-steps.

3. **Deviation register** `leanification/deviations.json` entry
   `collider_side_aware_at_self_loops` — `breaks` / `preserves` /
   `at_risk_pattern` describe scope as self-loops only; with the
   broader scope per addition clause (c), the entry should be updated
   (or superseded by a broader entry) to also mention writing-mirror
   walk-steps.

## Plan (re-solve)

1. **(this turn)** `formalize_definition_in_tex` — rewrite Encoding
   note paragraph to drop OR-of-channels; clarify that the side-aware
   reading is per addition (b) and the divergence from the literal
   stored-pair test is per addition (c) at BOTH self-loops and
   writing-mirror walk-steps. Other paragraphs likely unchanged.
2. `verify_tex_statement_only` (structural).
3. `verify_tex_statement_equivalence` (semantic vs LN + addition).
4. `add_design_choice_comments` — rewrite comment blocks above the
   three Lean declarations to match the corrected semantic. Drop
   OR-of-channels / writing-mirror union language; describe pure
   constructor-tag reading; document the wider divergence scope.
5. `review_design` + `verify_equivalence`.
6. `verify_equivalence_strict` (recommended; this def introduces new
   predicates).
7. (If strict-gate FAILs with writing-mirror divergence) update the
   deviation register entry via `accept_deviation` with the broader
   scope, then re-emit `solved`.
8. `solved` → orchestrator runs verify_row_solved + sorry-check +
   strict-gate.

## Things to remember

- `IsInto` (the helper from cdmg_typed_edges) is NOT touched by this
  refactor — leave it alone. Its current callers (`Walk.IsCollider`
  ORIGINAL, plus `SigmaSeparationSymmetric` / `AcyclicNonCollidersBlockable`
  via the original-IsCollider chain) keep using it during the
  refactor window. After Phase 7 cleanup, the ORIGINAL `IsCollider`
  is deleted and `IsInto` becomes orphaned; if the cleanup script
  doesn't surface it as a stray decl, we should consider wrapping it
  in a DELETE block in a follow-up turn.
- `Walk.IsNonCollider` ORIGINAL + `refactor_IsNonCollider` REPLACEMENT
  pair stays intact — only the reference to `IsCollider` changes
  shape; the def itself does not need re-work.
- All comments that say "writing-mirror union fix" / "OR-of-channels"
  / "the L-disjunct re-fires" are STALE and should be deleted /
  replaced.

## Run summary log
_(append per-run summaries if the row is paused and resumed)_
