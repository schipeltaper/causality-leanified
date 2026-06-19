# Workspace for def_3_17 — SigmaBlockedWalks

This file is the manager's scratchpad for this row. Use it for:

- The plan (output of `make_plan` worker)
- A running list of what has been tried and why it didn't work
- Notes for the next manager (if you `new_manager`-handoff or
  the run ends and a future invocation picks this row up again)

It is YAML-untyped markdown — feel free to add sections.

## Refactor port status (def_3_17, cdmg_typed_edges)

- Role: DEPENDENT, pulled in by roots `def_3_1`, `def_3_4`.
- Math unchanged; only upstream encoding (typed `refactor_WalkStep`, `Sym2`-based `L`) changes.
- Turn 1: dispatched `formalize_definition_in_lean` worker.
  - Result: port complete, `lake build` clean.
  - Markers in `SigmaBlockedWalks.lean`:
    - ORIGINAL: `IsSigmaOpenGiven` (lines 227/235), `IsSigmaBlockedGiven` (lines 304/312).
    - New `namespace Causality / refactor_CDMG / refactor_Walk` section from line 320.
    - REPLACEMENT: `IsSigmaOpenGiven` (line 450, `refactor_IsSigmaOpenGiven`), `IsSigmaBlockedGiven` (line 525, `refactor_IsSigmaBlockedGiven`).
    - Each REPLACEMENT body wrapped with `-- def_3_17 -- start/end statement`.
    - Variable lines wrapped with `-- def_3_17 --- start/end helper`.
  - Mechanical retargets used: `Walk → refactor_Walk`, `.vertices → .refactor_vertices`, `.IsCollider → .refactor_IsCollider`, `.IsBlockableNonCollider → .refactor_IsBlockableNonCollider`, `G.AncSet → G.refactor_AncSet`.
- Turn 2: `verify_equivalence` PASSED. The two REPLACEMENT blocks are byte-identical to ORIGINALs modulo mechanical `refactor_` retargets on five upstream symbols.
- Turn 3: `add_design_choice_comments` completed — added constructor-choice-invariance / Sym2-encoding rationale to both REPLACEMENT block comments.
- Skipped `review_design` and tex-statement steps: refactor DEPENDENT row with unchanged math; original row already passed both, and def refactors have no tex twin.
- Turn 4: `solved` FAILED at the strict-equivalence gate (CONTENT, root_cause=local). Strict checker flagged the bare `C : Set Node` on both REPLACEMENT signatures: the LN explicitly states `C ⊆ J ∪ V` as a typing premise, and the design-comment defence (out-of-graph c gives empty Anc; vertices live in J ∪ V) "documents but doesn't undo" the looseness.
- Chapter-wide audit:
  - def_3_18 (sibling refactor row, also `solved=no`) ALREADY uses the LN-faithful pattern: explicit `hA, hB, hC : ⊆ ↑G.J ∪ ↑G.V` on the signature, `set_option linter.unusedVariables false in` immediately before, and matching design comment about "silent-admission leak". Pattern is also documented as the convention for `HardInterventionOn`, `NodeSplittingOn`, `NodeSplittingHard`, `AddingInterventionNodes`, `MarginalizationAndIntervention`.
  - Only consumer of `(refactor_)IsSigmaBlockedGiven` in the repo is def_3_18 itself (line 304 of `ISigmaSeparation.lean`), which already has `hC` in scope. The original (pre-refactor) `IsSigmaBlockedGiven` will be deleted at Phase 7 cleanup, and def_3_18's pending REPLACEMENT block will pass `hC` through naturally.
- Decision: FIX the encoding (do not `accept_deviation`). Add `(hC : C ⊆ ↑G.J ∪ ↑G.V)` to both refactor REPLACEMENT signatures, prefix each with `set_option linter.unusedVariables false in`, and update the design-choice comment that currently says "no `C ⊆ J ∪ V` hypothesis is needed at the def site" to instead document the LN-faithful tightening.
- Turn 5: dispatched focused `spawn_agent_sub_task` worker to perform the tightening, then re-emit `solved` for the strict gate to re-run.
- Turn 5 result: worker added `(hC : C ⊆ ↑G.J ∪ ↑G.V)` to both REPLACEMENT signatures (lines 572-573 for σ-open, 720-721 for σ-blocked), each prefixed with `set_option linter.unusedVariables false in`. Design-choice comments updated to document `hC` (see comment blocks around lines 540-548 and 709-716). `lake build` clean. Pattern now matches `def_3_18`'s `IsISigmaSeparated` chapter-wide convention.
- Turn 6: re-emit `solved` → strict gate re-runs on the tightened signatures.
