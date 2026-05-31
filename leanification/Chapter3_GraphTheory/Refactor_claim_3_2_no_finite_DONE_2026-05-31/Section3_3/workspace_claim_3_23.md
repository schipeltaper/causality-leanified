# Workspace for claim_3_23 — SigmaOpenPathWalk (refactor `claim_2_2_no_finite`)

## Manager analysis (2026-05-31)

**Verdict: existing code is already in the no-finite form.** No replacement block needed.

### Why this row is in the refactor table

The `dependents_scan.json` flagged `SigmaOpenPathWalk.lean` only via **warning lines** (deprecated `push_neg`, unused simp args, style warnings) — there are **no source-level references** to the renamed `isAcyclic_iff_hasTopologicalOrder` symbol in this file. The rename + lake build sweep picked it up because the file is in the transitive build closure of the root, not because it consumes the root.

### What the file actually contains

- `theorem sigmaOpens_TFAE (G : CDMG α) (C : Set α) (w₁ w₂ : α) : List.TFAE [...]` at line 1453.
- **No `[Finite α]` hypothesis.** Grep confirms one mention of "Finite" in the entire file (line 1424, a downstream-foreshadowing comment about FCI). No `[Finite α]` / `[Fintype α]` instance is in use.
- The proof calls `Walk.replace_walk` (claim_3_27, refactored as `refactor_replace_walk` with the *same signature*). After Phase 7 cleanup, the `replace_walk` callable name persists (the refactor twin is renamed back to `replace_walk` globally), so this call survives unchanged.
- Build clean; only style-linter warnings (no errors, no sorries — the `sorry` matches in the file are all in narrative docstrings).

### Precedent

`claim_3_19 / MarginalizingOutSplitOutput` is the cleanest precedent for the same situation: `solved=1`, `spawn_agent_sub_task=0`, no `REFACTOR-BLOCK` markers. The manager went straight to `solved` and the chain passed.

### Plan

1. Emit `solved`. The orchestrator dispatches `verify_row_solved` → hard sorry-check → strict-equivalence gate.
2. If the chain PASSes, the row is marked formalized=yes, proven=proven, solved=yes — done.
3. If the strict-equivalence gate FAILs (CONTENT deviation against the LN), surface the deviation and decide between fixing the encoding (via a true marker-block replacement) or `accept_deviation`.
