# Workspace for claim_3_18 — MarginalizationAndIntervention (refactor: eqViaNodeMap_injective, DEPENDENT)

## Analysis: this row is a NO-OP for refactor `eqViaNodeMap_injective`

The dependent-scan briefing says this row was pulled in because root `claim_3_7`
changed `eqViaNodeMap` (added a `Set.InjOn` first conjunct). But on inspection
the row's Lean file `MarginalizationAndIntervention.lean`:

1. **Does NOT import `TwoDisjointNode.lean`.** Its imports are
   `CDMG`, `MarginalizationAK`, `HardInterventionOn`, `NodeSplittingOn`,
   `ExtendingCDMGsWith`, `MargPreservesAncestors`. None of these
   transitively imports `TwoDisjointNode.lean`. So no dependency on
   `eqViaNodeMap` exists at the build level.
2. **Does NOT reference `eqViaNodeMap` / `flattenSplit` /
   `twoDisjointNodeSplittingsCommute` as identifiers.** The three
   main theorems
   - `marginalize_hardInterventionOn_comm` (line 734)
   - `marginalize_extendingCDMGsWith_comm` (line 1708)
   - `marginalize_nodeSplittingOn_comm` (line 4786)
   each state literal `=` between two CDMGs in the SAME carrier
   (`CDMG Node` for part i, `CDMG (IntExtNode Node)` for part ii,
   `CDMG (SplitNode Node)` for part iii). Each side of each equation
   lives in the same carrier — no carrier-relabelling map needed.
   The file's docstring (line 40) explicitly calls this out:
   "each side of each equation lives in the same carrier (no
   `eqViaNodeMap` workaround needed; ...)".
3. The single `eqViaNodeMap` string hit flagged by
   `dependents_scan_claim_3_7.json` for this file (line 40) is in
   that *descriptive comment* explicitly contrasting this row's
   literal-`=` approach with `claim_3_7`'s `eqViaNodeMap` approach.
   It is unaffected by the refactor: post-cleanup
   `refactor_eqViaNodeMap` is renamed back to `eqViaNodeMap`, so the
   comment's reference remains accurate before, during, and after the
   refactor.

**Lake build sanity check.** Ran `lake build
Chapter3_GraphTheory.Section3_2.MarginalizationAndIntervention` on the
current refactor branch (root replacement coexists with original in
`TwoDisjointNode.lean`); build completed cleanly (8260 jobs, no
errors — only pre-existing style warnings about heartbeat comments
and long lines, all unrelated to the refactor). The file is
genuinely unaffected.

**Direct precedent.** Sibling row `claim_3_11`
(`DisjointHardInterventions`, SWIG analog) was in the exact same
position — also pulled in only via comment-mentions of
`eqViaNodeMap` — and was solved in 1 turn via `solved` with zero
Lean changes (commit 84a8a6c). The earlier `claim_3_8` sibling was
solved the same way (commit a64d714). Both have NO
`REFACTOR-BLOCK-*` markers in their files. This row faces the
identical no-op scenario.

## What gets shipped

Nothing. No REPLACEMENT markers needed (no `refactor_*` declarations
to wrap), no ORIGINAL markers needed (no declarations to swap), no
tex twin needed (no proof changes — the tex proof at
`tex/claim_3_18_proof_MarginalizationAndIntervention.tex` stays
verbatim from the `cdmg_typed_edges` refactor's solve). The existing
three theorems + tex proof were already verified equivalent to the LN
block via the `cdmg_typed_edges` refactor's strict-equivalence gate
and the LN block is unchanged in the `eqViaNodeMap_injective`
refactor.

## Action plan

Single action: `solved`. The orchestrator's gates run automatically:
- `verify_row_solved` (LLM) — confirms coherent solved state.
- hard sorry-check — no `sorry` in file (build is clean).
- strict-equivalence gate — runs `verify_equivalence_strict` against
  the LN tex_block; the three theorems were already verified
  equivalent via the prior chapter init + `cdmg_typed_edges` refactor,
  and the LN block is unchanged. Expected: PASS.

If the strict gate FAILs unexpectedly, the most likely cause is
transient drift in the strict-checker's reading; in that case,
inspect the verdict and either `accept_deviation` (if a registered
deviation explains it) or re-iterate. Expected outcome: PASS on
first emit, matching `claim_3_8` and `claim_3_11`.
