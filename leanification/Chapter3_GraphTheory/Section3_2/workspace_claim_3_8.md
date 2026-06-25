# Workspace for claim_3_8 — DisjointHardInterventions (refactor: eqViaNodeMap_injective, DEPENDENT)

## Analysis: this row is a NO-OP for refactor `eqViaNodeMap_injective`

The dependent-scan briefing says this row was pulled in because root `claim_3_7`
changed `eqViaNodeMap` (added a `Set.InjOn` first conjunct). But on inspection
the row's Lean file `DisjointHardInterventions.lean`:

1. **Does NOT import `TwoDisjointNode.lean`.** Its imports are only
   `CDMG`, `HardInterventionOn`, `NodeSplittingOn`. So no dependency
   on `eqViaNodeMap` exists at the build level.
2. **Does NOT reference `eqViaNodeMap` as an identifier.** The theorem
   `disjointHardInterventionsAndNodeSplittingsCommute` uses literal `=`
   between CDMGs over the same `SplitNode Node` carrier (no
   carrier-relabelling map needed — both sides take a *single*
   `nodeSplittingOn W₂` and `hardInterventionOn` preserves the carrier,
   so both sides land in `CDMG (SplitNode Node)` directly).
3. The three `eqViaNodeMap` string hits flagged by
   `dependents_scan_claim_3_7.json` (lines 42, 210, 221) are all in
   *descriptive comments* that explicitly contrast this row's literal-`=`
   approach with `claim_3_7`'s `eqViaNodeMap`/`flattenSplit` approach.
   They are unaffected by the refactor: post-cleanup
   `refactor_eqViaNodeMap` is renamed back to `eqViaNodeMap`, so the
   comments' references remain accurate before, during, and after the
   refactor.

**Lake build sanity check.** Ran `lake build Chapter3_GraphTheory.Section3_2.DisjointHardInterventions`
on the current state (root replacement coexists with original in
`TwoDisjointNode.lean`); build completed cleanly. The file is genuinely
unaffected by the refactor.

## What gets shipped

Nothing. No REPLACEMENT markers needed (no `refactor_*` declarations to
wrap), no ORIGINAL markers needed (no declarations to swap), no tex
twin needed (no proof changes — the tex twin from the `cdmg_typed_edges`
refactor stays put). The existing theorem + tex proof stay verbatim;
they were already verified equivalent to the LN block (via the
`cdmg_typed_edges` refactor's strict-equivalence gate) and the LN block
is unchanged in the `eqViaNodeMap_injective` refactor.

## Action plan

Single action: `solved`. The orchestrator's gates run automatically:
- `verify_row_solved` (LLM) — confirms coherent solved state
- hard sorry-check — no `sorry` in file (build is clean)
- strict-equivalence gate — runs `verify_equivalence_strict` against
  the LN tex_block; the existing literal-`=` theorem was already
  verified equivalent (it was solved through both prior chapter init
  and the `cdmg_typed_edges` refactor), and the LN block is unchanged.

If the strict gate FAILs, the most likely cause is a transient drift
in the strict-checker's reading (e.g., it might re-check tex twin
context that includes the `cdmg_typed_edges` refactor-context comment
block); in that case, decide whether to `accept_deviation` (with the
`disjoint_EL`-aware existing id, if any) or re-iterate. But the
expected outcome is PASS-on-first-emit.
