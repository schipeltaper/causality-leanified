# Workspace for claim_3_11 — DisjointHardInterventions (refactor: eqViaNodeMap_injective, DEPENDENT)

## Analysis: this row is a NO-OP for refactor `eqViaNodeMap_injective`

The dependent-scan briefing says this row was pulled in because root `claim_3_7`
changed `eqViaNodeMap` (added a `Set.InjOn` first conjunct). But on inspection
the row's Lean file `DisjointHardInterventionsSwig.lean`:

1. **Does NOT import `TwoDisjointNode.lean`.** Its imports are
   `CDMG`, `CDMGTypes`, `HardInterventionOn`, `AcyclicPreservedUnderDo`,
   `NodeSplittingOn`, `NodeSplittingHard`. So no dependency on
   `eqViaNodeMap` exists at the build level.
2. **Does NOT reference `eqViaNodeMap` / `flattenSplit` /
   `twoDisjointNodeSplittingsCommute` as identifiers.** The theorem
   `disjointHardInterventionsAndNodeSplittingHardsCommute` uses
   literal `=` between CDMGs over the same `SplitNode Node` carrier
   (the SWIG operator `nodeSplittingHard` lifts the carrier once,
   `hardInterventionOn` preserves the carrier, so both iteration
   orders land in `CDMG (SplitNode Node)` directly — no carrier-
   relabelling map needed).  The file's docstring (lines 47-54)
   explicitly calls this out: "No `eqViaNodeMap` / `flattenSplit`
   workaround is needed (contrast with `claim_3_10`'s iterated-SWIG
   case ...)."
3. The four `eqViaNodeMap` / `flattenSplit` string hits flagged by
   `dependents_scan_claim_3_7.json` for this file (lines 50, 367, 381)
   are all in *descriptive comments* that explicitly contrast this
   row's literal-`=` approach with `claim_3_7`'s `eqViaNodeMap` /
   `flattenSplit` approach.  They are unaffected by the refactor:
   post-cleanup `refactor_eqViaNodeMap` is renamed back to
   `eqViaNodeMap`, so the comments' references remain accurate before,
   during, and after the refactor.

**Lake build sanity check.** Ran `lake build
Chapter3_GraphTheory.Section3_2.DisjointHardInterventionsSwig` on the
current state (root replacement coexists with original in
`TwoDisjointNode.lean`); build completed cleanly (8260 jobs). The file
is genuinely unaffected by the refactor.

**Direct precedent.** Sibling row `claim_3_8`
(`disjointHardInterventionsAndNodeSplittingsCommute`, the spl analog
of this row) is in the exact same position — also pulled in only via
comment-mentions of `eqViaNodeMap` / `flattenSplit` — and was solved
in 1 turn via `solved` with zero Lean changes (commit a64d714).  This
row is its SWIG twin and faces the identical no-op scenario.

## What gets shipped

Nothing. No REPLACEMENT markers needed (no `refactor_*` declarations
to wrap), no ORIGINAL markers needed (no declarations to swap), no
tex twin needed (no proof changes — the tex twin from the
`cdmg_typed_edges` refactor stays put).  The existing theorem + tex
proof stay verbatim; they were already verified equivalent to the LN
block via the `cdmg_typed_edges` refactor's strict-equivalence gate
and the LN block is unchanged in the `eqViaNodeMap_injective`
refactor.

## Action plan

Single action: `solved`.  The orchestrator's gates run automatically:
- `verify_row_solved` (LLM) — confirms coherent solved state
- hard sorry-check — no `sorry` in file (build is clean)
- strict-equivalence gate — runs `verify_equivalence_strict` against
  the LN tex_block; the existing literal-`=` theorem was already
  verified equivalent (it was solved through both prior chapter init
  and the `cdmg_typed_edges` refactor), and the LN block is
  unchanged.

If the strict gate FAILs unexpectedly, the most likely cause is
transient drift in the strict-checker's reading; in that case,
inspect the verdict and either `accept_deviation` (if a registered
deviation explains it) or re-iterate.  Expected outcome: PASS on
first emit.
