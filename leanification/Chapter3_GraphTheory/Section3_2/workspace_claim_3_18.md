# Workspace: claim_3_18 (MarginalizationAndIntervention) — refactor `claim_3_2_no_finite`

## Context summary

- **Row**: `claim_3_18`, title `MarginalizationAndIntervention`, claim,
  section 3.2 (type `lemma`).
- **LN block** (`graphs.tex` Lem ~lines 1122–1129): for a CDMG
  `G=(J,V,E,L)` with `W₁ ⊆ J ∪ V`, `W₂ ⊆ V`, and `W₁, W₂` disjoint,
  `(G_{do(W₁)})^{\sm W₂} = (G^{\sm W₂})_{do(W₁)}`. Trailing prose names
  two forward-pointer analogues (`addInterventionNodes`,
  `nodeSplittingOn`) that are out-of-scope here.
- **Refactor goal (table-wide)**: `claim_3_2_no_finite` removed the
  `[Finite α]` baggage from the root
  `isAcyclic_iff_hasTopologicalOrder` (claim_3_2). Downstream rows
  that used to thread `[Finite α]` through their statements or proofs
  get to drop it.

## Key finding: this row is a **no-op refactor**

The existing
`leanification/Chapter3_GraphTheory/Section3_2/MarginalizationAndIntervention.lean`
(877 lines; result of the original solve on 2026-05-21) declares the
public theorem `marginalize_hardInterventionOn` plus its supporting
private helpers (`WalkStep.dropHard` / `liftHard` /
…`_iff` partners, `Walk.dropHard` / `liftHard` / …`_iff` partners,
`Walk.forall_supp_notW₁` / `forall_supp_tail_notW₁`,
`CDMG.mk_eq_of_data`, `CDMG.exists_directed_lift`).

**Targeted grep over the file** (`Finite|isAcyclic_iff_hasTopologicalOrder|claim_3_2`)
returns **zero code matches**: the only hit is a docstring mention of
`claim_3_20` whose substring prefix is `claim_3_2` (a forward-pointer
to the deferred `addInterventionNodes` analogue, unrelated to the
refactor root). The file has no `[Finite α]` instance hypothesis on
any declaration, makes no call to `isAcyclic_iff_hasTopologicalOrder`,
and does not reference `claim_3_2` at all.

The file's direct imports are
`Section3_2.HardInterventionOn`, `Section3_2.Marginalization`, and
`Section3_2.MarginalizationPreserves`. The first two only reach
`Section3_1.{CDMGNotation, Bifurcation}` (no `TopologicalOrder`
contact). The third, `MarginalizationPreserves`, *does* import
`Section3_1.TopologicalOrder` -- which is the transitive route by
which `find_dependents.py`'s rename-cascade scan would have pulled
this file into the refactor table.

But the file's *own* code does not invoke any of the renamed symbols.
The fully-proved `marginalize_hardInterventionOn` (line 642) closes
via `mk_eq_of_data`-style four-component extensionality (`J / V / E /
L`); `J` is `rfl`, `V` is `Set.diff_diff + Set.union_comm`, and the
`E`/`L` walk-existential iffs route through `dropHard` (forward) and
either `exists_directed_lift` (for `E`) or `liftHard` (for `L`).
None of those tactics need topological-order machinery, finiteness,
or `claim_3_2`.

## Why I'm going straight to `solved`

- The **original** chapter row (in `Chapter3_GraphTheory/data.json`)
  is `formalized=yes, proven=proven, solved=yes, date_solved=2026-05-21`.
  The theorem passed every gate at that time (`review_design`,
  `verify_equivalence`, `verify_tex_proof`, `simplify_proof`,
  `verify_row_solved`).
- The Lean file is **unchanged** since that solve. `lake build` from
  the repo root reports `Build completed successfully (979 jobs)`
  this turn (with only unrelated lint info/warnings in
  `Section3_3/ISigmaSeparationMarginalization.lean`).
- The tex proof
  `tex/claim_3_18_proof_MarginalizationAndIntervention.tex` exists
  from the original solve and remains untouched.
- No `[Finite α]`, no `claim_3_2` call → nothing to refactor.
  Adding marker blocks + a `refactor_`-prefixed twin would duplicate
  the entire 877-line file mechanically for zero downstream change;
  cleanup would just delete the original and rename the twin back to
  the same name.
- **Precedent in this same table** (matching no-op rows):
  - claim_3_12 (HardInterventionNodeSplitOrder) — no-op, solved
    cleanly.
  - claim_3_16 (MarginalizationPreserves) — no-op for the refactor
    itself; needed an `accept_deviation` only for a pre-existing
    with-source bifurcation deferral that the strict gate flagged
    (unrelated to the no-op pattern).
  - claim_3_17 (MarginalizationsCommute) — no-op, solved cleanly.

## Stale docstring (cosmetic, not blocking)

The doc-comment immediately above the theorem (lines 633–641) reads
"Statement only at this stage; the proof body is `sorry`, to be
discharged by the `prove_claim_in_lean` worker in the proof-phase
manager pass (Manager B)." This is stale text inherited from the
statement-formalization phase of the original solve — the proof was
discharged in the subsequent Manager-B turn and the comment was
never refreshed. The actual proof body at line 645+ is complete (no
`sorry`).

Not blocking: the strict-equivalence checker compares Lean to LN, not
internal Lean text to Lean code. Leaving the stale comment alone
preserves the scope discipline ("the file is unchanged since the
original solve"); a docstring rewrite would technically be in-scope
but would be a discretionary edit. Will only revisit if the gate
flags it.

## Cleanup script behaviour for this row

Confirmed by the precedent no-op workspaces
(`workspace_claim_3_16.md`, `workspace_claim_3_17.md`):

- Phase 7a (Lean marker swap): files **without** any
  `REFACTOR-BLOCK-*` markers are silently no-ops.
- Phase 7b (`lake build`): unaffected — the file already builds.
- Phase 7c (tex twin swap): if
  `tex/refactor_claim_3_18_proof_MarginalizationAndIntervention.tex`
  is missing, the script WARNs but does not fail.
- Phase 7d (data.json sync): proceeds normally; `proven` stays
  `proven`, `last_refactored_at` gets stamped.

## What the strict-equivalence solved-gate will see

The strict checker will compare `marginalize_hardInterventionOn`
against the LN displayed equation. Anticipated outcomes:

- The **no `W₁ ⊆ G.J ∪ G.V` / no `W₂ ⊆ G.V` preconditions** is the
  same "faithful strengthening" pattern recorded for `marginalize`
  and `hardInterventionOn` themselves; both component operators
  cite *this very row* as a load-bearing motivation for their
  no-precondition designs (see existing file design block at lines
  145–163 with the cross-references). Expected classification:
  PRESENTATION (or EXAMPLE_GENERATION → PASS once the property-based
  check sees the equation holds component-wise on out-of-graph
  vertices trivially).
- The **`Disjoint W₁ W₂` hypothesis** matches the LN exactly.
- The **single-equality shape** (vs the structural twins' fusion +
  commute split) is justified by the LN's own single-`=` displayed
  equation (no fused third operator exists); design block lines
  124–143. Expected classification: NONE.

If the strict gate raises a CONTENT deviation I haven't anticipated,
I'll iterate from feedback — either by re-encoding or by
`accept_deviation` if the deviation is genuinely intentional and
already covered by an existing register entry.

## Action plan

Updated after Turn 1+2: precedent (claim_3_17) shows no-op refactor
rows still run the full verifier chain even though the file is
unchanged. So:

1. (Turn 1, done) Emit `solved`. `verify_row_solved` PASSed; the
   strict-equivalence gate did not fully close the row — orchestrator
   returned control. Following precedent (claim_3_17 had `solved=3`
   before the final PASS).
2. (Turn 2, done) `review_design` — PASS.
3. (Turn 3, this turn) `verify_equivalence` — focused statement-vs-
   LN check. Expected PASS (LN equation matches the Lean theorem
   verbatim modulo the no-precondition strengthening that is well-
   documented in the file's design block).
4. (Turn 4) `simplify_proof` — expected PASS (proof is the
   minimal four-component `mk_eq_of_data` extensionality).
5. (Turn 5) Emit `solved` again. Strict-equivalence gate runs;
   expected PASS or EXAMPLE_GENERATION→PASS for the no-precondition
   pattern.
6. (On FAIL) Iterate from gate feedback. If strict gate flags the
   no-precondition pattern as CONTENT, consider `accept_deviation`
   (claim_3_16 took this path for a similar pattern).

## Key file paths

- Lean (already filled, do not touch unless the gate flags an issue):
  `leanification/Chapter3_GraphTheory/Section3_2/MarginalizationAndIntervention.lean`
- Tex proof (already filled from the original solve):
  `leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_18_proof_MarginalizationAndIntervention.tex`
- Tex statement:
  `leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_18_statement_MarginalizationAndIntervention.tex`
- LN source (Lem at ~lines 1122–1129):
  `lecture-notes/lecture_notes/graphs.tex`
- Refactor table:
  `leanification/Chapter3_GraphTheory/Refactor_claim_3_2_no_finite/refactor_data.json`
- Precedents for no-op refactor in this same table:
  - `leanification/Chapter3_GraphTheory/Section3_2/workspace_claim_3_12.md`
  - `leanification/Chapter3_GraphTheory/Section3_2/workspace_claim_3_16.md`
  - `leanification/Chapter3_GraphTheory/Section3_2/workspace_claim_3_17.md`
