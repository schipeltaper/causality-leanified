# Workspace: claim_3_12 (HardInterventionNodeSplitOrder) — refactor `claim_3_2_no_finite`

## Context summary

- **Row**: `claim_3_12`, title `HardInterventionNodeSplitOrder`, claim, section 3.2 (type `remark`).
- **LN block** (`graphs.tex` ~lines 702–709): narrative Remark walking
  through what happens when `W₁ ∩ W₂ ⊆ V` is non-empty in
  claim_3_11's hard-intervention-and-SWIG setup. Three operational
  scenarios + a punchline corollary about non-equality of post-SWIG
  hard interventions on a shared `w`.
- **Refactor goal (table-wide)**: `claim_3_2_no_finite` removes the
  `[Finite α]` baggage from the root `isAcyclic_iff_hasTopologicalOrder`
  iff. Downstream consumers that used to thread `[Finite α]` through
  their statements / proofs get to drop it.

## Key finding: this row is a **no-op refactor**

The existing
`leanification/Chapter3_GraphTheory/Section3_2/HardInterventionNodeSplitOrder.lean`
declares **four theorems**:

1. `swig_precondition_fails_on_intersection` — pure set-theoretic
   precondition-failure observation. No `[Finite α]`. Does not invoke
   acyclicity or topological-order anywhere.
2. `swig_hardInterventionOn_inputs_eq_self` — bit-for-bit CDMG equality
   via the `mk_eq_of_data` four-field check. No `[Finite α]`. No call
   to acyclicity / topological order.
3. `swig_hardInterventionOn_outputs_V` — `V`-projection identity via
   `Set.image_diff Sum.inl_injective` + the two `@[simp]` `_V`
   projections. No `[Finite α]`. No acyclicity.
4. `swig_then_hardInterventionOn_depends_on_copy_choice` — singleton
   punchline corollary combining (B1) + (B2). No `[Finite α]`. No
   acyclicity.

A targeted grep over the file (and its companion tex proof) confirmed
zero references to `claim_3_2`, `isAcyclic_iff_hasTopologicalOrder`,
`HasTopologicalOrder`, `IsTopologicalOrder`, `IsAcyclic`, or `Finite`.

The file's two imports are `HardInterventionOn.lean` and
`NodeSplittingHard.lean`; neither of those references claim_3_2 either.
The row was almost certainly pulled into the refactor table by the
`find_dependents.py` transitive build-cascade pass (renaming
`isAcyclic_iff_hasTopologicalOrder` would break the build of some
file far up the import graph, which then cascades down to anything
that transitively imports it).

## Why I'm going straight to `solved`

- The **original** chapter row (in `Chapter3_GraphTheory/data.json`)
  was already `solved=yes, formalized=yes, proven=proven` from a
  prior solve. The four theorems passed every gate at that time:
  `review_design`, `verify_equivalence`, `verify_tex_proof`,
  `simplify_proof`, `verify_row_solved`.
- The Lean file is **unchanged** since that solve. `lake build` from
  the repo root reports `Build completed successfully (979 jobs)`.
- The tex proof
  `tex/claim_3_12_proof_HardInterventionNodeSplitOrder.tex` exists,
  is filled in (231 lines, four-scenario structure mirroring the
  Lean), and previously passed `verify_tex_proof`.
- No `[Finite α]`, no claim_3_2 call → nothing to refactor. Adding
  marker blocks + a `refactor_`-prefixed twin would duplicate the
  whole file mechanically for zero downstream change; cleanup would
  just delete the original and rename the twin to the same name.
  Precedent from claim_3_6 (SplitTopologicalOrder): only the
  declarations whose proof genuinely changed got marker blocks
  (Part B); Part A and the `splitOrder` helper were left unwrapped.

## Cleanup script behaviour for this row

Confirmed by reading `extras/apply_refactor_cleanup.py`:

- Phase 7a (Lean marker swap): files **without** any
  `REFACTOR-BLOCK-*` markers are silently no-ops (line 451–453: if
  `new == old`, logged as `no-op` and skipped).
- Phase 7b (`lake build`): unaffected — the file already builds.
- Phase 7c (tex twin swap): if the
  `tex/refactor_<ref>_proof_<title>.tex` twin is missing, the script
  WARNs but does not fail (line 526–531: `n_missing += 1`).
- Phase 7d (data.json sync): proceeds normally; `proven` stays
  `proven`, `last_refactored_at` gets stamped.

So a no-op refactor for this row is mechanically supported by the
pipeline.

## What the strict-equivalence solved-gate will see

The strict checker will compare the four theorems against the LN's
narrative Remark. The Remark is not a clean equality — the
LN-faithful encoding *had* to decompose it into the four observations
(Scenario A: precondition failure for "HI then SWIG"; B1: input-copy
HI is a no-op; B2: output-copy HI shrinks V; Punchline: B1 ≠ B2 on
the singleton scenario). The file's design-choice comment blocks
already document this decomposition extensively (it is the second-
sentence of the file's docstring: "## Why this is *four*
observations, not one `Eq`"). If the strict gate raises this as a
**PRESENTATION** deviation, it's the correct one and the design is
already justified.

If the strict gate raises a **CONTENT** deviation I haven't
anticipated, I'll iterate from feedback.

## Action plan

1. (this turn) Emit `solved`. The orchestrator runs:
   - `verify_row_solved` — expected PASS (file is in solved state).
   - hard sorry-check — expected PASS (file-grep shows no `sorry`,
     `lake build` is clean).
   - strict-equivalence gate — expected PASS (LN-faithful
     four-scenario decomposition, already documented).
2. (on PASS) Row marked `solved=yes`, `proven=proven`,
   `last_refactored_at` set at Phase 7 cleanup time.
3. (on FAIL) Iterate from the gate's feedback. The most likely failure
   mode is a strict-gate complaint about a CONTENT deviation I have not
   anticipated. If that happens, decide between `accept_deviation`
   (register the deviation), re-encoding (re-dispatch the formalizer),
   or `refactor` of an upstream def.

## Key file paths

- Lean (already filled, do not touch unless gate flags an issue):
  `leanification/Chapter3_GraphTheory/Section3_2/HardInterventionNodeSplitOrder.lean`
- Tex proof (already filled, do not touch unless gate flags an issue):
  `leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_12_proof_HardInterventionNodeSplitOrder.tex`
- LN source (Remark):
  `lecture-notes/lecture_notes/graphs.tex` ~lines 702–709 (block
  immediately following the claim_3_11 proof at 672–700).
- Sibling refactor row precedent:
  `leanification/Chapter3_GraphTheory/Section3_2/SplitTopologicalOrder.lean`
  (claim_3_6, just solved in this same refactor; Part A had no
  refactor work, only Part B was wrapped in markers).
