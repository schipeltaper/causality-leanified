# Workspace: claim_3_19 (MarginalizingOutThe) — refactor `claim_3_2_no_finite`

## Context summary

- **Row**: `claim_3_19`, title `MarginalizingOutThe`, claim, section 3.2
  (type `lemma`).
- **LN block** (`graphs.tex` Lem ~lines 1167–1175): for a CDMG
  `G=(J,V,E,L)` and `W ⊆ V`, `G_{do(W)} ≅ (G_{swig(W)})^{∖ W^o}` with
  identification `w ↦ w^i`.
- **Refactor goal (table-wide)**: `claim_3_2_no_finite` removes the
  `[Finite α]` baggage from the root
  `isAcyclic_iff_hasTopologicalOrder` (claim_3_2). Downstream consumers
  that used to thread `[Finite α]` through their statements or proofs
  get to drop it.

## Key finding: this row is a **no-op refactor**

The existing
`leanification/Chapter3_GraphTheory/Section3_2/MarginalizingOutSplitOutput.lean`
(765 lines; result of the original solve on 2026-05-21) declares the
`CDMGNodeIso` local helper structure and the main
`noncomputable def hardInterventionOn_nodeIso_swig_marginalize_outputs`,
backed by four private proof helpers (`split1_injective`,
`no_swig_edge_source_in_inlW`, `second_vertex_mem_interior`,
`swig_directed_walk_interior_in_inlW_imp_edge`,
`swig_bifurcation_interior_in_inlW_imp_L_or_revE`).

**Targeted grep over the file** (`Finite|isAcyclic_iff_hasTopologicalOrder|claim_3_2[^0-9]|Fintype|DecidableEq`)
returns **zero matches**. The file has no `[Finite α]` instance
hypothesis on any declaration, makes no call to
`isAcyclic_iff_hasTopologicalOrder`, and does not reference claim_3_2
at all.

The file's direct imports are
`Section3_2.HardInterventionOn`, `Section3_2.Marginalization`, and
`Section3_2.NodeSplittingHard`. None of these introduce a path
through `TopologicalOrder` into the file's own declarations; the
file's code is purely about CDMG structure manipulation.

## Why this row was pulled into the refactor table

Same mechanism as claim_3_12, claim_3_16, claim_3_17, claim_3_18 (the
four preceding no-op rows in this table): `find_dependents.py` does a
transitive build-cascade scan after renaming
`isAcyclic_iff_hasTopologicalOrder` in claim_3_2's Lean file. Any file
whose import graph transitively sees the renamed symbol gets pulled
in, even when the file's own code does not invoke it. The cleanup
script handles this gracefully — no marker blocks means Phase 7a
treats it as a no-op (precedent: `workspace_claim_3_12.md` documents
the exact `apply_refactor_cleanup.py` line refs).

## Why I'm going straight to `solved`

- The **original** chapter row (in `Chapter3_GraphTheory/data.json`)
  is `formalized=yes, proven=proven, solved=yes, date_solved=2026-05-21`.
  The theorem passed every gate at that time.
- The Lean file is **unchanged** since that solve. `lake build` from
  the repo root reports `Build completed successfully (979 jobs)`
  this turn (warnings in `Section3_3/ISigmaSeparationMarginalization.lean`
  are unrelated).
- The tex proof
  `tex/claim_3_19_proof_MarginalizingOutThe.tex` exists from the
  original solve (66 lines, three-section Node-sets / Directed-edges /
  Bidirected-edges skeleton lifted verbatim from LN lines 1177–1210)
  and remains untouched.
- No `[Finite α]`, no `claim_3_2` call → nothing to refactor. Adding
  marker blocks + a `refactor_`-prefixed twin would duplicate the
  whole 765-line file mechanically for zero downstream change;
  cleanup would just delete the original and rename the twin back to
  the same name.
- **Precedents in this same table** (no-op rows that solved cleanly):
  claim_3_12, claim_3_16, claim_3_17, claim_3_18.

## Cleanup script behaviour for this row

Confirmed by precedent workspaces (`workspace_claim_3_17.md`,
`workspace_claim_3_18.md`):

- Phase 7a (Lean marker swap): files **without** any
  `REFACTOR-BLOCK-*` markers are silently no-ops.
- Phase 7b (`lake build`): unaffected — the file already builds.
- Phase 7c (tex twin swap): if
  `tex/refactor_claim_3_19_proof_MarginalizingOutThe.tex` is
  missing, the script WARNs but does not fail.
- Phase 7d (data.json sync): proceeds normally; `proven` stays
  `proven`, `last_refactored_at` gets stamped.

## What the strict-equivalence solved-gate will see

The strict checker will compare the `CDMGNodeIso` helper +
`hardInterventionOn_nodeIso_swig_marginalize_outputs` definition
against the LN displayed equation. Anticipated outcomes:

- The **local `CDMGNodeIso` helper** rather than the same-cardinality
  `CDMGEquiv` is the only viable encoding (LHS over `α`, RHS over
  `α ⊕ ↑W` — no `Equiv` exists in general). This is documented in
  the file's design block (lines 35–63 + 88–152). Expected
  classification: PRESENTATION.
- The **`split1 W` carrier-map witness** matches the LN's `w ↦ w^i`
  identification exactly (under the `Sum.inl = w^o` /
  `Sum.inr = w^i` convention from `NodeSplittingOn.lean`).
  Documented at lines 405–421. Expected classification: NONE.
- The **`Sum.inl '' W` rendering of `W^o`** is the exact encoding
  pinned down by the chapter (file lines 423–434). Expected:
  PRESENTATION (or NONE).
- The **`noncomputable def` rather than `theorem`** is correct
  (conclusion is data, not a proposition). Documented at lines
  475–486.

If the strict gate raises a CONTENT deviation I haven't anticipated,
I'll iterate from feedback — either by re-encoding or by
`accept_deviation` if the deviation is genuinely intentional.

## Action plan

1. (this turn) Emit `solved`. The orchestrator runs:
   - `verify_row_solved` — expected PASS (file is in solved state).
   - hard sorry-check — expected PASS (grep shows no `sorry`,
     `lake build` is clean).
   - strict-equivalence gate — outcome TBD; the file is already
     fully documented in its design block.
2. (on PASS) Row marked `solved=yes`, `proven=proven`;
   `last_refactored_at` gets stamped at Phase 7 cleanup time.
3. (on FAIL) Iterate from the gate's feedback. If the strict gate
   bounces, the precedents (claim_3_17, claim_3_18) suggest running
   `review_design`, `verify_equivalence`, `simplify_proof` in
   succession before re-emitting `solved`.

## Key file paths

- Lean (already filled, do not touch unless gate flags an issue):
  `leanification/Chapter3_GraphTheory/Section3_2/MarginalizingOutSplitOutput.lean`
- Tex proof (already filled from the original solve):
  `leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_19_proof_MarginalizingOutThe.tex`
- Tex statement:
  `leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_19_statement_MarginalizingOutThe.tex`
- LN source (Lem at ~lines 1167–1175, proof 1177–1210):
  `lecture-notes/lecture_notes/graphs.tex`
- Refactor table:
  `leanification/Chapter3_GraphTheory/Refactor_claim_3_2_no_finite/refactor_data.json`
- Precedents for no-op refactor in this same table:
  - `leanification/Chapter3_GraphTheory/Section3_2/workspace_claim_3_12.md`
  - `leanification/Chapter3_GraphTheory/Section3_2/workspace_claim_3_16.md`
  - `leanification/Chapter3_GraphTheory/Section3_2/workspace_claim_3_17.md`
  - `leanification/Chapter3_GraphTheory/Section3_2/workspace_claim_3_18.md`
