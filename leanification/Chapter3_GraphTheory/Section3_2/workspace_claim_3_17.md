# Workspace: claim_3_17 (MarginalizationsCommute) — refactor `claim_3_2_no_finite`

## Context summary

- **Row**: `claim_3_17`, title `MarginalizationsCommute`, claim,
  section 3.2 (type `lemma`).
- **LN block** (`graphs.tex` Lem ~lines 995–1005, label
  `marginalizations-commute`): the chained equality
  `(G^{\sm W₁})^{\sm W₂} = (G^{\sm W₂})^{\sm W₁} = G^{\sm (W₁ ∪ W₂)}`
  for a CDMG `G=(J,V,E,L)` and disjoint `W₁, W₂ ⊆ V`.
- **Refactor goal (table-wide)**: `claim_3_2_no_finite` removes the
  `[Finite α]` baggage from the root
  `isAcyclic_iff_hasTopologicalOrder` (claim_3_2). Downstream consumers
  that used to thread `[Finite α]` through their statements or proofs
  get to drop it.

## Key finding: this row is a **no-op refactor**

The existing
`leanification/Chapter3_GraphTheory/Section3_2/MarginalizationsCommute.lean`
(1069 lines; result of the original solve) declares **two theorems**:

1. `marginalize_marginalize` (the fusion lemma):
   `(G.marginalize W₁).marginalize W₂ = G.marginalize (W₁ ∪ W₂)`
   under `Disjoint W₁ W₂`.
2. `marginalize_comm` (the commute corollary):
   `(G.marginalize W₁).marginalize W₂ = (G.marginalize W₂).marginalize W₁`
   under `Disjoint W₁ W₂`. One-line consequence of the fusion lemma +
   `Set.union_comm`.

Plus seven public walk-translator helpers (`lift_directed_walk`,
`shrink_directed_walk`, `directed_walk_iff`,
`directed_walk_iff_no_length`, `lift_bifurcation_walk`,
`shrink_bifurcation_walk`, `bifurcation_walk_iff_no_length`) used
both internally and by `Section3_3/SigmaOpenWalkMarginalization.lean`
(claim_3_25 helper layer); plus five private list/CDMG-shape
helpers (`mk_eq_of_data`, `list_tail_dropLast`,
`start_in_support_dropLast`, `support_append_dropLast`,
`support_tail_in_V_of_isDirected`).

**Targeted grep over the file** (`Finite|isAcyclic_iff_hasTopologicalOrder|claim_3_2`)
returns **zero hits in code**: the only matches are three docstring
mentions of `claim_3_25` (the downstream consumer of the public
walk-translator helpers — unrelated to claim_3_2 and unrelated to
finiteness). The file has no `[Finite α]` instance hypothesis on
any theorem, makes no call to `isAcyclic_iff_hasTopologicalOrder`,
and does not reference `claim_3_2` at all.

The file's sole import is
`Chapter3_GraphTheory.Section3_2.MarginalizationPreserves`. That
imported file itself is also already finiteness-free — its references
to `claim_3_2` / `Finite` are all in design-note comments that
explicitly *justify the absence* of any such dependency (verified by
grep on the previous turn). So neither this file nor its direct
import threads `[Finite α]` or routes through the claim_3_2 iff.

## Why this row was pulled into the refactor table

Same mechanism as claim_3_12 and claim_3_16 (the two preceding no-op
rows in this table): `find_dependents.py` does a transitive
build-cascade scan after renaming `isAcyclic_iff_hasTopologicalOrder`
in claim_3_2's Lean file. Any file whose import graph transitively
sees the renamed symbol gets pulled in, even when the file's own
code does not invoke that symbol. The cleanup script handles this
gracefully — no marker blocks means Phase 7a treats it as a no-op
(see precedent workspace_claim_3_12.md for the exact
`apply_refactor_cleanup.py` line refs).

## Why I'm going straight to `solved`

- The **original** chapter row (in `Chapter3_GraphTheory/data.json`)
  is already `formalized=yes, proven=proven, solved=yes`. The two
  theorems passed every gate at that time:
  `review_design`, `verify_equivalence`, `verify_tex_proof`,
  `simplify_proof`, `verify_row_solved`.
- The Lean file is **unchanged** since that solve. `lake build` from
  the repo root reports `Build completed successfully (979 jobs)`
  this turn.
- The tex proof
  `tex/claim_3_17_proof_MarginalizationsCommute.tex` exists (147
  lines, two-half structure: directed edges + bidirected edges with
  hinge case-split), was previously written and verified, and remains
  untouched.
- No `[Finite α]`, no `claim_3_2` call → nothing to refactor. Adding
  marker blocks + a `refactor_`-prefixed twin would duplicate the
  whole 1069-line file mechanically for zero downstream change;
  cleanup would just delete the original and rename the twin back to
  the same name.
- **Precedent in this same table**: claim_3_12 and claim_3_16 were
  no-op refactors and both solved on the first `solved` attempt
  (claim_3_16 needed an `accept_deviation` for a separately
  documented with-source bifurcation deferral, but that was unrelated
  to the no-op pattern itself).

## Cleanup script behaviour for this row

Confirmed by reading `extras/apply_refactor_cleanup.py` (per prior
no-op workspace analyses):

- Phase 7a (Lean marker swap): files **without** any
  `REFACTOR-BLOCK-*` markers are silently no-ops.
- Phase 7b (`lake build`): unaffected — the file already builds.
- Phase 7c (tex twin swap): if the
  `tex/refactor_claim_3_17_proof_MarginalizationsCommute.tex` twin is
  missing, the script WARNs but does not fail.
- Phase 7d (data.json sync): proceeds normally; `proven` stays
  `proven`, `last_refactored_at` gets stamped.

## What the strict-equivalence solved-gate will see

The strict checker will compare the two theorems against the LN's
chained equality. Anticipated outcomes:

- The split into **fusion + commute** (rather than packaging both
  halves of the LN's `\[ X = Y = Z \]` as one chained equality) is
  a **PRESENTATION** deviation already documented in the file's
  design-note block (lines 894–921, citing the
  `HardInterventionsCommute.lean` precedent). The strict checker
  should classify as PRESENTATION.
- The **no `W₁, W₂ ⊆ G.V` precondition** is documented as a
  **faithful strengthening** of the LN (file lines 849–874, with a
  cross-reference to `Section3_2/Marginalization.lean`'s
  no-precondition design block). This is the same pattern recorded
  in the deviation register for `marginalize` itself; the strict
  checker should classify as PRESENTATION (or at worst trigger
  EXAMPLE_GENERATION → property-based check, which would PASS since
  the four-component equality holds on `W \ G.V` trivially).
- The **`Disjoint W₁ W₂` hypothesis** matches the LN's "disjoint"
  qualifier exactly; no deviation there.

If the strict gate raises a CONTENT deviation I haven't anticipated,
I'll iterate from feedback — either by re-encoding or by
`accept_deviation` if the deviation is genuinely intentional and
already covered by an existing register entry.

## Action plan

1. (this turn) Emit `solved`. The orchestrator runs:
   - `verify_row_solved` — expected PASS (file is in solved state).
   - hard sorry-check — expected PASS (file-grep shows no `sorry`,
     `lake build` is clean).
   - strict-equivalence gate — expected PASS (LN-faithful two-theorem
     decomposition, already documented).
2. (on PASS) Row marked `solved=yes`, `proven=proven`;
   `last_refactored_at` gets stamped at Phase 7 cleanup time.
3. (on FAIL) Iterate from the gate's feedback.

## Key file paths

- Lean (already filled, do not touch unless gate flags an issue):
  `leanification/Chapter3_GraphTheory/Section3_2/MarginalizationsCommute.lean`
- Tex proof (already filled):
  `leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_17_proof_MarginalizationsCommute.tex`
- Tex statement:
  `leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_17_statement_MarginalizationsCommute.tex`
- LN source (Lem at ~lines 995–1005, label `marginalizations-commute`):
  `lecture-notes/lecture_notes/graphs.tex`
- Refactor table:
  `leanification/Chapter3_GraphTheory/Refactor_claim_3_2_no_finite/refactor_data.json`
- Precedents for no-op refactor in this same table:
  - `leanification/Chapter3_GraphTheory/Section3_2/workspace_claim_3_12.md`
  - `leanification/Chapter3_GraphTheory/Section3_2/workspace_claim_3_16.md`
