# Refactor roadmap — chapter 3 deviation cleanup

**Date:** 2026-05-31
**Branch:** `server_setting_up_scaffold`
**Status:** five open deviations in `leanification/deviations.json`,
clustered into two unrelated root causes. One resolved deviation
(`claim_3_2_the_lean_statement_adds_finite_to_the_un`) was closed
on 2026-05-31 by the no-op refactor `claim_3_2_no_finite`.

This file is the **operator's checklist**: what to refactor next,
in what order, with what invocation, and what the expected scope is.
For the *full diagnostic* of why Cluster A's natural fix
(`def_3_14_no_L_exclusion`) is fundamentally impossible inside the
`def_3_14` scope, read
`Documenting Progression/02_CDMG_disjoint_EL_refactor_needed.tex`.
For the *original cascade narrative*, read
`Documenting Progression/01_disjoint_EL_cascade.tex`.

---

## TL;DR

Two refactors needed, in this order:

1. **`def_3_1_no_disjoint_EL`** — drops the
   `disjoint_EL : Disjoint E L` field from `CDMG`. Resolves four
   deviations (the entire Cluster A cascade). Out of scope for any
   `def_3_14`-rooted refactor; must be rooted at `def_3_1`.
2. **`def_3_4_collider_loose_n1`** (working name) — loosens the
   `n = 1` case of `Walk.IsCollider` to match the LN's literal
   note. Resolves one deviation (Cluster B). Two-line change in
   `WalkPredicates.lean`; no cascade.

The two refactors are independent. Cluster A is the heavyweight;
do it first because Cluster B's reproof set is small and disjoint
from anything Cluster A touches.

---

## Cluster A — the `disjoint_EL` cascade (4 deviations)

### Symptoms (what's registered)

| id | introduced_by_ref | one-line break |
|---|---|---|
| `def_3_14_marginalize_L_excludes_E` | `def_3_14` | `marginalize_L` adds `¬∃ directed walk` exclusion clauses to dodge a `disjoint_EL` violation; drops literal LN pairs. |
| `def_3_14_l_w_membership_in_marginalization` | `def_3_14` | Same observation refined by the auditor; explicitly cites `def_3_1.CDMG.disjoint_EL` as the *forcing culprit*. |
| `claim_3_16_with_source_bifurcation_deferred` | `claim_3_16` | With-source half of an LN remark cannot be encoded because L-exclusion can flip a no-source bifurcation in `G` into a with-source bifurcation in `G^{∖W}`. |
| `claim_3_25_the_lean_file_does_not_formalise_the_ln` | `claim_3_25` | The Lean theorem proves the *negation* of the LN iff (`isISigmaSeparated_marginalize_iff_disproved`). The counter-example is engineered precisely around the L-exclusion. |

### Root cause (one sentence)

`def_3_1.CDMG` carries a `disjoint_EL : Disjoint E L` field; the
LN's def_3_1 treats `E` and `L` as living in different ambient
types (`L` is a quotient `V × V / ~`), so the same vertex pair `(u,v)`
can be in both `E` and `L`. The LN's `claim_3_25` proof at
`graphs.tex:1559` literally needs the pair `(w, b_{j+1})` in both
`E^{∖u}` and `L^{∖u}` of the marginalized graph. Lean's
`disjoint_EL` makes that impossible by design.

### What was tried and discarded

The refactor branch `refactor_def_3_14_no_L_exclusion` was created
on 2026-05-31. The bullet-proof dependency scan produced a 7-row
table (root `def_3_14` plus claim_3_16, claim_3_17, claim_3_18,
claim_3_19, def_3_18, claim_3_25). The manager spent six turns
analyzing the four option-shapes:

- **(A) priority-E (current code)** — drops `claim_3_25`
- **(B) priority-L** — drops `claim_3_16` item 1
- **(C) helper-only abstraction** — doesn't actually remove the
  L-exclusion; doesn't unbreak `claim_3_25` either
- **(D) refactor `def_3_1`** — restores literal LN encoding; out of
  scope for a `def_3_14`-rooted refactor

After concluding (A)–(C) all just *shift* the deviation rather
than removing it, the manager halted via `request_from_human` with
escalation. The branch was discarded after the diagnosis was
extracted into article 02.

### Required refactor: `def_3_1_no_disjoint_EL`

**Two viable shapes.** Both restore LN ambient-type separation.

**Shape (1) — drop the field outright** (recommended, lighter cut):
delete `disjoint_EL : Disjoint E L` from the `CDMG` structure. Allow
pairs to live in both `E` and `L`. Downstream code that pattern-matched
on `E ∨ L` continues to work; code that exploited disjointness
uses either side explicitly.

**Shape (2) — re-stratify `L`** (better long-term, heavier):
move `L` to `Set (Sym2 α)` or a wrapped type. Makes the LN's
$V \times V / \sim$ quotient explicit in the Lean types. Defer to a
separate refactor.

### Impact estimate (Shape 1)

| Component | Count | Notes |
|---|---:|---|
| Files touched | ~13 | All in `leanification/Chapter3_GraphTheory/Section3_2` and `Section3_3`. |
| Lines modified | ~35-40 | Deletes 1 field + 5 hypothesis uses + ~12 field-discharges. |
| Re-proven rows | 7-25 | All seven rows from the failed `def_3_14_no_L_exclusion` attempt, plus the transitive scan may add Section 3.2 commutation claims (claim_3_10–claim_3_15) since the CDMG *type* changed. |
| Out-of-chapter-3 impact | **zero** | Chapter 4+ consumes CDMG values, not their structural fields. |

The major reproof work is `claim_3_25` itself: the existing (⇒)
direction proof in `SigmaOpenWalkMarginalization.lean` is 2246 lines
(no `sorry`) and carries over essentially unchanged; the missing
(⇐) direction is a fresh ~2000-2500 line positive proof against
the LN-literal statement.

### Recommended invocation

```bash
git checkout server_setting_up_scaffold
python extras/do_refactor.py init \
    --chapter 3 --root-ref def_3_1 \
    --name def_3_1_no_disjoint_EL
```

The transitive scan (now bullet-proof per the 2026-05-31
`find_dependents.py` baseline-then-diff fix) will produce the full
table automatically — likely 15-25 rows. All four cascade
deviations land in `deviations_to_resolve`; the
`accept_deviation` guard refuses any of those ids, so the manager
must actually fix the encoding.

### Alternative stopgap: Path δ (cheap, contained)

If the full refactor is too heavy, a `plan_subtasks` worker on
2026-05-31 identified a smaller-scope option:

> **Ship only the (⇒) direction of `claim_3_25` positively;
> retain the (⇐) disproof.**

```lean
theorem isISigmaSeparated_marginalize_forward
    (G : CDMG α) (A B C : Set α) {D : Set α} (hDV : D ⊆ G.V)
    (hDisj : Disjoint D (A ∪ B ∪ C)) :
    G.IsISigmaSeparated A B C →
      (G.marginalize D).IsISigmaSeparated A B C := ...
```

**Cost:** ~50-100 lines, reusing the existing
`lift_sigmaOpen_walk_through_single_vertex`. **Coverage:** improves
`claim_3_25` from "full iff disproved" to "(⇒) proven positively,
(⇐) disproved". **Downside:** the (⇐) direction is the
load-bearing direction for downstream do-calculus rule 3, so this
unlocks no downstream consumer; it's a partial credit move.

Full analysis (with the rejected Path α augmented-walk option and
the GenWalk parameterisation that would reduce Path α to ~3500
lines) is in
`Documenting Progression/appendix_path_alpha_genwalk_analysis.md`.

---

## Cluster B — `Walk.IsCollider` at n=1 (1 deviation)

### Symptom

| id | introduced_by_ref | one-line break |
|---|---|---|
| `def_3_4_the_encoding_of_walk` | `def_3_4` | The encoding of `Walk.IsCollider` deviates from the LN's literal n=1 note ("v ⌣ w in G"). Lean takes the strict reading (only bidirected single-step walks qualify); the LN takes the loose reading (any single-step walk qualifies). |

### Root cause

In `Section3_1/WalkPredicates.lean`, the `IsCollider` definition's
second pattern case reads:
```lean
| _, _, .cons s (.nil _)    => s.IsBidir
```
Under the LN's literal n=1 note, this should be
`s.HasArrowheadAtTarget ∨ s.HasArrowheadAtSource` (i.e. any of
forward / backward / bidir, equivalent to `True` given that
`WalkStep`'s existence already certifies adjacency).

The Lean file's own design block calls the loose reading
"slightly looser" and argues downstream uses only need the strict
version. That is a *content* choice, not a notation choice — it
changes which walks count as collider walks.

### Required refactor: `def_3_4_collider_loose_n1` (working name)

Two viable shapes, mirrors of each other:

**Shape (a) — loosen the n=1 case** (matches LN literally):
change the second pattern case to `True` (or
`s.HasArrowheadAtTarget ∨ s.HasArrowheadAtSource`). Any consumer
that relied on the strict reading needs its proof reworked.

**Shape (b) — keep the strict reading, register the deviation
properly**: move the entry from `auditor-draft` to
`manager-accepted` with the design-block justification copied into
`notes`, and document the at-risk pattern (any future row that
constructs a single-step collider walk from a non-bidirected
edge). No code change.

The `WalkPredicates.lean` design block prefers (b) for
"downstream-proof compositionality" reasons. If we go that route,
the deviation just needs proper acceptance, not a refactor.

If we want (a) — the LN-faithful version — the refactor invocation:
```bash
python extras/do_refactor.py init \
    --chapter 3 --root-ref def_3_4 \
    --name def_3_4_collider_loose_n1
```

The transitive scan should produce a small table; the def_3_4
ripple stops at consumers that pattern-match on `IsCollider`'s
n=1 case explicitly. Cluster B is structurally disjoint from
Cluster A (collider classification doesn't pass through
marginalization's L-membership predicates), so the two refactors
do not interact.

### Decision pending

Worth a human read of the `WalkPredicates.lean` design block
before invoking — the file's author explicitly chose (b) once
already; (a) is only correct if we now think LN-literal trumps
the downstream-compositionality argument.

---

## Order of operations

1. **Cluster A first**: `def_3_1_no_disjoint_EL` (or Path δ
   stopgap if the full refactor is deferred).
2. **Cluster B second**: decide between (a) and (b) for
   `Walk.IsCollider` n=1.

Both refactors land cleanly on `server_setting_up_scaffold` and
get merged back to it; neither touches the other's files.

---

## Pointer to the orchestrator fixes

Six bug fixes accumulated on `server_setting_up_scaffold` over
2026-05-30/31 (commits `cb557cd`, `f5a8247`, `7f990f8`) make the
above refactors safer to drive:

- `initialize_refactor.py`: root-first ordering
- `solve_chapter.py`: chapter-folder path resolution for refactor rows
- `find_dependents.py`: baseline-then-diff lake-build (no linter noise)
- `solve_chapter.py`: `RequestFromHumanEscalated` exception (clean hard halt)
- `solve_chapter.py`: `deviations_to_resolve` snapshot;
  `accept_deviation` refuses those ids
- `solve_chapter.py`: `request_from_human` threshold counted as
  *total per row* via `actions_tracking`, not consecutive

The full context for why these fixes mattered (and how the
absence of #5 produced a fraudulent "successful" first refactor
attempt) is in article 02 §"Why this was found so late".
