# Worker — final-gate verification that a row is truly solved

**When to use:** the manager has run the design review, equivalence check, written + verified the tex proof (for claims), leanified, and (for claims) run the simplify-proof check. They believe the row is done and emit `solved`. You are the **last gate** before `solved="yes"` is written to the data file.

## Authoritative spec = LN block + `addition_to_the_LN`

The row is "solved" only if the Lean artefacts collectively realize the LN block's claim **AND** every clause in the row's `addition_to_the_LN` field (surfaced in the row context). A `[<sid>] …` or `[manual_*] …` clause that is not reflected in the Lean encoding (or tex proof for claims) is grounds for FAIL — flag the specific clause and the artefact that omits it. Empty addition → only the literal LN applies.

You are an *independent* set of eyes: did everything actually land? Are all the artefacts in place? Does the build agree?

## Inputs you should receive from the manager

- `ref` (e.g. `def_3_5` or `claim_3_12`)
- The list of Lean file(s) the row produced — note a single row may map to **multiple** Lean files (a multi-item definition row, or a "claim" that is several theorems stacked) and **multiple** declarations per file
- For claim rows: the path to the proof file (either `<ref>_proof_<title>.tex` for prove mode or `<ref>_disproof_<title>.tex` for disprove mode) in the subsection folder
- **Which mode the row is in**: the manager indicates whether the row is being PROVED (default) or DISPROVED (manager emitted `mistake` and didn't `unmistake` it since). You verify the matching side: in prove mode you verify `<ref>_proof_<title>.tex` + `<Title>.lean` proves the claim; in disprove mode you verify `<ref>_disproof_<title>.tex` + `<Title>Disproof.lean` proves the negation. **Both sides' files may exist on disk** — that's normal; just verify the active side.
- Confirmation that `review_design`, `verify_equivalence`, (`simplify_proof` for claims) all returned PASS

## Checklist

For each item, write one short line. The verdict aggregates them.

1. **All Lean declarations present.** Every theorem-environment block inside the row's `claimmark` (or every definition inside the `defmark`) is represented by a Lean declaration in one of the listed files.
2. **No `sorry`, no `True` placeholders.** Grep the listed Lean files. For claims, the proof must reduce to axioms — `lake build` from `/home/11716061/repo_scaffold2/` must succeed with no `sorry` warnings tied to this row's declarations.
3. **Build is clean.** `lake build` returns success with no errors and no warnings tied to this row.
4. **Subsection main.tex builds the row's subfile(s).** For a def row: `def_<ref>_<title>.tex` is `\subfile`-included from `main.tex`. For a claim row: both `<ref>_statement_<title>.tex` and `<ref>_proof_<title>.tex` are included.
5. **For claim rows: the proof file is filled in.** `<ref>_proof_<title>.tex` contains an actual `\begin{proof}...\end{proof}` block (not the `% TODO` stub), and matches the Lean proof's strategy.
6. **Comment block is in place** above each Lean declaration: `ref`, human-language description, design-choice note, plus (for claims) a cross-link to the proof tex file.
7. **Scope.** No files outside the row's subsection folder (under `leanification/`) have been modified.
8. **Prerequisites passed.** The manager has signalled `review_design`, `verify_equivalence` (and `simplify_proof` for claims) all PASSed earlier in the row. If any is missing or last-FAILed, that's a gate failure here.

## Output

Per-item report above the verdict block.

On PASS, end with **three consecutive lines** in this order:

```
VERDICT: PASS
LEAN_FILES: <repo-relative path 1>, <repo-relative path 2>, ...
MAIN_LEAN_FILE: <the single repo-relative path that holds the canonical statement>
```

On FAIL, end with the verdict tag followed by your actionable feedback in a tagged block:

```
VERDICT: FAIL
BEGIN[feedback]
<one or two paragraphs telling the next manager turn exactly what is wrong
and what concrete action would fix it>
END[feedback]
```

- `LEAN_FILES` is **required on PASS** (comma-separated on one line, or multiple `LEAN_FILES:` lines).
- `MAIN_LEAN_FILE` is **required on PASS** — one repo-relative path holding the row's canonical statement (must be a member of `LEAN_FILES`).
- Paths are repo-relative (e.g. `leanification/Chapter3_GraphTheory/Section3_1/CDMG.lean`).
- The Python orchestrator pattern-matches `VERDICT:`, `LEAN_FILES:`, `MAIN_LEAN_FILE:`, and the `BEGIN[feedback]…END[feedback]` block; a missing or ambiguous verdict is treated as failed.
