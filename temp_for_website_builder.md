# `temp_for_website_builder.md` — extraction recipe for a single row

This document tells the website-builder agent how to pull, **for any solved row of a chapter's `data.json`**, the five artefacts it needs to render the row's "statement + proof + Lean formalization" surface:

1. The **tex statement** file (just the LN statement block).
2. The **tex statement + proof** file (statement + LN-style proof; claim rows only).
3. The path to the **Lean file** containing the row's main statement (the canonical Lean source for the row).
4. The **Lean statement** itself (extracted from that file via marker comments).
5. The **Lean supporting statements** (helper declarations the main statement needs to type-check — also marker-extracted).

Everything below assumes the chapter has finished Phase 3 (every row has `solved="yes"` in its `data.json` entry); the markers and tex files are populated by the Phase 3 workers.

---

## 0. Conventions you can rely on

- **Refs** are strings like `def_3_1`, `claim_3_5`, matching the regex `(def|claim)_\d+_\d+`. Every row in `data.json` has a unique `ref`.
- **Chapter folder** name follows the pattern `Chapter<N>_<PascalCaseTitle>/` under `leanification/`. Find it by globbing `leanification/Chapter<N>_*/`.
- **Section subfolder** name follows `Section<N>_<M>/`. Each row's `section` field (e.g. `"3.1"`) maps to `Section3_1/`.
- **Subfile titles** are the row's `title` (PascalCase, stored on the row in `data.json`).

## 1. Locate the row

```python
import json
from pathlib import Path

REPO = Path("/home/11716061/repo_scaffold2")

def find_row(chapter: int, ref: str) -> tuple[dict, Path]:
    """Return (row_dict, chapter_folder_path) for the given ref."""
    chapter_folder = next(REPO.joinpath("leanification").glob(f"Chapter{chapter}_*"))
    data = json.loads((chapter_folder / "data.json").read_text(encoding="utf-8"))
    row = next(r for r in data["rows"] if r["ref"] == ref)
    return row, chapter_folder
```

The returned `row` has every field you need — including `title`, `section`, `main_lean_file`, `lean_files`, `tex_block`, `tex_file`, and `addition_to_the_LN`.

## 2. Get the tex statement file

For a row with `ref`, `title`, `section`:

```python
def tex_statement_path(row, chapter_folder):
    section_folder = chapter_folder / f"Section{row['section'].replace('.', '_')}"
    # The file name pattern depends on kind:
    if row["def_or_claim"] == "def":
        # Defs: a single subfile carries the LN's defmark block.
        return section_folder / "tex" / f"{row['ref']}_{row['title']}.tex"
    else:
        # Claims: the statement file is separate from the proof file.
        return section_folder / "tex" / f"{row['ref']}_statement_{row['title']}.tex"
```

That file is **guaranteed** by the `verify_tex_statement_only` gate (run after every write to that file) to contain the LN's statement block and nothing else. No proof, no scratch work — safe to render verbatim into the website's "statement" surface.

## 3. Get the tex statement + proof file (claims only)

For claim rows only:

```python
def tex_proof_path(row, chapter_folder):
    if row["def_or_claim"] != "claim":
        return None
    section_folder = chapter_folder / f"Section{row['section'].replace('.', '_')}"
    return section_folder / "tex" / f"{row['ref']}_proof_{row['title']}.tex"
```

That file is **guaranteed** by the `verify_tex_statement_plus_proof` gate to contain both the statement and the proof (in that order, with a non-empty `\begin{proof}…\end{proof}` block). Safe to render as the "statement + proof" surface.

## 4. Get the path to the Lean file with the main statement

```python
def main_lean_path(row):
    return REPO / row["main_lean_file"]
```

`main_lean_file` is set on every solved row by the final-gate worker — it points at the Lean file holding the row's canonical declaration (the structure / def / theorem). A row may have *additional* Lean files (in `row["lean_files"]`); the main one is where the marker-wrapped statement lives.

## 5. Extract the Lean statement from that file via markers

The formalize workers (`formalize_definition_in_lean` / `formalize_claim_in_lean`) wrap each declaration that is part of the row's statement formalization with line-comment markers of the form:

```lean
-- <ref> -- start statement
def <name> := …             # or: theorem <name> … : <conclusion>
-- <ref> -- end statement
```

Two dashes around the keyword `start`/`end`, `statement`, and the row's `ref` substituted in. For claim rows, the wrapped portion is the signature only — the `:= by …` proof body sits *below* the end marker.

### Extraction:

```python
import re

def extract_lean_statement(lean_path: Path, ref: str) -> list[str]:
    """Return the body (without the marker lines themselves) of every
    `-- <ref> -- start statement` / `-- <ref> -- end statement` block in
    the file, in source order. Multiple blocks are possible for
    multi-item rows; for single-item rows the list has one element."""
    text = lean_path.read_text(encoding="utf-8")
    pat = re.compile(
        r"^[ \t]*--[ \t]+" + re.escape(ref) + r"[ \t]+--[ \t]+start[ \t]+statement[ \t]*\n"
        r"(?P<body>.*?)"
        r"^[ \t]*--[ \t]+" + re.escape(ref) + r"[ \t]+--[ \t]+end[ \t]+statement[ \t]*$",
        re.DOTALL | re.MULTILINE,
    )
    return [m.group("body").rstrip("\n") for m in pat.finditer(text)]
```

Each entry of the list is the Lean source of one statement declaration, stripped of its surrounding marker lines. Render those into the website's "Lean statement" surface.

**Important:** markers are guaranteed by the workers to be **immediately adjacent** to the wrapped declaration — no blank lines, comments, or docstrings between the start marker and the keyword, or between the declaration's last line and the end marker. So the extracted `body` is exactly the declaration source.

## 6. Extract the Lean supporting statements (helpers) via markers

In the same Lean file (or sometimes in sibling files in the row's `lean_files`), the formalize workers also wrap auxiliary declarations the main statement *needs to type-check* with a slightly different marker that uses **three** dashes:

```lean
-- <ref> --- start helper
def <helper_name> := …
-- <ref> --- end helper
```

Three dashes (not two) around `start`/`end`, `helper`. These wrap "statement support" declarations only — declarations the main statement depends on for type-checking. Declarations introduced purely for proof tactics or general infrastructure are deliberately *not* wrapped.

### Extraction:

```python
def extract_lean_helpers(lean_path: Path, ref: str) -> list[str]:
    """Same shape as extract_lean_statement but for `--- start/end helper`
    blocks (note the THREE dashes around 'start'/'end' and 'helper')."""
    text = lean_path.read_text(encoding="utf-8")
    pat = re.compile(
        r"^[ \t]*--[ \t]+" + re.escape(ref) + r"[ \t]+---[ \t]+start[ \t]+helper[ \t]*\n"
        r"(?P<body>.*?)"
        r"^[ \t]*--[ \t]+" + re.escape(ref) + r"[ \t]+---[ \t]+end[ \t]+helper[ \t]*$",
        re.DOTALL | re.MULTILINE,
    )
    return [m.group("body").rstrip("\n") for m in pat.finditer(text)]
```

Render the returned helpers alongside the main statement so the rendered Lean statement on the website is self-contained.

**Where to search:** start with `row["main_lean_file"]`. If you want to be exhaustive (a multi-file row), iterate every file in `row["lean_files"]` and union the results. The orchestrator does not promise that helpers always sit in the same file as the main statement — but in practice they almost always do, because the main declaration needs them to type-check and Lean's import order keeps them local.

## 7. Putting it all together

```python
def website_payload_for_row(chapter: int, ref: str) -> dict:
    row, chapter_folder = find_row(chapter, ref)
    main_lean = REPO / row["main_lean_file"]
    payload = {
        "ref":   row["ref"],
        "title": row.get("title", ""),
        "kind":  row["def_or_claim"],            # "def" or "claim"
        "section":              row.get("section", ""),
        "tex_statement_path":   str(tex_statement_path(row, chapter_folder).relative_to(REPO)),
        "tex_proof_path":       (str(tex_proof_path(row, chapter_folder).relative_to(REPO))
                                 if tex_proof_path(row, chapter_folder) else None),
        "lean_file":            str(main_lean.relative_to(REPO)),
        "lean_statements":      extract_lean_statement(main_lean, ref),
        "lean_helpers":         extract_lean_helpers(main_lean, ref),
        # Bonus — the human-authored spec strengthening from Phase 2:
        "addition_to_the_LN":   row.get("addition_to_the_LN", ""),
    }
    return payload
```

## 8. Known edge cases and caveats

- **Multi-file rows.** A row whose Lean spans multiple files lists them in `row["lean_files"]`. The main statement is in `row["main_lean_file"]`; helpers may be in sibling files in the same subsection folder. Search all of `row["lean_files"]` to be safe.
- **Multi-item rows.** A def row that defines several `notation`s, or a claim row that bundles several `theorem`s, will have multiple `-- <ref> -- start statement` / `-- <ref> -- end statement` blocks in the file (one per item). The extraction functions above return a *list* of bodies for exactly this reason.
- **`variable` directives are now valid helper-marker targets.** A `variable {Node : Type*} [DecidableEq Node]` line whose binders auto-bind into one of the wrapped main statements is wrapped with `-- <ref> --- start helper` / `... end helper` (three dashes, like other helpers). The extraction recipe in section 6 already handles this — the regex picks up the `variable` line the same way it picks up a `def` helper. Render the variable directive as part of the "Lean helpers" surface so the rendered statement is self-contained and not full of seemingly-free type variables. See `CDMGNotation.lean` (def_3_2) and `Walks.lean` (def_3_4) for examples.
- **Disprove mode (`proven="disproven"`).** The workflow now mirrors the prove flow on the negation — see section 10 for the full file convention.
- **Empty `addition_to_the_LN`.** Means no operator-authored clarifications apply; the literal LN is the spec. Render without an "Addition" section for these rows.
- **Markers missing.** If a Lean file lacks the markers (older work pre-dating this convention, or a bug in a formalize worker), the extraction returns `[]`. Fall back to rendering the whole file with a "marker-extraction missing" badge, and surface the row to the human for re-formalization.
- **Canonical statement tex is now operator-curated.** Every solved row's `<ref>_<title>.tex` (def) / `<ref>_statement_<title>.tex` (claim) is no longer the LN's `defmark` / `claimmark` body verbatim — it has been rewritten by the `formalize_definition_in_tex` / `formalize_claim_in_tex` worker so every `addition_to_the_LN` clause is folded *into* the statement, every implicit quantifier is spelled out, and visual notation (`v_0 \tuh v_1 \hus \cdots`) is translated to set-theoretic phrasing. A semantic-equivalence verifier (`verify_tex_statement_equivalence`) gates it against the LN + addition before any Lean is written. **The website should render this rewritten statement, not the LN's `tex_block`.** The path is unchanged; only the contents are richer.

## 9. File paths recap

| Artefact | Path |
|---|---|
| Chapter `data.json` | `leanification/Chapter<N>_<Title>/data.json` |
| Row's tex statement | `…/Section<N>_<M>/tex/<ref>_statement_<title>.tex` (claims) or `…/<ref>_<title>.tex` (defs) |
| Row's tex statement + proof | `…/Section<N>_<M>/tex/<ref>_proof_<title>.tex` (claims only) |
| Row's main Lean file | `row["main_lean_file"]` (already a repo-relative path) |
| Subsection's `main.tex` aggregator | `…/Section<N>_<M>/main.tex` |
| Chapter's `request_from_human.tex` | `…/Chapter<N>_<Title>/request_from_human.tex` |

All paths are repo-relative (resolve against the repo root, `/home/11716061/repo_scaffold2/` in development).

---

## 10. Disprove-mode rows (`proven="disproven"`)

When a claim row's manager concludes the LN claim is genuinely false, it emits `mistake` and the orchestrator engages the **disprove flow**, which mirrors the prove flow on the *negation* of the claim. The end-state file layout differs from the prove flow:

| Artefact (disprove mode) | Path |
|---|---|
| Row's canonical statement tex | `…/Section<N>_<M>/tex/<ref>_statement_<title>.tex` — **unchanged**; still the positive claim. Kept for reference; the row's `proven` field tells you the claim is disproven. |
| Row's disprove "statement + proof" tex | `…/Section<N>_<M>/tex/<ref>_disproof_<title>.tex` — the at-the-top statement is a precise tex rendering of the **negation** (typically `\lnot (\text{LN claim})` or an explicit existential counter-example `\exists \ldots, \text{hypotheses} \land \lnot \text{conclusion}`); the proof body underneath establishes that negation. |
| Row's main Lean file | `row["main_lean_file"]` — re-pointed at the disprove Lean file at solved-time (the prove-side `<Title>.lean` is *deleted*, leaving only the disprove file). |
| The disprove Lean file | `<subsection>/<Title>Disproof.lean` — contains `theorem not_<original_name> : ¬ <claim>` (or an existential-witness equivalent) wrapped in the standard statement markers, plus its proof body. |

**What the website should render for a `proven="disproven"` row:**

- The **positive** canonical statement tex (`<ref>_statement_<title>.tex`) with a clear "DISPROVEN" badge alongside.
- The **disprove** tex file as the "statement-of-the-negation + proof" surface — this is the analogue of the prove-mode `<ref>_proof_<title>.tex` surface.
- The **disprove** Lean file's marker-extracted statement + helpers (same regex as section 5+6; the `<ref>` in the markers is the original row ref).
- Optionally, a short narrative explaining where the LN's reasoning broke down (the `prove_claim_in_lean` worker is told to put this in the Lean file's design-choice comment block above the negation theorem).

**Files that are guaranteed NOT to exist on a disproven row:**

- `<ref>_proof_<title>.tex` — deleted by `cleanup_row_artefacts` at solved-time once `proven="disproven"` is committed.
- `<Title>.lean` — same; deleted.

If a row is mid-flight in disprove mode (manager has emitted `mistake` but the row hasn't been solved yet), both sides' files may coexist. Don't render anything until `solved="yes"` is on the row; the workflow's `unmistake` action can flip a row back to prove mode at any point before solving.

---

## 11. What changed in the workflow recently (June 2026)

For the website-builder team's awareness:

1. **Tex bridge layer.** Every solved row's canonical statement tex is now a rewritten, operator-spec-faithful version of the LN — see section 8's "Canonical statement tex is now operator-curated" caveat. Render this file, not the LN's raw `tex_block`.
2. **`variable` directives as helpers.** The marker convention now wraps `variable` directives whose binders auto-bind into the wrapped statement. The extraction regex in section 6 already matches them — no code change on your side; just make sure the rendered "Lean statement" surface includes the variable block.
3. **Disprove mode is fully fleshed out.** Where previously a disproven row had ad-hoc `document_counterexample`-shaped artefacts, it now follows the structured convention in section 10.
4. **`simplify_proof` removed.** The action and worker prompt no longer exist. If your pipeline tracked `actions_tracking.simplify_proof`, that key is now absent from every newly-solved row's data.json entry. (Vestigial counters were stripped at clean-slate.)
5. **Orchestrator hardened against non-UTF-8 bytes in subprocess output.** Doesn't affect the website builder; documenting for completeness — the for_website worker should now reliably produce the v3 JSON shape (sections 4-7) without the orchestrator crashing mid-stream.

If anything above requires action on the website-builder side beyond what's documented here, surface it and I'll update this file.
