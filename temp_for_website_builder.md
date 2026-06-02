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
- **Disproven claims.** A row with `proven="disproven"` has a `document_counterexample`-shaped Lean artefact instead of a real proof. The statement markers are still there (wrapping the *false* original claim); the proof file (if present) describes the counter-example. Render accordingly — the row is solved, just not proven.
- **Empty `addition_to_the_LN`.** Means no operator-authored clarifications apply; the literal LN is the spec. Render without an "Addition" section for these rows.
- **Markers missing.** If a Lean file lacks the markers (older work pre-dating this convention, or a bug in a formalize worker), the extraction returns `[]`. Fall back to rendering the whole file with a "marker-extraction missing" badge, and surface the row to the human for re-formalization.

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
