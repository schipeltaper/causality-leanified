# Finding the TeX and Lean statements for a given row `ref`

Every definition and claim in the leanification project has a stable
identifier — its `ref` — of the form `def_<chapter>_<n>` or
`claim_<chapter>_<n>` (e.g. `def_3_1`, `claim_3_10`). This document
explains:

1. Where the project state (`data.json`) lives.
2. How to read a `data.json` row.
3. How a Python script, given a `ref`, can locate:
   - the **TeX statement file** for that ref, and
   - the **Lean statement** (signature only — proofs are out of scope).
4. The runnable script that does this lookup:
   [`extras/find_by_ref.py`](./find_by_ref.py).

---

## 1. Where `data.json` lives

One `data.json` per chapter, at the chapter folder's root:

```
leanification/
├── Chapter3_GraphTheory/
│   ├── data.json                     ← chapter 3 state, 60 rows
│   ├── Section3_1/ …                 (Lean files + tex/ subfolder)
│   └── Section3_2/ …
├── Chapter4_StructuralCausalModels/
│   ├── data.json                     ← chapter 4 state (when created)
│   └── …
└── …
```

The chapter folder is named `Chapter<N>_<PascalCaseTitle>` where `<N>` is
the chapter number from the lecture notes. The chapter number embedded in
each row's `ref` is exactly that `<N>`, which makes it easy for a script
to jump straight to the right `data.json`.

## 2. Reading a `data.json` row

The file is a single JSON object:

```jsonc
{
  "chapter": 3,
  "title":   "Graph Theory",
  "columns": [ ... list of column names, for documentation only ... ],
  "rows":    [ { ... }, { ... }, ... ]
}
```

Each row in `rows` is one definition or claim. The fields you care
about when looking up a ref:

| field            | example                                              | meaning |
|------------------|------------------------------------------------------|---------|
| `ref`            | `"def_3_1"`, `"claim_3_4"`                           | stable identifier; primary key |
| `def_or_claim`   | `"def"` / `"claim"`                                  | controls the TeX filename pattern |
| `section`        | `"3.1"`                                              | maps to subsection folder `Section3_1` |
| `title`          | `"CDMG"`, `"AcyclicUnderIntervention"`               | PascalCase short name; appears in filenames and in the rendered header |
| `type`           | `"definition"`, `"lemma"`, `"remark"`, `"note"`, …   | drives the LaTeX theorem env (`Def`, `Lem`, `Rem`, `Note`, …) |
| `solved`         | `"yes"` / `"no"`                                     | whether a Lean formalization exists |
| `main_lean_file` | `"leanification/.../CDMG.lean"`                      | repo-relative path to the *canonical* Lean file |
| `lean_files`     | `["leanification/.../CDMG.lean", …]`                 | all Lean files that contain pieces of this row's formalization (a single claim can span several files; a Lean file can contain several rows) |
| `tex_block`      | `"\\begin{defmark}\\begin{Def}[CDMG]\\label{def-cdmg} …"` | the raw LaTeX excerpt from the lecture notes; only useful for re-creating stubs |

The other fields (`actions_tracking`, `agent_registry`, `tex_file`,
`tips`, `date_solved`, `formalized`, `proven`) are orchestration
bookkeeping and not needed for a "find me the statement" lookup.

## 3. Resolving a `ref` to its files

### 3.1 The TeX statement file

Per-row tex files live under `<chapter>/<section_folder>/tex/`. The
filename depends on `def_or_claim`:

- **`def` row**:    `<chapter>/<section_folder>/tex/<ref>_<title>.tex`
- **`claim` row**:  `<chapter>/<section_folder>/tex/<ref>_statement_<title>.tex`
  (note: `claim` rows also have a sibling `<ref>_proof_<title>.tex` that
  contains both the statement *and* the proof; we ignore that here.)

`<section_folder>` is `Section` followed by the row's `section` with `.`
replaced by `_`: `"3.1"` → `"Section3_1"`.

So for `claim_3_4` with `title = "HardInterventionsCommute"` and
`section = "3.2"`, the statement file is

```
leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_4_statement_HardInterventionsCommute.tex
```

### 3.2 The Lean statement

Open the row's `main_lean_file` (a repo-relative path). Inside, the
formalization is bracketed by **ref-marker comments**:

```lean
-- def_3_10
-- title: HardInterventionOn
--
-- (rich documentation, design notes, verbatim LN excerpt, …)
structure HardInterventionOn …
```

For a claim that is split into several Lean declarations, the markers
include a part suffix:

```lean
-- claim_3_1 (part 1/3)
-- title: JNodeProperties -- no arrowheads into an input node
theorem no_arrowhead_into_input …

-- claim_3_1 (part 2/3)
-- title: JNodeProperties -- directed edges out of J target V
theorem input_edge_target_mem_V …
```

The statement extraction recipe (used by [`find_by_ref.py`](./find_by_ref.py)):

1. Read every line of the lean file.
2. Find every line matching `^--\s+(def|claim)_\d+_\d+(\s+\(part \d+/\d+\))?\s*$` — these are the marker boundaries.
3. For each marker whose ref equals the target ref, the block runs from that line until the next marker (any ref) or end of file.
4. **Trim the proof body** for theorem/lemma/example declarations: stop at the line containing `:= by` (keep that line, drop the tactics that follow). For `structure`/`def`/`abbrev`/`class`/`instance`/`inductive`, keep the whole block — it *is* the statement.

When a row has multiple `lean_files`, scan each in turn. (The `main_lean_file` is the canonical one; `lean_files` may also include dependency files.) The Lean module that contains a given declaration is determined by the file's folder path: `leanification/Chapter3_GraphTheory/Section3_1/CDMG.lean` has module name `Causality.Chapter3_GraphTheory.Section3_1.CDMG` (with the chapter root namespace `Causality`).

## 4. The script

[`extras/find_by_ref.py`](./find_by_ref.py) implements the above.

### Usage

```
$ python3 extras/find_by_ref.py def_3_1
$ python3 extras/find_by_ref.py claim_3_4
```

### Output shape

```
# ref: <ref>
  title:   <title>
  section: <section>
  type:    <type>  (<def_or_claim>)
  solved:  yes|no

## TeX statement file
  path: <repo-relative path>
  ---
  <verbatim contents of the .tex file>

## Lean statement(s)
  --- <repo-relative .lean path>:<line> ---
  <ref-marker comments + signature + `:= by` opener>
  (one block per part; multi-part claims produce several blocks)
```

The TeX is printed in full (the per-row .tex file is small; the
self-contained `\documentclass[main]{subfiles}` framing plus the
`\begin{Def}/Lem/Rem/...}` body). The Lean is printed *only up to the
proof opener* — the script trims the tactic block so the output stays
about the statement.

### Error modes

- malformed ref (`blah`)  →  `error: malformed ref 'blah'; expected …` (exit 2)
- unknown ref (`def_99_1`) →  `error: ref 'def_99_1' not found in any chapter's data.json` (exit 2)
- row marked `solved=no`  →  the TeX path is still printed (stubs exist as soon as the row enters the queue); the Lean section reports `(no lean_files recorded -- row likely unsolved)`
- row has a `section` but the per-row `.tex` is missing  →  `(MISSING -- row may be unsolved)`

### Using the helpers from another script

The two functions you'd reuse:

```python
from extras.find_by_ref import find_row, tex_statement_path, extract_lean_statement

data_path, row = find_row("claim_3_4")
tex_path = tex_statement_path(data_path, row)
tex_source = tex_path.read_text(encoding="utf-8")

for lean_rel in [row["main_lean_file"], *row.get("lean_files", [])]:
    blocks = extract_lean_statement(REPO_ROOT / lean_rel, "claim_3_4")
    # `blocks` is a list of (start_line, list-of-source-lines)
```

That's the whole interface; everything in the script is built on top of
those three functions.
