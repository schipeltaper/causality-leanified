# Plan — `for_website` info collector (final)

**Status:** approved schema, ready to implement on user greenlight.

Each row's `<ref>_for_website.json` carries one Lean code panel (with-comments + without-comments variant for UI toggle), a single explanation article, a single design-choices article, and a small ordered list of GitHub source-file links — one entry per Lean file the row's formalization lives in.

---

## 1. JSON schema

```jsonc
{
  "ref":              "def_3_4",
  "title":            "Walks",
  "type":             "definition",
  "def_or_claim":     "def",
  "section":          "3.1",
  "lean_file_path":   "leanification/Chapter3_GraphTheory/Section3_1/Walks.lean",

  "lean_code_with_comments":    "/-- A single edge in a walk in the CDMG `G`... -/\ninductive WalkStep (G : CDMG α) : α → α → Type _ where\n  /-- A directed forward step ... -/\n  | forward {v w : α} (h : v ⟶[G] w) : WalkStep G v w\n  ...\n\n/-- A walk in `G` is built ... -/\ninductive Walk (G : CDMG α) : α → α → Type _ where\n  | nil ...\n",

  "lean_code_without_comments": "inductive WalkStep (G : CDMG α) : α → α → Type _ where\n  | forward {v w : α} (h : v ⟶[G] w) : WalkStep G v w\n  ...\n\ninductive Walk (G : CDMG α) : α → α → Type _ where\n  | nil ...\n",

  "lean_explanation": "The walks definition introduces ... [~150–500 word article] ...",
  "design_choices":   "The most subtle choice is ... [~150–500 word article] ...",

  "lean_source_urls": [
    { "title": "Walks.lean",
      "url":   "https://github.com/schipeltaper/causality-leanified/blob/server_setting_up_scaffold/leanification/Chapter3_GraphTheory/Section3_1/Walks.lean#L80-L622" }
  ]
}
```

### Field semantics

| field                       | type                                    | how it is produced                                                                                                                                                                  |
|-----------------------------|-----------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `ref`/`title`/`type`/`def_or_claim`/`section`/`lean_file_path` | strings | bookkeeping, copied verbatim from the row context.                                                                                                                                  |
| `lean_code_with_comments`   | string                                  | mechanical: verbatim slice of the Lean file(s) at the anchor ranges the LLM picked, concatenated with blank lines. Internal `--` / `/- -/` / `/-- -/` comments preserved as written. |
| `lean_code_without_comments`| string                                  | mechanical: `lean_code_with_comments` passed through the Lean comment-stripper.                                                                                                      |
| `lean_explanation`          | string                                  | LLM: ~150–500 word polished public-facing article on what the Lean code does and how it maps to the LN.                                                                              |
| `design_choices`            | string                                  | LLM: ~150–500 word polished article on the non-obvious encoding decisions and the alternatives that were rejected.                                                                   |
| `lean_source_urls`          | list of `{"title": str, "url": str}`    | mechanical: one entry per unique file appearing in the LLM's anchors; `title` is the file basename; `url` covers `[min line_start, max line_end]` across anchors in that file.       |

### Anchor concept (LLM-facing)

The LLM's only structural output (besides the two prose blocks) is a list of **anchors**:

```json
{
  "title":           "WalkStep",                                                    // short label for the orchestrator's reference (not surfaced to the website verbatim)
  "lean_file_path":  "leanification/Chapter3_GraphTheory/Section3_1/Walks.lean",    // any file the row's `lean_files` covers (most commonly `main_lean_file`)
  "line_start":      127,                                                            // 1-indexed; the LLM INCLUDES the `/-- … -/` doc comment immediately above the declaration if any
  "line_end":        143                                                             // 1-indexed inclusive; last line of the declaration body
}
```

The LLM picks line ranges that **bracket a single Lean declaration** plus its leading doc comment. The ranges must **exclude**: the `-- <ref>` / `-- title:` orchestrator markers, the long `## Design choice` blocks (which become `design_choices`), the `/- Verbatim from … -/` LN-citation blocks, and any in-file scaffold helpers that don't correspond to LN-level content.

Anchors feed two consumers:

1. **Code panel**: each anchor's range is sliced verbatim out of the Lean file. The slices are concatenated in source order (separator: one blank line) into `lean_code_with_comments`. Internal comments survive automatically because they're inside the slice; outer design / bookkeeping comments stay out because they're outside the slice.
2. **Source-URL list**: anchors are bucketed by `lean_file_path`. For each unique file, one URL entry is produced — `title = basename(lean_file_path)`, `url = github(branch, lean_file_path, min(line_start), max(line_end))`. So a row whose formalization lives in `Walks.lean` only yields one URL entry titled `"Walks.lean"`; a row whose anchors span `Walks.lean` and `WalkExtensions.lean` yields two entries.

---

## 2. Workflow stages

Three stages: mechanical pre-flight, LLM worker, mechanical post-flight.

### Stage A — Pre-flight (Python)

Done once per orchestrator run; values are reused for every row.

1. **GitHub URL template**:
   ```python
   remote = subprocess.check_output(["git", "remote", "get-url", "origin"]).decode().strip()
   match = re.match(r"git@github\.com:(.+?)(?:\.git)?$", remote) \
           or re.match(r"https://github\.com/(.+?)(?:\.git)?$", remote)
   repo_slug = match.group(1)
   branch = subprocess.check_output(
       ["git", "rev-parse", "--abbrev-ref", "HEAD"]).decode().strip()
   url_template = f"https://github.com/{repo_slug}/blob/{branch}/{{path}}#L{{start}}-L{{end}}"
   ```
   Branch-pinned (not commit-SHA-pinned) so URLs track the current state of the branch; line numbers may drift on file edits and re-pin the next time the row is re-solved.

Per row, the orchestrator additionally reads `main_lean_file`, the tex statement file, and any auxiliary `lean_files`. These become attachments / context for the LLM call.

### Stage B — LLM worker (`claude -p`)

Driven by the rewritten worker prompt at `scaffold/claude_prompts/row_workers/produce_for_website.md`. The LLM emits:

```json
{
  "lean_explanation": "...short article...",
  "design_choices":   "...short article...",
  "source_anchors": [
    {"title": "WalkStep", "lean_file_path": "leanification/.../Walks.lean", "line_start": 127, "line_end": 143},
    {"title": "Walk",     "lean_file_path": "leanification/.../Walks.lean", "line_start": 153, "line_end": 222},
    ...
  ]
}
```

Rules the prompt enforces:

- One anchor per Lean declaration that corresponds to an LN-level concept. Exclude helper lemmas / `@[simp]` membership lemmas / scaffold `instance` / `private` helpers that aren't part of the LN's content.
- `line_start` = the line of the `/-- … -/` Lean-doc comment immediately above the declaration if present, else the declaration head line.
- `line_end` = the last line of the declaration body (closing brace, end of `by` block, etc.).
- `lean_file_path` may be any file in the row's `lean_files`; default is `main_lean_file`.
- `title` is for orchestrator logs only — the website-facing title is computed mechanically from the file path.
- Anchors are listed in source order (per file). The orchestrator may receive anchors that span multiple files; group them by file in display.

The LLM produces the prose articles in clear public-facing language: backticks for Lean identifiers, `$…$` for LN-side math, flowing paragraphs (no headings), ~150–500 words each.

### Stage C — Post-flight (Python)

Parse the worker's JSON, then assemble the final file:

1. **Slice + concat** → `lean_code_with_comments`:
   ```python
   chunks = []
   for a in anchors:                      # source order
       lines = (REPO_ROOT / a["lean_file_path"]).read_text(encoding="utf-8").splitlines()
       s, e = max(1, a["line_start"]), min(len(lines), a["line_end"])
       chunks.append("\n".join(lines[s-1:e]))
   lean_code_with_comments = "\n\n".join(chunks)
   ```
2. **Strip** → `lean_code_without_comments = strip_lean_comments(lean_code_with_comments)`.
3. **Build URL list** → bucket anchors by `lean_file_path`, in first-appearance order:
   ```python
   buckets: dict[str, list[dict]] = {}
   for a in anchors:
       buckets.setdefault(a["lean_file_path"], []).append(a)
   lean_source_urls = []
   for path, group in buckets.items():
       start = min(a["line_start"] for a in group)
       end   = max(a["line_end"]   for a in group)
       lean_source_urls.append({
           "title": Path(path).name,                       # e.g. "Walks.lean"
           "url":   url_template.format(path=path, start=start, end=end),
       })
   ```
4. **Validate**:
   - Anchors are non-empty; line ranges in bounds (clamp + warn if not).
   - Every URL matches `^https://github\.com/`.
   - Prose fields are non-empty strings (warn if either is empty; the worker will be coached).
5. Write the JSON to `tex/<ref>_for_website.json`.

### Stage D — Comment-stripping rules (Python)

State machine over Lean source:

- Track `block_depth`: incremented at `/-` (including `/--`), decremented at `-/`. Lean 4 supports nesting, so the counter matters.
- When `block_depth > 0`, drop every character.
- When `block_depth == 0` and `--` is seen, drop everything to end-of-line.
- Otherwise keep the character.

After the pass: collapse runs of 3+ blank lines into 1, trim trailing whitespace per line.

Applied only to `lean_code_with_comments` to produce `lean_code_without_comments`. The Lean file itself is never modified.

---

## 3. Hard-code vs LLM split

| concern                                                        | done by | rationale                                                                                                                                         |
|----------------------------------------------------------------|---------|---------------------------------------------------------------------------------------------------------------------------------------------------|
| Read tex + Lean source                                         | Python  | trivial I/O                                                                                                                                       |
| Build the GitHub URL template                                  | Python  | mechanical git config parsing                                                                                                                     |
| Decide which Lean declarations are in scope for the row        | **LLM** | needs to distinguish row-relevant declarations from scaffold helpers; uses LN context to judge                                                    |
| Pick `line_start` / `line_end` per anchor (incl. doc comments) | **LLM** | requires reading both files and locating each declaration's range                                                                                 |
| Write `lean_explanation`                                       | **LLM** | natural-language writing                                                                                                                          |
| Write `design_choices`                                         | **LLM** | natural-language writing                                                                                                                          |
| Slice the Lean file at each anchor's range                     | Python  | trivial string ops once line numbers are known                                                                                                    |
| Concatenate slices into `lean_code_with_comments`              | Python  | deterministic                                                                                                                                     |
| Strip comments to produce `lean_code_without_comments`         | Python  | deterministic state machine; LLMs are slow + error-prone at this                                                                                  |
| Bucket anchors by file and build the URL list                  | Python  | trivial dict-of-lists; titles are `Path(file).name`                                                                                               |
| Validate the final JSON                                        | Python  | type + URL + bound checks                                                                                                                         |

---

## 4. Edge cases

| case                                                     | handling                                                                                                                                                                                                                                  |
|----------------------------------------------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Row has one declaration                                  | one anchor; `lean_code_*` are that declaration; URL list has one entry titled with the file's basename.                                                                                                                                    |
| Row spans multiple files                                 | multiple anchors with different `lean_file_path`s; the URL list has one entry per unique file, titled with each file's basename.                                                                                                          |
| Two anchors in the same file                             | concatenated in source order in `lean_code_with_comments`; collapsed into one URL entry whose range covers `[min start, max end]`. The single entry title is the file basename (no collision since one entry per file).                    |
| Anchors overlap (shared helper between two declarations) | allowed; orchestrator warns. The concatenation will include the shared lines twice — minor visual noise; if it ever matters we can de-dup in the slicer. URL still covers the file's total range correctly.                                |
| LLM picks `line_start` too low (drags in design text)    | the design text shows up in `lean_code_with_comments` and is stripped from `lean_code_without_comments`. Visually noisier than intended but not broken. The prompt warns against this.                                                     |
| LLM picks `line_end` past the next declaration           | two declarations appear under one anchor. Orchestrator warns. Not a hard failure.                                                                                                                                                          |
| Anchor range out of file bounds                          | Stage C clamps to `[1, file_line_count]` and warns.                                                                                                                                                                                        |
| `source_anchors` is empty                                | worker is buggy; Stage C falls back to the mechanical scanner (a stripped-down `generate_for_website` that derives anchors from the in-file `-- <ref>` markers and produces empty prose strings).                                          |
| Worker times out / writes invalid JSON                   | same fallback as above. Row's solve still commits; prose fields will be the row's raw comment text rather than polished prose.                                                                                                             |

---

## 5. Files touched

- **`scaffold/claude_prompts/row_workers/produce_for_website.md`** — rewrite around the Stage B contract: emit only prose + anchors.
- **`scaffold/solve_chapter.py`**:
  - Stage A: URL-template builder (once per orchestrator run; cached on the OrchestrationState or module-level).
  - Stage C: slice/concat/strip/bucket/validate; replaces the body of `run_for_website_worker`.
  - Stage D: `strip_lean_comments(text: str) -> str`.
  - Replace `generate_for_website` (mechanical fallback) to emit the new schema with empty prose strings.
- **`extras/temp_for_website_builder.md`** — refresh the schema description, drop the old list-shaped `lean_statement` documentation, document the comments-on/off UI toggle, document `lean_source_urls` as an ordered list with file-basename titles.
- **`extras/test_for_website_generation.py`** — update pretty-printer to:
  - print `len(lean_code_with_comments)` + `len(lean_code_without_comments)` + first 200 chars of each;
  - list URL count + each `{title, url}` pair;
  - print prose lengths + first 200 chars of each prose field.
- **`extras/run_for_website_batch.py`** — unchanged; remains the entry point for the chapter-3 backfill.
- **Backfill** every `*_for_website.json` under `leanification/Chapter*/Section*/tex/`.

---

## 6. Migration / backfill

After the refactor lands:

1. Pick a couple of representative rows manually, run `extras/test_for_website_generation.py 3 <i>` on each, eyeball the output:
   - **def_3_1 CDMG** — one structure, one anchor, one URL.
   - **def_3_2 CDMGNotation** — Membership + 6 edge-relation defs, expect ~7 anchors collapsing into 1 URL.
   - **def_3_4 Walks** — many sub-defs spanning ~600 lines, expect 6–10 anchors collapsing into 1 URL.
   - **claim_3_1 JNodeProperties** — 3 theorems, expect 3 anchors collapsing into 1 URL.
   - For each: with-comments code carries only internal comments; without-comments code is the same minus comments; URL opens to the right lines on GitHub.
2. If happy, kick off `extras/run_for_website_batch.py 3 0 32` to regenerate all 33 chapter-3 JSONs. ~2.5h estimated.
3. Commit + push in one go.

The website-builder side will need a reader update for the new schema. Coordinate so the reader change + the regenerated JSONs land together.

---

## 7. Test plan

Per the migration step 1 above plus:

- Spot-check a multi-file row if one exists in chapter 3 (e.g. claim_3_4 produced multiple Lean files) — confirm the URL list has multiple entries with distinct file-basename titles.
- Verify the comment-stripper on a fresh sample: feed it a Lean block with nested `/- /- … -/ -/` and a `/-- … -/` doc and a `-- line` comment; assert all three vanish.
- Confirm the worker fallback path: temporarily break the worker prompt (or simulate a worker timeout) and check that `generate_for_website` writes the new-schema JSON with anchors derived from `-- <ref>` markers and empty prose strings.

---

## Recap

- One Lean code panel per row; toggle between with-comments and without-comments.
- One explanation article, one design-choices article.
- `lean_source_urls` is an ordered list of `{title, url}` pairs, one per Lean file the row touches, with `title = basename(file)`.
- The LLM picks **anchors** (line ranges per declaration) and writes the two prose blocks. Python does everything else: slice, concat, strip, bucket, build URLs, validate.
- Backfill via `extras/run_for_website_batch.py` after the refactor lands.

Awaiting greenlight to implement.
