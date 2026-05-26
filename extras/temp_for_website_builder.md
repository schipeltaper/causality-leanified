# Temp doc — wiring the website builder to `<ref>_for_website.json`

**Audience:** the agent that will update `building_website/` to consume the per-row JSON the orchestrator produces. This doc explains what's in the JSON and what the website builder should do with it. The doc is temporary; delete it once the website builder is migrated.

---

## What the orchestrator writes

After a row in `leanification/Chapter*/data.json` is marked `solved`, the orchestrator writes one extra file alongside the existing tex statement / tex proof:

```
leanification/Chapter<N>_<Title>/Section<N>_<M>/tex/<ref>_for_website.json
```

The file is produced by a Claude worker (`scaffold/claude_prompts/row_workers/produce_for_website.md`) right after the row is verified solved and right before the per-row commit, so it lands in the same commit. A mechanical Python fallback (`generate_for_website` in `scaffold/solve_chapter.py`) takes over if the worker times out, fails to launch, writes invalid JSON, or omits required fields — in that case the prose fields are populated from raw Lean comments rather than polished prose.

## JSON schema

Eleven top-level fields. `lean_source_urls` is an ordered list of `{title, url}` pairs; everything else is a string or an enum-like field copied from the row context.

```jsonc
{
  "ref":              "def_3_4",                                                    // primary key
  "title":            "Walks",                                                       // PascalCase short name (matches filenames)
  "type":             "definition",                                                  // data.json "type" column
  "def_or_claim":     "def",                                                         // "def" | "claim"
  "section":          "3.1",
  "lean_file_path":   "leanification/.../Walks.lean",                                // repo-relative; the canonical Lean file (= row.main_lean_file)

  // The "with-comments" Lean code panel: a verbatim slice of the Lean
  // file at the anchors chosen by the worker (or by the fallback
  // scanner), concatenated in source order. Internal -- / /- -/ /-- -/
  // comments survive; outer design/explanation blocks are excluded by
  // anchor choice.
  "lean_code_with_comments":    "/-- A single edge in a walk ... -/\ninductive WalkStep ... where\n  ...\n\ninductive Walk ... where\n  | nil ...\n",

  // The "without-comments" variant: same string with all -- / /- -/
  // /-- -/ comments stripped by a deterministic state machine.
  // The website toggles between this and lean_code_with_comments.
  "lean_code_without_comments": "inductive WalkStep ... where\n  ...\n\ninductive Walk ... where\n  | nil ...\n",

  // ~150-500 word polished article, plain Markdown paragraphs (no
  // headings), inline backticks for Lean identifiers and $...$ for LN
  // math. Maps Lean names to LN symbols, names non-trivial Mathlib
  // idioms used, sketches the encoding shape.
  "lean_explanation": "The walks definition introduces ...",

  // ~150-500 word polished article. Each non-obvious encoding decision
  // is one paragraph leading with a bolded one-line summary, followed
  // by the rejected alternatives. Rewrites the in-file `## Design choice`
  // block for a public reader.
  "design_choices":   "The most subtle choice is ...",

  // One entry per unique Lean file the row's formalization lives in.
  // Title is the file basename. URL covers [min line_start, max line_end]
  // across all anchors in that file. Branch-pinned (so URLs track the
  // current state of the branch; line numbers may drift on file edits
  // and re-pin the next time the row is re-solved).
  "lean_source_urls": [
    { "title": "Walks.lean",
      "url":   "https://github.com/schipeltaper/causality-leanified/blob/server_setting_up_scaffold/leanification/.../Walks.lean#L127-L533" }
  ]
}
```

### Notes on each field

- **`lean_code_with_comments` / `lean_code_without_comments`** — both strings are derived mechanically from the worker's `source_anchors` (the worker chooses line ranges; Python slices verbatim and strips). The website toggles between the two; they share the same structural shape (same declarations, same order), just with or without inline Lean comments.
- **`lean_source_urls`** — a list (not a dict). Order is the order in which the worker's anchors first reference each file. For a row whose formalization fits in one file (the typical case), this is a list of one entry. For multi-file rows it has one entry per file. Title is the file basename so the user sees "Walks.lean" / "WalkExtensions.lean" / etc. URL ranges span the union of anchor ranges in each file.
- **`lean_explanation` / `design_choices`** — both can be empty strings if the fallback path fired and the source file had no comment content to draw on. Treat empty fields gracefully (don't crash; render a "no explanation written yet" placeholder).

## What the website builder needs to do

Three changes:

1. **Read `<ref>_for_website.json` directly** instead of regenerating `lean_explanation` / `design_choices` from raw Lean comments. The fields are already in publication-ready form.

2. **Replace the per-part Lean-block extractor** with the JSON's two code-panel strings + the comments toggle. `lean_code_with_comments` is the displayed code; `lean_code_without_comments` is the alternate view when the toggle is off. There's no per-part decomposition any more — one code panel per row.

3. **Use `lean_source_urls` directly** for "view source on GitHub" buttons. One button per entry (typically just one). Title goes on the button label; URL is the click target.

The existing **tex statement / tex proof extractors stay** — those files are still at the same paths under `tex/` and should be processed through `tex_to_html.py` as before. The for-website JSON does not include the rendered tex HTML.

## Pipeline interactions

- The orchestrator writes the JSON at solve-time, so it's on disk by the time the website builder runs against the repo.
- A row that's not yet solved has no `_for_website.json`. The website builder should treat the file's absence as "row not ready for publication" and skip it (the current filter `solved == "yes"` should already cover this).
- The website builder should **not** mutate `_for_website.json`. Corrections go via updating the Lean file's `## Design choice` block + re-running the orchestrator's worker (or opening a PR against the JSON directly, but the worker is the source of truth).

## Status as of today (chapter 3)

Every solved row in chapter 3 (all of sections 3.1 + 3.2 plus def_3_15 in 3.3, ~34 rows) has a worker-polished JSON in the v3 schema. Newly-solved rows pick up the worker path automatically as part of the orchestrator's cleanup-on-solve.

## Locating the helpers

- **Worker prompt**: `scaffold/claude_prompts/row_workers/produce_for_website.md` — instructs the worker to emit `{lean_explanation, design_choices, source_anchors}` only. The orchestrator post-processes the draft into the final JSON.
- **Orchestrator runner**: `run_for_website_worker(row, subsection_folder)` in `scaffold/solve_chapter.py` — called from the `solved` branch of `solve_current_row`, before the per-row commit.
- **Mechanical fallback**: `generate_for_website` in the same file — fires only when the worker fails. Produces the v3 schema with raw-comment-derived prose.
- **Standalone helpers** under `extras/`:
  - `test_for_website_generation.py <chapter> <row_index>` — drive the worker on one row, pretty-print the resulting JSON's structure.
  - `run_for_website_batch.py <chapter> <start_row> <end_row>` — loop the worker over a contiguous range (used for chapter-wide backfills).

## When this doc can go

Once the website builder no longer regenerates `lean_explanation` / `design_choices` from raw Lean comments — i.e. once its `process_lean_comments.py` either uses the JSON or is gone — `extras/temp_for_website_builder.md` can be deleted.
