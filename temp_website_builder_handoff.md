# Temp handoff — website builder reads `<ref>_for_website.json`

The orchestrator now writes one per-row JSON the website should consume directly. Delete this file once `building_website/` is migrated.

## Where the files live

```
leanification/Chapter<N>_<Title>/Section<N>_<M>/tex/<ref>_for_website.json
```

One file per solved row (e.g. `Section3_1/tex/def_3_1_for_website.json`). All currently-solved rows in chapter 3 (sections 3.1, 3.2, and `def_3_15`) have one. Rows that aren't yet solved have no file — skip them.

## Schema (11 fields, all top-level)

| field                       | type                                | what it carries                                                                                                |
|-----------------------------|-------------------------------------|----------------------------------------------------------------------------------------------------------------|
| `ref`                       | string                              | primary key (`def_3_1`, `claim_3_4`, ...)                                                                       |
| `title`                     | string                              | PascalCase short name (matches filenames)                                                                       |
| `type`                      | string                              | `definition` / `lemma` / `remark` / `note` / `proposition` / `notation` / `example`                              |
| `def_or_claim`              | `"def"` \| `"claim"`              |                                                                                                                |
| `section`                   | string                              | e.g. `"3.1"`                                                                                                    |
| `lean_file_path`            | string                              | repo-relative path of the canonical Lean file                                                                   |
| `lean_code_with_comments`   | string                              | Lean code panel, with all internal comments preserved (`--`, `/- -/`, `/-- -/`)                                  |
| `lean_code_without_comments`| string                              | same code, every comment stripped — used for the comments-off toggle                                            |
| `lean_explanation`          | string                              | polished ~150–500 word Markdown article on what the Lean code does and how it maps to the LN                    |
| `design_choices`            | string                              | polished ~150–500 word Markdown article on encoding trade-offs                                                  |
| `lean_source_urls`          | list of `{"title": str, "url": str}` | one entry per unique Lean file the row touches; `title` is the file basename (`"CDMG.lean"`); `url` is a GitHub `…/blob/<branch>/<path>#L<start>-L<end>` link covering the row's content in that file |

Both code-panel strings have **the same structural content** (same declarations, same order, same line breaks) — they differ only in whether comments are present. The website toggles between them.

`lean_source_urls` is a list (not a dict) so ordering is explicit. Most rows have one entry; a row whose formalization spans multiple Lean files has one entry per file.

`lean_explanation` and `design_choices` may be empty strings if the worker's mechanical fallback fired without comment content to draw on. Render a graceful placeholder in that case.

## What to do with it

Three changes versus the previous extraction approach:

1. **Read `<ref>_for_website.json` directly** — stop regenerating `lean_explanation` / `design_choices` from raw Lean comments. The JSON has them in publication-ready form.
2. **Drop any per-part Lean-block extractor** — there's no per-part decomposition any more. Display `lean_code_with_comments` as one panel; offer a toggle to switch to `lean_code_without_comments`.
3. **Use `lean_source_urls` directly** for "view source on GitHub" buttons — one button per entry. Title goes on the button label, URL is the click target.

The existing **tex statement / tex proof pipeline stays unchanged** — those files are still under `tex/` and still go through `tex_to_html.py`. The for-website JSON does not include rendered tex HTML.

## How fresh JSONs get produced

The orchestrator dispatches a one-shot worker (`scaffold/claude_prompts/row_workers/produce_for_website.md`) right after each solve. The worker only emits a draft (`lean_explanation`, `design_choices`, `source_anchors`); Python in `scaffold/solve_chapter.py` post-processes (slices Lean lines, strips comments, builds URLs) and overwrites with the final JSON. So the JSON is already correct on disk when you run against the repo.

## When this doc can go

Once the website builder consumes the JSON instead of regenerating its prose fields from raw comments, this file can be deleted.
