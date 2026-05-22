# Temp doc — wiring the website builder to `<ref>_for_website.json`

**Audience:** the agent that will update `building_website/` to consume the new per-row JSON the orchestrator produces. This doc explains what changed in the leanification side, what the new JSON contains, and what the website builder should do with it. The doc is temporary; delete it once the website builder is migrated.

---

## What changed in the orchestrator

After a row in `leanification/Chapter*/data.json` is marked `solved`, the orchestrator now writes one extra file alongside the existing tex statement / tex proof:

```
leanification/Chapter<N>_<Title>/Section<N>_<M>/tex/<ref>_for_website.json
```

This file is produced *by a Claude worker* (see `scaffold/claude_prompts/row_workers/produce_for_website.md`) right after the row is verified solved and right before the per-row commit. So it lands in the same commit as the row's Lean + tex artefacts. A mechanical Python fallback runs if the worker times out or produces invalid JSON.

The orchestrator does NOT update existing solved rows automatically — only newly-solved rows get the worker-produced JSON. Currently-solved rows have a mechanically-extracted version written via the fallback path (good enough for testing but lower prose quality).

## JSON schema

Exactly nine fields, all top-level:

```json
{
  "ref":              "def_3_1",                                                    // primary key
  "title":            "CDMG",                                                       // PascalCase short name (matches filenames)
  "type":             "definition",                                                 // data.json "type" column: definition/lemma/remark/note/proposition/...
  "def_or_claim":     "def",                                                        // "def" | "claim"
  "section":          "3.1",
  "lean_file_path":   "leanification/Chapter3_GraphTheory/Section3_1/CDMG.lean",    // repo-relative; the canonical Lean file (= row.main_lean_file)
  "lean_statement":   "structure CDMG (α : Type*) where ...",                       // signature only -- no proofs, no helpers, no -- comments above
  "lean_explanation": "A *conditional directed mixed graph* over an ambient ...",   // polished Markdown prose for a public reader
  "design_choices":   "**Polymorphic `α : Type*`.** The LN does not commit ..."     // polished Markdown prose explaining encoding trade-offs
}
```

### `lean_statement` content rules

- **Definitions** (`def_or_claim = "def"`): the `structure` / `def` / `abbrev` / `class` / `inductive` block, with any leading `/-- ... -/` doc comment, but **without** trailing helper lemmas, `@[simp]` membership lemmas, instance declarations, etc. Just the LN-corresponding construct.
- **Claims** (`def_or_claim = "claim"`): the `theorem` / `lemma` / `example` *signature only*, terminated at `:= by` (the proof body is dropped). Multi-part claims include every part's signature, separated by a blank line, in source order.
- Leading `--` ref-marker comments (`-- def_3_1` / `-- title: ...`) are stripped; design and explanation comments above the declaration are also stripped (they go into the prose fields).

### `lean_explanation` content rules

Polished Markdown prose (~100–400 words, flowing paragraphs, no headings) describing:

1. What each Lean variable / binder corresponds to in the LN's notation.
2. Any non-trivial Mathlib idiom used (`Disjoint`, `×ˢ`, `⦃⦄` strict-implicit binders, `Set.prod`, `Quotient`, etc.) — one short sentence each.
3. A short paragraph on the shape of the encoding (e.g. "the definition bundles N data fields and M constraint fields", or "the theorem takes hypotheses X, Y and concludes Z").

Inline backticks for Lean identifiers; inline `$…$` for LN symbols where useful. No proof strategy here.

### `design_choices` content rules

Polished Markdown prose explaining the non-obvious encoding decisions. Each decision is its own paragraph, leading with a bolded one-line summary, then explaining the alternative(s) considered and why they were rejected. The orchestrator's worker rewrites the Lean file's `## Design choice` block for a public reader (dropping in-jokes, scaffold-isms, and references to other refs that wouldn't be familiar).

## What the website builder needs to do

Two changes:

1. **Read `<ref>_for_website.json` directly** instead of regenerating `lean_explanation` / `design_choices` from raw Lean comments. The fields are already in the form the website should display.

2. **Keep using the existing extractors** for the other fields:
   - The tex statement and tex proof are still at the same paths under `tex/` and should be processed through `tex_to_html.py` as before. The new JSON does **not** include the rendered tex HTML.
   - The Lean file's raw comments / per-part split / source-line numbers (used for the `lean[]` array of "blocks") can still be extracted from the Lean file directly — `lean_statement` in the new JSON is a *single*, *curated* string for the display panel, not a structured part-by-part decomposition. If you want both, keep your existing structured extractor for the per-part view and use the JSON's `lean_statement` for a "canonical statement" panel.

In short: the new JSON gives you (a) the publication-ready prose for the explanation and design-choice panels, and (b) a pre-curated `lean_statement` string. Everything else stays.

## Pipeline interactions

- The orchestrator's worker writes the file at solve-time, so by the time the website builder runs against the repo, the JSON is already in `tex/`.
- A row that's not yet solved has no `_for_website.json`. The website builder should treat the file's absence as "row not ready for publication" and skip those rows from the manifest (current behavior already filters by `solved == "yes"`, so this should be automatic).
- The website builder should **not** mutate `_for_website.json`. If a field needs polishing or correction, the right fix is to update the Lean file's design-choice block + re-run the orchestrator's worker (or open a PR against the JSON directly — but the worker is the source of truth going forward).

## Locating the helper

If you want to spot-check the worker output yourself, the worker prompt is at `scaffold/claude_prompts/row_workers/produce_for_website.md`. The orchestrator runs it via `run_for_website_worker` in `scaffold/solve_chapter.py`. The fallback mechanical extractor (used only if the worker fails) is `generate_for_website` in the same file.

## When this doc can go

Once the website builder no longer regenerates `lean_explanation` / `design_choices` from raw Lean comments — i.e., once its `process_lean_comments.py` either uses the JSON or is gone — `extras/temp_for_website_builder.md` can be deleted.
