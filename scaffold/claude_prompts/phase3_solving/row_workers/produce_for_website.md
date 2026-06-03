# Worker — produce a `<ref>_for_website.json` *draft*

**When to use:** the row has just been verified solved. The orchestrator dispatches you, one-shot, to draft the JSON the website builder will consume. After your message returns, the orchestrator post-processes your draft (slicing Lean source, stripping comments, building GitHub URLs) and overwrites the file with the final JSON. Then the orchestrator commits + pushes.

You are not solving anything new. The Lean file is final; the tex files are final. Your job is to *select anchors* and *write two short prose articles* for a public-facing website.

## Inputs (provided in the row-context block below)

- `ref`, `title`, `type`, `def_or_claim`, `section`
- `main_lean_file` — repo-relative path of the canonical Lean file for the row
- `lean_files` — every Lean file the verifier reported for this row (may be one or more)
- `tex statement` / `tex proof` paths — read them so your prose maps Lean to LN
- `output path` — where to write the draft JSON

## What to write

A single JSON file at `output path` with **exactly** these three fields:

```json
{
  "lean_explanation": "<polished article, ~150–500 words>",
  "design_choices":   "<polished article, ~150–500 words>",
  "source_anchors": [
    {
      "title":          "CDMG",
      "lean_file_path": "leanification/Chapter3_GraphTheory/Section3_1/CDMG.lean",
      "line_start":     17,
      "line_end":       120
    },
    ...
  ]
}
```

**Don't add other keys.** The orchestrator copies `ref`/`title`/`type`/`def_or_claim`/`section`/`lean_file_path` from the row context and computes `lean_code_with_comments` / `lean_code_without_comments` / `lean_source_urls` mechanically from your anchors. Extra keys in your draft are ignored.

### `source_anchors` — what each anchor means

The anchors are the central abstraction. Each anchor names a Lean line range that the orchestrator will:

1. Slice verbatim out of the Lean file and concatenate into `lean_code_with_comments` (the comments-on view).
2. Strip of comments to produce `lean_code_without_comments` (the comments-off view).
3. Bucket by file to build one `{title: <file basename>, url: ...}` entry per unique Lean file.

So your anchor's `[line_start, line_end]` decides three things at once: what code appears, what gets stripped, and where the source-URL points. Pick the range so it bracket a **single Lean declaration** plus its leading `/-- ... -/` doc comment if any, and excludes the surrounding orchestrator bookkeeping.

Per-anchor rules:

- **One anchor per Lean declaration** that corresponds to LN-level content. Exclude helper lemmas, `@[simp]` membership lemmas, scaffold `instance` declarations, and `private` helpers that don't appear in the LN.
- **`line_start`** = the line of the `/-- ... -/` Lean-doc comment immediately above the declaration if present, else the declaration head line (`structure ...`, `theorem ...`, etc.). Include the doc comment so the reader sees the inline documentation.
- **`line_end`** = the last line of the declaration body (closing brace for `structure`, last `| case` for `inductive`, last line of the `by` block for `theorem`/`lemma`).
- **DO NOT include**: the `-- <ref>` / `-- title:` orchestrator markers, the `## Design choice` `--` blocks (those become the `design_choices` article), the `/- Verbatim from … -/` LN-citation blocks, the long `--` explanation paragraphs above the declaration.
- **`title`** — for orchestrator logs only (the website-facing title is computed as the file basename). Use the Lean identifier name (`CDMG`, `WalkStep`, `no_arrowhead_into_input`). For multi-part claims, use the part's theorem name (e.g. `no_arrowhead_into_input`, `input_edge_target_mem_V`).
- **`lean_file_path`** — any file listed in the row's `lean_files`. Most rows use `main_lean_file` only. If the row's formalization spans multiple files, emit anchors for each file as needed.
- **Anchors are listed in source order per file.** When two files are involved, group by file: all anchors for file A first (in order), then all anchors for file B (in order).

### `lean_explanation` — content

Polished Markdown prose, ~150–500 words, flowing paragraphs (no headings). For a reader who knows mathematics but is reading the Lean encoding for the first time. Cover, in this order, what applies:

1. **What each Lean variable / binder corresponds to** in the LN's notation. e.g. *"`α : Type*` is the ambient vertex type, matching the LN's silent assumption that the graph is over some carrier."*
2. **Non-trivial Mathlib idioms used.** Anything a mathematician outside Lean wouldn't immediately recognise: `Disjoint`, `×ˢ`, `⦃⦄` strict-implicit binders, `Set.prod`, `Quotient.lift`, etc. One short sentence each.
3. **The shape of the encoding.** A single short paragraph: *"the definition bundles N data fields and M constraint fields"*, *"the theorem takes hypotheses X and Y and concludes Z"*. No proof strategy.

Inline backticks for Lean identifiers; inline `$…$` for LN-side math.

### `design_choices` — content

Polished Markdown prose, same style as `lean_explanation`. Each non-obvious encoding decision is its own paragraph: lead with a bolded one-line summary, then explain the alternative(s) and why they were rejected.

Pull material from the Lean file's `## Design choice` `--` block if present — but **rewrite for a public reader**. The in-file comments are written for the next maintainer; here we want a curious mathematician who's wondering why the formalization looks the way it does. Drop in-jokes, scaffold-isms, and references to other ref names unless they're already well-known to the reader.

If the Lean file has no design notes (rare), write a single short paragraph: *"This row admits a single natural encoding; see the source file for the definition."* Don't fabricate trade-offs.

## How to do it

1. Read the row context block at the bottom.
2. Read `main_lean_file` in full. For multi-file rows, read the other `lean_files` too.
3. Read the tex statement file (so your prose maps Lean names back to LN symbols).
4. Decide which declarations get anchors. Pick the line ranges.
5. Write the JSON file at `output path` using `Write`.

## Rules

- **Edit no Lean file. Edit no tex file. Only write the JSON.**
- **Don't run `lake build`.** The row is already verified.
- **Don't touch `data.json`, `agent_registry`, or any orchestrator state.**
- **Three keys exactly** in the JSON (`lean_explanation`, `design_choices`, `source_anchors`). The orchestrator's post-flight adds the rest.
- **JSON must be valid** (parseable by `json.loads`). Use double quotes; escape backslashes and newlines as `\\` / `\n` inside strings. Use UTF-8.
- **Anchors must have all four keys** (`title`, `lean_file_path`, `line_start`, `line_end`) and the line numbers must be 1-indexed integers with `line_start <= line_end`.

## Report back

End your message with:

```
WROTE: <output path>
```

followed by a one-paragraph summary that names each anchor's `title` and what your prose fields covered. The orchestrator log uses this to spot-check at a glance.
