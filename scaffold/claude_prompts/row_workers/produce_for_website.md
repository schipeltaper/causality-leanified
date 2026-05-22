# Worker — produce the row's `<ref>_for_website.json` file

**When to use:** the row has just been verified solved. The orchestrator dispatches you, one-shot, to write the JSON file the website builder will consume. After your work the orchestrator commits + pushes everything; this is the last step before the commit.

You are not solving anything new. The Lean file is final, the tex statement / proof files are final. Your job is to *summarise and curate* the row for a public-facing website.

## Inputs you receive from the orchestrator

- `ref`, `title`, `type`, `def_or_claim`, `section`
- `main_lean_file` — repo-relative path of the canonical Lean file for this row
- `lean_files` — all Lean files the verifier reported for this row (a row may span several)
- `tex statement path` and (for claims) `tex proof path` — for reference only; the website already reads them directly, so don't include their contents in the JSON
- `output path` — where to write the JSON

## What to write

A single JSON file at the `output path` with **exactly** these fields:

```json
{
  "ref":             "<row ref>",
  "title":           "<row title>",
  "type":            "<row type>",
  "def_or_claim":    "def" | "claim",
  "section":         "<section>",
  "lean_file_path":  "<repo-relative path of main_lean_file>",
  "lean_statement":  [ {"name": "...", "kind": "...", "code": "..."}, ... ],
  "lean_explanation": "<see below>",
  "design_choices":  "<see below>"
}
```

The six bookkeeping fields (`ref`/`title`/`type`/`def_or_claim`/`section`/`lean_file_path`) you copy verbatim from the row context.

### `lean_statement`  ← **LIST**, not a string

`lean_statement` is a **JSON list of objects**, one element per *distinct sub-statement* in the LN block.

Why a list: the LN often packs several pieces into a single Def/Lem block. `def 3.4 "Walks"` defines a walk-step type, the walks themselves, walk reversal, length, support, append, etc. — half a dozen LN-level concepts in one `\begin{Def}`. Each of these should be its own list element with its own Lean code, so the website can show them side-by-side with the LN.

For multi-part claims (`-- <ref> (part 1/3)` / `-- <ref> (part 2/3)` / ...) and multi-item defs (`-- <ref> (item N, ...)`), the orchestrator's ref-marker comments in the Lean file already segment the row — use those as your guide, but **scan the LN tex statement first** to make sure each LN-level concept ends up in its own element, even if multiple Lean declarations back it.

Each element has exactly these keys:

```json
{
  "name": "<the Lean identifier of the declaration>",   // e.g. "WalkStep", "Walk", "no_arrowhead_into_input"
  "kind": "<theorem|lemma|example|def|abbrev|structure|class|instance|inductive>",
  "code": "<the Lean code: signature only for theorems, full body for structures/defs>"
}
```

`code` content rules per element:

- **structure / inductive / class**: the full declaration, including all field doc comments (`/-- ... -/` lines). Plus any leading `/-- ... -/` Lean-doc comment immediately preceding it.
- **def / abbrev**: the declaration head + body if short (one-liner); for longer defs that recursively pattern-match (e.g. `Walks.reverse`), include the full body — it's part of the definition. Plus any leading `/-- ... -/` Lean-doc.
- **theorem / lemma / example**: the *signature only*, trimmed at `:= by` (keep the `:= by` token so the reader sees where the proof begins). **No proof tactics.** Plus any leading `/-- ... -/` Lean-doc.

Strip from every element:

- the `-- <ref>` / `-- title: ...` ref-marker comments (orchestrator bookkeeping),
- any `-- ...` / `/- ... -/` design / explanation comments above the declaration (those go into `lean_explanation` / `design_choices` instead),
- **but keep** the `/-- ... -/` Lean-doc immediately preceding the declaration — that's part of the public-facing definition.

**Exclude helpers**: `@[simp]` membership lemmas, auxiliary `instance` declarations, helper `def`s that don't correspond to an LN-level concept. Include only what the LN block introduces (or what is *strictly* required to state it — rare; in that case add a one-line `--` comment above it noting "helper required to state the row").

**List order**: source order in the Lean file (i.e. the order in which the ref-markers appear). For rows with a single declaration, the list has length 1.

### `lean_explanation`

Polished prose (Markdown, but plain paragraphs — no headings) explaining the Lean encoding for a reader who knows mathematics but is reading the formal statement for the first time. Cover, in this order, only what applies:

1. **What each variable / binder stands for.** The mapping from Lean names to the LN's symbols. e.g. *"`α : Type*` is the ambient vertex type, matching the LN's silent assumption that the graph is over some carrier."*
2. **Non-trivial Mathlib idioms used.** Anything that a mathematician outside Lean wouldn't immediately recognise: `Disjoint`, `×ˢ`, `⦃⦄` strict-implicit binders, `Set.prod`, `Quotient.lift`, etc. Brief, one sentence each.
3. **The shape of the encoding.** A single short paragraph: *"the definition bundles N data fields and M constraint fields"*, or *"the theorem takes hypotheses X and Y and concludes Z"*. No proof strategy here.

Stay tight. Aim for 100–400 words. No bullet headings; flowing prose with inline backticks for Lean identifiers and `$…$` for the matching LN symbols where useful.

### `design_choices`

Polished prose (same style as `lean_explanation`) explaining the **non-obvious encoding decisions** and what alternatives were considered. Each major decision is its own paragraph; lead with a bolded one-line summary, then explain the alternative(s) and why they were rejected.

Pull from the `-- ## Design choice` block in the Lean file if present — but **rewrite it for a public reader**: the in-file comments are written for the next maintainer; here we want a reader who is curious why the formalization looks the way it does. Drop in-jokes, scaffold-isms, and references to other ref names unless they're already well-known to the reader.

If the Lean file has no design notes (rare), produce a short paragraph along the lines of *"This row admits a single natural encoding; see `<lean_file_path>` for the definition."* — don't fabricate trade-offs.

## How to do it

1. Read the row context block (passed to you below).
2. Read `main_lean_file` in full. Identify the ref-marker, the declaration, and any `--` / `/-` blocks above it.
3. Read the LN tex statement file at the path given (so the variable-name mapping in `lean_explanation` is grounded in the LN's symbols).
4. Write the JSON file at `output path` using `Write`. Don't print the contents to chat — only the path + a one-line confirmation.

## Rules

- **Edit no Lean file.** Edit no tex file. You only create the JSON.
- **Don't run `lake build`.** The row is already verified.
- **Don't touch `data.json`, `agent_registry`, or any orchestrator state.**
- **The five JSON keys are fixed.** Don't add or rename keys; the website builder reads them by name.
- **JSON must be valid** (parseable by `json.loads`). Use double quotes; escape backslashes and newlines as `\\` / `\n` inside string fields.
- **Be concise.** This is for a public reader; over-long entries hurt readability.

## Report back

End your message with:

```
WROTE: <output path>
```

followed by a one-paragraph summary of what you put in each of the three prose fields (so a human glancing at the orchestrator log knows what landed). Nothing else.
