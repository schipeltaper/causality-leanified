# Worker — plan and apply a refactor (heavy redesign with trickle-down)

**When to use:** the manager has decided that a Lean object — typically a foundational definition, but sometimes a notation or a structural choice — has the wrong shape, and that getting it right requires not just changing the object itself but **re-doing every row that built on it**.

This is the heaviest operation in the project. The goal is "do it correctly the first time around" so we rarely need this. When we do need it, your job is to:

1. **Plan** the refactor (the foundational change + every downstream consequence).
2. **Persist** the plan to `leanification/refactors/refactor_<title>.json`.
3. **Apply** the plan by resetting every affected row across **all** chapter `data.json` files back to `not solved`, deleting the Lean files those rows produced, and seeding `tips` on each affected row so the next manager who picks it up knows why.

After you return, the orchestrator ends the current row's run; the next `solve_chapter` iteration will start with the redesigned foundation (the first-unsolved row will be the earliest affected `ref`).

## Inputs you should receive from the manager

- The current row's context (you may be running while a row was in progress).
- A description of what is being refactored and **why** — what design pain made this necessary.
- A proposed new shape (in words, not Lean code yet) for the foundational object.

## Step 1: Read enough to plan honestly

Before touching anything:

- Re-read `claude.md` and skim the LN's `main.tex` so you know the chapter order.
- Read the **entire lecture notes** — start at `lecture-notes/lecture_notes/main.tex` and follow its `\input` chain. A refactor that looks safe in one chapter often hits four other chapters; this is the moment to find that out.
- For each chapter folder under `leanification/`, open its `data.json` and skim every solved row's `tex_block` to find references to the concept you're refactoring (use `grep`-style file reads liberally — there is no token shortage for this worker).
- Open every Lean file touched by those rows; trace the usage graph. The transitive closure is what gets unsolved.

## Step 2: Pick a title and decide the plan

- Title: short PascalCase, suitable for a filename (e.g. `CDMGWithExplicitInputs`, `WalksAsCoinductive`).
- Plan rows. The **first row** is always the foundational redesign itself. Subsequent rows are downstream consumers in dependency order (so the foundation can be redone before the consumers). Each row has:
  - `ref` — the row's ref in some chapter's `data.json` (e.g. `def_3_5`).
  - `chapter` — the chapter folder containing that ref (e.g. `Chapter3_GraphTheory`).
  - `kind_of_change` — `"redesign"` (the foundational change) or `"update"` (consumer needs to be re-done because of the foundation change).
  - `rationale` — one sentence explaining what about this row will change, written so the *next* manager working on this row can immediately understand the new shape.
  - `status` — `"pending"` for everything you create now. The orchestrator (or a future you-helper) flips this to `"done"` when the corresponding `data.json` row gets re-solved.

## Step 3: Write the plan file

Create the directory if it doesn't exist:

```
leanification/refactors/refactor_<title>.json
```

Schema:

```json
{
  "title": "<PascalCaseTitle>",
  "rationale": "<two-or-three-sentence why; this is what a future reader will read first>",
  "proposed_new_shape": "<paragraph describing the target Lean shape>",
  "date_started": "<UTC ISO date>",
  "date_completed": "",
  "columns": ["ref", "chapter", "kind_of_change", "rationale", "status"],
  "rows": [
    {"ref": "def_3_5", "chapter": "Chapter3_GraphTheory", "kind_of_change": "redesign", "rationale": "...", "status": "pending"},
    {"ref": "claim_3_2", "chapter": "Chapter3_GraphTheory", "kind_of_change": "update", "rationale": "uses def_3_5 in its proof's induction step; needs to be re-proven with the new shape", "status": "pending"},
    ...
  ]
}
```

Pretty-print the JSON (`indent=2`, `ensure_ascii=False`).

## Step 4: Apply the plan to every affected `data.json` row

For each row in `rows` above (including the foundational `redesign` row):

1. Open the corresponding chapter's `data.json`. Find the row with the matching `ref`.
2. Reset the row's solve-state fields **exactly** as follows:
    - `formalized` → `"no"`
    - `proven` → `"not proven"` if `def_or_claim == "claim"`, else `"n/a"`
    - `solved` → `"no"`
    - `date_solved` → `""`
    - `lean_files` → `[]`
    - `main_lean_file` → `""`
    - `agent_registry` → `[]`
3. **Append** to the row's `tips` field (don't overwrite anything that was there):

   ```
   <existing tips, if any, with a blank line separator>
   refactor_<title> (<UTC ISO date>): being redone because of the foundational redesign of <foundational ref>. <one-or-two-sentence note from this row's `rationale` field, lightly rewritten so it makes sense to a manager that hasn't read the refactor plan>.
   ```
4. Save the data.json.
5. **Delete every Lean file** that was listed in the row's old `lean_files` (do this AFTER updating the data, so the row's record of which files to delete is captured first). Also remove any `workspace_<ref>.md` file in the subsection folder.
6. Regenerate the corresponding subsection's `main.tex` so it no longer references deleted files. (The tex stubs under `<subsection>/tex/` you can leave — they have the LN block content and will be re-used when the row is re-solved. They'll get fresh proof bodies, etc.)
7. Regenerate the chapter's `<Chapter>.lean` aggregator so it no longer imports the deleted modules.

(You can `\input` `scaffold/solve_chapter.py` helpers if Python is reachable from inside your worker context; otherwise emulate them — the regeneration logic is in `regenerate_chapter_aggregator` and `regenerate_subsection_main_tex`.)

## Step 5: Verify your own work and report back

Run `lake build` from `/home/11716061/repo_scaffold2/`. Build is **expected to fail** mid-refactor (modules that used the deleted ones are referenced and missing — that's *correct*; the orchestrator will re-do them). What you're checking is: there are no syntax errors in the JSON, no orphan `import` lines pointing at files you didn't actually delete, no stray references.

Report back to the manager in this exact form:

```
REFACTOR_TITLE: <title>
REFACTOR_FILE: leanification/refactors/refactor_<title>.json
AFFECTED_REFS: <ref1>, <ref2>, ..., <refN>
FIRST_UNSOLVED_AFTER: <the earliest ref (in data.json render order) that is now unsolved -- this is what the next manager will pick up>
```

Then add a short paragraph summarising the new shape and any *unexpected* downstream consequences you discovered (e.g. "Touching `def_3_5` also forces us to re-do `claim_5_7` because of the inductive argument it uses; this wasn't in the manager's original request.").

## Rules

- This action **rewrites cross-chapter project state**. Be conservative — touch the minimum set of rows that actually need updating.
- If you discover the refactor would touch a row in a chapter that has not yet been initialised, note it in the report but don't try to reach into a non-existent file.
- Never silently widen the change beyond the manager's request without flagging it. Surface every additional row you're proposing to mark unsolved, with a one-line reason each, in the report.
- If you decide on closer inspection that the refactor is **not** justified (the design pain has a lighter fix), STOP and report back to the manager with that finding — do not write the refactor file or reset any rows.
