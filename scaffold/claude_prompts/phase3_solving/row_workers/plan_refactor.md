# Worker — plan a refactor (advisory only)

**When to use:** the manager has decided that a Lean object — typically a foundational definition, but sometimes a notation or a structural choice — has the wrong shape, and that getting it right requires not just changing the object itself but **producing a replacement and re-validating every consumer that uses it**.

This is the heaviest operation in the project. The goal is "do it correctly the first time around" so we rarely need this. When we do need it, your job is **plan, don't apply**: write a markdown plan that the human will read before launching the actual refactor pipeline.

**You do not touch any `data.json`. You do not delete or modify any Lean / tex files. You do not reset any rows.** The new (non-destructive) refactor pipeline does all of that via `extras/do_refactor.py`, which builds a separate `Refactor_<name>/refactor_data.json` table on a dedicated `refactor_<name>` git branch, lets the manager solve each refactor row using the same-file marker convention (Lean) and tex twin convention (`tex/refactor_<ref>_proof_<title>.tex`), and only at the very end runs `apply_refactor_cleanup.py` to swap originals for replacements. **The original code stays untouched on the server branch until the refactor is fully validated and merged back.**

## Inputs you should receive from the manager

- The current row's context (you may be running while a row was in progress).
- A description of what is being refactored and **why** — what design pain made this necessary.
- A proposed new shape (in words, not Lean code yet) for the foundational object.

## Step 1: Read enough to plan honestly

Before writing the plan:

- Re-read `claude.md` and skim the LN's `main.tex` so you know the chapter order.
- Read the **entire lecture notes** — start at `lecture-notes/lecture_notes/main.tex` and follow its `\input` chain. A refactor that looks safe in one chapter often hits four other chapters; this is the moment to find that out.
- For each chapter folder under `leanification/`, open its `data.json` and look at rows whose `tex_block` or proof tex references the concept you're refactoring (`grep`-style file reads are fine — you have the token budget).
- Open every Lean file touched by those rows; trace the usage graph. The transitive closure is what gets put through the refactor pipeline.

You can also recommend the human run `extras/find_dependents.py --chapter N --ref REF` for the bullet-proof transitive closure (it renames the target declaration to `<name>_REFACTOR_DISABLED`, runs `lake build`, scrapes every error site, then restores). Mention it in the plan if you want the human to validate your hand-traced list.

## Step 2: Pick a refactor name

A short snake_case or PascalCase name suitable for both a git branch name and a folder name. Examples: `CDMG_NoDisjointEL`, `WalksAsCoinductive`, `Marginalize`. The git branch will be `refactor_<name>`; the data folder will be `leanification/Chapter{N}_*/Refactor_<name>/`.

## Step 3: Write the plan markdown

Create the directory if it doesn't exist:

```
leanification/refactors/refactor_<name>.md
```

(Plain markdown, not JSON — this is human-facing.) Structure:

```markdown
# Refactor plan: <name>

**Status:** proposed (not yet executed)
**Date:** <UTC ISO date>
**Root ref:** <e.g. def_3_14>
**Root chapter:** <e.g. 3>
**Source branch:** server_setting_up_scaffold
**Proposed refactor branch:** refactor_<name>

## Why this refactor is needed
<two-or-three paragraphs explaining the design pain — what claims are getting blocked by the current shape, which deviations are accumulating in the register, etc. Be specific: which proof, which step, which encoding constraint.>

## Proposed new shape
<paragraph describing the target Lean shape — fields, type signature, the LN property it newly preserves. No Lean code yet (the refactor row's manager will work that out).>

## Affected rows (consumers)
Transitive consumers identified by hand-tracing (validate with `extras/find_dependents.py`):

| Ref | Chapter | What changes for this row |
|-----|---------|---------------------------|
| def_3_14 | 3 | the foundational redesign itself |
| claim_3_25 | 3 | proof needs to rebuild without the disjoint_EL exclusion |
| ... | ... | ... |

## Risks I see
<bullet list of unexpected downstream consequences you discovered — e.g. "touching def_3_14 also forces re-doing claim_5_7 because of the inductive argument it uses", "the proposed new shape can't express the joint distribution that def_4_3 implicitly assumes; possible mitigation: keep an explicit reduction map">.

## Recommended invocation
After review, the human executes:

```
git checkout server_setting_up_scaffold        # must be on this branch
python extras/do_refactor.py init \
    --chapter <root_chapter> \
    --root-ref <root_ref> \
    --name <name>
```

`do_refactor.py init` will: create the `refactor_<name>` branch, run `find_dependents.py` (bullet-proof transitive scan), run `initialize_refactor.py` (build the refactor_data.json table from the dependents list), commit, and push the new branch. Then the human drives the table with `python scaffold/scripts/phase3_solving/solve_chapter.py --data-path <refactor_data.json>`, and finalizes with `do_refactor.py finalize` + `do_refactor.py merge` once every refactor row is solved.
```

## Step 4: Report back

End your message with this exact block (the orchestrator parses it):

```
REFACTOR_PLAN_FILE: leanification/refactors/refactor_<name>.md
ROOT_REF: <ref>
ROOT_CHAPTER: <N>
NAME: <name>
RECOMMENDED_INVOCATION: python extras/do_refactor.py init --chapter <N> --root-ref <ref> --name <name>
```

Then a one-paragraph summary in prose: the rationale, the affected refs, and any *unexpected* downstream consequences you found.

## Rules

- **Read-only.** You do not modify any `data.json`, Lean file, or tex file. Your only write is the plan markdown under `leanification/refactors/`.
- Touch the minimum set of rows that actually need updating. If a row is only indirectly affected (e.g. its proof uses a lemma that uses the refactored def, but the lemma is wrapped via a stable interface), it may not need to be in the refactor table — note this in the plan's "Affected rows" rationale.
- Never silently widen the change beyond the manager's request without flagging it in the "Risks" section.
- If on closer inspection the refactor is **not** justified (the design pain has a lighter fix — e.g., a local proof rewrite, or `accept_deviation` is the right move), STOP and report that finding to the manager. Do not write the plan file.
- The orchestrator ends the current row's run after you return, regardless. The manager's row remains exactly as it was (solved or unsolved) on the server branch; the human decides whether to launch the refactor pipeline based on your plan.
