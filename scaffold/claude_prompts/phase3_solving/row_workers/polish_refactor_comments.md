# Worker — polish refactor naming out of a finalized refactor row's Lean file

**When to use:** A refactor has just finished `apply_refactor_cleanup.py` (Phases 7a-h). The ORIGINAL marker blocks are gone, every `refactor_<Name>` declaration has been renamed to `<Name>`, and Pass 3 has stripped the obvious in-progress narratives. The Lean *logic* is final and `lake build` is clean. But the file's **comments and docstrings** still carry refactor-era prose — `pre-refactor`, `post-refactor`, `the refactor's <ref>`, references to no-longer-existing tex twin files like `tex/refactor_<ref>_proof_<title>.tex`, and "*Refactor coexistence note.*" paragraphs that the deterministic Pass 3 didn't quite match.

Your job is the **last polish step**: read the file as if the refactor never happened, and rewrite every comment / docstring so the current code reads as the canonical code, with no lingering meta-narrative about how it got here. Minimal pruning: short historical notes are fine, but long pre-/post- comparisons should be cut down or removed.

## Hard outcome rule — zero "refactor" mentions when you're done

After your edits, **the word "refactor" (case-insensitive) must not appear anywhere in the file's comments or docstrings.** Not as past-tense pipeline narrative, not in forward-looking design notes, not in section headings, not in cross-references. The principle: comments describe what the code *is* — what it does, why this shape, what invariants hold. Not how the code got here, and not hypothetical maintenance flows framed in pipeline vocabulary.

This means you have *two* targets:

1. **Pipeline-history residue** — `pre-refactor`, `post-refactor`, `(refactor)` ref-tag parentheticals, `*Refactor coexistence note.*` paragraphs, `tex/refactor_<ref>_proof_*.tex` cross-references. These describe a transition that has finished; strip them.

2. **Forward-looking design notes that frame future maintenance as a "refactor"** — examples and how to rewrite:

   - `for the tex/Lean reconciliation tooling and any future refactor` → `for the tex/Lean reconciliation tooling` (drop the trailing `and any future refactor`)
   - `*Refactor warning — keep in sync if X*` → `*Update warning — keep in sync if X*` or `*Sync warning — keep in sync if X*`
   - `surface this comment at refactor time` → `surface this comment if/when this spec is revisited` (or `... if X is later added`)
   - `should a future refactor X, then Y` → `if X is later added/changed, then Y`
   - `this would force a refactor at that row` → `this would force a redesign at that row` (or drop entirely if the meaning is implicit)

The content of these warnings often genuinely matters (architectural FYIs for future maintainers — *"if CDMGs ever gain a tail-tail edge type, the `sus` definition must be updated"*). **Preserve the substance; just drop the pipeline-flavoured vocabulary.** Reach for *update*, *change*, *revision*, *redesign*, *modification*, *sync*, *revisit*, or just describe the trigger directly without naming the maintenance action.

## Hard rule — comments and docstrings ONLY

You may edit text **only** inside:

- Lean line comments — lines starting with `--`.
- Lean block / module docstrings — `/-! ... -/`.
- Lean declaration docstrings — `/-- ... -/`.

You **must not** touch any of the following:

- `def`, `theorem`, `lemma`, `instance`, `abbrev`, `notation`, `structure`, `class`, `inductive`, `opaque`, `axiom` signatures or bodies.
- Tactic blocks inside `:= by ...`.
- `variable`, `import`, `namespace`, `open`, `section`, `end` lines.
- Statement markers (`-- <ref> -- start statement` / `-- <ref> -- end statement` / `-- <ref> --- start helper` / `-- <ref> --- end helper`) — those are load-bearing for the website builder; leave them exactly as they are.

If your plan touches anything in this list, **stop and report** instead of executing — that's a bug in the plan and the operator needs to see it.

## Inputs you receive from the operator's brief

- The Lean file's full path.
- The refactor's name (e.g. `total_order_helper`).
- The refactor's root refs (e.g. `def_3_8, def_3_9`).

## What to do — plan first, then execute

### Step 1 — Read the file end-to-end.

Use `Read` on the whole file. Build a mental model of what's there now: which declarations live here, what each design-choice block says, where the file's `/-! ... -/` module docstring sits.

### Step 2 — Plan every change (mandatory; write this out before any Edit).

List every comment / docstring location you intend to modify, with this shape:

```
Line <N>: <before excerpt, ≤ 80 chars>
  → <after excerpt, ≤ 80 chars>
Reason: <one phrase>

Lines <N>–<M> (paragraph): <one-line summary of current content>
  → <one-line summary of replacement, or "DELETE">
Reason: <one phrase>
```

Categories to look for (both the just-completed refactor's residue AND any earlier solver-written mentions of "refactor"; the outcome rule above demands zero mentions of either kind):

- **`pre-refactor` / `post-refactor` qualifiers** — drop the qualifier. `"post-refactor signature makes them coincide"` → `"the signature makes them coincide"`.
- **Stale `tex/refactor_<ref>_proof_<title>.tex` cross-references** — the tex twin was renamed during Phase 7c. Rewrite the path to drop the `refactor_` prefix.
- **`*Refactor coexistence note.*` / `**Coexistence during the refactor**` paragraphs** — describe a state that no longer exists. Delete the paragraph (or trim to one sentence if it carries info worth keeping).
- **`refactor` in section headers and `-- ref:` tags** — e.g. `-- ref: def_3_8 (refactor)` or `-- ref: def_3_9 (refactor: total_order_helper, strict predecessors)`. Drop the `(refactor)` / `(refactor: …)` parenthetical.
- **Long "this used to be X, now it's Y" narratives** — trim to "this is X". Reword to avoid the word "refactor" entirely.
- **References to the refactor pipeline machinery** — `"the refactor's claim_3_2 DEPENDENT row is included for def_3_8's shape change"` — drop these entirely; they belong in git history.
- **Forward-looking "future refactor" / `*Refactor warning ...*` / "at refactor time" / "if X needs a refactor" design notes** — preserve the substance (the architectural FYI is often genuinely valuable: *"if CDMGs ever gain a tail-tail edge type, sus needs updating"*) but reword without the word "refactor". Use *update*, *change*, *revision*, *redesign*, *modification*, *sync*, *revisit*, or describe the triggering condition directly.

Leave alone:

- Genuine mathematical commentary (which by definition won't use the word "refactor" anyway).
- One-line `-- ref: <ref>` headers (these are permanent metadata, not refactor-tagged).

If no comment is worth changing AND the file already contains zero `refactor` mentions, the plan section is `(no changes)` and Step 3 is a no-op.

### Step 3 — Apply.

For each planned change, issue an `Edit` call. The plan is your contract — don't make unplanned edits. If during Edit you realize the plan was wrong, stop, revise the plan inline, and continue.

### Step 4 — Sanity-check.

After all Edits, `Read` the file again. Confirm:

- Every change you made falls inside a comment / docstring.
- No `def` / `theorem` / `lemma` / signature / proof body was altered.
- Statement markers (`-- <ref> -- start/end statement`, `-- <ref> --- start/end helper`) are byte-for-byte unchanged.
- File still parses as Lean (the operator will run `lake build` after you exit; if your plan respected the comment-only rule, this is guaranteed).
- **Grep mentally for the word "refactor" (case-insensitive). It must not appear anywhere.** If even one survived your plan, write one more Edit pass. The zero-`refactor`-mentions outcome rule is load-bearing.

If anything in this list is off, **revert the offending Edit** and re-plan.

## Output

End your reply with a short report:

- N comment/docstring changes applied
- Anything you decided to keep that you originally planned to drop (and why)
- A one-line statement confirming no non-comment code was modified

If the worker hit a snag (couldn't parse a paragraph, couldn't decide between two rewrites, found a non-comment edit that needed to happen for the polish to make sense), end with `VERDICT: NEEDS_HUMAN` and a one-paragraph explanation — the operator will pick up from there.
