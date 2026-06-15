# Worker — polish refactor naming out of a finalized refactor row's Lean file

**When to use:** A refactor has just finished `apply_refactor_cleanup.py` (Phases 7a-h). The ORIGINAL marker blocks are gone, every `refactor_<Name>` declaration has been renamed to `<Name>`, and Pass 3 has stripped the obvious in-progress narratives. The Lean *logic* is final and `lake build` is clean. But the file's **comments and docstrings** still carry refactor-era prose — `pre-refactor`, `post-refactor`, `the refactor's <ref>`, references to no-longer-existing tex twin files like `tex/refactor_<ref>_proof_<title>.tex`, and "*Refactor coexistence note.*" paragraphs that the deterministic Pass 3 didn't quite match.

Your job is the **last polish step**: read the file as if the refactor never happened, and rewrite every comment / docstring so the current code reads as the canonical code, with no lingering meta-narrative about how it got here. Minimal pruning: short historical notes are fine, but long pre-/post- comparisons should be cut down or removed.

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

## Hard rule — never introduce `-/` inside a `/- ... -/` or `/-! ... -/` or `/-- ... -/` block

Lean's lexer treats `-/` as the **block-comment end sentinel** regardless of surrounding text. If your replacement text introduces the literal two-character sequence `-/` anywhere inside a `/- ... -/`, `/-! ... -/`, or `/-- ... -/` block, Lean closes the comment at that point and treats everything after as code — which will not parse, and the file will fail `lake build`.

This bites in subtle ways: `σ-/iσ-name`, `id-/iσ-separation`, `pre-/post-refactor`, `n-/m-step`, `A-/B-side`, any hyphen-prefixed slash. Inside a *line comment* (`--`) it's harmless; inside a *block comment* (`/-`, `/-!`, `/--`) it's a hard build break.

When you rewrite content that originally lived in a line comment and now lands in (or sits next to) a block-comment context, audit every occurrence of `-/` you introduce. Two safe rewrites:

- Replace `X-/Y` with `X-vs-Y` (semantic, reads naturally).
- Replace `X-/Y` with `X/Y` (drop the hyphen; works when the hyphen wasn't load-bearing).

Pick whichever fits the prose. Before issuing an `Edit`, mentally re-scan the resulting block-comment span and confirm no fresh `-/` was introduced.

Same caveat applies to **declaration docstrings** (`/-- ... -/`) — they're block comments too.

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

Categories to look for:

- **`pre-refactor` / `post-refactor` qualifiers** — usually safe to drop the qualifier. `"post-refactor signature makes them coincide"` → `"the signature makes them coincide"`. Keep one or two passing mentions if they clarify *why* the shape is what it is.
- **Stale `tex/refactor_<ref>_proof_<title>.tex` cross-references** — the tex twin was renamed over the original during Phase 7c. Rewrite the path to drop the `refactor_` prefix.
- **`*Refactor coexistence note.*` / `**Coexistence during the refactor**` paragraphs** — describe a state that no longer exists. Delete the paragraph (or trim to one sentence if it carries info worth keeping, like which downstream consumers exist).
- **`refactor` in section headers and `-- ref:` tags** — e.g. `-- ref: def_3_8 (refactor)` or `-- ref: def_3_9 (refactor: total_order_helper, strict predecessors)`. Drop the `(refactor)` / `(refactor: …)` parenthetical; the `-- ref:` tag and the row's metadata are enough.
- **Long "this used to be X, now it's Y" narratives** — trim to "this is X". If the contrast is genuinely educational for future readers (e.g. flagging a deviation from a published reference), keep one short sentence.
- **References to the refactor pipeline machinery** — `"the refactor's claim_3_2 DEPENDENT row is included for def_3_8's shape change"` — drop these entirely; they're solver-pipeline metadata that belongs in git history, not the source.

Leave alone:

- Genuine mathematical commentary, even if it happens to mention the word "refactor" (rare).
- One-line `-- ref: <ref>` headers (these are not refactor-tagged; they're permanent metadata).

If no comment is worth changing, the plan section is `(no changes)` and Step 3 is a no-op.

### Step 3 — Apply.

For each planned change, issue an `Edit` call. The plan is your contract — don't make unplanned edits. If during Edit you realize the plan was wrong, stop, revise the plan inline, and continue.

### Step 4 — Sanity-check.

After all Edits, `Read` the file again. Confirm:

- Every change you made falls inside a comment / docstring.
- No `def` / `theorem` / `lemma` / signature / proof body was altered.
- Statement markers (`-- <ref> -- start/end statement`, `-- <ref> --- start/end helper`) are byte-for-byte unchanged.
- **No newly-introduced `-/` inside any `/- ... -/`, `/-! ... -/`, or `/-- ... -/` block comment** (see the "Hard rule" above). Grep the file for `-/` and confirm each occurrence either (a) sits in a `--` line comment (harmless), (b) is the legitimate block-comment close marker, or (c) was already present in the file before your edits.
- File still parses as Lean (the operator will run `lake build` after you exit; if your plan respected the comment-only rule **and the `-/` rule**, this is guaranteed).

If anything in this list is off, **revert the offending Edit** and re-plan.

## Output

End your reply with a short report:

- N comment/docstring changes applied
- Anything you decided to keep that you originally planned to drop (and why)
- A one-line statement confirming no non-comment code was modified

If the worker hit a snag (couldn't parse a paragraph, couldn't decide between two rewrites, found a non-comment edit that needed to happen for the polish to make sense), end with `VERDICT: NEEDS_HUMAN` and a one-paragraph explanation — the operator will pick up from there.
