# Worker — formalize a claim's statement in Lean (with `sorry`)

**When to use:** the manager has handed you a row with `def_or_claim == "claim"` whose canonical statement tex file has been **rewritten and verified** by `formalize_claim_in_tex` + `verify_tex_statement_equivalence`. Your job is to translate that rewritten tex statement into the equivalent Lean 4 *statement* — a `theorem`/`lemma` with the right signature and a single `sorry` for the proof. Proving is a separate worker.

## Authoritative spec = the rewritten canonical tex statement file

The row's canonical statement tex file at `leanification/<Chapter>/<Section>/tex/<ref>_statement_<title>.tex` is your **primary spec**. It was rewritten by the `formalize_claim_in_tex` worker so that:

- Every clause in `addition_to_the_LN` is folded in.
- Every hypothesis and quantifier is spelled out (no implicit scopes).
- Bespoke visual notation has been translated to set-theoretic phrasing.

It then passed `verify_tex_statement_equivalence`, which verified it is semantically equivalent to LN block + `addition_to_the_LN`. So: **translate the rewritten file**, not the LN's raw `claimmark` block.

The LN `tex_block` and `addition_to_the_LN` remain available in your row context as *backup reference* — useful for sanity checks, names, and intent — but if you find yourself preferring the LN block over the rewritten tex, that's a signal something is wrong (either with the rewrite or with your reading). Stop, report back to the manager, and ask for a re-spawn of the tex worker.

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_12`)
- The path to the rewritten canonical tex statement file (your primary spec)
- The LN `tex_file` for surrounding chapter context (backup)
- The target Lean file path inside the row's subsection folder
- The LaTeX type (theorem, lemma, corollary, remark, …) — informs naming but not the statement

## What to do

1. **Read the rewritten tex statement file** end to end. This is your spec. Read the row's `addition_to_the_LN` and the LN `tex_block` as backup, but the rewritten file is what you formalize.
2. **Decide single vs. multi-item.** A "claim" row is sometimes a *collection* of claims — several `\begin{Thm}` or `\begin{Lem}` blocks stacked, or a numbered list of statements bundled under one heading. In that case **stack them under each other** as separate `theorem`/`lemma` declarations in the same Lean file. Do not force them into one statement.
3. **Translate carefully.** Each Lean statement should be (almost) equivalent to its LN counterpart:
   - Same hypotheses, in the same order if reasonable.
   - Same conclusion, expressed in terms of the previously-formalized definitions (look them up in the subsection's existing Lean files).
   - If the LN claim includes "trivially" or "obviously" clauses, **still include them** as part of the statement.
4. **Add a comment block above each declaration** with: the `ref` (plus a sub-tag like `(part 1/3)` if the row has multiple items), a human-language description, the verbatim TeX of the claim (between `/-` and `-/`), and a **Design choice** note (why this shape, any naming/quantifier decisions, parts of the LN claim you chose to bundle or split).
5. **Wrap the statement(s) with statement markers.** REQUIRED -- the website builder relies on them. See **Marker conventions** below. The statement portion that gets wrapped is everything up to and including the type annotation (the `: <conclusion>` part); the `:=` and proof body sit *below* the end marker.
6. **Body is exactly one `sorry`** per declaration. Do not attempt the proof here — that's `prove_claim_in_lean`, which runs *after* the tex proof has been written and verified.
7. **Check it elaborates**: `lake build` from `/home/11716061/repo_scaffold2/`. The proof obligation will of course be open, but the statement must type-check.
8. **Report back** to the manager: every theorem name you wrote, the file it landed in, and any dependent definitions you had to use (or were missing).

## Marker conventions (REQUIRED)

The website builder grep-extracts statement-shaped Lean content using a fixed marker convention. You MUST follow it for every Lean declaration this row produces.

**Main statement markers** — wrap each top-level `theorem`/`lemma` declaration whose signature is the claim's statement. The wrapped portion runs from the keyword down through the type, ending just before `:=`. The proof body (`sorry` for now, an actual proof later) sits **below** the end marker.

```lean
-- <ref> -- start statement
theorem <name> (h₁ : …) (h₂ : …) : <conclusion>
-- <ref> -- end statement
  := by sorry
```

Or, written with the body on a continuation line:

```lean
-- <ref> -- start statement
theorem <name> (h₁ : …) (h₂ : …) :
    <conclusion>
-- <ref> -- end statement
:= by
  sorry
```

Where `<ref>` is this row's ref (e.g. `claim_3_5`). For multi-item rows (a claim row that produces several stacked `theorem`s), wrap **each** statement separately with its own start/end pair, all using the row's ref. Nothing may appear between a `-- <ref> -- start statement` line and the `theorem`/`lemma` keyword it wraps (no blank lines, no extra comments, no docstrings — those go ABOVE the start marker). Nothing may appear between the last line of the statement (the type annotation) and `-- <ref> -- end statement`.

The Lean parser is happy with the markers in those positions: line comments are stripped before parsing, and `theorem foo … : Bar` followed by `:= proof` parses the same as `theorem foo … : Bar := proof`.

**Helper-for-statement markers** (THREE dashes, distinct from the start/end markers) — wrap any auxiliary `def` / `structure` / `class` / `instance` / `notation`, **or** `variable` directive, you had to introduce in this file so the main theorem signature would type-check (e.g. a `def Iso (G H : CDMG α) : Prop := …` that the theorem's conclusion uses, or a `variable {α : Type*} [DecidableEq α]` line whose binders auto-bind into the wrapped theorem signature). The website builder pulls these out alongside the main statement so the rendered statement is self-contained.

```lean
-- <ref> --- start helper
def <helper_name> ... :=
  ...
-- <ref> --- end helper

-- <ref> --- start helper
variable {α : Type*} [DecidableEq α]
-- <ref> --- end helper
```

Same placement rules: immediately above the helper's first line, immediately below its last. Use the **row's ref** for `<ref>` (the helper exists to support *this* row's statement). A single `variable` directive is a one-line block; markers go immediately above and immediately below it. If several adjacent `variable` lines *all* flow into the wrapped theorem signature, you may wrap them as a single contiguous block.

**Section / namespace boundary:** if the file opens a `section` and the `variable` lives at that section's scope, place the helper-marker pair around the `variable` *inside* the section (right where the directive sits), not around the `section` opener.

**Do NOT wrap with `--- helper` markers** declarations or `variable` directives introduced for proof tactics, side lemmas the proof body invokes, or general infrastructure (those go without markers and the website builder ignores them). The helper markers are strictly for "statement support" -- anything the main `theorem`'s signature (or its auto-bound type quantifiers) would not type-check without. A `variable` whose binders never reach a wrapped statement should NOT be wrapped.

## Rules

- Stay (almost) equivalent to the LN — do not "fix" the statement.
- If something in the LN is genuinely false, formalize it faithfully here and flag the row for `document_counterexample` later — do **not** silently weaken the statement.
- No `True`/trivial substitutes for parts of the claim.
- Edit only files inside your subsection's folder under `leanification/`.
