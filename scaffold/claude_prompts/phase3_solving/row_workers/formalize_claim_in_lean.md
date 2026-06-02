# Worker — formalize a claim's statement in Lean (with `sorry`)

**When to use:** the manager has handed you a row with `def_or_claim == "claim"` that is not yet formalized. The lecture notes have the source text wrapped in `\begin{claimmark}...\end{claimmark}`. Your job is to write the equivalent Lean 4 *statement* — a `theorem`/`lemma` with the right signature and a single `sorry` for the proof. Proving is a separate worker.

## Authoritative spec = LN block + `addition_to_the_LN`

The row's `addition_to_the_LN` field (surfaced in the row context) is **part of the claim's statement**. It carries human-authored clarifications, strengthenings, or disambiguations written during the initialization phase. The Lean theorem signature must capture the claim's literal LN reading **AND** every clause in the addition. If the addition contradicts the literal LN, the addition wins. Empty addition → only the literal LN applies.

Concretely: a `[<sid>] The variable W is implicitly universally quantified …` clause means your Lean theorem must explicitly bind `W` with the right quantifier and hypothesis. A `[manual_1] The vertex sets are finite.` clause means the hypotheses include `[Finite α]` (or analogous). Read every paragraph in `addition_to_the_LN` and make sure no constraint is silently dropped from the Lean statement.

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_12`)
- `tex_file` and the line range of the `claimmark` block (or the raw contents)
- the target Lean file path inside the row's subsection folder
- the LaTeX type (theorem, lemma, corollary, remark, …) — informs naming but not the statement

## What to do

1. **Read the source.** The full `claimmark` block plus enough surrounding text to disambiguate notation and quantification.
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

**Helper-for-statement markers** (THREE dashes, distinct from the start/end markers) — wrap any auxiliary `def` / `structure` / `class` / `instance` / `notation` you had to introduce in this file so the main theorem signature would type-check (e.g. a `def Iso (G H : CDMG α) : Prop := …` that the theorem's conclusion uses). The website builder pulls these out alongside the main statement so the rendered statement is self-contained.

```lean
-- <ref> --- start helper
def <helper_name> ... :=
  ...
-- <ref> --- end helper
```

Same placement rules: immediately above the helper's first line, immediately below its last. Use the **row's ref** for `<ref>` (the helper exists to support *this* row's statement).

**Do NOT wrap with `--- helper` markers** declarations introduced for proof tactics, side lemmas the proof body invokes, or general infrastructure (those go without markers and the website builder ignores them). The helper markers are strictly for "statement support" -- declarations the main `theorem`'s signature would not type-check without.

## Rules

- Stay (almost) equivalent to the LN — do not "fix" the statement.
- If something in the LN is genuinely false, formalize it faithfully here and flag the row for `document_counterexample` later — do **not** silently weaken the statement.
- No `True`/trivial substitutes for parts of the claim.
- Edit only files inside your subsection's folder under `leanification/`.
