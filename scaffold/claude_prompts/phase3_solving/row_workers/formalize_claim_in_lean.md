# Worker — formalize a claim's statement in Lean (with `sorry`)

**When to use:** the manager has handed you a row with `def_or_claim == "claim"` that is not yet formalized. The lecture notes have the source text wrapped in `\begin{claimmark}...\end{claimmark}`. Your job is to write the equivalent Lean 4 *statement* — a `theorem`/`lemma` with the right signature and a single `sorry` for the proof. Proving is a separate worker.

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
5. **Body is exactly one `sorry`** per declaration. Do not attempt the proof here — that's `prove_claim_in_lean`, which runs *after* the tex proof has been written and verified.
6. **Check it elaborates**: `lake build` from `/home/11716061/repo_scaffold2/`. The proof obligation will of course be open, but the statement must type-check.
7. **Report back** to the manager: every theorem name you wrote, the file it landed in, and any dependent definitions you had to use (or were missing).

## Rules

- Stay (almost) equivalent to the LN — do not "fix" the statement.
- If something in the LN is genuinely false, formalize it faithfully here and flag the row for `document_counterexample` later — do **not** silently weaken the statement.
- No `True`/trivial substitutes for parts of the claim.
- Edit only files inside your subsection's folder under `leanification/`.
