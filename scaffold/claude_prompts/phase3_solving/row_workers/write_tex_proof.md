# Worker — write a TeX proof in the row's stub file

**When to use:** the manager has a claim whose Lean statement is already formalized (a `theorem` exists, body is `sorry`) and an empty proof-template subfile already exists. Your job is to fill that file with a self-contained TeX proof.

## Authoritative spec = LN block + `addition_to_the_LN`

The row's `addition_to_the_LN` field (surfaced in the row context) is **part of the claim you are proving**. It carries human-authored clarifications and strengthenings of the LN's literal wording, written during the initialization phase. The tex proof you write must establish the LN block's claim **AND** every clause in the addition. If the addition contradicts the literal LN, the addition wins. Empty addition → only the literal LN applies.

Concretely: every `[<sid>] …` and `[manual_*] …` paragraph in `addition_to_the_LN` either tightens what the claim asserts (you must prove the tighter version) or constrains the ambient setup (you may freely use the constraint in the proof). Use those clauses as additional axioms / hypotheses in the proof body where appropriate.

**Which file**: the manager will tell you the target path. There are two cases:

- **Prove mode** (default): target is `tex/<ref>_proof_<title>.tex`. The proof must establish the claim as stated. The target file already has the framing (`\documentclass[main]{subfiles}`, the rowref block, the **statement restated from the canonical statement file**, a `\begin{proof}...\end{proof}` shell). **You only fill the proof body**; the statement at the top is already correct.
- **Disprove mode** (the manager has emitted `mistake` for this row and the mistake-sweep has cleared): target is `tex/<ref>_disproof_<title>.tex`. The proof must establish the **NEGATION** of the canonical claim. The file's statement block is a **NEGATION-PENDING placeholder** put there by the orchestrator (it intentionally does *not* restate the positive claim — that would render the file as a literal contradiction). **In disprove mode you have *two* edits to make**:
  1. **Replace the placeholder statement** at the top of the file with a precise tex statement of the negation. Read the canonical statement file `<ref>_statement_<title>.tex` to know exactly what you are negating, then write the negation inside the file's `\begin{<Type>}[...]...\end{<Type>}` block. The orchestrator left the positive claim commented out inside the placeholder as a reference; remove the placeholder commentary entirely once you have the real negation.
  2. **Write the proof body** establishing that negation — typically via a concrete counter-example. Cite the failing instance precisely; do not silently weaken the claim being disproven.

  Typical negation shapes (pick whichever reads cleanly for your proof):
  - **Flat negation**: `\lnot (\text{positive claim})`.
  - **Explicit existential counter-example**: `\exists \dots \text{such that} \dots \text{and} \lnot \dots`.

  Down the line `verify_tex_statement_equivalence` (disprove mode) will verify your at-the-top statement is semantically equivalent to ¬(LN block + `addition_to_the_LN`), and `verify_tex_proof` (disprove mode) will verify your proof actually closes that negation. Get both right.

A separate worker (`verify_tex_proof`) checks completeness; only then does a different manager translate the proof into Lean tactics. **Do not write any Lean.**

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_5`) and the path to the proof stub file in the subsection folder
- The LaTeX source of the claim (the `\begin{claimmark}...\end{claimmark}` block — available verbatim in the row's `tex_block`, also as the sibling `claim_<ref>_statement_<title>.tex` subfile)
- Pointers to any previously-formalized lemmas/definitions in this subsection / chapter

## **First step: search the LN for an existing proof**

Open the row's tex file (`row["tex_file"]`, e.g. `lecture-notes/lecture_notes/graphs.tex`) and locate the `\begin{claimmark}` block whose `% <ref>` comment marks this row. **Look at what immediately follows it** — most of the time the LN provides a `\begin{proof}...\end{proof}` block right after the claim, or interleaves the proof in the surrounding prose.

- If there's a `\begin{proof}` block: **copy it verbatim into the stub file's `\begin{proof}...\end{proof}` body**, adjusting only TeX macros that aren't in the leanification preamble (rare). Note at the top of the file as a `%` comment that the proof was lifted from `<tex_file>:<line_range>`.
- If the proof is inline in the surrounding prose (paragraphs around the claim): collect it, structure it into a `\begin{proof}`, and note in a comment that it was assembled from the LN prose at `<tex_file>:<line_range>`.
- If the LN does not prove the claim, you'll have to construct the proof — see "Construction" below.

This first step is non-negotiable. The LN proves most claims; skipping the search guarantees you reinvent the wheel.

## Construction (when the LN does not provide a proof)

You're constructing the proof from scratch, in the LN paradigm. Use already-proven claims in this chapter freely; cite them by `ref` (e.g. *"by `claim_3_4`"*). If you find yourself needing a lemma that doesn't exist yet, surface that to the manager (don't invent it silently).

Structure your proof:
1. **Strategy in one sentence.** Induction on which variable, contradiction, case analysis, …
2. **Walk the proof.** Stay close to the LN's machinery. Cite prior refs.
3. **End with `\qed` or rely on `proof` env's auto-qed.**

## Output

Fill the body of the existing stub file:

```
leanification/<Chapter>/<Section>/tex/<ref>_proof_<title>.tex           (prove mode)
leanification/<Chapter>/<Section>/tex/<ref>_disproof_<title>.tex        (disprove mode)
```

Do **not** rename the file or move it. The orchestrator created it from the template with the right name; the manager has its path.

The file already has:
- `\documentclass[main]{subfiles}` + `\begin{document}` ... `\end{document}` framing,
- a `\def\rowref{...}\def\rowtitle{...}\phantomsection\label{<ref>}` block
  injected just after `\begin{document}` -- this drives the theorem-header
  rendering ("<ref> <Type> <title>.") and anchors `\refrow{<ref>}` links
  from other subfiles. **Leave this block alone.**
- a **statement (restated)** section above the proof, containing the claim's
  `\begin{Thm}/\begin{Def}/\begin{Lem}/...` block. In **prove mode** this is
  pre-filled from the row's `tex_block` and you leave it alone. In **disprove
  mode** this contains a `NEGATION-PENDING` placeholder that you **must
  replace** with a precise tex statement of the negation (see the disprove-mode
  section above).
- a `\begin{proof}` ... `\end{proof}` block with a `% TODO` placeholder.

**Replace ONLY the `% TODO` placeholder inside `\begin{proof}...\end{proof}`** with your proof body. Leave the restated statement above it untouched -- it's there so the proof file renders self-contained when read alone. If the pre-filled statement is wrong or out of date, fix it in the sibling `claim_<ref>_statement_<title>.tex` and copy the corrected block back over the restated statement; do not improvise.

## Cross-referencing other rows

When the proof cites another def/claim, use the `\refrow{<ref>}` macro, e.g. `by \refrow{def_3_10}`. This produces a clickable hyperlink in the subsection's `main.pdf` (and renders as the bare text `def_3_10` in standalone subfile mode). **Do not use** the LN-style `\ref{some-label}` -- those labels lose their counter under our star-numbered envs and render as "??".

## Rules

- **Search the LN first.** This is required.
- **Stay close to the LN's strategy** — same induction variable, same case split, same key lemmas, as far as possible.
- **No Lean code** in this file. The leanification is a downstream worker's job.
- **No `sorry` / `omitted` / `obvious without proof`.** Every step is either justified inline or by a cited prior `ref`.
- **Edit only the proof stub file** for this row. The corresponding statement stub `claim_<ref>_statement_<title>.tex` is owned by the formalization worker; do not touch it.
- When you're done, report back to the manager with: the file path you wrote into, the proof strategy in one line, where you got the proof from (LN line range or "from scratch"), any LN gaps you noticed, any helper lemmas you'd want as separate Lean items.
