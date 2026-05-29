# Worker — write a TeX proof in the row's stub file

**When to use:** the manager has a claim whose Lean statement is already formalized (a `theorem` exists, body is `sorry`) and an empty proof-template subfile already exists. Your job is to fill that file with a self-contained TeX proof.

**Which file**: the manager will tell you the target path. There are two cases:

- **Prove mode** (default): target is `tex/claim_<N>_<M>_proof_<title>.tex`. The proof must establish the claim as stated.
- **Disprove mode** (the manager has emitted `mistake` for this row): target is `tex/claim_<N>_<M>_disproof_<title>.tex`. The proof must establish the **NEGATION** of the claim — typically via a concrete counter-example.

In both cases the target file already has the framing (`\documentclass[main]{subfiles}`, the rowref block, the statement restated, a `\begin{proof}...\end{proof}` shell). You only fill the proof body.

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
leanification/<chapter_folder>/<subsection_folder>/claim_<N>_<M>_proof_<title>.tex
```

Do **not** rename the file or move it. The orchestrator created it from the template with the right name; the manager has its path.

The file already has:
- `\documentclass[main]{subfiles}` + `\begin{document}` ... `\end{document}` framing,
- a `\def\rowref{...}\def\rowtitle{...}\phantomsection\label{<ref>}` block
  injected just after `\begin{document}` -- this drives the theorem-header
  rendering ("<ref> <Type> <title>.") and anchors `\refrow{<ref>}` links
  from other subfiles. **Leave this block alone.**
- a **statement (restated)** section above the proof, containing the claim's
  `\begin{Thm}/\begin{Def}/\begin{Lem}/...` block (pre-filled at stub creation
  from the row's `tex_block`),
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
