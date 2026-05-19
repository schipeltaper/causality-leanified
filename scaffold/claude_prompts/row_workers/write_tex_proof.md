# Worker — write a TeX proof in the row's stub file

**When to use:** the manager has a claim whose Lean statement is already formalized (a `theorem` exists, body is `sorry`) and an empty proof-template subfile already exists at the row's `claim_<N>_<M>_proof_<title>.tex` path. Your job is to fill that file with a self-contained TeX proof.

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

The file already has the `\documentclass[main]{subfiles}` and `\begin{document}` ... `\end{document}` framing, and contains a `\begin{proof}` ... `\end{proof}` block with a `% TODO` placeholder. Replace the placeholder with your proof.

## Rules

- **Search the LN first.** This is required.
- **Stay close to the LN's strategy** — same induction variable, same case split, same key lemmas, as far as possible.
- **No Lean code** in this file. The leanification is a downstream worker's job.
- **No `sorry` / `omitted` / `obvious without proof`.** Every step is either justified inline or by a cited prior `ref`.
- **Edit only the proof stub file** for this row. The corresponding statement stub `claim_<ref>_statement_<title>.tex` is owned by the formalization worker; do not touch it.
- When you're done, report back to the manager with: the file path you wrote into, the proof strategy in one line, where you got the proof from (LN line range or "from scratch"), any LN gaps you noticed, any helper lemmas you'd want as separate Lean items.
