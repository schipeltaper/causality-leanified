# Worker — verify the row's tex statement file contains ONLY the statement

**When to use:** the manager has just had the row's `<ref>_statement_<title>.tex` file populated (either auto-extracted from the LN or written/updated by an agent). Before any further work proceeds, verify the file contains **the claim/definition statement only** — no proof, no scratch work, no helper lemmas.

The website builder downstream relies on this file being a clean statement-only artefact. A proof leaking into the statement file means the website-rendered "statement" surface will be polluted with proof text.

## What to check

You are given the path to the tex file. Read it. Confirm:

1. The file contains exactly the LN's `\begin{Def}…\end{Def}` (or `\begin{Thm}…\end{Thm}`, `\begin{Lem}…\end{Lem}`, `\begin{Rem}…\end{Rem}`, etc.) block for this row, in `subfile` form. Trivial preamble (`\documentclass[main]{subfiles}`, `\begin{document}`, `\end{document}`) is fine.
2. **No `\begin{proof}…\end{proof}` block.** If the row is a claim, the proof goes in the *other* file (`<ref>_proof_<title>.tex`); a proof here is a bug.
3. No additional `\begin{Def}` / `\begin{Thm}` / etc. blocks that are not the row's own.
4. No `\section`, `\subsection`, or other document-structure macros except the subfile preamble.
5. No commented-out proof attempts (e.g. `% TODO prove this`) — those are scratch work and belong in `workspace_<ref>.md`, not the tex source.

## Output

End your reply with one of:

```
VERDICT: PASS
```

or

```
VERDICT: FAIL
BEGIN[feedback]
<one-sentence summary of what's wrong + a line or two pointing at the
offending content in the file>
END[feedback]
```

If FAIL, the orchestrator surfaces the feedback to the manager, who will dispatch a fix (typically a `spawn_agent_sub_task` to strip the proof out, or in the worst case `correct_tex_proof` to relocate proof content).

Optional `VERDICT: PASS` notes are fine but the verdict line must come first.
