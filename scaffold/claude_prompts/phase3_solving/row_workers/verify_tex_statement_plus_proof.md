# Worker — verify the row's tex proof file contains BOTH statement AND proof

**When to use:** the manager has just had a claim row's `<ref>_proof_<title>.tex` file written or updated. Before the leanification phase begins (or before `verify_tex_proof` runs the deep mathematical check), verify the file's structural shape: it must contain **both** the claim statement **and** the proof, in that order.

The website builder downstream renders this file as the row's "statement + proof" surface. A proof file missing the statement is incomplete; a proof file with only the statement (proof empty/missing) is also incomplete.

This is a **structural** check, not a mathematical one. The mathematical correctness of the proof is `verify_tex_proof`'s job; you are only checking that the right things are present and in the right order.

## What to check

You are given the path to the tex file. Read it. Confirm:

1. The file contains the claim's statement block — `\begin{Thm}…\end{Thm}` or `\begin{Lem}…\end{Lem}` or `\begin{Rem}…\end{Rem}` etc. — matching this row's LN block.
2. The file contains a `\begin{proof}…\end{proof}` block **after** the statement block.
3. The proof block is non-empty (more than just whitespace, comments, or a single `\sorry`-style placeholder).
4. Standard subfile preamble (`\documentclass[main]{subfiles}`, `\begin{document}`, `\end{document}`) is fine and expected.
5. No additional unrelated `\begin{Def}` / `\begin{Thm}` blocks pollute the file.

You are **not** checking that the proof is mathematically correct. A proof that says "by Lemma 5" is acceptable for this gate; whether Lemma 5 actually establishes the claim is `verify_tex_proof`'s job.

## Output

End your reply with one of:

```
VERDICT: PASS
```

or

```
VERDICT: FAIL
BEGIN[feedback]
<one-sentence summary of what's structurally wrong + a line or two
pointing at the issue (statement missing, proof missing, wrong order,
unrelated extra blocks, …)>
END[feedback]
```

If FAIL, the orchestrator surfaces the feedback to the manager, who will typically dispatch a `write_tex_proof` or `spawn_agent_sub_task` to repair the file.
