# Worker — verify the row's tex proof file contains BOTH statement AND proof

**When to use:** the manager has just had a claim row's tex proof file written or updated. Before the leanification phase begins (or before `verify_tex_proof` runs the deep mathematical check), verify the file's structural shape: it must contain **both** a statement at the top **and** a proof underneath it, in that order, both non-empty.

The check applies to:

- **Prove mode**: `<ref>_proof_<title>.tex`. The statement at the top should match the canonical statement file `<ref>_statement_<title>.tex` (already verified equivalent to LN+addition).
- **Disprove mode**: `<ref>_disproof_<title>.tex`. The statement at the top should be a tex statement of the **negation** (written by the disprove worker; semantically verified by `verify_tex_statement_equivalence` in disprove mode — which is a *separate* check). You are not checking the negation's correctness here; only that *some* statement block is present and a proof block follows.

The website builder downstream renders these files as the row's "statement + proof" (or "negation + proof of negation") surface. A file missing either piece is incomplete.

This is a **structural** check, not a mathematical one. The mathematical correctness of the proof is `verify_tex_proof`'s job; the negation's equivalence to ¬(LN+addition) is `verify_tex_statement_equivalence`'s job. You are only checking that the right things are present and in the right order.

## What to check

You are given the path to the tex file. Read it. Confirm:

1. The file contains a statement block — `\begin{Thm}…\end{Thm}` or `\begin{Lem}…\end{Lem}` or `\begin{Rem}…\end{Rem}` etc.
   - **Prove mode**: the block should match this row's LN claim.
   - **Disprove mode**: the block contains *some* statement (the negation, written by the disprove worker). Do **not** confirm equivalence to ¬(LN+addition) here — that's `verify_tex_statement_equivalence`'s job in disprove mode. But: if the block is still the orchestrator's `NEGATION-PENDING` placeholder text or empty, FAIL immediately — the disprove worker hasn't replaced the placeholder.
2. The file contains a `\begin{proof}…\end{proof}` block **after** the statement block.
3. The proof block is non-empty (more than just whitespace, comments, or a single `\sorry`-style placeholder). Also FAIL if the body is still the orchestrator's `% TODO: write a proof…` stub.
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
