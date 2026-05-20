# Worker — rewrite a TeX proof to fix a mistake found while leanifying

**When to use:** a TeX proof exists in `tex_proofs/<ref>_proof_<title>.tex` (previously verified by `verify_tex_proof`), but a downstream leanifier discovered a real flaw — a missing case, a wrong invariant, a citation that doesn't actually establish what was claimed. Your job is to **rewrite the TeX proof** to fix the mistake, after which `verify_tex_proof` will run again.

This is different from `expand_proof`: that worker adds detail to a step that's underspecified. Here, the proof is actually wrong (or wrong in part) and must be corrected.

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_5`)
- The path to the `.tex` proof file under `tex_proofs/`
- **A concrete description of the flaw** — the leanifier's report on *what* doesn't go through and *why*. The manager should pass this verbatim; don't guess.
- Pointers to the relevant definitions/lemmas in this chapter (and any new helper lemma the leanifier needs you to introduce)

## What to do

1. **Read everything in scope.** The current TeX proof, the LN block for the claim, and the LN's own proof (if any). Look at the surrounding chapter — sometimes a "missing step" is one the LN handles a few pages later.
2. **Identify the minimal change.** Often only one paragraph or one case needs rewriting; do not throw away the rest of the proof.
3. **Apply the fix in place.** Edit only the row's `claim_<ref>_proof_<title>.tex` in the subsection `tex/` folder. Preserve the surrounding text and the file's overall structure. In particular, the **restated statement** block above `\begin{proof}` must stay -- it makes the file render self-contained. If the restated statement is itself wrong, copy the corrected block from the sibling `claim_<ref>_statement_<title>.tex` over it; do not improvise.
4. **Justify the fix.** Add a `% correction (<date>):` comment near the rewritten section explaining what was wrong and why this fix is correct. Future readers (and the next leanifier) will be able to see *why* the proof differs from the LN's version, if it now does.
5. **Surface any new helper lemma** the corrected proof now requires — if it's non-trivial, the manager may want to lift it into its own row before re-leanifying.
6. **No `sorry`, no "omitted", no "obvious".** The corrected steps must be fully justified inline or by citing prior refs.

## When the fix is itself the LN's mistake

If the leanifier's "flaw" exposes a real bug in the LN (the original claim is genuinely false), do **not** quietly weaken the claim. Stop, hand back to the manager with that observation, and let the manager dispatch `mistake` → `document_counterexample`.

## Rules

- Edit only the affected tex proof file under `tex_proofs/`.
- Stay close to the LN's argument; only deviate where the leanifier's report shows the LN argument is wrong or incomplete.
- Report back to the manager with: a one-paragraph summary of the change, the location in the file, whether the fix introduces a new helper lemma, and whether you suspect this is an LN-level mistake.
