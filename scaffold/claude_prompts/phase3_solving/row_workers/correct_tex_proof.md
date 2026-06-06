# Worker — rewrite a TeX proof to fix a mistake found while leanifying

**When to use:** a TeX proof exists in `leanification/<Chapter>/<Section>/tex/<ref>_proof_<title>.tex` (previously verified by `verify_tex_proof`), but a downstream leanifier discovered a real flaw — a missing case, a wrong invariant, a citation that doesn't actually establish what was claimed. Your job is to **rewrite the TeX proof** to fix the mistake, after which `verify_tex_proof` will run again.

## Authoritative spec = LN block + `addition_to_the_LN`

The row's `addition_to_the_LN` field is part of the claim's spec — the corrected proof must still establish the LN's literal claim **plus** every clause in `addition_to_the_LN`. If the flaw the leanifier surfaced is rooted in a clause from `addition_to_the_LN` (e.g. a finiteness hypothesis was overlooked), use that clause as the load-bearing repair. Empty addition → only the literal LN applies.

This is different from `expand_proof`: that worker adds detail to a step that's underspecified. Here, the proof is actually wrong (or wrong in part) and must be corrected.

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_5`)
- The path to the `.tex` proof file (`leanification/<Chapter>/<Section>/tex/<ref>_proof_<title>.tex` in prove mode, or `…/<ref>_disproof_<title>.tex` in disprove mode)
- **A concrete description of the flaw** — the leanifier's report on *what* doesn't go through and *why*. The manager should pass this verbatim; don't guess.
- Pointers to the relevant definitions/lemmas in this chapter (and any new helper lemma the leanifier needs you to introduce)

## What to do

1. **Read everything in scope.** The current TeX proof, the LN block for the claim, and the LN's own proof (if any). Look at the surrounding chapter — sometimes a "missing step" is one the LN handles a few pages later.
2. **Identify the minimal change.** Often only one paragraph or one case needs rewriting; do not throw away the rest of the proof.
3. **Apply the fix in place.** Edit only the row's tex file — `claim_<ref>_proof_<title>.tex` in **prove mode** (default), or `claim_<ref>_disproof_<title>.tex` in **disprove mode** (the manager will tell you which). Both files may coexist on disk if the manager has toggled between modes; **only touch the active one**. Preserve the surrounding text and the file's overall structure. In particular, the **restated statement** block above `\begin{proof}` must stay -- it makes the file render self-contained. If the restated statement is itself wrong, copy the corrected block from the sibling `claim_<ref>_statement_<title>.tex` over it; do not improvise. Also leave the `\def\rowref{...}\def\rowtitle{...}\phantomsection\label{...}` block right after `\begin{document}` alone -- it drives the theorem-header rendering and cross-subfile links.
3a. **Cross-references to other rows** must use `\refrow{<ref>}` (e.g. `\refrow{claim_3_4}`), not the LN-style `\ref{label}` (which is broken under our star-numbered envs).
4. **Justify the fix.** Add a `% correction (<date>):` comment near the rewritten section explaining what was wrong and why this fix is correct. Future readers (and the next leanifier) will be able to see *why* the proof differs from the LN's version, if it now does.
5. **Surface any new helper lemma** the corrected proof now requires — if it's non-trivial, the manager may want to lift it into its own row before re-leanifying.
6. **No `sorry`, no "omitted", no "obvious".** The corrected steps must be fully justified inline or by citing prior refs.

## When the fix is itself the LN's mistake

If the leanifier's "flaw" exposes a real bug in the LN (the original claim is genuinely false), do **not** quietly weaken the claim. Stop, hand back to the manager with that observation, and let the manager dispatch `mistake` → `document_counterexample`.

## Rules

- Edit only the affected tex proof file under the row's `leanification/<Chapter>/<Section>/tex/` folder (the active one — prove or disprove — depending on the row's mode).
- Stay close to the LN's argument; only deviate where the leanifier's report shows the LN argument is wrong or incomplete.
- Report back to the manager with: a one-paragraph summary of the change, the location in the file, whether the fix introduces a new helper lemma, and whether you suspect this is an LN-level mistake.
