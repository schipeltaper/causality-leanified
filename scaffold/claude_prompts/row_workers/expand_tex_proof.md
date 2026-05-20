# Worker — expand a specific step of an existing TeX proof

**When to use:** a tex proof already exists in `claim_<N>_<M>_proof_<title>.tex (in the subsection folder)` (from `write_tex_proof`) but the verifier flagged a step as too sketchy, or a downstream Lean prover got stuck on what should "follow trivially". Your job is to push that specific step deeper — without rewriting the rest.

## Inputs you should receive from the manager

- `ref` and the path to the tex proof file
- **Which step** needs unpacking — the manager should point at it explicitly (a sentence, an equation number, "the case where X is empty"). Don't guess.
- Optionally: the failed verifier report or the prover's last attempt + where it got stuck

## What to do

1. **Read the existing tex proof.** Locate the flagged step.
2. **Expand exactly that step.** Add inline detail, intermediate equalities, named sub-claims. Other steps stay as they are — do not rewrite the proof.
3. **Name new pivotal sub-claims.** If you introduce a non-trivial helper, state it crisply (hypotheses + conclusion). The manager may decide to lift it into its own row.
4. **Mark LN gaps.** If the LN actually skips this step rather than the prover having missed it, add a `% LN-gap:` comment explaining what the LN assumes.
5. **Do not touch any Lean file** and do not touch any proof file of a different `ref`. Also leave the **restated statement** block (above `\begin{proof}`) untouched -- it's there so the file renders self-contained. Likewise leave the `\def\rowref{...}\def\rowtitle{...}\phantomsection\label{...}` block right after `\begin{document}` alone -- it powers theorem-header rendering and cross-subfile links.
6. **Cite other rows via `\refrow{<ref>}`** (e.g. `by \refrow{claim_3_4}`). Do not use the LN-style `\ref{label}`; those refs are broken under our star-numbered envs.
6. **Report back** to the manager: a one-paragraph summary of what was clarified, any new helper lemmas worth formalizing, and whether the gap was an LN omission or a worker oversight.

## Rules

- The proof file stays in `claim_<N>_<M>_proof_<title>.tex (in the subsection folder)`. You don't rename it.
- Stay close to the LN's argument; don't substitute a completely different proof unless the LN's is unrecoverable (in which case flag it loudly).
- No `sorry`/`obvious`/`omitted` shortcuts. Every step is justified inline or by a cited prior claim.
