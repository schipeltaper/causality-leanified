# Worker — check whether a Lean proof is unnecessarily complex

**When to use:** a claim has been Lean-proven and the row is *about* to be marked `solved` — but before locking it in, the manager wants an independent agent (with **full lecture-notes context**) to look at the proof and ask: *is this proof unnecessarily complex? Could it have been shorter, cleaner, more in line with the LN's own style?*

If you find a genuinely simpler proof, you propose it. The manager will then run it through `prove_claim_in_lean` (rewriting the Lean proof) and `verify_row_solved` again.

If you cannot find a simpler proof after honest effort, you PASS — the existing proof stays.

## Read first
- `claude.md` (project rules) and `lecture-notes/lecture_notes/main.tex`
- The LN chapter the claim lives in -- pay particular attention to its proof style, the lemmas it relies on, and any "the proof is left as an exercise / immediate from X" hints
- The tex proof at `tex_proofs/<ref>_proof_<title>.tex`
- The Lean proof (in the row's `lean_files`)

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_5`)
- The Lean file and the declaration name
- The tex proof file path
- The `lean_files` list (in case multiple files contributed)

## What to do

1. **Read the LN's own proof if it exists** — it's the gold standard for "how the author thought about this". If the LN's proof is a 5-liner and the Lean proof is 50 lines, that's a strong signal.
2. **Read the tex proof.** This is the verified mathematical argument; the Lean version should be a translation, not a re-derivation.
3. **Read the Lean proof.** Look for symptoms of unnecessary complexity:
   - Long tactic blocks where `simp [foo]` or `omega` would close the goal
   - Repeated case-splits that could be unified
   - Local helper lemmas inlined that should be lifted to the file's preamble, or vice versa
   - Manual rewriting where a single `rw [...]` or `exact h ▸ rfl` suffices
   - Universes / instance arguments threaded unnecessarily
4. **Try alternatives** using the lean-lsp MCP (`lean_multi_attempt`, `lean_state_search`, `lean_hammer_premise`). If a much shorter tactic block closes the goal, you've found a simplification.
5. **If you find a simpler proof:** report it concretely — exact tactic block, the diff against the current proof, and the rationale (why it's simpler AND still in the LN's paradigm). The manager will dispatch `prove_claim_in_lean` (with `correct_tex_proof` first if the tex sketch needs to mirror the simpler argument) to rewrite.
6. **If you do not find one:** report the avenues you tried, briefly, then PASS. Honest "no simpler version" is the right answer for proofs that are intrinsically long.

## Output

End your message with **exactly one** of:

```
VERDICT: PASS
```
(the existing proof is as simple as it reasonably gets), or:

```
VERDICT: FAIL
BEGIN[feedback]
<a concrete description of the simpler proof: which lines to replace, the
new tactic block, and why it's correct>
END[feedback]
```

The orchestrator extracts both `VERDICT:` and the `BEGIN[feedback]`/`END[feedback]` block, surfacing your alternative directly to the manager so it can dispatch the prover with the simpler proof. (`correct_tex_proof` first if the tex sketch needs to mirror the change.)

## Rules

- "Simpler" is judged by **readability and adherence to the LN's style**, not raw line count. A 3-line `simp_all` that obscures what the proof does is **worse** than a 10-line proof that mirrors the LN's reasoning step-for-step.
- Do not propose simplifications that change the *strategy* (induction variable, case split structure) -- those belong in `correct_tex_proof`.
- Do not edit any file -- only read and report.
- If the proof is short to begin with (≤ 5 lines, or single-tactic), default to PASS unless something is genuinely wrong.
