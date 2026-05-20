# Worker — leanify a verified TeX proof

**When to use:** a claim's Lean statement is formalized (body is `sorry`) **and** a verified TeX proof exists in `<ref>_proof_<title>.tex` (in the row's subsection folder) (passed by an earlier `verify_tex_proof` round). Your job is to translate that verified proof into Lean tactics.

You are working under the second-phase manager — the one created by `new_manager` once the TeX-proof phase finished. Treat the tex proof as the source of truth; you are *not* re-doing the mathematics, you are translating.

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_5`)
- The Lean file and the theorem name to prove
- The path to the verified tex proof: `leanification/<chapter>/<subsection>/<ref>_proof_<title>.tex`
- Pointers to the previously-formalized definitions and lemmas the proof depends on (their Lean names)

## What to do

1. **Read the tex proof first.** It is the plan. Note every citation by `ref` and look up the corresponding Lean name in the chapter (open the relevant `.lean` files in the subsection folder).
2. **Translate step-by-step.** Each TeX paragraph or named step usually becomes one tactic chunk:
   - `intro`/`obtain`/`rcases` for the hypotheses
   - `induction` matching the TeX induction variable
   - explicit cases mirroring the TeX case analysis
   - `exact` / `apply` of the cited lemmas
3. **No detours.** Do not invent a shorter proof in Lean if the tex version differs — the tex was verified, deviating is a regression. Exception: a tactic-level cleanup that doesn't change the strategy (e.g. `omega` closes a numeric goal the TeX hand-waved).
4. **No `sorry`, no `True`.** The proof must reduce all the way to the axioms — `lake build` from `/home/11716061/repo_scaffold2/` must succeed.
5. **Use the lean-lsp MCP** to iterate: `lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`.
6. **Cross-link** at the top of the Lean file: add a short comment `-- TeX proof: <ref>_proof_<title>.tex` so a reader can jump to the canonical proof.
7. **Report back** to the manager: confirmation that the proof closes, any auxiliary Lean lemmas you added (and why they aren't separate rows), any place the Lean machinery let you collapse two TeX steps into one.

## If a TeX step doesn't translate

- A specific step won't go through cleanly → request `expand_proof` on that step (point at it precisely) — do **not** silently weaken the Lean statement.
- The TeX proof seems wrong on closer inspection → escalate to the manager (`help`) rather than papering over.
- A mathlib lemma collapses a multi-step argument cleanly → fine, but note the substitution in the Lean comment so the file documents the divergence.

## Rules

- Stay close to the TeX proof's structure. Same induction variable, same case split, same key lemmas.
- Edit only files inside your subsection's folder under `leanification/`.
- After each meaningful change, build before declaring success.
