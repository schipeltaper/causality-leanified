# Worker — leanify a verified TeX proof

**When to use:** a verified TeX proof exists and the manager wants it translated into Lean tactics.

You are operating in one of two **modes**:

- **Prove mode** (default): a claim's Lean statement is already formalized (body is `sorry`) in `<Title>.lean`, and a verified prove-side TeX proof exists in `<ref>_proof_<title>.tex` (passed an earlier `verify_tex_proof` round). Your job is to translate that verified proof into Lean tactics, replacing the `sorry`.
- **Disprove mode**: the manager has emitted `mistake` (and the mistake-sweep has cleared), and a verified disprove-side TeX proof exists in `<ref>_disproof_<title>.tex`. Your job is to write a **new file** `<Title>Disproof.lean` containing both the **negation theorem signature** AND the proof of it. Do not touch the prove-side `<Title>.lean` — it stays untouched so the row can flip back via `unmistake`.

Treat the verified tex proof as the source of truth in both modes; you are *not* re-doing the mathematics, you are translating.

## Authoritative spec = LN block + `addition_to_the_LN`

**In prove mode**, the row's `addition_to_the_LN` field is **part of the claim's statement and spec**, and the tex proof you're translating was written to establish that strengthened claim. Your Lean proof must close exactly the Lean theorem statement — which itself was written to capture the LN block + every clause in `addition_to_the_LN`. Empty addition → just the literal LN.

**In disprove mode**, the spec you are negating is still (LN block + `addition_to_the_LN`). Your Lean theorem must state ¬(that spec) (or an existential counter-example equivalent to it) and its proof must close that negation.

If during translation you realise the Lean statement (the existing one in prove mode, or the one you are writing in disprove mode) does not capture some clause in `addition_to_the_LN`, surface that to the manager rather than papering over with `by exact?` — the Lean statement needs to be re-formalized first.

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_5`)
- **Mode signal**: `MODE: prove` (default) or `MODE: disprove`.
- **Prove mode**: the existing Lean file `<Title>.lean` and the theorem name with the `sorry` body to fill. Path to the verified tex proof: `leanification/<chapter>/<subsection>/tex/<ref>_proof_<title>.tex`.
- **Disprove mode**: the *new* file `<Title>Disproof.lean` you will create (sibling of the existing `<Title>.lean`), the existing prove-side theorem name (so you can name the negation, e.g. `not_<original_name>`), and the path to the verified disprove tex: `leanification/<chapter>/<subsection>/tex/<ref>_disproof_<title>.tex`.
- Pointers to the previously-formalized definitions and lemmas the proof depends on (their Lean names).

## Lean statement markers — respect them

**In prove mode**, the theorem you're proving was wrapped by the formalizer with `-- <ref> -- start statement` / `-- <ref> -- end statement` line comments around the signature. The proof body (`:= by sorry` or `:= proof_term`) sits **below** the end marker. Replace the `sorry` (or whatever placeholder is there) with the real tactic block; **do not move, delete, or alter the marker lines**, and do not write any proof content above the end marker. Final shape:

```lean
-- <ref> -- start statement
theorem <name> ... : <conclusion>
-- <ref> -- end statement
:= by
  <your tactic proof here>
```

**In disprove mode**, you are creating a brand-new file `<Title>Disproof.lean` and you must add the markers yourself. Wrap the negation signature exactly as the formalizer would have for a prove-side theorem:

```lean
-- <ref> -- start statement
theorem not_<original_name> ... : ¬ <original_conclusion>
-- <ref> -- end statement
:= by
  <proof of the negation here>
```

Or, if the negation is more natural as an existential counter-example:

```lean
-- <ref> -- start statement
theorem not_<original_name> ... :
    ∃ <witness>, <hypotheses of original claim hold for witness>
                  ∧ ¬ <conclusion of original claim at witness>
-- <ref> -- end statement
:= by
  <proof exhibiting the concrete counter-example>
```

If you need helper definitions for the negation signature to type-check, wrap them with `-- <ref> --- start helper` / `-- <ref> --- end helper` (three dashes). Proof helpers do NOT get any markers — markers are reserved for statement content.

In both modes, the website builder relies on the end-statement marker being immediately above the `:=` so it can render the statement separately from the proof. If a proof helper (a small lemma the proof needs but the statement doesn't) lands in the same file, place it OUTSIDE the markers.

## What to do

1. **Read the tex proof first.** It is the plan. Note every citation by `ref` and look up the corresponding Lean name in the chapter (open the relevant `.lean` files in the subsection folder).
   - **Prove mode**: read the verified `<ref>_proof_<title>.tex`. The statement it restates is the one you're proving.
   - **Disprove mode**: read the verified `<ref>_disproof_<title>.tex`. The negation it restates is what your Lean theorem signature must capture; the proof inside is what you translate into the tactic block.
2. **Translate step-by-step.** Each TeX paragraph or named step usually becomes one tactic chunk:
   - `intro`/`obtain`/`rcases` for the hypotheses
   - `induction` matching the TeX induction variable
   - explicit cases mirroring the TeX case analysis
   - `exact` / `apply` of the cited lemmas
   - **Disprove via counter-example**: write the concrete witness explicitly (`refine ⟨witness, ?_, ?_⟩`), then prove the hypotheses are satisfied and the conclusion fails for that witness.
3. **No detours.** Do not invent a shorter proof in Lean if the tex version differs — the tex was verified, deviating is a regression. Exception: a tactic-level cleanup that doesn't change the strategy (e.g. `omega` closes a numeric goal the TeX hand-waved).
4. **No `sorry`, no `True`.** The proof must reduce all the way to the axioms — `lake build` from `/home/11716061/repo_scaffold2/` must succeed.
5. **Use the lean-lsp MCP** to iterate: `lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`.
6. **Cross-link** at the top of the Lean file: add a short comment `-- TeX proof: <ref>_proof_<title>.tex` (or `<ref>_disproof_<title>.tex` in disprove mode) so a reader can jump to the canonical proof.
7. **Disprove-mode file discipline**: in disprove mode the new file `<Title>Disproof.lean` lives alongside the existing `<Title>.lean`. **Do not edit `<Title>.lean`** — that file holds the prove-direction work and stays untouched in case the row flips back via `unmistake`. Add a one-line cross-reference comment near the top of `<Title>Disproof.lean` pointing at `<Title>.lean` (e.g. `-- Disprove-side of <Title>.lean — the row's manager emitted mistake.`). Imports go just like for any new Lean file in this subsection.
8. **Report back** to the manager: confirmation that the proof closes, the file path(s) you wrote, the theorem name(s), any auxiliary Lean lemmas you added (and why they aren't separate rows), any place the Lean machinery let you collapse two TeX steps into one. **In disprove mode**, also confirm that `<Title>.lean` was not touched.

## If a TeX step doesn't translate

- A specific step won't go through cleanly → request `expand_proof` on that step (point at it precisely) — do **not** silently weaken the Lean statement.
- The TeX proof seems wrong on closer inspection → escalate to the manager (`help`) rather than papering over.
- A mathlib lemma collapses a multi-step argument cleanly → fine, but note the substitution in the Lean comment so the file documents the divergence.

## Rules

- Stay close to the TeX proof's structure. Same induction variable, same case split, same key lemmas.
- Edit only files inside your subsection's folder under `leanification/`.
- After each meaningful change, build before declaring success.
