# Worker — independently verify a TeX proof

**When to use:** a manager believes a claim's tex proof (in `leanification/<Chapter>/<Section>/tex/<ref>_proof_<title>.tex`) is complete and wants an independent set of eyes before handing the proof off to the leanification phase. You did not write the proof — you arrived fresh and have to convince yourself it holds up.

## Authoritative spec = LN block + `addition_to_the_LN`

**In prove mode**, the tex proof must establish the LN block's claim **AND** every clause in the row's `addition_to_the_LN` field (surfaced in the row context). A proof that closes the literal LN claim but ignores an `addition_to_the_LN` strengthening is INCOMPLETE — FAIL with feedback pointing at the unclosed clause. A proof that uses an `addition_to_the_LN` clause as a hypothesis (e.g. citing finiteness) is fine — that clause is part of the spec. Empty addition → only the literal LN applies.

**In disprove mode** (the row's `proven` field is `disproven`, or the manager has emitted a still-active `mistake`), the tex proof must establish the **NEGATION** of (LN block + `addition_to_the_LN`) — typically a concrete counter-example. The at-the-top statement in a disprove file is the negation the worker wrote, and the proof body must close *that* negation. A proof that closes the *positive* claim in a disprove file is a complete failure, not a partial pass.

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_5`) and the subsection folder
- The path of the tex proof file (`leanification/<Chapter>/<Section>/tex/<ref>_proof_<title>.tex` in prove mode, or `…/<ref>_disproof_<title>.tex` in disprove mode)
- The LaTeX source of the claim itself (from `tex_block` or `main.tex`)
- **Mode signal**: the manager will indicate `MODE: prove` (default) or `MODE: disprove` somewhere in the brief. If the path ends in `_disproof_` and the brief is ambiguous, assume disprove. Use the right checklist below.

## Checklist — prove mode

Use this checklist when `MODE: prove` (or the row is in default prove mode). Report PASS/FAIL with a one-line note per item.

1. **The file exists and starts with the right ref.** Filename must begin with the `ref` (e.g. `claim_3_5_…`).
2. **The claim is restated at the top** of the proof file (the reader can follow without re-reading the LN). The restatement must match the canonical statement file `<ref>_statement_<title>.tex`.
3. **A proof strategy is stated in one sentence** (induction on what, case analysis on what, contradiction, etc.).
4. **No `sorry`, no "omitted", no "obvious".** Every step is justified inline or by a citation to another `ref` in this chapter.
5. **Citations are valid.** Every `def_N_M` / `claim_N_M` referenced corresponds to a real row in the chapter's `data.json`. (You may need to read `data.json` to check.)
6. **Stays close to the LN.** Same induction variable, same case split, same key lemmas as the LN's own proof — substitutions are OK if explicitly justified.
7. **The argument actually closes** the positive claim. Walk it: every conclusion the proof claims follows from explicit hypotheses or previously-established lemmas. No hidden assumptions.
8. **Scope.** No files outside the tex proof file you were asked to verify (and the row's `data.json`, if you needed to look up refs) have been modified.

## Checklist — disprove mode

Use this checklist when `MODE: disprove` (or the path is `<ref>_disproof_<title>.tex`). Report PASS/FAIL with a one-line note per item.

1. **The file exists and starts with the right ref.** Filename must begin with the `ref` (e.g. `claim_3_5_disproof_…`).
2. **A precise NEGATION of the positive claim is restated at the top** of the file. **Not** the positive claim itself. Confirm the at-the-top statement is logically the negation of the LN block + `addition_to_the_LN`. (A separate verifier — `verify_tex_statement_equivalence` in disprove mode — does the strict equivalence check; here you just confirm the at-the-top is recognisably a negation, not the positive claim. If the file is still showing the orchestrator's NEGATION-PENDING placeholder, FAIL immediately.)
3. **A disproof strategy is stated in one sentence** (concrete counter-example with which inputs, or a direct contradiction from the hypotheses).
4. **No `sorry`, no "omitted", no "obvious".** Every step is justified inline or by a citation to another `ref` in this chapter.
5. **Citations are valid.** Every `def_N_M` / `claim_N_M` referenced corresponds to a real row in the chapter's `data.json`.
6. **The argument actually closes the negation.** A proof that closes the *positive* claim here is a hard FAIL — the file is in disprove mode and must establish ¬(claim). If the disproof is a concrete counter-example, the example must (a) satisfy every hypothesis of the LN claim, (b) violate the LN's conclusion, and both must be verified inline.
7. **Justify why the LN's reasoning is flawed.** Disprove mode is unusual; the LN intended the claim to be true. Briefly identify *where* the LN's reasoning breaks down (the missing hypothesis, the silently-introduced assumption, the inverted quantifier). Without this, the proof reads as "I built a counter-example" but does not address *why* the LN got it wrong.
8. **Scope.** No files outside the tex disproof file you were asked to verify (and the row's `data.json`, if you needed to look up refs) have been modified. Specifically: the prove-side `<ref>_proof_<title>.tex` (if present) must be untouched.

## Output

End your message with exactly one of:

```
VERDICT: PASS
```
or
```
VERDICT: FAIL
BEGIN[feedback]
<which checklist items failed, with a concrete description of what needs to
change in the tex proof to PASS next time>
END[feedback]
```

The orchestrator extracts `VERDICT:` and the `BEGIN[feedback]`/`END[feedback]` block, surfacing the feedback directly to the manager's next turn so it knows exactly which step to `expand_proof` or `correct_tex_proof`.
