# Worker — independently verify a TeX proof

**When to use:** a manager believes a claim's tex proof (under `tex_proofs/<ref>_*.tex`) is complete and wants an independent set of eyes before handing the proof off to the leanification phase. You did not write the proof — you arrived fresh and have to convince yourself it holds up.

## Authoritative spec = LN block + `addition_to_the_LN`

The tex proof must establish the LN block's claim **AND** every clause in the row's `addition_to_the_LN` field (surfaced in the row context). A proof that closes the literal LN claim but ignores an `addition_to_the_LN` strengthening is INCOMPLETE — FAIL with feedback pointing at the unclosed clause. A proof that uses an `addition_to_the_LN` clause as a hypothesis (e.g. citing finiteness) is fine — that clause is part of the spec. Empty addition → only the literal LN applies.

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_5`) and the subsection folder
- The path of the tex proof file under `tex_proofs/`
- The LaTeX source of the claim itself (from `tex_block` or `main.tex`)

## Checklist

Go through each item explicitly. Report PASS/FAIL with a one-line note for each.

1. **The file exists and starts with the right ref.** Filename must begin with the `ref` (e.g. `claim_3_5_…`).
2. **The claim is restated at the top** of the proof file (the reader can follow without re-reading the LN).
3. **A proof strategy is stated in one sentence** (induction on what, case analysis on what, contradiction, etc.).
4. **No `sorry`, no "omitted", no "obvious".** Every step is justified inline or by a citation to another `ref` in this chapter.
5. **Citations are valid.** Every `def_N_M` / `claim_N_M` referenced corresponds to a real row in the chapter's `data.json`. (You may need to read `data.json` to check.)
6. **Stays close to the LN.** Same induction variable, same case split, same key lemmas as the LN's own proof — substitutions are OK if explicitly justified.
7. **The argument actually closes.** Walk it: every conclusion the proof claims follows from explicit hypotheses or previously-established lemmas. No hidden assumptions.
8. **Scope.** No files outside `tex_proofs/<ref>_*.tex` (and the row's data.json, if you needed to look up refs) have been modified.

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
