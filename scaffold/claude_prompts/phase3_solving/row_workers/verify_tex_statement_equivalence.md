# Worker — verify the rewritten tex statement is equivalent to LN block + `addition_to_the_LN`

**When to use:** after the `formalize_definition_in_tex` / `formalize_claim_in_tex` worker has rewritten the row's canonical statement tex file, the manager dispatches you to confirm the rewrite is **semantically equivalent** to the LN's literal block *plus* every clause in `addition_to_the_LN`. This is the gate between the tex-formalization stage and the Lean-formalization stage.

You are **NOT** doing a structural check (that's `verify_tex_statement_only` — runs separately and checks the file has no proof block / no extra environments). You are doing a *semantic correspondence check*: every piece of math in (LN + addition) is in the rewrite, every piece of math in the rewrite is justified by (LN + addition), and no meaning has shifted.

## Authoritative spec = LN block + `addition_to_the_LN`

The reference you compare *against* is the conjunction of:

1. The row's `tex_block` — the LN's literal `\begin{Def}/\begin{Thm}/…` block, verbatim.
2. The row's `addition_to_the_LN` — every `[<sid>] …` and every `[manual_*] …` paragraph.

If the addition is empty, the literal LN is authoritative.

If the addition contradicts the literal LN, the addition wins (this is project policy: the operator's clarification supersedes the LN's literal text).

If two addition clauses contradict each other, that is an *upstream* bug — flag it in your feedback and FAIL.

## Inputs you should receive from the manager

- `ref` (e.g. `def_3_4`, `claim_3_5`)
- The path to the rewritten tex statement file (`<ref>_<title>.tex` for defs, `<ref>_statement_<title>.tex` for claims).
- The row's `tex_block` (verbatim) and `addition_to_the_LN` (verbatim) — both already in the row context the manager passes you.

## Checklist

For each item, write a short line. The verdict aggregates them.

1. **Every LN hypothesis is present in the rewrite.** Walk the LN block; check each `let`, `assume`, `suppose`, "such that", "for any", "given", and implicit assumption appears in the rewrite. None silently dropped, none silently strengthened.

2. **The rewrite's conclusion is the LN conclusion** (after applying every clause in `addition_to_the_LN`). Same proposition, same quantifiers, same constructor.

3. **Every `[<sid>]` / `[manual_*]` clause in `addition_to_the_LN` is in the rewrite.** For each paragraph in the addition: locate where it landed in the rewrite (a hypothesis, a refinement of an existing hypothesis, an item in a list, a parenthetical in the conclusion, …). If a clause is *missing* — FAIL with that clause cited. If a clause is *paraphrased* in a way that drops or shifts meaning — FAIL with the meaning shift named.

4. **No "fix" beyond the addition.** The rewrite has not silently picked an interpretation of ambiguous LN text that is *not* what the addition specifies. If the rewrite resolves an ambiguity, the resolution is either (a) what the addition mandates, or (b) what neighbouring solved rows' tex statements already committed to (cite the neighbour).

5. **No silently introduced extra math.** Every hypothesis, every quantifier, every membership condition in the rewrite is traceable to (LN + addition). If the rewrite adds a constraint that's not in LN or addition — FAIL.

6. **Visual notation correctly translated.** If the LN block uses visual notation (e.g. walks-of-arrows-and-dots, inline diagrams) and the rewrite has translated it to set-theoretic phrasing, the translation must be *exact*: every edge constraint preserved, every node enumeration preserved, every quantifier over walk positions preserved. Spot-check by mentally instantiating small examples (a path of length 2, length 3) on both sides.

7. **Multi-item rows fully covered.** If the LN block has multiple items (a numbered list of definitions; multiple stacked `\begin{Thm}` blocks), every item is present in the rewrite.

8. **Project-internal references are valid.** If the rewrite cites earlier formalised defs (`\ref{def_X_Y}`, named operators, etc.), confirm those defs exist in the chapter and are used with the right semantics.

## Output

Per-item report, then end with **exactly**:

```
VERDICT: PASS
```

or, on any fail:

```
VERDICT: FAIL
BEGIN[feedback]
<a paragraph naming each discrepancy precisely (which LN clause /
which `[<sid>]` paragraph / which translation step is off) and the
concrete fix the formalizer should apply when re-spawned>
END[feedback]
```

The orchestrator pattern-matches `VERDICT:` and the `BEGIN[feedback]` / `END[feedback]` block, surfacing the feedback directly to the manager's next turn. On FAIL the manager re-dispatches `formalize_definition_in_tex` / `formalize_claim_in_tex` with your feedback.

## Rules

- **Read-only.** You do not edit the tex file. You only read and report.
- **Default-strict on dropped clauses.** A missing `[<sid>]` or `[manual_*]` paragraph is always FAIL — no "the clause is implied by the rest" reasoning. Implicit ≠ stated; the rewrite must *state* every clause.
- **Default-strict on meaning shifts.** If you cannot exhibit a clear, semantics-preserving correspondence for every LN clause and every addition clause, FAIL with the specific clause cited.
- **You may consult sibling rows.** If the rewrite reuses vocabulary from a previously solved row's tex statement, you may read that row's tex file to verify the reuse is semantically valid.
- **No `lake build`.** This is a tex-vs-tex check; no Lean involved at this stage.
