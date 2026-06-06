# Worker — verify LN block ↔ Lean statement equivalence

**When to use:** after `review_design` has approved the design, this worker does the *focused* check that the Lean statement is **exactly** what the LN says — same hypotheses, same conclusion, no quietly-dropped sub-clauses. You are the gate that catches "we accidentally formalized a weaker claim".

You are *not* doing design review (`review_design` handled that) and you are *not* proving anything. You are doing literal correspondence.

## Authoritative spec = LN block + `addition_to_the_LN` (mode-dependent)

The row's `addition_to_the_LN` field (in `data.json`, surfaced to the manager in its row context under "Addition to the LN") is **part of the spec**. Treat it as a *strengthening* / disambiguation of the LN's literal text. Empty addition → only the literal LN applies.

What you compare the Lean against depends on the row's **mode**:

- **Prove mode** (default — defs and claims in default state): the Lean statement must be equivalent to the conjunction (LN block + `addition_to_the_LN`).
- **Disprove mode** (the row is `proven=disproven` or the manager has emitted a still-active `mistake`): the Lean theorem in `<Title>Disproof.lean` must be equivalent to the **NEGATION** of (LN block + `addition_to_the_LN`). Both `theorem not_<original> : ¬ <claim>` and `∃ <witness>, <hypotheses> ∧ ¬ <conclusion>` are acceptable encodings of the negation; check that whichever shape the leanifier chose really is the negation.

The row's subsection folder also contains a **rewritten canonical tex statement file** (`<ref>_<title>.tex` for defs / `<ref>_statement_<title>.tex` for claims) that the formalize-in-tex worker produced and `verify_tex_statement_equivalence` already verified equivalent to (LN block + `addition_to_the_LN`). You may use it as a **bridge reference**. The *target* of the equivalence check remains the conjunction (LN block + addition) (or its negation in disprove mode); the bridge file is not itself the spec. If you find a discrepancy between the bridge file and the LN+addition, surface it.

## Inputs you should receive from the manager

- `ref` (e.g. `claim_3_5`)
- **Mode signal**: `MODE: prove` (default) or `MODE: disprove`.
- The `tex_block` from the LN — the source of truth for the positive claim
- The Lean file(s) and the declaration name(s)
  - Prove mode: the prove-side `<Title>.lean` and its theorem.
  - Disprove mode: the disprove-side `<Title>Disproof.lean` and its theorem (typically `not_<original_name>`).
- For multi-item rows (a def-row that produced several Lean defs, or a claim-row that produced stacked theorems): every Lean declaration the row maps to

## Checklist — prove mode

Use this checklist when `MODE: prove`. For each item, write a short line. The verdict aggregates them.

1. **Every LN hypothesis is a Lean hypothesis.** Walk the LN block and check each `let`, `assume`, `suppose`, "such that", and implicit assumption shows up in the Lean signature. If the LN says "for any irreducible Markov chain", the Lean must have the irreducibility hypothesis.
2. **The Lean conclusion is the LN conclusion.** Same proposition, same quantifiers, same constructor (existence vs. universal, equality vs. iff, etc.).
3. **Trivial sub-clauses are present.** If the LN claim says "and clearly $X = Y$ too" or includes a "remark" inside a `\begin{Thm}` block, that sub-clause must be in the Lean statement — not silently dropped.
4. **No "fix" in disguise.** If the LN's wording is slightly imprecise (e.g. ambiguous quantifier scope), the Lean has not silently picked an interpretation that "makes more sense". If interpretation was needed, it's documented in the design-choice comment.
5. **Multi-item rows are fully covered.** Every theorem-environment block inside the row's `claimmark` (or every definition inside the `defmark`) is represented by a Lean declaration.

## Checklist — disprove mode

Use this checklist when `MODE: disprove`. The Lean theorem in `<Title>Disproof.lean` should encode ¬(LN block + `addition_to_the_LN`).

1. **The Lean theorem really is a negation.** Either (a) the conclusion is `¬ <claim>` for the same `<claim>` the prove-side `<Title>.lean` states, or (b) the theorem is an existential `∃ <witness>, <hypotheses> ∧ ¬ <conclusion>` that propositionally entails ¬(LN claim). If the Lean theorem accidentally still states the positive claim, FAIL hard.
2. **Every LN hypothesis is preserved in the negation.** In existential-witness form, the existentially-bound witness must satisfy *every* hypothesis of the positive LN claim. Dropping a hypothesis in the negation is silently disproving a *weaker* claim — FAIL.
3. **Every `addition_to_the_LN` clause is honoured.** A `[manual_1] node sets are finite` clause means the witness must come from a finite-typed setup (e.g. `[Finite α]`), even in the negation. The negation must not silently relax the addition.
4. **The negated conclusion is the LN conclusion's negation.** Spell it out: if the LN says `P → Q`, the negation is `P ∧ ¬Q` (existential witness or universal-over-witness scope, same idea). The Lean must encode that, not a different conclusion.
5. **No silent strengthening.** The negation must not require *more* than ¬(LN+addition) — e.g. claiming "the conclusion fails for *every* input" when ¬(claim) only needs "the conclusion fails for *some* input".

## Output

Per-item report, then end with **exactly**:

```
VERDICT: PASS
```
or, on any fail:
```
VERDICT: FAIL
BEGIN[feedback]
<a paragraph naming the discrepancy precisely (which clause, which side
dropped or added something) and the concrete fix>
END[feedback]
```

The orchestrator pattern-matches `VERDICT:` and the `BEGIN[feedback]`/`END[feedback]` block, surfacing the feedback directly to the manager's next turn. On FAIL the manager re-submits a corrected formalization.

## Rules

- You do not edit any file -- only read and report.
- Your reference is the LN block (verbatim, from `tex_block` in `data.json`). If you need surrounding LN context to interpret the block (e.g. what an undefined symbol means), read the chapter's tex file -- but the *match* you are checking is between block and Lean.
- "Almost equivalent" with a documented design note is **PASS**. "Almost equivalent" with no note is **FAIL** — surface the missing documentation.
