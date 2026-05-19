# Worker — document a counter-example to a claim

**When to use:** the manager has concluded that a `claim` row is genuinely false (not just hard to prove). Your job is to make that argument rigorously — by producing a counter-example — and capture it in the Lean source so the row can be marked `proven=disproven` and `solved=yes`.

> The lecture notes are known to contain at least one big mistake. Treat this as a real possibility, not a last resort. But also: do **not** weaken a claim's statement just because you can't prove it. The bar for "disproven" is a concrete counter-example, not "I'm stuck".

## Inputs you should receive from the manager

- `ref` and the Lean file/theorem name (statement is already formalized, body is `sorry`)
- The LN source of the claim
- The manager's reason for suspecting the claim is false (a failed proof attempt? a worked example that breaks it?)

## What to do

1. **Confirm the suspicion.** Construct a concrete example — a specific graph, a specific kernel, a specific finite measurable space — for which:
   - All hypotheses of the claim hold
   - The conclusion fails
   Make the example as small and explicit as possible.
2. **Formalize the counter-example in Lean** in the row's subsection folder. Either:
   - Replace `theorem foo : <claim> := sorry` with `theorem not_foo : ¬ (<claim>) := <proof using the example>`, or
   - Keep `foo` as the original statement (commented out / left as `sorry`) and add a separate `theorem foo_counterexample : ∃ <setup>, hypotheses ∧ ¬ conclusion := …` next to it.
   Whichever shape better matches the subsection's style — be consistent within the folder.
3. **Update the comment block** above the original claim with:
   - A `-- LN-mistake: …` line explaining what the LN claims, what's wrong, and where the counter-example lives.
   - A pointer to the new `not_foo` / `foo_counterexample` declaration.
4. **Build clean**: `lake build` from `/home/11716061/`.
5. **Report back** to the manager: a one-paragraph summary of the counter-example, why you're confident the claim is genuinely false (not just "hard to prove"), and the names of the new declarations.

## Rules

- Do not modify the LN `.tex` itself beyond what `claude.md` allows (it has rules for "Big mistake" annotations).
- The counter-example must be a **proof**, not a sketch — fully Lean-checkable, no `sorry`.
- Stay within the subsection's folder.
- If after working through it you no longer believe the claim is false, say so and hand back to the manager for another proof attempt.
