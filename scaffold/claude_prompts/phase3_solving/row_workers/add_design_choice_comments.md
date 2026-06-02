# Worker — write or expand the design-choice comments above a Lean declaration

**When to use:** a definition or claim-statement has just been formalized in Lean, and the manager has already PASSed `review_design` and `verify_equivalence`. Before the row can proceed (to `solved` for defs, or to the proof phase for claims), the design-choice comment block above each affected Lean declaration must be filled in with the **why** behind the Lean shape — what alternatives were considered, why this one wins, what downstream lemmas it sets up for.

## Authoritative spec = LN block + `addition_to_the_LN`

When you write the "why", **explicitly reference every clause in the row's `addition_to_the_LN`** that influenced the Lean shape. E.g. if a `[manual_1] vertex sets are finite` clause led to the `[Finite α]` typeclass on the structure, the comment should say so — that's load-bearing context for a future reader. If a `[<sid>] …` clause was the reason a particular field was added, mention it. Empty addition → no addition-driven design choices to mention.

The formalize worker may have left a stub `Design choice:` line; you replace or extend it with a substantive few paragraphs.

## Inputs you should receive from the manager

- `ref` (e.g. `def_3_5` or `claim_3_12`)
- The Lean file(s) and the declaration name(s) — note this is sometimes a list (multi-item rows)
- The `tex_block` from the LN, and the path to the LN tex file
- A short summary of the verifier feedback from `review_design` and `verify_equivalence` so you know what was already considered

## What to do

For each Lean declaration the row produced, edit the comment block immediately above it to include:

1. **One-sentence summary** of what the declaration represents.
2. **`Design choice:`** — a paragraph (3–8 sentences) covering:
    - *Why this Lean shape* (e.g. `structure` vs `class` vs `def`, `Set` vs `Finset` vs `List`, dependent vs non-dependent indexing).
    - *Alternatives considered and rejected*, briefly, with the reason. (If the formalize worker already mentioned one, sharpen it; don't drop it.)
    - *Downstream consequences*: which later LN chapters will pattern-match on this shape, and what would have to be redone if we'd picked the alternative.
    - *Mathlib re-use*: did we build on a mathlib structure, or roll our own, and why.
3. **Constraints / known limitations** (if any): things this shape can't express that the LN handles implicitly. Surface them so they're not a surprise downstream.
4. Preserve the existing `-- <ref>` header line, the human-language description, and any verbatim tex-of-the-block already in the comment. Only add / replace the design-choice paragraph(s).

For multi-item rows (a "def" row that produced several declarations, or a "claim" row that produced stacked theorems), write the design-choice comment **above each declaration separately** — the rationale for one item is rarely the same as for the others.

## Rules

- Edit only files inside the row's subsection folder under `leanification/`.
- No `sorry` introduced. No new claim statements. No rewriting of the declaration itself.
- After your edit, `lake build` from `/home/11716061/repo_scaffold2/` must still succeed.
- Report back to the manager: a one-paragraph summary of what you wrote and any LN-downstream concern your write-up surfaced that the manager should escalate.
