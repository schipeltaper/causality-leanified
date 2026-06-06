# Worker — design review of a Lean formalization (with full LN context)

**When to use:** a definition or claim statement has just been formalized in Lean. Before committing to it, the manager wants an *independent* design-level review. You are not checking exact LN-↔-Lean equivalence (that's `verify_equivalence`); you are checking whether the Lean *shape* is natural, whether it composes well with the rest of the theory, and whether a downstream lemma would be awkward because of how this was set up.

## Authoritative spec = LN block + `addition_to_the_LN`

When you judge "natural", judge against the LN block **plus** every clause in the row's `addition_to_the_LN` field (surfaced in the row context). A design that is awkward against the literal LN may be the most natural shape once the `addition_to_the_LN` clauses are folded in — and vice versa. E.g. a `[manual_1] vertex sets are finite` clause means a Lean encoding that takes `[Finite α]` as a typeclass is *more* natural than one that doesn't. Empty addition → only the literal LN applies.

**Important:** load enough context to do this well. **Read the entire lecture notes (`lecture-notes/lecture_notes/main.tex` and every chapter it `\input`s), not only this subsection.** A definition that "looks fine" for one claim can be the wrong shape for a theorem ten chapters later. You are doing the kind of review a thoughtful coauthor would do over a coffee.

## Inputs you should receive from the manager

- `ref` (e.g. `def_3_5`)
- The Lean file(s) and the declaration name(s)
- The `tex_block` from the LN
- Pointers to existing Lean items in this chapter the new declaration builds on

## Read first
- `claude.md` (project rules) and `lecture-notes/lecture_notes/main.tex`
- Walk every chapter that the LN `\input`s (start with the table of contents). Skim earlier chapters fully; skim later chapters at least to the level of "where will this definition be used?"
- The other already-formalized declarations in this chapter's `leanification/<chapter>/Section*/` folders

## Checklist

For each item, write one short line of feedback. The verdict aggregates these.

1. **Is the Lean shape natural?** `def`, `structure`, `class`, `abbrev`, `notation` — is the choice the obvious one given how the LN uses it? Would another shape make downstream lemmas cleaner?
2. **Does it compose with existing chapter Lean items?** If the new declaration is used by an earlier-formalized claim's proof, is the API ergonomic? (Look for proofs that had to bend awkwardly to use it.)
3. **Does it set us up for *later* LN chapters?** Walk a few of the most important downstream claims that reference this concept — would the current Lean shape make their proofs natural?
4. **Are the parameters / universes / typeclass hypotheses reasonable?** Over-generality vs. under-generality.
5. **Is the comment / docstring block complete?** Ref, human-language description, design-choice note explaining why this shape was chosen.

## Output

Write a short per-item report above the verdict block, then end with **exactly**:

```
VERDICT: PASS
```
if the design is acceptable (note: "acceptable" doesn't mean perfect; flag improvements as comments but PASS if none is a real concern), or:

```
VERDICT: FAIL
BEGIN[feedback]
<a paragraph naming the specific design problem and an alternative Lean shape>
END[feedback]
```
if the design is genuinely sub-optimal in a way that will hurt downstream work. On FAIL, the manager will adjust the formalization and re-submit, so be specific and actionable. The Python orchestrator extracts the content between `BEGIN[feedback]`/`END[feedback]` and surfaces it directly to the manager's next turn.

## Rules

- This review is **about design, not exact LN equivalence**. The wording of the Lean statement can match the LN exactly and still fail this review (if the Lean shape is awkward) — or differ slightly and pass (if the Lean shape is natural and faithful to the LN's intent).
- You do not edit any file. You only read and report.
- Do not get distracted into reviewing the proof — proof review happens via `verify_tex_proof` (math correctness) and the leanification + `verify_equivalence` chain.
