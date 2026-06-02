# Worker — formalize a definition in Lean

**When to use:** the manager has handed you a row with `def_or_claim == "def"` that is not yet formalized. The lecture notes have the source text wrapped in `\begin{defmark}...\end{defmark}`. Your job is to write the equivalent Lean 4 declaration.

## Authoritative spec = LN block + `addition_to_the_LN`

The row's `addition_to_the_LN` field (surfaced in the row context) is **part of the spec**. It carries human-authored clarifications, strengthenings, or disambiguations written during the initialization phase. Treat them as part of the LN: the Lean definition you write must satisfy the LN's literal reading **AND** every clause in the addition. If the addition contradicts the literal LN, the addition wins. Empty addition → only the literal LN applies.

Concretely: every `[<sid>] …` paragraph and every `[manual_*] …` paragraph in `addition_to_the_LN` is a constraint your Lean encoding must respect. E.g. a `[manual_1] The vertex sets J and V are assumed to be finite.` clause means the Lean carrier types must be `Finite` (or `Fintype`), even though the literal LN does not say so.

## Inputs you should receive from the manager

- `ref` (e.g. `def_3_5`)
- `tex_file` and the line range of the `defmark` block (or the raw block contents)
- the target Lean file path inside the row's subsection folder under `leanification/`
- any tips on the row

## What to do

1. **Read the source.** Open the `tex_file` and read the full `defmark` block (and a few surrounding paragraphs if context is needed).
2. **Decide single vs. multi-item.** A "definition" row in the data file is sometimes a *collection* of definitions — a notation block with several bullet points, or a list of operators introduced together. In that case **do not force them into one Lean declaration**: produce as many `def`s / `notation`s / `structure`s as it takes to mirror the LN faithfully, split across multiple files if a file would otherwise grow past ~700 lines or a natural module boundary suggests it.
3. **Plan the shape.** For each item decide whether it becomes a `def`, an `abbrev`, a `structure`, a `class`, or a `notation`. Prefer the construct that lets dependent theory build naturally on top of it.
4. **Write the Lean declaration(s)** in the target file(s), with a comment block above each one containing:
   - The `ref` (e.g. `-- def_3_5`)
   - A short human-language description of what is being defined
   - The TeX of the definition (verbatim, between `/-` and `-/`), for traceability
   - A short **Design choice** note: why you chose this Lean shape, what mathlib structure you built on (or why you didn't), trade-offs
5. **Check it builds**: `lake build` from `/home/11716061/repo_scaffold2/`. Fix any errors.
6. **Report back** to the manager: every Lean file path you wrote to, each declaration name, and any decisions that may affect later claims that depend on this definition.

## Rules

- Stay close to the lecture notes — same names where reasonable, same notation, same structure.
- No `sorry` and no `True` placeholders.
- If the definition needs supporting structure (a helper `def`, an instance) that the LN takes for granted, include it.
- If the definition uses something from mathlib that fits exactly, build on it. If not, build your own and document why.
- Edit only files inside your subsection's folder under `leanification/`.
