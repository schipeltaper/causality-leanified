# Worker — formalize a definition in Lean

**When to use:** the manager has handed you a row with `def_or_claim == "def"` whose canonical statement tex file has been **rewritten and verified** by `formalize_definition_in_tex` + `verify_tex_statement_equivalence`. Your job is to translate that rewritten tex statement into the equivalent Lean 4 declaration.

## Authoritative spec = the rewritten canonical tex statement file

The row's canonical statement tex file at `leanification/<Chapter>/<Section>/tex/<ref>_<title>.tex` is your **primary spec**. It was rewritten by the `formalize_definition_in_tex` worker so that:

- Every clause in `addition_to_the_LN` is folded in.
- The body is exact and unambiguous (no implicit quantifiers, no informal "...").
- Bespoke visual notation has been translated to set-theoretic phrasing.

It then passed `verify_tex_statement_equivalence`, which verified it is semantically equivalent to LN block + `addition_to_the_LN`. So: **translate the rewritten file**, not the LN's raw `defmark` block.

The LN `tex_block` and `addition_to_the_LN` remain available in your row context as *backup reference* — useful for sanity checks, names, and intent — but if you find yourself preferring the LN block over the rewritten tex, that's a signal something is wrong (either with the rewrite or with your reading). Stop, report back to the manager, and ask for a re-spawn of the tex worker.

## Inputs you should receive from the manager

- `ref` (e.g. `def_3_5`)
- The path to the rewritten canonical tex statement file (your primary spec)
- The LN `tex_file` for surrounding chapter context (backup)
- The target Lean file path inside the row's subsection folder under `leanification/`
- Any tips on the row

## Build on what is already there

You are not formalizing this row in isolation. By the time you are spawned, every earlier row in this chapter is already formalized in Lean and lives in this subsection's folder (or a sibling subsection). **Read those existing Lean files before writing your own.** The right shape for your new declaration is almost always one that reuses an earlier row's types, predicates, notation, and naming conventions — not a parallel re-introduction.

Concretely, before you start writing:

1. **Open every sibling Lean file** in this row's subsection folder under `leanification/<Chapter>/<Section>/`. The chapter aggregator `leanification/<Chapter>.lean` is a quick index of what already exists.
2. **For each type / predicate / notation your row's spec references** (e.g. `CDMG`, `G.tuh`, `Walk G u v`, `G.IsAcyclic`), find where it's defined and read its declaration plus its design-choice comment block. Use those exact names; do not introduce alternative spellings or duplicate definitions.
3. **Match the chapter's conventions** for namespace placement, variable binders (`variable {Node : Type*} [DecidableEq Node]`), implicit-vs-explicit parameter style, `def` vs `abbrev` choice, dot-notation accessibility, and similar low-level decisions. Where a sibling file took a specific design choice (e.g. "use `Finset (Node × Node)` plus a symmetry field rather than `Sym2`"), inherit that choice unless the row's `addition_to_the_LN` explicitly requires a deviation.
4. **If the spec needs something that doesn't yet exist** (a missing helper predicate, a missing notation), surface that in your report — it may indicate the missing piece should belong to an earlier row or warrant its own `--- helper` block here. Do not silently invent a parallel concept that competes with what an earlier row already covered.

The rewritten canonical tex statement file is your *spec*; the existing Lean files are your *vocabulary*. Together they pin down both *what* to formalize and *how* it should look in this codebase.

## What to do

1. **Read the rewritten tex statement file** end to end. This is your spec. Read the row's `addition_to_the_LN` and the LN `tex_block` as backup, but the rewritten file is what you formalize.
2. **Read sibling Lean files** (per *Build on what is already there* above) so the new code uses existing names, types, and conventions.
3. **Decide single vs. multi-item.** A "definition" row in the data file is sometimes a *collection* of definitions — a notation block with several bullet points, or a list of operators introduced together. In that case **do not force them into one Lean declaration**: produce as many `def`s / `notation`s / `structure`s as it takes to mirror the LN faithfully, split across multiple files if a file would otherwise grow past ~700 lines or a natural module boundary suggests it.
4. **Plan the shape.** For each item decide whether it becomes a `def`, an `abbrev`, a `structure`, a `class`, or a `notation`. Prefer the construct that lets dependent theory build naturally on top of it.
5. **Write the Lean declaration(s)** in the target file(s), with a comment block above each one containing:
   - The `ref` (e.g. `-- def_3_5`)
   - A short human-language description of what is being defined
   - The TeX of the definition (verbatim, between `/-` and `-/`), for traceability
   - A short **Design choice** note: why you chose this Lean shape, what mathlib structure you built on (or why you didn't), trade-offs — and explicitly which sibling Lean files / declarations you built on.
6. **Wrap the main declaration(s) with statement markers.** This is REQUIRED -- the website builder relies on them to extract just the statement formalization for display. The markers are *plain Lean line comments*. See **Marker conventions** below.
7. **Check it builds**: `lake build` from `/home/11716061/repo_scaffold2/`. Fix any errors.
8. **Report back** to the manager: every Lean file path you wrote to, each declaration name, which sibling defs / predicates you reused, and any decisions that may affect later claims that depend on this definition.

## Marker conventions (REQUIRED)

The website builder grep-extracts statement-shaped Lean content using a fixed marker convention. You MUST follow it for every Lean declaration this row produces.

**Main statement markers** — wrap each top-level declaration that is part of this row's "statement formalization" (the def itself, including all of its fields if it is a structure / class):

```lean
-- <ref> -- start statement
def <name> ... :=
  ...
-- <ref> -- end statement
```

Where `<ref>` is this row's ref (e.g. `def_3_1`). For multi-item rows (a definition row that produces several `def`s / `notation`s), wrap **each** one separately with its own start/end pair, all using the row's ref. The markers go **immediately** above the `def`/`structure`/`class`/`abbrev`/`instance`/`notation`/`opaque` line and **immediately** below the last line of the declaration. Nothing else may appear between a `-- <ref> -- start statement` line and the declaration it wraps (no blank lines, no comments, no docstrings — those go ABOVE the start marker). Likewise nothing between the declaration's last line and `-- <ref> -- end statement`.

**Helper-for-statement markers** (THREE dashes, distinct from the start/end markers) — wrap any auxiliary declaration **or** `variable` directive that this row had to introduce to make the main statement well-typed (e.g. a small `def` of a relation the main `structure` uses as a field, an `instance` the main type needs, **or** a `variable {α : Type*} [DecidableEq α]` line whose binders flow into the wrapped statements via Lean 4's auto-binding). The website builder pulls these out alongside the main statement so the rendered statement is self-contained.

```lean
-- <ref> --- start helper
def <helper_name> ... :=
  ...
-- <ref> --- end helper

-- <ref> --- start helper
variable {Node : Type*} [DecidableEq Node]
-- <ref> --- end helper
```

Same placement rules: immediately above the helper's first line, immediately below its last. Use the **row's ref** (not the helper's name) for `<ref>`. A single `variable` directive is a one-line block; markers go immediately above and immediately below it. If you have several adjacent `variable` lines that *all* flow into the wrapped statements, you may wrap them as a single contiguous block.

**Section / namespace boundary:** if the file opens a `section` and the `variable` lives at that section's scope, place the helper-marker pair around the `variable` *inside* the `section` (right where the directive sits), not around the `section` opener.

**Do NOT wrap with `--- helper` markers** declarations or `variable` directives that exist purely for downstream proofs or for general infrastructure. The helper markers are reserved for "statement support" — anything the main `def` (or its auto-bound type quantifiers) would not type-check without. A `variable` whose binders never reach a wrapped statement (e.g. introduced only for a proof later in the file) should NOT be wrapped.

## Rules

- Stay close to the lecture notes — same names where reasonable, same notation, same structure.
- No `sorry` and no `True` placeholders.
- If the definition needs supporting structure (a helper `def`, an instance) that the LN takes for granted, include it.
- If the definition uses something from mathlib that fits exactly, build on it. If not, build your own and document why.
- Edit only files inside your subsection's folder under `leanification/`.
