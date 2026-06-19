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

## Helper predicates for substantive sub-concepts

Sometimes the rewritten canonical tex statement introduces a substantive sub-concept that doesn't have its own LN definition row — e.g., *"Let `<` be a total order of `J ∪ V`"* introduces "total order on `J ∪ V`" as a concept, used inline rather than as a separate LN def. When this happens, **introduce the sub-concept as a named helper predicate** in the Lean (with `--- start helper` markers) *before* writing the main def, then use the helper as a hypothesis (or as a conjunct / field) of the main def. Two reasons:

1. **Makes the sub-concept reusable.** Downstream rows that need "the LN's <sub-concept>" hypothesis can write `(h : G.IsXxx ...)` directly, rather than re-spelling the atomic conditions every time.
2. **Forces the hypothesis to be carried explicitly through downstream rows.** A later row that defines something *in terms of* this sub-concept will naturally take `(h : G.IsXxx ...)` as a hypothesis — the existence of the helper predicate is a constant reminder that the LN's premise must be enforced at the type level, not pushed to a use-site obligation.

Three signals that a sub-concept earns its own helper. **All three required**:

- **(a)** It is genuinely referenced by this row's spec (not invented for ergonomics or hypothetical futures).
- **(b)** It has *substantive content* — at least 2-3 atomic conditions, not a single typeclass or unary predicate.
- **(c)** It is likely to be referenced by a downstream row's hypothesis (so the helper becomes reusable, not a one-off).

Single-line predicates ("the set is non-empty", "the relation is decidable") do **not** earn their own helper — fold them into the main def's signature directly.

**Worked example** — `def_3_8` (IsTopologicalOrder) introduces "total order on `J ∪ V`" as a sub-concept. Three atomic conditions, referenced again by `def_3_9` (Predecessors). The right shape:

```lean
-- def_3_8 --- start helper
def IsTotalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  (∀ v ∈ G, ¬ lt v v) ∧
  (∀ u ∈ G, ∀ v ∈ G, ∀ w ∈ G, lt u v → lt v w → lt u w) ∧
  (∀ v ∈ G, ∀ w ∈ G, lt v w ∨ v = w ∨ lt w v)
-- def_3_8 --- end helper

-- def_3_8 -- start statement
def IsTopologicalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  G.IsTotalOrder lt ∧ (∀ v w, v ∈ G.Pa w → lt v w)
-- def_3_8 -- end statement
```

Now `def_3_9`'s `Pred` can naturally take `(h : G.IsTotalOrder lt)` as a hypothesis, and the LN's "let `<` be a total order" survives all the way into the Lean's type contract. **Without the helper**, the next formalizer is tempted to drop the LN's hypothesis with a "constraint at use-site" rationale — which `verify_equivalence` (item 1a) will now FAIL, and `verify_equivalence_strict` will mark CONTENT.

Helpers carry their own `## Design choice` comment block — same treatment as a main declaration.

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
7. **No proofs inside the wrapped definition.** See **Constructor-proof obligations live outside the def** below. The main wrapped declaration must be data-shaped — no `by ...` tactic blocks inside a `where`-clause / structure literal / `{ ... }` record-update body.
8. **Check it builds**: `lake build` from `/home/11716061/repo_scaffold2/`. Fix any errors.
9. **Report back** to the manager: every Lean file path you wrote to, each declaration name, which sibling defs / predicates you reused, and any decisions that may affect later claims that depend on this definition.

## Constructor-proof obligations live outside the def

When the row's definition constructs an instance of a `structure` (a common case in this project — every CDMG-operator row produces `CDMG Node where { J := ..., V := ..., hJV_disj := ..., E := ..., hE_subset := ..., L := ..., hL_subset := ..., hL_irrefl := ..., hL_symm := ... }`), the structure's *proof-shaped fields* (the `h*` invariants — disjointness, subset, irreflexivity, symmetry, etc.) **must NOT** be written as inline `by ...` tactic blocks inside the structure literal.

Each proof obligation gets its own **private lemma** declared *above* the def; the def then references each lemma by name. Concrete shape:

```lean
private lemma <opName>_<obligation>
    (G : CDMG Node) (W : Finset Node) (hW : W ⊆ G.J ∪ G.V) :
    <statement of the obligation> := by
  <tactic proof>

-- (one private lemma per proof obligation: hJV_disj, hE_subset, hL_subset, hL_irrefl, hL_symm, …)

-- <ref> -- start statement
def <opName> (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V) : CDMG Node where
  J := G.J ∪ W
  V := G.V \ W
  hJV_disj := <opName>_hJV_disj G W hW
  E := G.E.filter (fun e => e.2 ∉ W)
  hE_subset := <opName>_hE_subset G W hW
  L := G.L.filter (fun e => e.1 ∉ W ∧ e.2 ∉ W)
  hL_subset := <opName>_hL_subset G W hW
  hL_irrefl := <opName>_hL_irrefl G W hW
  hL_symm := <opName>_hL_symm G W hW
-- <ref> -- end statement
```

**Concrete check**: the wrapped def's body should contain only *data* (`field := <expression>` where the expression is data, not a proof) and *lemma-name references* (`field := <lemma_name> <args>` where the lemma was declared above). There should be **zero** `by` tokens between the `start statement` and `end statement` markers.

**Why**: the website renders the marker-wrapped def as the row's "what is this operator?" surface. A reader needs to see what data the operator produces — they don't need to wade through `refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩` tactic proofs of well-formedness. The lemmas above the def carry the proof obligations; the def itself reads as the mathematical definition of the operator.

**The lifted obligation lemmas do NOT get helper markers.** They're proof-supporting infrastructure for the def's well-typedness — they belong to the proof side, not the statement side. See "Marker conventions" below for the helper-marker scope rule.

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

**For record-literal `def`s using `where { fields }`** (the CDMG-operator shape — `def <opName> (...) : CDMG Node where  J := ...  V := ...  ...  hL_irrefl := ...`), the entire `where` block is part of the declaration — it *is* the definition. The end marker MUST sit AFTER the last field of the `where` block, NOT after the type annotation. Common mistake: placing `-- <ref> -- end statement` right after `: CDMG Node` (which terminates the type annotation) but BEFORE the `where` keyword. That leaves the website extractor showing only the signature with no fields, which renders the definition as opaque to a reader. Correct placement: see the worked example at the top of this prompt (`def <opName> ... : CDMG Node where  ... hL_symm := <opName>_hL_symm G W hW` followed immediately by `-- <ref> -- end statement`).

**Helper-for-statement markers** (THREE dashes, distinct from the start/end markers) — wrap exactly the declarations the **main statement's signature can't type-check without**. The website builder pulls these out alongside the main statement so the rendered statement surface is self-contained.

**Litmus test for when to wrap**: would removing this declaration cause the main-statement-marker-wrapped signature to fail to compile? If yes → wrap as a helper. If no → leave it unwrapped.

Concrete categories that pass the litmus test and DO get helper markers:

- `variable {α : Type*} [DecidableEq α]` directives whose binders auto-bind into the wrapped statements via Lean 4's auto-binding — without them the wrapped signature has free type variables.
- A small `def` of a relation or operator the wrapped def uses inside its own signature or body — e.g. `def IsTotalOrder` declared before `def IsTopologicalOrder` that uses it.
- An `instance` the wrapped type needs to reduce / decide membership.
- A `structure` the wrapped def takes as a parameter.

Concrete categories that DO NOT pass the litmus test and get NO markers (they're proof-supporting infrastructure, invisible to the website):

- Smart-constructor `def`s used only inside tactic blocks downstream (e.g. `def mkSomething := ...`).
- Lifted obligation proofs from "Constructor-proof obligations live outside the def" above (e.g. `private lemma hardInterventionOn_hJV_disj`).
- Walk-algebra / set-algebra / general-utility lemmas used only inside `:= by ...` proof bodies of downstream rows.
- Any `private lemma` whose only consumers are proof bodies.

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

**Helper signature only, no proof body** — when a helper-marker-wrapped declaration is a `lemma` (has a `:= by ...` proof body), the end marker sits *immediately after the type annotation* and the `:= by ...` proof body sits *below* the end marker — exactly like the main-statement marker convention:

```lean
-- <ref> --- start helper
lemma <name> (...) : <type>
-- <ref> --- end helper
:= by
  <proof tactics>
```

For a helper `def` with `:= <expr>` (no `by`, no proof — just data), the markers wrap the whole declaration (start above, end below the last line of the body). For a helper `variable` line, no proof exists, markers wrap the single line. The rule: anywhere there's a `:= by ...` tactic block, it lives *outside* the helper markers.

**Negative case (won't pass review)**: wrapping a `private lemma` whose only purpose is to discharge a proof obligation inside a downstream `:= by ...`. Such lemmas are proof helpers — they get no markers and stay invisible to the website builder. Examples include lifted constructor-proof obligations (per "Constructor-proof obligations live outside the def" above), smart-constructor smart-`def`s used only in tactic proofs, and structural lemmas like `Walk.comp_assoc`.

## Rules

- Stay close to the lecture notes — same names where reasonable, same notation, same structure.
- No `sorry` and no `True` placeholders.
- If the definition needs supporting structure (a helper `def`, an instance) that the LN takes for granted, include it.
- If the definition uses something from mathlib that fits exactly, build on it. If not, build your own and document why.
- Edit only files inside your subsection's folder under `leanification/`.
