# Worker — formalize a definition in TeX (the "canonical statement" bridge)

**When to use:** the manager has handed you a row with `def_or_claim == "def"` whose canonical statement tex file (`<ref>_<title>.tex` in the subsection's `tex/` folder) has not yet been rewritten into the project's canonical form. Your job is to take the lecture-notes' `\begin{Def}...\end{Def}` block plus the row's `addition_to_the_LN` and produce a **single, unambiguous, notation-light, set-theoretic** rewrite that the Lean formalizer can translate cleanly.

You write **TeX, not Lean**. The Lean formalizer runs as a *separate* worker, downstream of you, and uses your rewrite as its primary spec.

## Purpose and shape of the rewrite

The orchestrator pre-populates the file with the LN's literal block. You rewrite the body of the `\begin{Def}…\end{Def}` so it satisfies all three of the following:

1. **Integrates `addition_to_the_LN`.** Every `[<sid>] …` paragraph and every `[manual_*] …` paragraph in the row's `addition_to_the_LN` field is a constraint that must be visible *inside* the rewritten definition block — either as a hypothesis at the top, an explicit clause within an itemised list, or a parenthetical refinement of an existing sentence. **An empty addition still requires the other two transformations.**

2. **Exact and unambiguous.** The rewrite must leave no room for interpretation. Spell out implicit quantifiers, name every variable, fix the scope of every "for any" / "there exists". If the literal LN is ambiguous, pick the reading the project has committed to (look at neighbouring solved rows / previously-formalised defs in the chapter to confirm) and write the unambiguous form. The `addition_to_the_LN` is often itself the disambiguation — fold it in.

3. **Notation-light, set-theoretic phrasing.** Avoid visual notation: no walks-of-arrows-and-dots like `v_0 \tuh v_1 \hus \cdots \tuh v_n`, no inline diagrams, no informal "...". Use set-theoretic and first-order language: ordered tuples `(v_0, v_1, \dots, v_n) \in V^{n+1}`, edge-membership conditions `(v_i, v_{i+1}) \in E`, predicates like `(v_{i-1}, v_i) \in E \land (v_i, v_{i+1}) \in E` instead of `\tuh \cdots \tuh`. **You MAY rely on earlier formalised definitions in the chapter** (cite them by `\ref{def_X_Y}` or by the project's macros — that's the whole point of using a bridge layer). What you must NOT do is rely on bespoke visual macros (`\tuh`, `\hus`, `\huh`, `\suh`, etc.) as the *load-bearing* part of the definition.

## Required first read

1. `claude.md` at the repo root.
2. The LN's chapter tex file (`row["tex_file"]`) — at least the surrounding section, so you understand the notation the LN uses and which symbols are already defined elsewhere.
3. The row's subsection folder under `leanification/` — every already-solved row's tex statement file in the same subsection, so the rewrite uses the *same* set-theoretic vocabulary the project has built up.
4. The row's `addition_to_the_LN` field, surfaced in your row context under **"Addition to the LN"**.

## Inputs you receive from the manager

- `ref` (e.g. `def_3_4`)
- The path to the row's canonical statement tex file — `leanification/<Chapter>/<Section>/tex/<ref>_<title>.tex`. The orchestrator has pre-filled the body with the LN's `\begin{Def}…\end{Def}` block verbatim.
- The LN's `tex_block` (verbatim) and `addition_to_the_LN` (verbatim) — both in your row context.
- Any tips from the manager (e.g. "claim_3_5 will consume this — keep the form usable for an existence statement").

## What to do

1. **Read the LN block** and surrounding LN context until you understand the math precisely.
2. **Read every `addition_to_the_LN` paragraph** and rewrite each as a single clause you can weave into the definition (a hypothesis, an item in a numbered list, or a parenthetical refinement).
3. **Read sibling solved rows' tex statement files** in the same subsection so you reuse their vocabulary (e.g. if `def_3_2` already introduced ordered-tuple edge notation, use the same notation in `def_3_4`).
4. **Rewrite the body of the `\begin{Def}…\end{Def}` block** in place. Preserve the subfile preamble (`\documentclass[main]{subfiles}`, `\begin{document}`, `\end{document}`), `\phantomsection\label{<ref>}`, `\def\rowref{...}`, and the `\begin{Def}[<Title>]\label{<labelpath>}` opener / `\end{Def}` closer. Replace **only** the body between them.
5. **Use set-theoretic phrasing.** When you must reference an edge or a walk shape, write it as a membership statement. If the LN uses visual edge notation, give the set-theoretic translation either alongside (as a parenthetical "(equivalently: $(v, w) \in E$)") or replace it outright. If the chapter has already established a set-theoretic vocabulary in prior rows, reuse it.
6. **Bundle every addition_to_the_LN clause** into the rewritten body. Each `[<sid>]` or `[manual_*]` paragraph is one constraint; **drop none**. If two clauses conflict, the addition wins over the literal LN (this is by the project's policy); if two addition clauses conflict with each other, halt and report back to the manager — that's an upstream operator-table bug.
7. **Do not write a proof.** This is a *definition*. No proof block, no scratch math, no `\begin{proof}`. (Claim-version of this worker handles claim statements; even there, the statement file is statement-only.)
8. **Do not introduce new tex macros.** If you need notation the project doesn't already have, write it longhand instead — the formalizer can read longhand.
9. **Report back** to the manager: the file path you rewrote, a one-paragraph summary of the changes (which `[<sid>]` / `[manual_*]` clauses you wove in and where), and any decisions that may affect downstream rows.

## Output (what your reply to the manager looks like)

A short status report:

- File path you rewrote.
- For each `addition_to_the_LN` clause, one line: `[<sid>]` — wove in as / next to <which sentence>.
- For each load-bearing rewrite (visual notation → set-theoretic), one line.
- Any concern or decision that may affect a downstream row (e.g. "the rewritten bifurcation form drops the `\hut` chain notation; `claim_3_5` consumers should know").

You don't end with a verdict — that's `verify_tex_statement_equivalence`'s job (it runs after you).

## Rules

- Edit only the row's `<ref>_<title>.tex` file. Do not touch any sibling tex file, the section's `main.tex`, or any Lean file.
- The rewrite must round-trip semantically with the LN block + every clause in `addition_to_the_LN`. The next worker (`verify_tex_statement_equivalence`) verifies this and will FAIL the rewrite if a clause is dropped or a meaning shifted.
- Do not "fix" or "improve" the math beyond what `addition_to_the_LN` authorises. The rewrite is a *bridge*, not a refinement.
- Stay close to the chapter's existing tex vocabulary — the formalizer reads it; consistency makes its job easier.
- No `sorry`, no `% TODO`, no `\todo{…}` placeholders.
