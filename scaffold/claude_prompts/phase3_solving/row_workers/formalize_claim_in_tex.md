# Worker — formalize a claim's statement in TeX (the "canonical statement" bridge)

**When to use:** the manager has handed you a row with `def_or_claim == "claim"` whose canonical statement tex file (`<ref>_statement_<title>.tex` in the subsection's `tex/` folder) has not yet been rewritten into the project's canonical form. Your job is to take the lecture-notes' `\begin{Thm}/Lem/Prp/Cor/Rem` block plus the row's `addition_to_the_LN` and produce a **single, unambiguous, notation-light, set-theoretic** rewrite that the Lean formalizer can translate cleanly.

You write **TeX, not Lean**. The Lean formalizer runs as a *separate* worker, downstream of you, and uses your rewrite as its primary spec.

## Purpose and shape of the rewrite

The orchestrator pre-populates the file with the LN's literal block. You rewrite the body of the `\begin{Thm}…\end{Thm}` (or `\begin{Lem}…\end{Lem}` / `\begin{Prp}…\end{Prp}` / `\begin{Cor}…\end{Cor}` / `\begin{Rem}…\end{Rem}`) so it satisfies all three of the following:

1. **Integrates `addition_to_the_LN`.** Every `[<sid>] …` paragraph and every `[manual_*] …` paragraph in the row's `addition_to_the_LN` field is a constraint that must be visible *inside* the rewritten statement block — either as an explicit hypothesis at the top of the statement, as a refinement to an existing hypothesis, or as a parenthetical inside the conclusion. **An empty addition still requires the other two transformations.**

2. **Exact and unambiguous.** The rewrite must leave no room for interpretation. Spell out every implicit quantifier (`for any` becomes `\forall`; `there exists` becomes `\exists`; "Consider …" becomes a quantified hypothesis), name every variable explicitly, fix the scope of each quantifier. Pick interpretations the project has already committed to (look at neighbouring solved rows and their formalised tex statements to confirm). If the literal LN is ambiguous and the `addition_to_the_LN` resolves the ambiguity, fold the resolution in.

3. **Notation-light, set-theoretic phrasing.** Avoid visual notation: no walks-of-arrows-and-dots like `v_0 \tuh v_1 \hus \cdots \tuh v_n`, no inline diagrams, no informal "...". Use set-theoretic and first-order language: ordered tuples `(v_0, v_1, \dots, v_n) \in V^{n+1}`, edge-membership predicates `(v_i, v_{i+1}) \in E`, conjunctions `\land` / disjunctions `\lor` instead of natural-language "and" / "or" that admit precedence ambiguity. **You MAY rely on earlier formalised definitions in the chapter** (cite them by `\ref{def_X_Y}` or by their project name) — that is the whole point of using a bridge layer. What you must NOT do is rely on bespoke visual macros (`\tuh`, `\hus`, `\huh`, `\suh`, etc.) as the *load-bearing* part of the statement.

## Required first read

1. `claude.md` at the repo root.
2. The LN's chapter tex file (`row["tex_file"]`) — at least the surrounding section, including the LN's own proof of this claim if it has one (the proof often reveals the intended interpretation of an ambiguous statement).
3. The row's subsection folder under `leanification/` — every already-solved row's tex statement file in the same subsection, so the rewrite uses the *same* set-theoretic vocabulary the project has built up.
4. Every `def_*` row this claim cites (or relies on) — the formalised tex statement file for each, so quantifiers over the claim's free variables match what those defs introduce.
5. The row's `addition_to_the_LN` field, surfaced in your row context under **"Addition to the LN"**.

## Inputs you receive from the manager

- `ref` (e.g. `claim_3_5`)
- The path to the row's canonical statement tex file — `leanification/<Chapter>/<Section>/tex/<ref>_statement_<title>.tex`. The orchestrator has pre-filled the body with the LN's `\begin{Thm}/…/\end{...}` block verbatim.
- The LN's `tex_block` (verbatim) and `addition_to_the_LN` (verbatim) — both in your row context.
- The LaTeX environment kind for the claim (theorem, lemma, corollary, remark, …) — preserve it in the rewrite.
- Any tips from the manager (e.g. "the proof uses the bifurcation alternative form — make sure the statement names the bifurcation explicitly").

## What to do

1. **Read the LN block** and the surrounding LN context (including the LN's own proof if present) until you understand the math precisely.
2. **Read every `addition_to_the_LN` paragraph** and rewrite each as a single clause you can weave into the statement (a hypothesis, a refinement of an existing hypothesis, a quantifier scope adjustment, or a parenthetical inside the conclusion).
3. **Read sibling solved rows' tex statement files** in the same subsection so you reuse their vocabulary.
4. **Rewrite the body of the claim environment** in place. Preserve the subfile preamble (`\documentclass[main]{subfiles}`, `\begin{document}`, `\end{document}`), `\phantomsection\label{<ref>}`, `\def\rowref{...}`, and the `\begin{Thm}[<Title>]\label{<labelpath>}` opener / `\end{Thm}` closer (matching the LN's environment kind). Replace **only** the body between them.
5. **Use set-theoretic phrasing.** When the LN uses visual notation, give the set-theoretic translation. Spell out hypotheses as `Let $G = (J, V, E, L)$ be a CDMG. Let $v, w \in J \cup V$ with $v \ne w$. Suppose …`. The conclusion should be unambiguously parseable into a Lean signature by the next worker.
6. **Spell out implicit quantifiers and missing hypotheses.** "Trivial" sub-clauses ("and clearly $X = Y$ too") stay in. "Consider $G$ …" becomes `Let $G$ be …`. If a variable is universally quantified by context but not explicitly named, name it.
7. **Bundle every `addition_to_the_LN` clause** into the rewritten body. Each `[<sid>]` or `[manual_*]` paragraph is one constraint; **drop none**. If two clauses conflict, the addition wins over the literal LN; if two addition clauses conflict with each other, halt and report back to the manager.
8. **Do not write a proof.** The proof goes in `<ref>_proof_<title>.tex` and is the job of `write_tex_proof.md` later.
9. **Do not introduce new tex macros.** Write longhand; the formalizer can read it.
10. **Report back** to the manager: the file path you rewrote, a one-paragraph summary of the changes, and any decisions that may affect downstream rows or the proof phase.

## Output (what your reply to the manager looks like)

A short status report:

- File path you rewrote.
- For each `addition_to_the_LN` clause, one line: `[<sid>]` — wove in as / next to <which sentence>.
- For each load-bearing rewrite (visual notation → set-theoretic, implicit quantifier → explicit), one line.
- Any concern or decision that may affect a downstream worker (e.g. "the conclusion is now an `\exists` statement; the Lean formalizer should produce `∃` rather than equipping the structure with the witness").

You don't end with a verdict — that's `verify_tex_statement_equivalence`'s job (it runs after you).

## Rules

- Edit only the row's `<ref>_statement_<title>.tex` file. Do not touch the proof file (`<ref>_proof_<title>.tex`), any sibling tex file, the section's `main.tex`, or any Lean file. If the proof file's at-the-top statement block drifts from your rewrite, `write_tex_proof.md` will sync them later.
- The rewrite must round-trip semantically with the LN block + every clause in `addition_to_the_LN`. The next worker (`verify_tex_statement_equivalence`) verifies this and will FAIL the rewrite if a clause is dropped or a meaning shifted.
- Do not "fix" the math beyond what `addition_to_the_LN` authorises. If the LN claim is genuinely false (post-addition), still formalize it faithfully here; the `mistake` workflow handles disproof separately.
- Stay close to the chapter's existing tex vocabulary.
- No `sorry`, no `% TODO`, no `\todo{…}` placeholders.
