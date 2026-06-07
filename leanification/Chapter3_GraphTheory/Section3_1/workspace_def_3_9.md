# Workspace for def_3_9 — Predecessors (REFACTOR ROOT)

## Refactor context

- Refactor: `total_order_helper` (roots: `def_3_8`, `def_3_9`).
- Sibling root `def_3_8` (TopologicalOrder.lean) is **already solved** in this
  refactor table: it introduces `refactor_IsTotalOrder` as a named helper
  predicate (wrapped in REPLACEMENT markers; uses `--- helper` triple-dash
  markers) and `refactor_IsTopologicalOrder := G.refactor_IsTotalOrder lt ∧
  (∀ v w, v ∈ G.Pa w → lt v w)`. See `TopologicalOrder.lean` for the precedent.
- Plan markdown: `leanification/refactors/refactor_total_order_helper.md`.
- Why: `verify_equivalence` item 1a / `verify_equivalence_strict` "loosening a
  quantifier's domain" — pre-refactor `Pred G lt v` is well-typed for *any*
  binary relation `lt`, but the LN's `Pred^G_<(v)` is only well-defined when
  `<` is a total order on `J ∪ V`. The fix: add `(h : G.IsTotalOrder lt)` as
  an explicit type-level hypothesis between `lt` and `v` (per plan §"`def_3_9`
  (Predecessors.lean)").

## Consumer scope (transitive)

Grepped for `\.Pred\b\|\.PredLE\b` across `leanification/`:
- `Predecessors.lean` itself (`PredLE` calls `Pred`) — internal.
- `TopologicalOrder.lean` — only in *doc comments* (mentions `Predecessors.lean`
  as a downstream consumer); no live call.
- Chapter aggregator + archive — non-substantive.

Per plan §"Affected rows": no §3.1 row outside this refactor table consumes
`Pred` / `PredLE`. The refactor table already includes `claim_3_2` as a
DEPENDENT, but that's because of `def_3_8`'s shape change, not `def_3_9`.

So: the refactor is purely a Lean shape change inside `Predecessors.lean`.
No tex twin (def refactors don't get a tex twin — the LN `\begin{Def}` block
doesn't change, only the Lean encoding).

## Target shape for the replacement

```lean
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Pred (was: refactor_Pred)
-- ## Design choice -- documents the new (h : refactor_IsTotalOrder lt) hyp
-- def_3_9 -- start statement
def refactor_Pred (G : CDMG Node) (lt : Node → Node → Prop)
    (h : G.refactor_IsTotalOrder lt) (v : Node) : Set Node :=
  {w | w ∈ G ∧ lt w v}
-- def_3_9 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: Pred

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: PredLE (was: refactor_PredLE)
-- ## Design choice
-- def_3_9 -- start statement
def refactor_PredLE (G : CDMG Node) (lt : Node → Node → Prop)
    (h : G.refactor_IsTotalOrder lt) (v : Node) : Set Node :=
  G.refactor_Pred lt h v ∪ {v}
-- def_3_9 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: PredLE
```

Key notes:
- The helper name in REPLACEMENT must be `refactor_IsTotalOrder` (matches the
  prefixed name def_3_8's REPLACEMENT block introduced). The cleanup script
  globally renames `refactor_*` → unprefixed at finalize.
- `h` is *not used* in the body — intentional. It enforces the LN's premise at
  the type level. The strict checker then sees the hypothesis on the signature
  rather than hidden in design comments.
- The `variable {Node : Type*} [DecidableEq Node]` line stays outside both
  REFACTOR blocks (shared between original and replacement), as in
  `TopologicalOrder.lean`.

## Plan (manager actions)

1. `spawn_agent_sub_task` → `formalize_definition_in_lean.md` with refactor
   briefing: wrap existing `Pred` / `PredLE` in ORIGINAL markers, write
   `refactor_Pred` / `refactor_PredLE` in REPLACEMENT markers with the
   explicit `(h : G.refactor_IsTotalOrder lt)` hypothesis. Update the file
   docstring with a `## Refactor` section (mirroring TopologicalOrder.lean).
2. `review_design` — check the new shape is natural in full LN context.
3. `verify_equivalence` — focused statement-vs-(LN + addition) check.
4. `verify_equivalence_strict` — adversarial check; specifically verify the
   loosened-quantifier-domain leak is closed.
5. `add_design_choice_comments` — make the *why* explicit (signal a/b/c judgment).
6. `solved` → `verify_row_solved` + hard sorry-check + strict-equivalence gate.

## What has been tried

- **Turn 1 (formalize_definition_in_lean)**: REPLACEMENT blocks for
  `refactor_Pred` and `refactor_PredLE` written into
  `Predecessors.lean`. Both signatures take
  `(h : G.refactor_IsTotalOrder lt)` between `lt` and `v`; bodies
  are textually identical to the originals (`{w | w ∈ G ∧ lt w v}`
  and `Pred lt v ∪ {v}`). The strict-form binder is `_h` (unused
  in body); the non-strict binder is `h` (forwarded into
  `refactor_Pred`). Extensive design comments in place (carry-over
  rationales (a)-(d), refactor-coexistence note, downstream
  consumer survey). File docstring extended with `## Refactor
  total_order_helper (in progress)` section mirroring
  `TopologicalOrder.lean`. Import `Chapter3_GraphTheory.Section3_1
  .TopologicalOrder` added (no cycle).
- **Turn 2 (review_design)**: reviewer dispatched downstream-usage
  scan sub-agents. Finding: every LN `\Pred` call site (CBN
  factorisation, do-calculus, σ/d-sep, iSCMs, ID algorithm in
  id-algorithm.tex §lines 228/248/284/348/466) opens with "Let
  `<` be a topological order" — but def_3_9's own LN block
  specifies "a total order of J ∪ V" (literal). Reviewer was
  weighing both and converging on the LN-faithful answer (use
  IsTotalOrder, the weaker helper, matching def_3_9's own
  premise; the design comment for the strict block preemptively
  defends this choice via the ID-algorithm "preceding Markov
  blanket" slice, which uses total-order content only, not
  topological-order). Standard checklist started: "1. Lean shape
  natural? Yes. `def : Set Node` matches `def_3_5`'s family-set
  convention…"; the rest of the verdict was truncated by the
  orchestrator. Treat as effectively PASS based on the visible
  reasoning chain.
