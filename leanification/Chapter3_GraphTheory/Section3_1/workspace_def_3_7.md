# Workspace for def_3_7 — GraphTypes

## What this row defines
Seven *names* the LN attaches to a CDMG `G = (J, V, E, L)` based on
combinations of three side conditions:

| name  | acyclic | J = ∅ | L = ∅ |
| ----- | ------- | ----- | ----- |
| CADMG | yes     |       |       |
| DMG   |         | yes   |       |
| ADMG  | yes     | yes   |       |
| CDG   |         |       | yes   |
| DG    |         | yes   | yes   |
| CDAG  | yes     |       | yes   |
| DAG   | yes     | yes   | yes   |

The CDMG itself (def_3_1) is the most general case (none required); these
seven are *names for special cases*.

## Foundation already in place
- `Causality.CDMG α` (def_3_1) in `CDMG.lean` — structure with fields
  `J`, `V`, `E`, `L`, plus disjointness / inclusion / symmetry side
  conditions.
- `Causality.CDMG.IsAcyclic` (def_3_6) in `Acyclicity.lean` —
  `Prop`-valued predicate on `CDMG α`.

So the seven graph-type names are pure predicate combinations of
`G.IsAcyclic`, `G.J = ∅`, `G.L = ∅`.

## Shape decision (for the worker)
Seven `Prop`-valued predicates inside the `Causality.CDMG` namespace, so
they read as `G.IsDAG`, `G.IsCADMG`, etc. — matching the LN's prose
"$G$ is a DAG", "if $G$ is a CADMG, then …". This composes cleanly with
the existing `G.IsAcyclic` already in place.

A subtype / structure form (e.g. `{G : CDMG α // G.IsAcyclic}`) is
worse: downstream lemmas in chapters 4–16 typically take an arbitrary
CDMG and add the acyclic-and-empty-J side condition as a *hypothesis*,
not as a different ambient type. Forcing every later signature through
a coercion would needlessly clutter things.

## File
New file: `leanification/Chapter3_GraphTheory/Section3_1/GraphTypes.lean`.
Imports `Acyclicity` (which transitively imports CDMG).

## Plan
1. `spawn_agent_sub_task` → `formalize_definition_in_lean.md`
2. `review_design` — full-LN-context check
3. `verify_equivalence` — focused statement-vs-LN check
4. `solved` → `verify_row_solved`
