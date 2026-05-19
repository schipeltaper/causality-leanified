# Workspace for def_3_6 — Acyclicity

## LN block

> A CDMG `G=(J,V,E,L)` is called *acyclic* if there does not exist any
> non-trivial directed walk from `v` to itself in `G` for any node `v ∈ G`.

## Plan

1. **Formalize** — `formalize_definition_in_lean` worker creates a new file
   `Acyclicity.lean` under `Section3_1/`, defining `Causality.CDMG.IsAcyclic`
   (or `Causality.IsAcyclic`) as a `Prop`-valued predicate on `CDMG α`.
2. **Review design** — `review_design` verifier (full-LN context: chapters
   4-16 will reference acyclicity through CBNs, do-calculus, SCMs,
   discovery algorithms).
3. **Verify equivalence** — `verify_equivalence` against the LN block.
4. **Solved** — `verify_row_solved` final gate.

## Shape sketch (formalizer chooses final form)

```lean
def IsAcyclic (G : CDMG α) : Prop :=
  ∀ v ∈ (G.J ∪ G.V),
    ¬ ∃ π : Walk G v v, π.IsDirected ∧ 1 ≤ π.length
```

Pieces already available:
- `Causality.CDMG` (def 3.1, `CDMG.lean`)
- `Causality.Walk` (def 3.4 item 1, `Walks.lean`)
- `Causality.Walk.length` (`Walks.lean`)
- `Causality.Walk.IsDirected` (def 3.4 item 2, `WalkPredicates.lean`)

Notes:
- "non-trivial" = length ≥ 1 (i.e. not the trivial `nil v` walk). The
  comment at `Walks.lean:294` already commits the project to this reading.
- "node v ∈ G" = `v ∈ G.J ∪ G.V` (any input or output node).
- The `nil v` walk has `IsDirected = True` but `length = 0`, so the
  `length ≥ 1` conjunct is exactly what excludes it.

## What the worker should produce

- New file `leanification/Chapter3_GraphTheory/Section3_1/Acyclicity.lean`.
- A `Causality`-namespaced predicate. Decide on either `CDMG.IsAcyclic G`
  (dot-projection from a CDMG) or top-level `IsAcyclic G`; check what reads
  most naturally with how downstream LN uses this (e.g. "$G$ is acyclic").
- Comment block with the verbatim LN block, ref tag `def_3_6`, title
  "Acyclicity", and design-choice discussion.
- Add the new file to `leanification/Chapter3_GraphTheory.lean`
  aggregator if the scaffold has not done so automatically.
- `lake build` clean from the repo root.

## History

- **Turn 1 — formalize (DONE).** Worker (`spawn_agent_sub_task` id=794315d7)
  created `Acyclicity.lean` with `Causality.CDMG.IsAcyclic`:
  ```lean
  def IsAcyclic (G : CDMG α) : Prop :=
    ∀ v ∈ G, ¬ ∃ π : Walk G v v, π.IsDirected ∧ 1 ≤ π.length
  ```
  Picked `v ∈ G` (uses the `Membership` instance from def_3_2, so unfolds
  to `v ∈ G.J ∪ G.V`), inline conjunction, `Prop`-valued, dot-projection
  via `CDMG` namespace, no helper / no simp char lemma. Aggregator
  `Chapter3_GraphTheory.lean` updated. `lake build` reported clean by
  worker.
- **Turn 2 — review_design (dispatching now).** Full-LN context check
  that `Causality.CDMG.IsAcyclic` is the natural shape — does it compose
  cleanly with def_3_7 (graph types), claim_3_2 (topological order),
  claim_3_8 (hard-intervention preservation), and the chapter-4-16
  downstream uses?
