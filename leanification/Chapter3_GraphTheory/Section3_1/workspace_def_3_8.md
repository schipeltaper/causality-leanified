# Workspace for def_3_8 — TopologicalOrder (refactor `total_order_helper`, ROOT)

## Goal of this refactor row

Original `IsTopologicalOrder` is a flat 4-way `∧`. Refactor extracts the
strict-total-order conjuncts (irreflexive, transitive, trichotomous on
`J ∪ V`) into a named helper predicate `IsTotalOrder`, and reshapes
`IsTopologicalOrder := IsTotalOrder ∧ parent_precedes`. The two shapes
are logically equivalent (same three atomic conditions unfold in same
order); destructure pattern flips from `⟨_, _, _, _⟩` to `⟨⟨_, _, _⟩, _⟩`.
`IsTotalOrder` exposure lets `def_3_9` (refactor's second root) take
`(h : G.IsTotalOrder lt)` as type-level hypothesis on `Pred` / `PredLE`,
closing the loosened-domain leak.

## Progress

### Turn 1 — spawn_agent_sub_task → formalize_definition_in_lean
Wrote three blocks in `TopologicalOrder.lean`:
1. `REFACTOR-BLOCK-ORIGINAL-BEGIN/END: IsTopologicalOrder` wrapping the
   original flat 4-conjunct (unchanged).
2. `REFACTOR-BLOCK-REPLACEMENT-BEGIN/END: IsTotalOrder` (net-new helper,
   declared as `refactor_IsTotalOrder`, three-dash helper markers
   `-- def_3_8 --- start helper`).
3. `REFACTOR-BLOCK-REPLACEMENT-BEGIN/END: IsTopologicalOrder` (declared
   as `refactor_IsTopologicalOrder`, two-dash statement markers
   `-- def_3_8 -- start statement`). Body
   `G.refactor_IsTotalOrder lt ∧ (∀ v w, v ∈ G.Pa w → lt v w)`.
Design-choice comments already written by the formalizer.

### Turn 2 — review_design → PASS
Reviewer confirmed `IsTotalOrder ∧ parent_precedes` mirrors the LN's
two-tier reading literally and supports the downstream consumer story
(`def_3_9.Pred` taking `(h : G.IsTotalOrder lt)`).

### Next steps (planned order)
- **Turn 3:** `verify_equivalence` (friendly: replacement vs LN block).
- `verify_equivalence_strict` (+ examples if requested; this row
  introduces a new helper predicate `IsTotalOrder`, so the strict
  checker is worth invoking voluntarily before solved).
- design-choice comments are already written by the formalizer — verify
  they capture the *why* of the refactor before `solved`; if thin,
  dispatch `add_design_choice_comments`.
- `solved` → orchestrator runs verify_row_solved + sorry check + strict
  gate on `refactor_IsTopologicalOrder`.
