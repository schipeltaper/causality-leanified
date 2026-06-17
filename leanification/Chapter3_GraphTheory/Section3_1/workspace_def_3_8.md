# Workspace for def_3_8 — TopologicalOrder (REFACTOR row, DEPENDENT)

## Refactor briefing

- **Refactor:** `cdmg_typed_edges`
- **Role:** DEPENDENT (root: `def_3_1` — `CDMG`'s `L` field went
  `Finset (Node × Node) + hL_symm + hL_irrefl_pair`
  → `Finset (Sym2 Node) + hL_irrefl(¬ s.IsDiag)`; `hL_subset` re-stated
  via `Sym2.Mem`).
- **Upstream shifts that touch this row:**
  - `CDMG Node` → `refactor_CDMG Node` (def_3_1)
  - `v ∈ G` resolves via the `refactor_instMembership` instance on
    `refactor_CDMG Node` (def_3_2, in `CDMGNotation.lean`)
  - `G.Pa w` → `G.refactor_Pa w` (def_3_5, in
    `FamilyRelationships.lean`)
- **NOT touched by this row:**
  - `G.E`, `G.J`, `G.V` shapes are unchanged by the refactor.
  - The LN block is unchanged (def refactors have no tex twin).
  - The wording-check subtleties
    `equivalent_indexing_assumes_finite_node_set` and
    `quantifier_domain_v_w_in_G_is_tuple_not_set` were folded into
    the original canonical tex; both remain accurate.
  - `addition_to_the_LN` is empty.

## File-shape pattern (model on `Acyclicity.lean` / `CDMGTypes.lean`)

```
namespace CDMG
  -- existing helper variable (unchanged)
  -- existing IsTotalOrder def, wrapped REFACTOR-BLOCK-ORIGINAL: IsTotalOrder
  -- existing IsTopologicalOrder def, wrapped REFACTOR-BLOCK-ORIGINAL: IsTopologicalOrder
end CDMG

namespace refactor_CDMG
  -- helper variable (copy of original)
  -- REFACTOR-BLOCK-REPLACEMENT: IsTotalOrder (was: refactor_IsTotalOrder)
  --   def refactor_IsTotalOrder (G : refactor_CDMG Node) (lt) : Prop := ...
  --     (helper markers --- start/end helper)
  -- REFACTOR-BLOCK-REPLACEMENT: IsTopologicalOrder (was: refactor_IsTopologicalOrder)
  --   def refactor_IsTopologicalOrder (G : refactor_CDMG Node) (lt) : Prop := ...
  --     (statement markers -- start/end statement)
end refactor_CDMG
```

## Port table (mechanical mapping)

| Original                                            | Replacement                                                       |
|-----------------------------------------------------|-------------------------------------------------------------------|
| `def IsTotalOrder (G : CDMG Node) (lt) : Prop := (∀ v ∈ G, ¬ lt v v) ∧ ...` | `def refactor_IsTotalOrder (G : refactor_CDMG Node) (lt) : Prop := (∀ v ∈ G, ¬ lt v v) ∧ ...` |
| `def IsTopologicalOrder (G : CDMG Node) (lt) : Prop := G.IsTotalOrder lt ∧ (∀ v w, v ∈ G.Pa w → lt v w)` | `def refactor_IsTopologicalOrder (G : refactor_CDMG Node) (lt) : Prop := G.refactor_IsTotalOrder lt ∧ (∀ v w, v ∈ G.refactor_Pa w → lt v w)` |

The `∀ v ∈ G, …` quantifier ports verbatim because the Membership
instance on `refactor_CDMG Node` lives at `refactor_instMembership`
(`CDMGNotation.lean`).  The body of each conjunct (irreflexive,
transitive, trichotomous, parent-precedence) reads identically; only
the upstream type and the cross-call `G.IsTotalOrder` → `G.refactor_IsTotalOrder`
and `G.Pa` → `G.refactor_Pa` change.

## Marker shapes (preserve from original)

- `IsTotalOrder` is a **helper-for-statement** → three-dash
  `-- def_3_8 --- start/end helper` markers (inside the
  REFACTOR-BLOCK-REPLACEMENT).
- `IsTopologicalOrder` is the **statement** → two-dash
  `-- def_3_8 -- start/end statement` markers (inside the
  REFACTOR-BLOCK-REPLACEMENT).
- The `variable {Node : Type*} [DecidableEq Node]` in the
  `namespace refactor_CDMG` block also gets three-dash helper
  markers (matches the `namespace CDMG` block above).

## Action plan

1. `spawn_agent_sub_task` (formalize_definition_in_lean) — produce
   the refactor twin in-file following the `Acyclicity.lean` /
   `CDMGTypes.lean` structural model.
2. `review_design` on the replacement (refactor mode — design unchanged
   from the original; the design-choice block should explicitly state
   that and list upstream-type shifts).
3. `verify_equivalence` on the replacement vs the LN block.
4. `add_design_choice_comments` — confirm the *why* (port + unchanged
   design) is written into each REPLACEMENT block.
5. `solved` → `verify_row_solved` + sorry-check + strict-equivalence gate.

## Notes

- Same-file marker convention; no tex changes; no new helper files.
- `lake build` must stay green throughout (the existing `IsTotalOrder`
  and `IsTopologicalOrder` defs remain consumed by downstream rows
  like `AcyclicIffTopologicalOrder.lean` and `Predecessors.lean`).
