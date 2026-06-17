# Workspace for def_3_7 — CDMGTypes (REFACTOR row, DEPENDENT)

## Refactor briefing

- **Refactor:** `cdmg_typed_edges`
- **Role:** DEPENDENT (roots: `def_3_1`, `def_3_4`)
- **Upstream shifts that affect this row:**
  - `CDMG Node` → `refactor_CDMG Node` (root `def_3_1`)
  - `G.IsAcyclic` → `G.refactor_IsAcyclic` (root `def_3_6`, ported in `Acyclicity.lean`'s `namespace refactor_CDMG`)
  - `G.J = ∅` is unchanged (`J : Finset Node` in both shapes).
  - `G.L = ∅` is unchanged at the spelling level — `L`'s type
    became `Finset (Sym2 Node)` instead of `Finset (Node × Node)`,
    but `∅` is the empty `Finset` of whatever type, so `G.L = ∅`
    reads identically.

The LN block is unchanged (def refactors have no tex twin).
Wording-check returned `NO_SUBTLETIES`. No `addition_to_the_LN`.

## File-shape pattern (model on `Acyclicity.lean`)

```
namespace CDMG
  -- existing helper variable (unchanged)
  -- existing 7 comment blocks + IsXXX defs, EACH wrapped with
  -- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsXXX / END
end CDMG

namespace refactor_CDMG
  -- helper variable (copy of the original)
  -- 7 REPLACEMENT blocks, each:
  --   REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsXXX (was: refactor_IsXXX)
  --   ref/LN-tex/design-choice comments
  --   -- def_3_7 -- start statement
  --   def refactor_IsXXX (G : refactor_CDMG Node) : Prop := ...
  --   -- def_3_7 -- end statement
  --   REFACTOR-BLOCK-REPLACEMENT-END: IsXXX
end refactor_CDMG
```

## Port table (mechanical mapping)

| Original                                              | Replacement                                                                  |
|-------------------------------------------------------|-------------------------------------------------------------------------------|
| `IsCADMG (G : CDMG Node) := G.IsAcyclic`              | `refactor_IsCADMG (G : refactor_CDMG Node) := G.refactor_IsAcyclic`           |
| `IsDMG (G : CDMG Node) := G.J = ∅`                    | `refactor_IsDMG (G : refactor_CDMG Node) := G.J = ∅`                          |
| `IsADMG (G : CDMG Node) := G.IsAcyclic ∧ G.J = ∅`     | `refactor_IsADMG (G : refactor_CDMG Node) := G.refactor_IsAcyclic ∧ G.J = ∅`  |
| `IsCDG (G : CDMG Node) := G.L = ∅`                    | `refactor_IsCDG (G : refactor_CDMG Node) := G.L = ∅`                          |
| `IsDG (G : CDMG Node) := G.J = ∅ ∧ G.L = ∅`           | `refactor_IsDG (G : refactor_CDMG Node) := G.J = ∅ ∧ G.L = ∅`                 |
| `IsCDAG (G : CDMG Node) := G.IsAcyclic ∧ G.L = ∅`     | `refactor_IsCDAG (G : refactor_CDMG Node) := G.refactor_IsAcyclic ∧ G.L = ∅`  |
| `IsDAG (G : CDMG Node) := G.IsAcyclic ∧ G.J = ∅ ∧ G.L = ∅` | `refactor_IsDAG (G : refactor_CDMG Node) := G.refactor_IsAcyclic ∧ G.J = ∅ ∧ G.L = ∅` |

The 4 / 7 / 7 predicates that mention `G.IsAcyclic` get the upstream
shift; the 3 / 7 that don't (`IsDMG`, `IsCDG`, `IsDG`) port with only the
type-annotation change (`CDMG Node` → `refactor_CDMG Node`).

## Action plan

1. `spawn_agent_sub_task` (formalize_definition_in_lean) — produce the
   refactor twin in-file following the Acyclicity.lean structural model.
2. `review_design` on the replacement (in refactor mode — design unchanged
   from the original, but the design-choice block should explicitly state
   that and list the upstream-type shifts).
3. `verify_equivalence` on the replacement vs the LN block.
4. `add_design_choice_comments` — write the *why* (port + unchanged design)
   into each REPLACEMENT block.
5. `solved` → verify_row_solved + sorry-check + strict-equivalence gate.

## Notes

- Same-file marker convention; no tex changes; no new helper files.
- `lake build` must stay green throughout (the existing `IsXXX` defs
  remain consumed by downstream rows like `CDMGRestrictions.lean`,
  `AcyclicIffTopologicalOrder.lean`, etc.).
