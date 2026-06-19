# Workspace for def_3_18 — ISigmaSeparation (refactor: cdmg_typed_edges)

## Context

This is the FINAL row of the `cdmg_typed_edges` refactor table. All other 36
rows are solved. This row is a DEPENDENT pulled in because root(s) `def_3_1`
(CDMG, with `L : Finset (Sym2 Node)`) and `def_3_4` (typed `WalkStep` /
`Walk`) changed underneath it.

## Plan

Mechanical port of the 5 declarations in `ISigmaSeparation.lean`. No tex change
(def refactors don't have tex twins). Mirror the pattern from `def_3_17`'s
refactor section (bottom of `SigmaBlockedWalks.lean`, lines 320–733).

### Step 1: Add ORIGINAL markers around each of the 5 existing declarations.

The 5 declarations (in file order):
1. `IsISigmaSeparated`              (lines 301–305)
2. `IsNotISigmaSeparated`           (lines 360–363)
3. `IsISigmaSeparatedEmpty`         (lines 424–426)
4. `IsSigmaSeparated`               (lines 518–521)
5. `IsNotSigmaSeparated`            (lines 565–568)

For each, add `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: <Name>` immediately above
the existing `-- def_3_18 -- start statement` line (i.e., above the
`set_option linter.unusedVariables false in` for #1, #4, #5; directly above
the start-statement marker for #2, #3) and `-- REFACTOR-BLOCK-ORIGINAL-END:
<Name>` immediately below the existing `-- def_3_18 -- end statement` line.

### Step 2: Add the refactor section at the bottom of the file.

Structure mirrors `SigmaBlockedWalks.lean`:

```
namespace Causality
namespace refactor_CDMG

-- def_3_18 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_18 --- end helper

-- [Design-choice block]
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsISigmaSeparated (was: refactor_IsISigmaSeparated)
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def refactor_IsISigmaSeparated (G : refactor_CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  ∀ {u v : Node} (π : refactor_Walk G u v),
      u ∈ A → v ∈ (G.J : Set Node) ∪ B → π.refactor_IsSigmaBlockedGiven C hC
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsISigmaSeparated

-- [...similar for the other 4 refactor versions]

end refactor_CDMG
end Causality
```

### Key upstream retargets in the bodies

- `CDMG Node` → `refactor_CDMG Node`
- `Walk G u v` → `refactor_Walk G u v`
- `π.IsSigmaBlockedGiven C` → `π.refactor_IsSigmaBlockedGiven C hC`
  (def_3_17's refactor added the `hC` arg — see SigmaBlockedWalks.lean
  line 720)
- `G.IsISigmaSeparated`/etc → `G.IsISigmaSeparated`-renamed-to-refactor_
- `G.J = ∅` carries through unchanged (J is still `Finset Node`)
- `Set.empty_subset _` and `(G.J : Set Node) ∪ B` carry through unchanged

### Validation after port

- `lake build` clean.
- `verify_equivalence` on the new section vs LN block + addition.
- `add_design_choice_comments` on the 5 refactor blocks.
- `solved` → strict-equivalence gate runs against LN block; if PASS, mark
  refactor row as solved (so cleanup can be invoked by the human).
