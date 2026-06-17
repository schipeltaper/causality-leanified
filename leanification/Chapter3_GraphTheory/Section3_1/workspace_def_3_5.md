# Workspace for def_3_5 — FamilyRelationships

## Plan

This is a DEPENDENT refactor row. The existing file
`FamilyRelationships.lean` defines 14 declarations:

1. `Pa` (per-vertex), `PaSet` (set form)
2. `Ch`, `ChSet`
3. `Sib` (per-vertex only — LN has no `SibSet`)
4. `Anc`, `AncSet`
5. `Desc`, `DescSet`
6. `NonDesc` (set form only)
7. `Sc`, `ScSet`
8. `Dist`, `DistSet`

Plus the `variable {Node : Type*} [DecidableEq Node]` helper.

**Mechanical substitutions for the refactor port** (per the
BEFORE/AFTER blocks in the row briefing):

- `CDMG Node` → `refactor_CDMG Node` (root `def_3_1`)
- `Walk G u v` → `refactor_Walk G u v` (root `def_3_4`)
- `p.IsDirectedWalk` → `p.refactor_IsDirectedWalk`
- `p.IsBidirectedWalk` → `p.refactor_IsBidirectedWalk`
- For `Sib`: `(v, w) ∈ G.L` → `s(v, w) ∈ G.L`
  (L now `Finset (Sym2 Node)`)
- Cross-references inside the file: `G.Pa v` → `G.refactor_Pa v`,
  `G.Anc v` → `G.refactor_Anc v`, `G.Desc v` → `G.refactor_Desc v`,
  `G.DescSet A` → `G.refactor_DescSet A`, etc.
- The CDMGNotation membership instance `w ∈ G` works
  unchanged for `refactor_CDMG` (via `refactor_instMembership`),
  so the `w ∈ G` guard reads the same.
- `G.J`, `G.V`, `G.E`, `G.J ∪ G.V` all unchanged (only `G.L`'s
  carrier changed).

**File structure to add.** The existing file ends with
`end CDMG` then `end Causality`. Append a new
`namespace Causality / namespace refactor_CDMG / ... /
end refactor_CDMG / end Causality` block holding all 14
refactor declarations, mirroring the Walks.lean and
CDMGNotation.lean layout.

**Marker layout.** Each of the 14 originals stays where it
is, wrapped with `-- REFACTOR-BLOCK-ORIGINAL-BEGIN/END: <Name>`.
Each refactor twin sits in the new namespace, wrapped with
`-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: <Name> (was:
refactor_<Name>)` / `-- REFACTOR-BLOCK-REPLACEMENT-END: <Name>`.
Statement markers (`-- def_3_5 -- start/end statement`) stay
attached to each declaration, on both the original and the
twin, to keep the website-extraction markers consistent.

## What's been tried

(nothing yet — first turn)

## Next step

Dispatch porting worker via `spawn_agent_sub_task`. After it
finishes: structural sanity check, then `review_design` +
`verify_equivalence` on the new Lean.
