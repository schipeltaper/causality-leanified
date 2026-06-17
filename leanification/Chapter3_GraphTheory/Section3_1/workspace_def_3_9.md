# Workspace for def_3_9 — Predecessors (REFACTOR cdmg_typed_edges)

## Refactor context

This is a DEPENDENT row in the `cdmg_typed_edges` refactor. Root: `def_3_1`
(CDMG's `L` field retyped from `Finset (Node × Node)` to `Finset (Sym2 Node)`).

This row's content (`Pred`, `PredLE`) does **NOT touch the `L` field at all** —
only `J ∪ V` via the `Membership` instance, and `IsTotalOrder` via `def_3_8`.
So the port is mechanical: only the upstream type names change.

## Upstream replacements available
(verified from `CDMGNotation.lean`, `TopologicalOrder.lean`):

* `CDMG Node` → `refactor_CDMG Node`
* `Membership Node (CDMG Node)` (instance `instMembership`) →
  `Membership Node (refactor_CDMG Node)` (instance `refactor_instMembership`)
  — both have body `v ∈ G.J ∪ G.V`; so `w ∈ G` reads identically.
* `G.IsTotalOrder lt` (`def_3_8`) → `G.refactor_IsTotalOrder lt` —
  body unchanged; only `G : refactor_CDMG Node`.

## Plan

1. Wrap the existing `Pred` and `PredLE` declarations (the `def_3_9 -- start statement` blocks
   inside `namespace CDMG`) with `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: Pred / END: Pred` and
   `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: PredLE / END: PredLE` markers. The existing
   `def_3_9 --- start helper` `variable` line stays in `namespace CDMG` (no REFACTOR
   markers — matches TopologicalOrder.lean / CDMGNotation.lean convention).

2. After `end CDMG`, open `namespace refactor_CDMG`. Inside it:
   - Add a fresh `def_3_9 --- start helper` block:
     ```lean
     -- def_3_9 --- start helper
     variable {Node : Type*} [DecidableEq Node]
     -- def_3_9 --- end helper
     ```
   - Add `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: Pred (was: refactor_Pred)` block
     containing `def refactor_Pred (G : refactor_CDMG Node) (lt : Node → Node → Prop)
     (_h : G.refactor_IsTotalOrder lt) (v : Node) : Set Node := {w | w ∈ G ∧ lt w v}`.
   - Add `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: PredLE (was: refactor_PredLE)` block
     containing `def refactor_PredLE (G : refactor_CDMG Node) (lt : Node → Node → Prop)
     (h : G.refactor_IsTotalOrder lt) (v : Node) : Set Node := G.refactor_Pred lt h v ∪ {v}`.
   - Each new declaration carries a "refactor twin" design-choice comment block.
     Style matches `TopologicalOrder.lean` lines 414-568.

3. `lake build` must stay clean.

## Conventions verified from sibling files

* TopologicalOrder.lean: two namespaces (`CDMG` then `refactor_CDMG`), each
  with its own `--- start helper` `variable` line, marker pairs only around
  the def declarations (not around the helper variable line).
* The refactor twin's design-choice block lists the *upstream-type shifts*
  explicitly and notes which LN content carries over unchanged.
* Statement markers use TWO dashes (`-- start statement`); helper markers use
  THREE dashes (`--- start helper`). Per manager.md, the `variable` line
  here gets the helper-marker shape because it's statement-typing
  infrastructure, not the LN content itself.
