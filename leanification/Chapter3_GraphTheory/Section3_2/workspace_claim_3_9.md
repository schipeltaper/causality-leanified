# Workspace for claim_3_9 — SwigAcyclic (REFACTOR row, cdmg_typed_edges)

## Refactor situation

This is a DEPENDENT row in refactor `cdmg_typed_edges` (roots:
`def_3_1`, `def_3_4`).  Upstream roots changed `L`'s typing on
`CDMG`:
- BEFORE: `L : Finset (Node × Node)` + `hL_subset` + `hL_irrefl
  (v1 v2 → v1 ≠ v2)` + `hL_symm`.
- AFTER : `L : Finset (Sym2 Node)` + `hL_subset` (`v ∈ s → v ∈ V`)
  + `hL_irrefl (¬ s.IsDiag)` (no `hL_symm` — definitional via Sym2).

All upstream rows are already solved (def_3_1 / def_3_4 roots and
every dependent through def_3_12 / claim_3_8 / claim_3_2).  This row
is the first unsolved claim row in the refactor table.

## Critical observation

The existing `SwigAcyclic.lean` proofs **do NOT directly touch
`L` or `hL_*`**.  The bidirected-edge set is irrelevant to both
sub-claims — see the file header and tex proof, both of which
explicitly note "The bidirected-edge set `L` plays no role in
either sub-claim" because `IsAcyclic` only sees directed walks
and `IsTopologicalOrder` only sees `Pa` (which is built from `E`).

So the port is mechanical:
- Replace `CDMG` → `refactor_CDMG`
- Replace `G.IsCADMG` → `G.refactor_IsCADMG`
- Replace `G.nodeSplittingHard hCADMG W hW` → `G.refactor_nodeSplittingHard hCADMG W hW`
- Replace `.IsAcyclic` → `.refactor_IsAcyclic`
- Replace `G.IsTopologicalOrder` → `G.refactor_IsTopologicalOrder`
- Replace `SplitNode` → `refactor_SplitNode`
- Replace `splOrder` → `refactor_splOrder`
- Replace `toCopy0` / `toCopy1` → `refactor_toCopy0` / `refactor_toCopy1`
- Replace `acyclic_iff_topological_order` (claim_3_2) → `refactor_acyclic_iff_topological_order`

## Template: SplitTopologicalOrder.lean (claim_3_6, architectural twin)

That file shows the exact pattern:

```
namespace Causality

namespace CDMG

  -- claim_3_6 --- start helper
  variable {Node : Type*} [DecidableEq Node]
  -- claim_3_6 --- end helper

  -- REFACTOR-BLOCK-ORIGINAL-BEGIN: splOrder
  ... existing splOrder def + design block ...
  -- REFACTOR-BLOCK-ORIGINAL-END: splOrder

  ... helpers (baseOf, tagOf, splOrder_iff, splitNode_ext,
      baseOf_mem, splOrder_lifted_edge, splOrder_transfer_edge,
      aux_splTopologicalOrder) — NO refactor markers, kept as-is

  -- REFACTOR-BLOCK-ORIGINAL-BEGIN: splAcyclic
  ... splAcyclic ...
  -- REFACTOR-BLOCK-ORIGINAL-END: splAcyclic

  -- REFACTOR-BLOCK-ORIGINAL-BEGIN: splTopologicalOrder
  ... splTopologicalOrder ...
  -- REFACTOR-BLOCK-ORIGINAL-END: splTopologicalOrder

end CDMG

namespace refactor_CDMG

  -- claim_3_6 --- start helper
  variable {Node : Type*} [DecidableEq Node]
  -- claim_3_6 --- end helper

  -- REFACTOR-BLOCK-REPLACEMENT-BEGIN: splOrder (was: refactor_splOrder)
  ... refactor_splOrder ...
  -- REFACTOR-BLOCK-REPLACEMENT-END: splOrder

  -- REFACTOR-BLOCK-REPLACEMENT-BEGIN: baseOf (was: refactor_baseOf)
  private def refactor_baseOf ...
  -- REFACTOR-BLOCK-REPLACEMENT-END: baseOf

  ... etc for every helper ...

  -- REFACTOR-BLOCK-REPLACEMENT-BEGIN: splAcyclic (was: refactor_splAcyclic)
  theorem refactor_splAcyclic ...
  -- REFACTOR-BLOCK-REPLACEMENT-END: splAcyclic

  -- REFACTOR-BLOCK-REPLACEMENT-BEGIN: splTopologicalOrder (was: refactor_splTopologicalOrder)
  theorem refactor_splTopologicalOrder ...
  -- REFACTOR-BLOCK-REPLACEMENT-END: splTopologicalOrder

end refactor_CDMG

end Causality
```

Key insight: original helpers (NO `refactor_` prefix) live in
`namespace CDMG`; refactor helpers (with `refactor_` prefix) live
in `namespace refactor_CDMG`.  Namespace separation prevents
cleanup-rename collisions (the renamed `refactor_baseOf → baseOf`
inside `refactor_CDMG` doesn't collide with `CDMG.baseOf`).
Cleanup also handles the namespace rename `refactor_CDMG → CDMG`.

## Manager B handoff: this row only needs the Lean port

Manager A already (in the original solve) verified the tex statement
and proof.  Tex files are pre-existing and don't need touching for
this refactor (the LN remark doesn't change; only the Lean encoding
does).

Per the refactor briefing: "**No tex twin for def rows** — definitions'
LN block doesn't change in a refactor; only the Lean encoding does."
But this is a CLAIM row, so technically a `refactor_claim_3_9_proof_*.tex`
twin COULD be made.  However, since the proof mathematics is unchanged
and the existing tex proof references the LN-level CDMG / SWIG structure
abstractly (no Lean-specific encoding decisions), there's nothing to
update.  We will SKIP the tex twin (no diff to capture).

## Plan

1. spawn_agent_sub_task → port `SwigAcyclic.lean`:
   - Wrap `swigAcyclic` and `swigTopologicalOrder` theorems in
     `REFACTOR-BLOCK-ORIGINAL` markers.
   - Open `namespace refactor_CDMG` after `end CDMG`.
   - Add `REFACTOR-BLOCK-REPLACEMENT` blocks for every helper
     (`refactor_baseOf`, `refactor_tagOf`, `refactor_splOrder_iff`,
     `refactor_splitNode_ext`, `refactor_baseOf_mem_swig`,
     `refactor_splOrder_lifted_edge`, `refactor_aux_swigTopologicalOrder`)
     and the two main theorems (`refactor_swigAcyclic`,
     `refactor_swigTopologicalOrder`).
   - Use refactored upstream types throughout.
   - Verify `lake build` clean.
2. review_design (refactor twin)
3. verify_equivalence (refactor twin vs LN block)
4. add_design_choice_comments (if review_design surfaces new design notes)
5. solved → verify_row_solved + strict-equivalence gate

## Notes

- Statement block tex (`claim_3_9_statement_SwigAcyclic.tex`) is unchanged
  — was rewritten and verified equivalent in the original solve.
- Proof tex (`claim_3_9_proof_SwigAcyclic.tex`) is unchanged — was
  written and verified in the original solve.  The refactor doesn't
  alter the LN-level argument.
- `refactor_role: dependent`, `caused_by_roots: ['def_3_1']` (the
  refactor table records only def_3_1 caused this row to be pulled in;
  def_3_4 — walk typing — didn't touch this row because the proof
  uses `IsAcyclic` and `IsTopologicalOrder` as black boxes, not raw
  walks).
