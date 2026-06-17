# Workspace for def_3_11 — NodeSplittingOn (REFACTOR row)

Refactor: `cdmg_typed_edges` — DEPENDENT, caused by `def_3_1`.
Root structural change: `L : Finset (Node × Node)` + `hL_symm` →
`L : Finset (Sym2 Node)` (no `hL_symm`); `hL_irrefl` becomes
`¬ s.IsDiag`; `hL_subset` becomes `∀ v ∈ s, v ∈ V`.

## Strategy (mirror of `def_3_10` HardInterventionOn pattern)

The existing `NodeSplittingOn.lean` lives in `namespace CDMG` and
contains: `SplitNode` inductive, `toCopy0` / `toCopy1` functions,
private `toCopy0_inj`, five proof-helper lemmas, and the `def
nodeSplittingOn` with `L := G.L.image (fun e => (toCopy0 W e.1,
toCopy0 W e.2))`.

Approach (matches def_3_10's HardInterventionOn refactor exactly):
1. Wrap the entire `namespace CDMG` content (helpers + lemmas +
   def) with `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: nodeSplittingOn`
   / `END` markers.
2. Add a new top-level `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN:
   nodeSplittingOn (was: refactor_nodeSplittingOn)` / `END`
   block at the end of the file (after the original's `end CDMG`)
   containing `namespace refactor_CDMG ... end refactor_CDMG`.
3. Inside REPLACEMENT, re-create `refactor_SplitNode`,
   `refactor_toCopy0`, `refactor_toCopy1`, `refactor_toCopy0_inj`,
   four new proof-helper lemmas (one fewer than original — no
   `hL_symm`), and `def refactor_nodeSplittingOn`.
4. Each renamed declaration (`refactor_SplitNode`,
   `refactor_toCopy0`, `refactor_toCopy1`, `refactor_toCopy0_inj`,
   `refactor_nodeSplittingOn` + its four helpers) MUST be wrapped
   in its own `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: <name> (was:
   refactor_<name>)` markers OR the whole REPLACEMENT can be one
   marker block — choose the latter (matches def_3_10).

## Key Sym2 adaptations

**Old**:
```
L := G.L.image (fun e => (toCopy0 W e.1, toCopy0 W e.2))
```

**New** (`refactor_L`):
```
L := G.L.image (Sym2.map (toCopy0 W))
```

Proof obligations on the new shape:
- `hL_subset : ∀ ⦃s⦄, s ∈ L → ∀ ⦃v⦄, v ∈ s → v ∈ V`
  - Use `Sym2.mem_map` to extract `w ∈ s₀` with `toCopy0 W w = v`
  - Case-split `w ∈ W`: copy0 branch lands in `W.image .copy0`;
    else `w ∈ G.V \ W` lands in `(G.V \ W).image .unsplit`.
- `hL_irrefl : ∀ ⦃s⦄, s ∈ L → ¬ s.IsDiag`
  - Suppose `s.IsDiag`. Destructure `s₀ = s(a, b)` via `Sym2.ind`;
    `s = s(toCopy0 W a, toCopy0 W b)`. IsDiag ⇒ `toCopy0 W a =
    toCopy0 W b` ⇒ (by `refactor_toCopy0_inj`) `a = b` ⇒
    `s₀.IsDiag`, contradicting `G.hL_irrefl`.
- No `hL_symm` (gone).

`hJV_disj`, `hE_subset` proofs are mechanical ports — no Sym2
involvement.

## Reference

- Template: `Section3_2/HardInterventionOn.lean` (def_3_10's
  refactor, already solved).
- Root CDMG refactor: `Section3_1/CDMG.lean` REPLACEMENT block.
- Existing impl: `Section3_2/NodeSplittingOn.lean`.
