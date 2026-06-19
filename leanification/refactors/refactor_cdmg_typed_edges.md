# Refactor plan: cdmg_typed_edges

**Status:** proposed (not yet executed)
**Date:** 2026-06-17
**Root refs:** `def_3_1` (`CDMG`), `def_3_4` (`Walk` / `WalkStep`)
**Root chapter:** 3
**Source branch:** `server_setting_up_scaffold`
**Proposed refactor branch:** `refactor_cdmg_typed_edges`

## Why this refactor is needed

`claim_3_22` (σ-separation symmetry) cannot be closed under the current encoding without an artificial structural assumption. The reason is a chain of three encoding choices, the FIRST of which is the actual source:

1. **`def_3_1` lets `E` and `L` share an ambient type**: both are `Finset (Node × Node)`. The operator clarification `[edge_set_disjointness_under_specified]` says "the same ordered pair `(v, w)` may belong to both `E` and `L` simultaneously". This admits a class of pathological CDMGs (writing-mirror) where `(u, v) ∈ G.L \ G.E` and `(v, u) ∈ G.E` coexist.

2. **`def_3_4`'s `WalkStep` has no backward-L disjunct.** When reversing a walk step, an L-edge must have its stored pair swapped (to use forward-L on the reversed traversal direction via `hL_symm`).

3. **Predicates downstream** (e.g. `def_3_16`'s `IsBlockableNonCollider`) reconstruct "is this walk-edge an E-edge?" by checking `a ∈ G.E` on the stored pair. After (2)'s forced swap on writing-mirror CDMGs, the swapped pair lands in `E` coincidentally, and the predicate misclassifies an L-step as an E-step.

(1) is the *source*. The downstream predicates' "what channel is this edge?" question only becomes ambiguous because the encoding admits (1) and (2) can't preserve channel info across reversal. Fix (1) at the type level and the ambiguity disappears — predicates pattern-match on a constructor, walks reverse cleanly, no axiomatic workaround needed.

Previous refactor attempts on this row tried fixing only the symptoms — adding `hEL_disj` to `def_3_1` (path (c) from claim_3_22's refactor plans), refactoring `def_3_16`'s predicate (the blockable refactor), refactoring `def_3_18`'s aliases (the sigma_separation_J_empty_premise refactor). Each closed part of the problem; the residue persisted. The operator's call is to fix the encoding at the foundation.

## Proposed new shape

### `def_3_1` (`Section3_1/CDMG.lean`)

Move L to `Finset (Sym2 Node)` — unordered pairs as Mathlib's symmetric quotient. Drop `hL_symm` (free under Sym2). Reformulate `hL_subset` over Sym2 membership; reformulate `hL_irrefl` as "no diagonal element".

```lean
structure CDMG (Node : Type*) [DecidableEq Node] where
  J : Finset Node
  V : Finset Node
  hJV_disj : Disjoint J V
  E : Finset (Node × Node)
  hE_subset : ∀ ⦃e : Node × Node⦄, e ∈ E → e.1 ∈ J ∪ V ∧ e.2 ∈ V
  L : Finset (Sym2 Node)
  hL_subset : ∀ ⦃s : Sym2 Node⦄, s ∈ L → ∀ ⦃v : Node⦄, v ∈ s → v ∈ V
  hL_irrefl : ∀ ⦃s : Sym2 Node⦄, s ∈ L → ¬ s.IsDiag
  -- hL_symm removed; symmetry is built into Sym2 by construction
```

### `def_3_4` (`Section3_1/Walks.lean`)

`WalkStep` becomes a Type-level inductive with explicit constructors for each channel and direction. Walk-edge data carries the channel at the term level — no inference from the stored pair.

```lean
inductive WalkStep (G : CDMG Node) : Node → Node → Type where
  | forwardE  {u v : Node} (h : (u, v) ∈ G.E) : WalkStep G u v
  | backwardE {u v : Node} (h : (v, u) ∈ G.E) : WalkStep G u v
  | bidir     {u v : Node} (h : s(u, v) ∈ G.L) : WalkStep G u v
```

`Walk G u v` becomes:

```lean
inductive Walk (G : CDMG Node) : Node → Node → Type where
  | nil (v : Node) (hv : v ∈ G) : Walk G v v
  | cons (vMid : Node) (h : WalkStep G u vMid) (p : Walk G vMid w) : Walk G u w
```

The `cons` no longer stores an `a : Node × Node`; the endpoints come from the `WalkStep`'s type indices and the channel comes from the constructor.

### Reversal becomes trivial

```lean
def WalkStep.reverse {G : CDMG Node} {u v : Node} :
    WalkStep G u v → WalkStep G v u
  | .forwardE  h => .backwardE h
  | .backwardE h => .forwardE  h
  | .bidir     h => .bidir (by rw [Sym2.eq_swap]; exact h)
```

Three lines. No `hL_symm` invocation, no stored-pair swap, no possibility of an L-step being mistaken for an E-step on the reversed walk. The channel is structurally preserved.

### `claim_3_22` (`Section3_3/SigmaSeparationSymmetric.lean`)

The proof obstacle dissolves. Under the new shape, `Walk.IsBlockableNonCollider_of_reverse` is a direct constructor case split on `WalkStep`; the swap branch that previously needed a `sorry` becomes an `.bidir h => .bidir ...` case that's vacuous for the E-check.

### Operator clarification on `def_3_1`

Rewrite `[edge_set_disjointness_under_specified]` to record the new type-level separation:

> `[edge_set_types_distinct]` Bidirected edges live in `Sym2 Node` and directed edges in `Node × Node`. The LN's "(disjoint)" qualifier is upgraded from set-level (which the previous clarification weakened to ordered-pair-shareable) to *type-level*: an L-edge and an E-edge are objects of distinct mathematical types and cannot share a representation. The writing-mirror class of CDMGs admitted by the previous reading is no longer representable.

## Affected rows

This refactor's blast radius is the largest in the project so far — every chapter-3 row that destructures `G.L` or constructs a CDMG needs source-level adjustment. The `find_dependents.py` scan (run during `do_refactor.py init`) will produce the authoritative list by renaming `CDMG` to `CDMG_REFACTOR_DISABLED` and watching `lake build` break.

| Ref | File | What changes |
|-----|------|--------------|
| `def_3_1` | `Section3_1/CDMG.lean` | **Root**: structure reshape per above |
| `def_3_4` | `Section3_1/Walks.lean` | **Root**: `WalkStep` becomes Type-level inductive; `Walk` cons no longer stores an ordered pair; structural reversal |
| `def_3_10`/`def_3_11`/`def_3_12`/`def_3_13`/`def_3_14` | `Section3_2/*.lean` | CDMG constructors: rewrite `L'` field assignments under Sym2; discharge the new `hL_subset` / `hL_irrefl` shape; `hL_symm` discharge disappears |
| `claim_3_16`/`claim_3_17`/`claim_3_18`/`claim_3_19` | `Section3_2/*.lean` | Re-validate under new shape; most likely needs source touches at L-destructuring sites |
| `def_3_15`/`def_3_16`/`def_3_17`/`def_3_18` | `Section3_3/*.lean` | Re-validate; `IsBlockableNonCollider`'s E-check pattern can simplify (channel from constructor instead of from `a ∈ G.E`) |
| `claim_3_20`/`claim_3_21`/`claim_3_22` | `Section3_3/*.lean` | claim_3_22's `sorry` closes by construction; others re-validate |

Any §3.1 row that doesn't touch L (e.g. `def_3_5` ancestral relations, `def_3_6` acyclicity, `claim_3_1` etc.) likely rebuilds without source changes — the find_dependents scan will confirm.

## Risks

- **Mathlib `Sym2` interaction overhead.** Existing rows that `.image` / `.filter` over `G.L` now operate on `Finset (Sym2 Node)`. `Sym2.lift` / quotient-respecting morphisms add boilerplate; each L-manipulation site needs review.
- **One-shot migration.** A half-migrated state (some rows still using `Finset (Node × Node)` for L, others using `Finset (Sym2 Node)`) doesn't typecheck. The refactor table has to land all rows in one synchronized cut.
- **Walk-using rows downstream of `def_3_4` may have proofs that pattern-match on the old `Walk.cons` shape**. The new `cons` has a different parameter list (no `a`, WalkStep moves into the cons proper). Every walk-pattern site needs update.
- **The `polish_refactor_comments` worker** will see substantial `pre-refactor` / `post-refactor` prose in the design-choice blocks and will need to digest it cleanly. The recently-added "no `-/` inside block comments" guard should hold.

## Why now

The recent refactor-system enhancement (commit `0b23dcb`) embeds each root's BEFORE/AFTER blocks directly in every dependent row's manager briefing. That makes the dependent rows' "port mechanically" workflow cheap: the manager arrives with the structural diff in working memory and translates rather than re-derives. This was the prerequisite for taking on a refactor with this many dependent rows.
