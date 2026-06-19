# Refactor plan: total_order_helper

**Status:** proposed (not yet executed)
**Date:** 2026-06-07
**Root refs:** def_3_8 (IsTopologicalOrder), def_3_9 (Predecessors)
**Root chapter:** 3
**Source branch:** server_setting_up_scaffold
**Proposed refactor branch:** refactor_total_order_helper

## Why this refactor is needed

After yesterday's prompt updates landed (`verify_equivalence` item 1a, `verify_equivalence_strict`'s new "loosening a quantifier's domain" CONTENT example, and the helper-predicates section of `formalize_definition_in_lean.md`), two §3.1 rows are now in violation of the equivalence checkers' rules:

1. **`def_3_8` (IsTopologicalOrder)** bundles three total-order properties (irreflexive, transitive, trichotomous on `J ∪ V`) with the topological condition (`∀ v w, v ∈ G.Pa w → lt v w`) into a single flat 4-way `∧`. The LN says *"Let `<` be a total order of `J ∪ V`"* and then *"... such that whenever `v ∈ Pa^G(w)` we have `v < w`"* — the LN treats "total order on `J ∪ V`" as a substantive sub-concept (mentioning it inline rather than as a separate def). The Lean encoding doesn't reflect that structure: there's no named `IsTotalOrder` to point at, the design notes consider one and reject it, and downstream `Pred` / `PredLE` (def_3_9) consequently drop the total-order hypothesis entirely.

2. **`def_3_9` (Predecessors)** takes a raw `lt : Node → Node → Prop` argument to `Pred` / `PredLE`, with **no** total-order hypothesis in the type contract. The LN's *"Let `<` be a total order"* premise lives only in 60+ lines of design-choice comments. This is exactly the failure mode `verify_equivalence` item 1a is designed to catch ("hypothesis dropped from Lean's type contract; only documented in design comments"), and it's exactly the CONTENT example `verify_equivalence_strict` was just updated to flag ("loosening a quantifier's domain"). The Lean's `Pred G lt v` is well-defined for any binary relation; the LN's `Pred^G_<(v)` is only well-defined when `<` is a total order on `J ∪ V`. They aren't the same mathematical object even though they coincide on the LN's intended inputs.

A refactor — rather than a row-level re-solve — is warranted because the fix changes the **shape** of a foundational def (`IsTopologicalOrder`) and propagates downstream: consumers of `IsTopologicalOrder` see a different constructor / destructor pattern, and consumers of `Pred` / `PredLE` see an extra hypothesis on the signature. Doing this row-by-row in the normal solve loop would force each affected row to fail its equivalence gate first, then refactor — clumsy, and the `IsTopologicalOrder` shape change would break the build between rows.

## Proposed new shape

### `def_3_8` (TopologicalOrder.lean)

Introduce `IsTotalOrder` as a named helper predicate inside the same file, wrapped with `-- def_3_8 --- start helper` / `-- def_3_8 --- end helper` markers (three dashes — the standard helper-marker convention). The new `IsTopologicalOrder` is defined in terms of it:

```lean
-- def_3_8 --- start helper
def IsTotalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  (∀ v ∈ G, ¬ lt v v) ∧
  (∀ u ∈ G, ∀ v ∈ G, ∀ w ∈ G, lt u v → lt v w → lt u w) ∧
  (∀ v ∈ G, ∀ w ∈ G, lt v w ∨ v = w ∨ lt w v)
-- def_3_8 --- end helper

-- def_3_8 -- start statement
def IsTopologicalOrder (G : CDMG Node) (lt : Node → Node → Prop) : Prop :=
  G.IsTotalOrder lt ∧ (∀ v w, v ∈ G.Pa w → lt v w)
-- def_3_8 -- end statement
```

Logically equivalent to the current 4-way `∧`. The destructure pattern changes:

- **Old:** `obtain ⟨h_irrefl, h_trans, h_total, h_topo⟩ := h_iso`
- **New:** `obtain ⟨h_to, h_topo⟩ := h_iso; obtain ⟨h_irrefl, h_trans, h_total⟩ := h_to`

(Or `obtain ⟨⟨h_irrefl, h_trans, h_total⟩, h_topo⟩ := h_iso` in one step.)

The constructor pattern changes symmetrically:

- **Old:** `refine ⟨irrefl_proof, trans_proof, total_proof, topo_proof⟩`
- **New:** `refine ⟨⟨irrefl_proof, trans_proof, total_proof⟩, topo_proof⟩`

Both old and new will coexist in TopologicalOrder.lean during the refactor (the original `IsTopologicalOrder` lives in a `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsTopologicalOrder` block; the replacement `refactor_IsTopologicalOrder` lives in a `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN` block). Build stays green until `apply_refactor_cleanup` swaps them at finalize-time.

### `def_3_9` (Predecessors.lean)

`Pred` and `PredLE` gain `(h : G.IsTotalOrder lt)` as an explicit hypothesis between `lt` and `v`:

```lean
-- def_3_9 -- start statement
def Pred (G : CDMG Node) (lt : Node → Node → Prop)
    (h : G.IsTotalOrder lt) (v : Node) : Set Node :=
  {w | w ∈ G ∧ lt w v}
-- def_3_9 -- end statement

-- def_3_9 -- start statement
def PredLE (G : CDMG Node) (lt : Node → Node → Prop)
    (h : G.IsTotalOrder lt) (v : Node) : Set Node :=
  G.Pred lt h v ∪ {v}
-- def_3_9 -- end statement
```

The `h` argument is *not used* in the body — that's intentional. It's there to enforce the LN's premise at the type level: callers can only invoke `Pred` / `PredLE` if they can supply a proof that `lt` is a total order on `J ∪ V`. Downstream consumers (chapter 4 CBN factorisation, chapter 5 do-calculus, σ/d-separation in chapters 6-7, iSCMs in chapters 8-10) typically already have a `G.IsTopologicalOrder lt` hypothesis in scope, from which `G.IsTotalOrder lt` falls out by `.1` projection.

### `claim_3_2` (AcyclicIffTopologicalOrder.lean)

The theorem statement is unchanged in shape (it's an iff over `∃ lt, G.IsTopologicalOrder lt`). But the proof body has two pattern-matching sites that need adjusting:

- The **forward direction (Acyclic → ∃ TO)** constructs `IsTopologicalOrder` at the end. The constructor goes from a flat 4-tuple to a nested `⟨⟨...⟩, ...⟩`.
- The **backward direction (∃ TO → Acyclic)** destructures an `IsTopologicalOrder` hypothesis to pull out the three total-order properties + the topological condition. Same flat-to-nested change in reverse.

The high-level proof strategy (mathlib's `extend_partialOrder` for the forward direction; chain-of-strict-inequalities-contradicting-walk for the backward direction) is unchanged. Only the destructure / construct patterns flip.

## Affected rows (consumers)

Transitive consumer set, hand-traced:

| Ref | Chapter | File | What changes for this row |
|---|---|---|---|
| `def_3_8` | 3 | `TopologicalOrder.lean` | Add `IsTotalOrder` helper; redefine `IsTopologicalOrder := IsTotalOrder ∧ topo_clause`. |
| `def_3_9` | 3 | `Predecessors.lean` | Add `(h : G.IsTotalOrder lt)` hypothesis to `Pred` and `PredLE`; ripple `h` through the `PredLE` body's use of `Pred`. |
| `claim_3_2` | 3 | `AcyclicIffTopologicalOrder.lean` | Proof destructure / construct patterns flip from flat 4-tuple to nested `⟨⟨irrefl, trans, total⟩, topo⟩`. Theorem statement is unchanged. |

No other §3.1 row currently consumes `Pred` / `PredLE` (def_3_9 is the last row of §3.1). No §3.1 row consumes `IsTopologicalOrder` other than `claim_3_2`. Validation: run `extras/find_dependents.py --chapter 3 --ref def_3_8` and again with `--ref def_3_9` during `do_refactor.py init`; this gives the bullet-proof transitive closure (the script renames each target to `_REFACTOR_DISABLED`, runs `lake build`, scrapes every error site, then restores). If `find_dependents.py` surfaces any row I missed, the refactor table will pick it up automatically.

## Why-rationale references for the strict checker

If `verify_equivalence_strict` is run during the refactor on the *new* shape, it will see `G.IsTotalOrder lt` as a named hypothesis on `Pred` — the loosened-domain pattern is gone. The new design-block on `IsTotalOrder` documents *why* the helper exists (per the new prompt's signal-(a)+(b)+(c) judgment: referenced by spec, substantive content, reused by downstream). The new design-block on `IsTopologicalOrder` documents the slight structural change (4-way `∧` → 2-way `∧` with a sub-conjunction).

The deviation register (`leanification/deviations.json`) is empty for both rows — there are no `accept_deviation` entries to flip. After the refactor, the rows pass the equivalence gates cleanly without needing any deviation acceptance.

## Recommended invocation

```
RECOMMENDED_INVOCATION: python extras/do_refactor.py init --chapter 3 --root-refs def_3_8,def_3_9 --name total_order_helper
REFACTOR_PLAN_FILE: leanification/refactors/refactor_total_order_helper.md
```
