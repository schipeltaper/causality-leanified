# Workspace for def_3_1 — CDMG

## Outcome

- Wrote `Section3_1/CDMG.lean` with `structure Causality.CDMG (α : Type*)`.
- `lake build` clean from repo root (no warnings).

## Shape pinned down for downstream chapters

Future rows will destructure CDMGs constantly ("Let `G = (J, V, E, L)` be a
CDMG"). They get those field names:

```
G.J  : Set α
G.V  : Set α
G.disjoint_JV : Disjoint G.J G.V
G.E  : Set (α × α)              -- directed edges
G.E_subset    : G.E ⊆ (G.J ∪ G.V) ×ˢ G.V
G.L  : Set (α × α)              -- bidirected edges (symmetric subset of V×V)
G.L_subset    : G.L ⊆ G.V ×ˢ G.V
G.L_irrefl    : ∀ ⦃v₁ v₂⦄, (v₁, v₂) ∈ G.L → v₁ ≠ v₂
G.L_symm      : ∀ ⦃v₁ v₂⦄, (v₁, v₂) ∈ G.L → (v₂, v₁) ∈ G.L
G.disjoint_EL : Disjoint G.E G.L
```

Imports used: `Mathlib.Data.Set.Prod` (for `×ˢ`) and `Mathlib.Order.Disjoint`
(for `Disjoint`).

## Notes for next workers in Section 3.1

- def_3_2 (CDMGNotation): the LN defines `v ∈ G`, `v₁ → v₂ ∈ G`, etc. as
  *notation*. These should be `notation` / `scoped notation` on top of
  `CDMG`, not new fields. `v ∈ G` means `v ∈ G.J ∪ G.V`, etc. Bear in mind
  that `(G : CDMG α)` is not a `Set` itself, so `v ∈ G` will need a custom
  `Membership` instance (or a non-Membership notation).
- claim_3_1 (JNodeProperties): the LN remark "no `j ∈ J` has any arrowheads
  pointing at it" should follow from `E_subset` and `disjoint_JV` alone,
  combined with the future def_3_2 notation. No new structural fields
  needed.
- def_3_7 (graph types): DG/DAG/etc. are predicates on `CDMG`, defined by
  things like `G.J = ∅`, `G.L = ∅`, plus acyclicity. Don't make them
  separate structures.

## Why `Disjoint E L` is a field

The LN says "two (disjoint) sets of edges". Both `E` and `L` live in
`Set (α × α)` here, so the disjointness is a meaningful constraint —
it forbids the same ordered pair `(v₁, v₂)` from being both a directed
*and* a bidirected edge. Without this field, a pathological CDMG could
have `(v₁, v₂) ∈ E ∩ L`, which the LN's quotient phrasing rules out by
type but ours has to rule out by axiom.

## Open: shape worth revisiting if it bites

- The asymmetry between `J ⊆ α` and `α` being the ambient type is fine
  for now, but later chapters that quantify "over all vertices of `G`"
  will phrase it as `v ∈ G.J ∪ G.V`. If that gets cumbersome, we can
  add a derived `nodes : Set α := J ∪ V` lemma/abbrev later.
- `L_symm` and `L_irrefl` are propositionally equivalent to a single
  combined field matching the LN's literal phrasing
  `(v₁,v₂) ∈ L → v₁ ≠ v₂ ∧ (v₂,v₁) ∈ L`. Split for ergonomics.
