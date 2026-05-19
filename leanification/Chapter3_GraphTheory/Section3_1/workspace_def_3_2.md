# Workspace for def_3_2 — CDMGNotation

## What this row is

A notation block (`\begin{Not}`) on top of the `CDMG` structure introduced in
def_3_1. The LN defines seven notations:

1. `v ∈ G` ≡ `v ∈ G.J ∪ G.V` (node membership)
2. `v₁ → v₂ ∈ G` ≡ `(v₁, v₂) ∈ G.E` (directed edge, `\tuh`)
3. `v₁ ← v₂ ∈ G` ≡ `(v₂, v₁) ∈ G.E` (reverse directed, `\hut`)
4. `v₁ ↔ v₂ ∈ G` ≡ `(v₁, v₂) ∈ G.L` (bidirected, `\huh`)
5. `v₁ ⇸ v₂ ∈ G` ≡ `→` or `↔` (`\suh`, star-to-head; "into v₂")
6. `v₁ ⇷ v₂ ∈ G` ≡ `←` or `↔` (`\hus`, head-to-star; "into v₁")
7. `v₁ ↮ v₂ ∈ G` ≡ `→` or `←` or `↔` (`\sus`, "any edge between")

The "star" placeholder means "arrowhead or tail".

## Plan

- Single formalize_definition_in_lean worker dispatch.
- Target Lean file: `Section3_1/CDMGNotation.lean` (mirrors row title, keeps
  `CDMG.lean` focused on the structure itself).
- For (1): a `Membership α (CDMG α)` instance so `v ∈ G` literally works.
- For (2)-(7): seven `def`s (one per edge relation) plus user-facing
  `scoped notation` lines under namespace `Causality.CDMG` so callers can
  write `v₁ →[G] v₂` or equivalent. Decide exact concrete syntax inside the
  worker — leave the choice to whoever writes the Lean, but the *semantics*
  must match the LN one-to-one and the notation must parse the LN's `\tuh`,
  `\hut`, `\huh`, `\suh`, `\hus`, `\sus` arrows visually as closely as
  reasonable.
- Verify with `lake build` from repo root.

## Then

- `review_design` — full-LN-context check of the shape.
- `verify_equivalence` — focused statement-vs-LN check.
- `solved` → `verify_row_solved`.

## Notes

- def_3_1 (CDMG) shape and rationale: see `workspace_def_3_1.md`.
- This notation will be used heavily by def_3_3 through def_3_9 and every
  later chapter — must be ergonomic.
