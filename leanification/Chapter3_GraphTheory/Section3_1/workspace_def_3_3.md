# Workspace for def_3_3 — EdgeRelations (REFACTOR `cdmg_typed_edges`)

## Refactor context
This is a DEPENDENT row, pulled in because `def_3_1` (CDMG) changed:
`L : Finset (Node × Node) + hL_symm + hL_irrefl` → `L : Finset (Sym2 Node) + hL_subset (via Sym2.Mem) + hL_irrefl (via ¬ s.IsDiag)`.

The original `def_3_3` (in `EdgeRelations.lean`) defines three things on `CDMG`:
1. `adjacent (G : CDMG Node) (v1 v2 : Node) : Prop := G.sus v1 v2`
2. `into (G : CDMG Node) (v : Node) (e : Node × Node) : Prop := (e ∈ G.E ∧ e.2 = v) ∨ (e ∈ G.L ∧ (e.1 = v ∨ e.2 = v))`
3. `outOf (G : CDMG Node) (v : Node) (e : Node × Node) : Prop := e ∈ G.E ∧ e.1 = v`

Under the refactor:
- `G.E : Finset (Node × Node)` — unchanged carrier
- `G.L : Finset (Sym2 Node)` — new carrier; ordered-pair indexing impossible

## Design decision: split `into` into `intoE` and `intoL`

The original unified `into : Node → Node × Node → Prop` is no longer
well-typed: its `L`-clause checks `e ∈ G.L` with `e : Node × Node`,
but `G.L : Finset (Sym2 Node)`. Under Sym2 the L-edge has no canonical
ordered-pair representative.

Two natural redesigns:

**Option A: split** into two predicates by channel.
- `intoE (G : refactor_CDMG Node) (v : Node) (e : Node × Node) : Prop := e ∈ G.E ∧ e.2 = v`
- `intoL (G : refactor_CDMG Node) (v : Node) (s : Sym2 Node) : Prop := s ∈ G.L ∧ v ∈ s`
- `outOf (G : refactor_CDMG Node) (v : Node) (e : Node × Node) : Prop := e ∈ G.E ∧ e.1 = v`

**Option B: sum** — `into v (e : Node × Node ⊕ Sym2 Node)`.
- One predicate, but forces every use site to wrap edges in `Sum.inl` / `Sum.inr`.

**Choosing A.** Reasons:
- Matches the typed-edges design ethos of `cdmg_typed_edges`: channels are
  typed separately, so consumers reach for the right predicate by edge type
  rather than threading a sum at every site.
- Downstream operations on `G.E` vs `G.L` (e.g. `def_3_10` intervention
  filters, `def_3_5` family sets) operate on the two `Finset`s separately
  anyway — they were never going to share a unified iteration.
- Each downstream walk-step in the refactored `def_3_4` is typed by channel,
  so `intoEnd` / `outOfEnd` on a walk-step naturally picks the channel-
  specific predicate.
- The LN's "into v" is a single named relation, but the LN's typing already
  splits at the carrier level (E vs L); the Sym2 refactor just makes that
  type-level distinction load-bearing for L too.

**Tradeoff accepted.** Calls like "the set of all edges into v" must now
build two `Finset`s and operate on them together. This was already the
case at the implementation level (since `G.E` and `G.L` are separate
`Finset`s); the refactor just makes it apparent at the API level.

## Plan
1. Dispatch `formalize_definition_in_lean` worker with explicit refactor
   briefing: wrap existing `adjacent`, `into`, `outOf` in
   `REFACTOR-BLOCK-ORIGINAL` markers; add three new `REFACTOR-BLOCK-REPLACEMENT`
   blocks for `refactor_adjacent`, `refactor_intoE`, `refactor_intoL`,
   `refactor_outOf` (and the namespace tweak — they must sit in
   `namespace refactor_CDMG`).
2. `review_design` (refactor-aware) — check the split is natural.
3. `verify_equivalence` — focused friendly equivalence vs LN+addition.
4. `verify_equivalence_strict` (recommended for a def introducing new
   predicates) — adversarial check.
5. `add_design_choice_comments` — write the *why* into the comment
   blocks above each new declaration (split rationale, Sym2 boilerplate
   trade-off, downstream consumer notes).
6. `solved` → orchestrator's three-check gate.

## Notes for downstream rows
- `intoE` and `intoL` replace the original `into`. Downstream rows that
  use `CDMG.into` (Walks.lean's `intoEnd`/`outOfEnd`, CollidersAndNon.lean's
  collider predicate) will need to dispatch the right one based on the
  walk-step's channel. The split is load-bearing for the typed-walks
  design in the refactored `def_3_4`.
- `outOf` is unchanged in body (only its `G` parameter type changes from
  `CDMG` to `refactor_CDMG`).
- `adjacent` is just `G.refactor_sus v1 v2`.
