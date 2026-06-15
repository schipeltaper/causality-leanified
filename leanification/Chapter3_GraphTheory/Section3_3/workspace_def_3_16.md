# Workspace for def_3_16 — BlockableAndUnblockable

## Refactor plan reading (2026-06-15, first manager turn)

The refactor plan at `leanification/refactors/refactor_blockable_noncollider_first.md`
proposes two coupled changes:

1. **Swap primary/derived.** Make `IsBlockableNonCollider` the primary
   predicate (positive-existence: at least one outgoing walk-edge of `v_k`
   lands outside `G.Sc vk`), derive `IsUnblockableNonCollider` as
   `IsNonCollider ∧ ¬IsBlockableNonCollider`.
2. **Include L-edges as "outgoing arrowhead from v_k".**

## Decision: execute (1) with a slot-agnostic ∃ form; DROP (2)

A deep LN reading by an Explore worker (independent of the existing Lean
and the refactor plan) confirms that the LN's def_3_16 is **E-only**:

- The blockable elaboration uses `$v_k \tuh v_{k\pm1}$` which per def_3_2
  is strictly `(v_k, v_{k\pm1}) \in E` — directed E-edges only, never L.
- def_3_3's definition of "out of v_1" explicitly excludes L-edges.
- The three patterns (left chain, right chain, fork) are internally
  consistent with the E-only reading: where a pattern's shorthand
  (`\hus`, `\suh`) admits both E and L, the SCC condition is attached
  only to the E-edge slot — the L-edge slot has no SCC requirement.
- Downstream consumers (claim_3_20 acyclic-blockable, claim_3_22
  σ-separation symmetric) are consistent with E-only.
- The existing canonical tex's "Reconciliation" explicitly excludes
  L-edges from the "outgoing walk-edge" predicate.

Adding L-coverage as the refactor proposes would make some currently
LN-unblockable positions become refactor-blockable — a content
divergence from the LN that `verify_equivalence_strict` (and probably
`verify_equivalence`) will FAIL.

## What the refactor's architectural improvement actually requires

The genuine improvement is the **slot-agnostic ∃ formulation**: instead
of literal-pair patterns keyed to slot index, quantify over outgoing
walk-edges from `v_k`. This composes cleanly under walk-reversal
(claim_3_22's blocker), regardless of whether L-edges are included.

## Final new shape (E-only, slot-explicit disjunction matching LN's
"blockable disjunction" form)

```lean
def IsBlockableNonCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  p.IsNonCollider k ∧
  ( k = 0 ∨ k = p.length ∨
    (1 ≤ k ∧ ∃ (vkm1 vk : Node),
        p.vertices[k - 1]? = some vkm1 ∧
        p.vertices[k]? = some vk ∧
        p.edges[k - 1]? = some (vk, vkm1) ∧
        (vk, vkm1) ∈ G.E ∧
        vkm1 ∉ G.Sc vk) ∨
    (∃ (vk vkp1 : Node),
        p.vertices[k]? = some vk ∧
        p.vertices[k + 1]? = some vkp1 ∧
        p.edges[k]? = some (vk, vkp1) ∧
        (vk, vkp1) ∈ G.E ∧
        vkp1 ∉ G.Sc vk) )

def IsUnblockableNonCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  p.IsNonCollider k ∧ ¬ p.IsBlockableNonCollider k
```

This:

- Mirrors the LN's blockable elaboration (end-position OR at least one
  outgoing `$v_k \tuh v_{k\pm 1}$` to non-SC) directly as the primary
  definition.
- Keeps `IsUnblockableNonCollider` as a derived predicate via negation
  on the `IsNonCollider` sub-class, making the LN's "every non-collider
  is exactly one of blockable / unblockable" definitional.
- Is mathematically equivalent to the existing canonical tex (which
  already spells out both the "two implications" unblockable form and
  the "disjunction" blockable form — the refactor just picks the
  blockable side as primary).
- Drops the L-coverage that the refactor plan asked for (LN-unsound).

## Tex file

For a def refactor, per the manager's "Refactor rows" section, there
is no tex twin — the canonical statement tex stays as-is. The existing
canonical tex already contains both the negation-form and the
disjunction-form characterisations of blockable, so the math is
already covered. The new Lean's design comments will explain that we
pick the disjunction form as primary (whereas the original picked the
negation form).

## Plan of actions

1. `spawn_agent_sub_task` → `formalize_definition_in_lean.md` with
   REFACTOR-BLOCK markers around both originals + replacements.
2. `review_design` on the replacement declarations.
3. `verify_equivalence` (then optionally `verify_equivalence_strict` +
   `verify_with_examples`).
4. `add_design_choice_comments` (mandatory before solved).
5. `solved`.

## Notes for any future manager

- DO NOT add L-edge coverage to the predicate, even though the
  refactor plan asks for it. The LN is E-only. See the Explore
  worker's findings above for the receipts.
- If claim_3_20 / claim_3_22 still struggle with walk-reversal after
  the slot-agnostic reshape, the next step is to add walk-reversal
  lemmas, NOT to broaden the predicate.
- The refactor briefing's `addition_to_the_LN` is empty and stays
  empty — no new LN clauses are introduced by this refactor (it's
  purely a Lean shape change, with the math preserved).
