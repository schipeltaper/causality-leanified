# Refactor plan: blockable_noncollider_first

**Status:** proposed (not yet executed)
**Date:** 2026-06-15
**Root ref:** def_3_16 (`BlockableAndUnblockable`)
**Root chapter:** 3
**Source branch:** server_setting_up_scaffold
**Proposed refactor branch:** refactor_blockable_noncollider_first

## Why this refactor is needed

The current `IsUnblockableNonCollider` predicate (`Section3_3/BlockableAndUnblockable.lean:271`) checks outgoing arrowheads from `v_k` by pattern-matching the stored walk-edge ordered pair against `(vk, vkm1) ∈ G.E` / `(vk, vkp1) ∈ G.E`. This catches the case where `v_k` is the source of a directed E-edge but **silently misses two cases that the LN's "outgoing arrowhead from v_k" semantics include**:

1. **L-edges incident to v_k.** A bidirected edge between `v_k` and a neighbor on `π` contributes an arrowhead at `v_k` by the LN's convention for L-edges; the current predicate only checks `∈ G.E` and never `∈ G.L`, so L-edges never trigger the outgoing-arrowhead obligation.
2. **Symmetric L-storage.** Even if extended to L, the predicate's literal-pattern `p.edges[k-1]? = some (vk, vkm1)` fails on L-edges stored as `(vkm1, vk)` (which `hL_symm` makes equivalent to `(vk, vkm1) ∈ L`).

The current shape forces every consumer that reasons about unblockable preservation under walk-reversal (claim_3_22 onward) to contend with a predicate whose channel-distinction relies on a fragile literal-pair pattern, rather than on the LN's clean "outgoing arrowhead from `v_k`" structural reading.

## Proposed new shape

**Swap the definitional ordering.** Make `IsBlockableNonCollider` the **primary** predicate (positive existence form, cleanly enumerating outgoing arrowheads from `v_k`):

```lean
def IsBlockableNonCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  p.IsNonCollider k ∧
  -- non-collider v_k is blockable iff it is an end-node OR
  -- it has at least one outgoing arrowhead on π whose other walk-endpoint
  -- lies in a DIFFERENT strongly connected component (i.e. ∉ G.Sc vk).
  ( (k = 0 ∨ k = p.length) ∨
    ∃ (target : Node),
      (target is a walk-neighbour of v_k on π via an outgoing-arrowhead-from-v_k
       walk-edge — covering E-source-at-v_k AND L-incident-at-v_k,
       across both `(vk, target)` and `(target, vk)` storage orderings of L) ∧
      target ∉ G.Sc vk )
```

Then **derive `IsUnblockableNonCollider`** as the complement:

```lean
def IsUnblockableNonCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  p.IsNonCollider k ∧ ¬ p.IsBlockableNonCollider k
```

Why this is cleaner:

1. The positive existence form in `IsBlockableNonCollider` lets channel-distinction (E vs L, source-at-v_k vs incident) be enumerated explicitly across all walk-edge storage orderings — no implicit dependency on a literal-pair pattern that drops L cases.
2. `IsUnblockableNonCollider` becomes a derived predicate; downstream proofs about "preservation under walk-reversal" no longer touch a literal-pair pattern at all — they reduce to preservation of `IsBlockableNonCollider` and `IsNonCollider`.
3. Mutual exclusivity ("every non-collider is exactly one of blockable or unblockable") becomes definitional via the negation.

## Affected rows

| Ref | File | What changes |
|-----|------|--------------|
| `def_3_16` | `Section3_3/BlockableAndUnblockable.lean` | Foundational redesign — swap definitional order, fix the L-channel coverage in `IsBlockableNonCollider`'s positive form |
| `def_3_17` | `Section3_3/SigmaBlockedWalks.lean` | Re-validate (depends on blockable / unblockable classifiers) |
| `def_3_18` | `Section3_3/ISigmaSeparation.lean` | Re-validate (builds on def_3_17) |
| `claim_3_20` | `Section3_3/AcyclicNonCollidersBlockable.lean` | Re-prove (the proof under the new shape may simplify or need a different angle) |

`claim_3_22+` (not yet started in their current form) consume the new shape directly; they are not in the refactor table.

## Risks

- `claim_3_20`'s proof under the new shape may need a substantively different argument; both that and a clean port are acceptable outcomes.
- The new `IsBlockableNonCollider` body is longer (positive existence covering multiple E/L cases and storage orderings) than the current derived form. That length is the cost of getting the LN's "outgoing arrowhead from v_k" semantics fully right — the LN-faithful payoff is that downstream walk-reversal arguments become tractable.
- `def_3_17` and `def_3_18` may not need source-level changes (consumer rows of a foundational redesign often rebuild as-is); the refactor table should still carry them for re-validation.

## Why this refactor and not a CDMG-level one

A separate refactor proposal (`refactor_cdmg_E_L_disjoint.md`, now discarded) attributed the same downstream symptom (claim_3_22 walk-reversal failure) to a foundational ambiguity in `def_3_1` (CDMG) and proposed an `hEL_disj` field on the CDMG structure. After analysis: the LN's `def_3_1` is fine; the real fault is local to the unblockable-non-collider predicate's channel-distinction. Fixing that here keeps the blast radius confined to one chapter-3 subsection (4 rows), avoiding a touch on the foundational CDMG type.
