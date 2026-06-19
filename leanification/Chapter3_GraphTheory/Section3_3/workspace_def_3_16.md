# Workspace for def_3_16 — BlockableAndUnblockable (refactor `cdmg_typed_edges`)

## Plan (set by manager on first turn)

**Role:** DEPENDENT row in `cdmg_typed_edges` refactor. Roots `def_3_1`
(CDMG: `L : Finset (Sym2 Node)`) and `def_3_4` (typed
`refactor_WalkStep` constructors `.forwardE / .backwardE / .bidir`).

**File to edit (append-only):**
`leanification/Chapter3_GraphTheory/Section3_3/BlockableAndUnblockable.lean`.
The original `def IsBlockableNonCollider` / `def IsUnblockableNonCollider`
(under `namespace CDMG.Walk`) stay untouched — wrap them with
`REFACTOR-BLOCK-ORIGINAL-BEGIN/END: IsBlockableNonCollider` and
`REFACTOR-BLOCK-ORIGINAL-END: IsUnblockableNonCollider` markers.

Add an `end Causality`-then-`namespace Causality / namespace refactor_CDMG
/ namespace refactor_Walk` block at the bottom containing the replacements.

**Encoding map (LN → refactor port):**

The original interior disjuncts used `p.edges[k-1]? = some (vk, vkm1) ∧
(vk, vkm1) ∈ G.E` (resp. slot-k variant) — Option-membership lookups
into `p.edges`. Under the refactor, `p.refactor_edges` does NOT exist
(intentional omission, see `Walks.lean:1631-1685`'s "Why no
`refactor_edges`" block). Channel/direction info is now on the typed
WalkStep's constructor tag:

- Slot-(k-1) "outgoing E-walk-edge from v_k to v_{k-1}" = the step
  `s_{k-1} : refactor_WalkStep G v_{k-1} v_k` is `.backwardE h`
  (h : (v_k, v_{k-1}) ∈ G.E). Direction-mirrors the walk.
- Slot-k "outgoing E-walk-edge from v_k to v_{k+1}" = the step
  `s_k : refactor_WalkStep G v_k v_{k+1}` is `.forwardE h`
  (h : (v_k, v_{k+1}) ∈ G.E). Direction-aligned with the walk.

These are E-only / no writing-mirror union (LN's `\tuh` is E-only per
`def_3_2` item 2). This mirrors `refactor_outOfStart` / `refactor_outOfEnd`'s
constructor-tag-only convention — contrast `refactor_IsInto`, which DOES
union because the LN's `\into` is itself a union over E and L channels.
The original was constructor-choice-dependent at writing-mirror walks (the
walker's `p.edges` storage choice determined whether the disjunct fired);
the refactor preserves that dependence via the constructor-tag reading.

**Recursive-pattern shape (mirrors `refactor_IsCollider` in this file):**

Two thin helpers descend the walk to the slot of interest, then
constructor-pattern-match on the WalkStep:

```lean
def refactor_HasBlockingLeftSlot : ∀ {u v : Node}, refactor_Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ _ _, 0 => False
  | u, _, .cons v (.backwardE _) _, 1 => u ∉ G.refactor_Sc v
  | _, _, .cons _ (.forwardE _) _, 1 => False
  | _, _, .cons _ (.bidir _) _, 1 => False
  | _, _, .cons _ _ p, k + 2 => p.refactor_HasBlockingLeftSlot (k + 1)

def refactor_HasBlockingRightSlot : ∀ {u v : Node}, refactor_Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | u, _, .cons v (.forwardE _) _, 0 => v ∉ G.refactor_Sc u
  | _, _, .cons _ (.backwardE _) _, 0 => False
  | _, _, .cons _ (.bidir _) _, 0 => False
  | _, _, .cons _ _ p, k + 1 => p.refactor_HasBlockingRightSlot k
```

(Index arithmetic: outer slot k-1 = tail slot k-2 (tail position
shifts by 1), so `HasBlockingLeftSlot` at outer `k+2` recurses to tail
with `k+1`; outer slot k = tail slot k-1, so `HasBlockingRightSlot` at
outer `k+1` recurses to tail with `k`.)

Then the two main defs are non-recursive:

```lean
def refactor_IsBlockableNonCollider {u v : Node} (p : refactor_Walk G u v) (k : ℕ) : Prop :=
  p.refactor_IsNonCollider k ∧
  ( k = 0 ∨ k = p.refactor_length ∨
    p.refactor_HasBlockingLeftSlot k ∨
    p.refactor_HasBlockingRightSlot k )

def refactor_IsUnblockableNonCollider {u v : Node} (p : refactor_Walk G u v) (k : ℕ) : Prop :=
  p.refactor_IsNonCollider k ∧ ¬ p.refactor_IsBlockableNonCollider k
```

**Marker wrapping:**
- `IsBlockableNonCollider` (original): wrap with `REFACTOR-BLOCK-ORIGINAL`
  pair. Replacement: `def refactor_IsBlockableNonCollider`, wrap with
  `REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsBlockableNonCollider (was:
  refactor_IsBlockableNonCollider)`.
- `IsUnblockableNonCollider` (original): wrap with `REFACTOR-BLOCK-ORIGINAL`
  pair. Replacement: `def refactor_IsUnblockableNonCollider`, wrap with
  `REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsUnblockableNonCollider (was:
  refactor_IsUnblockableNonCollider)`.
- Two new helpers `refactor_HasBlockingLeftSlot` / `refactor_HasBlockingRightSlot`
  are net-new — wrap each with a REPLACEMENT-only pair using the
  `(was: refactor_<Name>)` form.

**Worked sanity checks** (manager performed in head before dispatch):
- nil walk, k=0: end-position disjunct fires → True. (Matches original.)
- length-1 walk, k=0 or k=1: end-position disjuncts fire → True. (Matches.)
- length-2 walk with forward-forward (left chain at v_1): right slot
  fires iff v_2 ∉ Sc v_1; left slot does NOT fire (s_0 = .forwardE,
  not .backwardE). (Matches original at this writing.)
- length-2 walk with backward-forward (fork at v_1): both slots can
  fire (left iff v_0 ∉ Sc v_1, right iff v_2 ∉ Sc v_1). (Matches.)
- Out-of-range k > p.refactor_length: refactor_IsNonCollider conjunct
  fails (since k ≤ p.refactor_length is part of its body), so whole
  predicate is False.

## Notes / what's been tried

_(populated as the run progresses)_
