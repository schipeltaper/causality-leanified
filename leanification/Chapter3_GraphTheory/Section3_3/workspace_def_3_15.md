# Workspace for def_3_15 — CollidersAndNon (refactor: cdmg_typed_edges, DEPENDENT)

## Refactor role

DEPENDENT, pulled in by roots `def_3_1` (CDMG: `L : Finset (Sym2 Node)` + Sym2.IsDiag irrefl) and `def_3_4` (Walk: typed `WalkStep` with three constructors `.forwardE / .backwardE / .bidir`).

The canonical tex (`tex/def_3_15_CollidersAndNon.tex`) is **unchanged** by the refactor — the LN's collider/non-collider definition doesn't change. Only the Lean encoding changes, because the original used `G.into vk a` on edges stored as `Node × Node`, and that ordered-pair-plus-G.into machinery is replaced by direct pattern matching on the typed `refactor_WalkStep` constructors.

## Plan

1. Add net-new helper `refactor_IsInto` in a new `namespace refactor_WalkStep` block in `CollidersAndNon.lean`. This is the canonical per-WalkStep "arrowhead-at-node" predicate, tested by node-equality on the WalkStep's type indices.
2. Port `IsCollider` to `refactor_IsCollider` in a `namespace refactor_CDMG / namespace refactor_Walk` block. Use recursive pattern-match shape consistent with `refactor_IsBifurcationWithSplit` (Walks.lean L2444-2456); per-step "into v_k" via `s.refactor_IsInto vk` calls. REPLACEMENT block named `IsCollider`.
3. Port `IsNonCollider` to `refactor_IsNonCollider` (mechanical retarget: `p.length` → `p.refactor_length`, `p.IsCollider k` → `p.refactor_IsCollider k`). REPLACEMENT block named `IsNonCollider`.
4. Wrap the existing `IsCollider` and `IsNonCollider` with `REFACTOR-BLOCK-ORIGINAL-BEGIN/END` markers.
5. `lake build` clean.
6. `review_design` on the port.
7. `verify_equivalence` against LN tex_block + (empty) addition.
8. `add_design_choice_comments` capturing port rationale.
9. `solved`.

## Helper — refactor_IsInto

The canonical "edge into a node" predicate at the typed-WalkStep level. Tests arrowhead-presence by node-equality on the WalkStep's type indices (NOT by a constructor-tag "source vs target" reading, which loses information at directed self-loops):

```
def refactor_IsInto : ∀ {u v : Node}, refactor_WalkStep G u v → Node → Prop
  | _, v, .forwardE _, w => w = v          -- forward u→v: arrowhead at v
  | u, _, .backwardE _, w => w = u         -- backward v→u: arrowhead at u
  | u, v, .bidir _, w => w = u ∨ w = v     -- bidirected: at both endpoints
```

Net-new declaration (no original counterpart); wrapped in `REFACTOR-BLOCK-REPLACEMENT-BEGIN/END: IsInto` and `def_3_15 --- start/end helper` markers per net-new-helper convention. Lives in `namespace refactor_WalkStep` for dot-notation `s.refactor_IsInto vk` lookup.

## Encoding map (LN → refactor_WalkStep), via the helper

For position `k` in walk `π = (v_0 s_0 v_1 s_1 ... s_{n-1} v_n)`, the two walk-incident steps are `s_{k-1} : WalkStep G v_{k-1} v_k` and `s_k : WalkStep G v_k v_{k+1}`. The LN's "edge into v_k" reading at each step:

- `s_{k-1}.IsInto v_k`:
  - `.forwardE _` (target index = v_k): True ✓
  - `.backwardE _` (source index = v_{k-1}): True iff v_{k-1} = v_k (self-loop)
  - `.bidir _`: True (arrowheads at both endpoints, including v_k)
- `s_k.IsInto v_k`:
  - `.forwardE _` (target index = v_{k+1}): True iff v_{k+1} = v_k (self-loop)
  - `.backwardE _` (source index = v_k): True ✓
  - `.bidir _`: True

So `IsCollider p 1` (interior position 1) iff `s_0.IsInto v_1 ∧ s_1.IsInto v_1`. For k ≥ 2, recurse on the tail (shift index by 1).

## Self-loop semantics

Self-loop semantics preserved via the `refactor_IsInto` helper: at a self-loop position `v_{k-1} = v_k`, both `.forwardE` and `.backwardE` encodings test `IsInto v_k = True` by node-equality, matching the original `G.into v_k (v_k, v_k) = True` (E-clause's `e.2 = v_k`).

Concretely, with `E = {(v_0, v_1), (v_1, v_1)}` and walk `cons _ (.forwardE h₁) (cons _ (.forwardE h₂) (.nil _ hv))`:
- s_0 = .forwardE h₁ : WalkStep G v_0 v_1 → IsInto v_1 = (v_1 = v_1) = True ✓
- s_1 = .forwardE h₂ : WalkStep G v_1 v_1 (self-loop) → IsInto v_1 = (v_1 = v_1) = True ✓
- IsCollider p 1 = True ✓ (matches original)

A naive constructor-tag enumeration (without the node-equality helper) would classify `s_1 = .forwardE` as "no arrowhead at v_1 since target side, not source" and return False — diverging from the original. The IsInto helper resolves this by node-equality testing.

`.bidir` is impossible on a self-loop because `hL_irrefl` forbids `s.IsDiag` in L.

## Pattern-match shape (refactor_IsCollider)

5-branch shape (down from the original draft's 12-branch enumeration):

```
| _, _, .nil _ _, _ => False
| _, _, .cons _ _ (.nil _ _), _ => False
| _, _, .cons _ _ (.cons _ _ _), 0 => False
| _, _, .cons vk s₀ (.cons _ s₁ _), 1 => s₀.refactor_IsInto vk ∧ s₁.refactor_IsInto vk
| _, _, .cons _ _ (p@(.cons _ _ _)), k + 2 => p.refactor_IsCollider (k + 1)
```

The k=1 branch binds `vk` (the cons-cell's middle vertex = walk's v_1) and the two WalkSteps `s₀`, `s₁`, then delegates the "into v_k" test to the `refactor_IsInto` helper at each step.

## refactor_IsNonCollider

Mechanical port; `refactor_IsCollider` reference now resolves to the helper-based predicate so self-loop semantics are preserved through this indirection.
```
def refactor_IsNonCollider {u v : Node} (p : refactor_Walk G u v) (k : ℕ) : Prop :=
  k ≤ p.refactor_length ∧ ¬ p.refactor_IsCollider k
```
