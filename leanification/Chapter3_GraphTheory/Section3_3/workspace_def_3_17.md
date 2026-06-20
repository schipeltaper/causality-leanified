# Workspace for def_3_17 — SigmaBlockedWalks

## Refactor context (collider_side_aware)

- **Role**: DEPENDENT (caused by root `def_3_15`).
- **Upstream root changes** (`CollidersAndNon.lean`):
  - `refactor_HeadAtTarget` / `refactor_HeadAtSource` — net-new helpers (zero-arg, constructor-tag-only).
  - `refactor_IsCollider` — REPLACEMENT for `IsCollider`; clause-1 body
    `s₀.refactor_HeadAtTarget ∧ s₁.refactor_HeadAtSource` (no middle-vertex binder).
  - `refactor_IsNonCollider` — REPLACEMENT for `IsNonCollider`; body
    `k ≤ p.length ∧ ¬ p.refactor_IsCollider k`.
- **Adjacent dependent already ported** (`BlockableAndUnblockable.lean`):
  - `refactor_IsBlockableNonCollider` — REPLACEMENT for `IsBlockableNonCollider`;
    body identical to ORIGINAL modulo `p.IsNonCollider k → p.refactor_IsNonCollider k`.
    Helpers `HasBlockingLeftSlot` / `HasBlockingRightSlot` are untouched
    (they pattern-match on WalkStep constructors only; no side-aware
    head reading needed).
  - The same retarget discipline applies here.

## This row's port

Both `IsSigmaOpenGiven` and `IsSigmaBlockedGiven` reference
`p.IsCollider` and `p.IsBlockableNonCollider`. Under the refactor
window the unqualified dot-notation would resolve to the ORIGINAL
upstream defs (literal-name shadowing rule), which means the
σ-open/σ-blocked pair would silently keep the pre-refactor self-loop
classification — breaking the very property the refactor exists to fix.
The retargets to `p.refactor_IsCollider` and
`p.refactor_IsBlockableNonCollider` are therefore load-bearing during
the refactor window. After Phase 7 cleanup's whole-word renames they
collapse back to the LN-named symbols.

### Plan (one worker, mechanical port)

1. Wrap the existing `def IsSigmaOpenGiven` (lines 365–372 incl.
   `set_option linter.unusedVariables false in` and the
   `-- def_3_17 -- start/end statement` markers) and ALL its
   preceding comment block (from `-- ref: def_3_17 (paragraph
   "C-σ-open walk") — refactor` to the closing `set_option …`)
   in a `REFACTOR-BLOCK-ORIGINAL-BEGIN/END: IsSigmaOpenGiven`
   pair.
2. Append a `REFACTOR-BLOCK-REPLACEMENT-BEGIN/END:
   IsSigmaOpenGiven (was: refactor_IsSigmaOpenGiven)` pair
   containing the side-aware-retargeted `def refactor_IsSigmaOpenGiven`
   with a design-choice header explaining the retarget (cf.
   `refactor_IsBlockableNonCollider`'s design block at lines 632–
   800 of `BlockableAndUnblockable.lean` for the canonical
   template).
3. Same shape for `IsSigmaBlockedGiven`.

### What stays untouched

- The file-header docstring (`/-! … -/`), `open` declarations,
  `variable {Node : Type*} [DecidableEq Node]` / `variable {G :
  CDMG Node}` blocks, namespaces.
- Both ORIGINAL defs' bodies and comments — they keep using
  `p.IsCollider` / `p.IsBlockableNonCollider` and build during
  the refactor window.

### Verifier chain

After the port:
1. `verify_tex_statement_only` (canonical tex unchanged, but
   worth a fast cheap structural confirmation it still parses).
2. `verify_tex_statement_equivalence` (canonical tex vs LN + addition;
   semantics unchanged, but the strict gate will demand both halves
   agree on the spec).
3. `review_design` on the REPLACEMENT (mode: refactor port, focus on
   the retarget rationale and that nothing else moved).
4. `verify_equivalence` between REPLACEMENT Lean and the canonical
   tex (now mediated by side-aware upstream).
5. `verify_equivalence_strict` (the strict gate runs in `solved`
   anyway; running it voluntarily catches CONTENT deviations early).
6. `add_design_choice_comments` if any gap surfaces in step 3.
7. `solved` → `verify_row_solved` → strict-equivalence gate.
