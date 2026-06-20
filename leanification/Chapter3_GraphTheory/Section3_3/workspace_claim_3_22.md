# Workspace for claim_3_22 — SigmaSeparationSymmetric

## Context

This is a **DEPENDENT** row in the `collider_side_aware` refactor (root: `def_3_15`).

The row's existing file (`SigmaSeparationSymmetric.lean`, 1338 lines) was previously proven against the OLD `IsCollider`/`IsBlockableNonCollider`/`IsSigmaSeparated` predicates. It now needs to be *ported* against the side-aware refactor partners `refactor_IsCollider`/`refactor_IsBlockableNonCollider`/`refactor_IsSigmaSeparated`.

The tex statement (`tex/claim_3_22_statement_SigmaSeparationSymmetric.tex`) is pure σ-language and does NOT need to change. The tex proof needs a twin file (`tex/refactor_claim_3_22_proof_SigmaSeparationSymmetric.tex`); mathematical content is identical to the original.

## Why the new refactor predicates make the proof CLEANER

The new `refactor_IsCollider` at position 1 (cons-cons) reads:
```
s₀.refactor_HeadAtTarget ∧ s₁.refactor_HeadAtSource
```
This *asymmetric* pattern is perfectly suited to reversal:

- `WalkStep.reverse` flips `.forwardE ↔ .backwardE` and `.bidir ↔ .bidir` (via `Sym2.eq_swap`).
- Under the flip:
  - `.forwardE`: HeadAtTarget = True,           HeadAtSource = s(u,v) ∈ G.L
  - `.backwardE`: HeadAtTarget = s(u,v) ∈ G.L, HeadAtSource = True
  - `.bidir`: HeadAtTarget = True,              HeadAtSource = True
- So `s.reverse.HeadAtTarget ↔ s.HeadAtSource` and `s.reverse.HeadAtSource ↔ s.HeadAtTarget` (with `Sym2.eq_swap` for the L-disjunct case).
- This gives: `p.reverse.refactor_IsCollider (p.length - k) ↔ p.refactor_IsCollider k` directly via `s₀.HeadAtTarget ∧ s₁.HeadAtSource ↔ (s₁.reverse).HeadAtTarget ∧ (s₀.reverse).HeadAtSource = s₁.HeadAtSource ∧ s₀.HeadAtTarget = s₀.HeadAtTarget ∧ s₁.HeadAtSource` (by And.comm).

No "writing-mirror artifact" because the new predicates honor the writing-mirror via the explicit L-disjunct, which is `Sym2`-invariant under swap.

## Plan

### Phase 1 (Manager A) — statement port

1. **`spawn_agent_sub_task` → `formalize_claim_in_lean.md`** — wrap the existing `sigma_separation_symmetric` theorem with `REFACTOR-BLOCK-ORIGINAL-BEGIN/END: sigma_separation_symmetric` markers; ADD a `REFACTOR-BLOCK-REPLACEMENT-BEGIN/END: sigma_separation_symmetric (was: refactor_sigma_separation_symmetric)` block containing the new `refactor_sigma_separation_symmetric` theorem signature against `refactor_IsSigmaSeparated`, with body `:= by sorry`. Keep both statement-marker blocks (`-- claim_3_22 -- start/end statement`) for the refactor theorem too. The existing original `-- claim_3_22 -- start/end statement` markers around the OLD theorem are PRESERVED inside the ORIGINAL block.

2. **`verify_tex_statement_only`** — (tex statement file is unchanged, but verify it still passes structurally).

3. **`verify_tex_statement_equivalence`** — semantic check on the statement file (unchanged tex; should pass trivially).

4. **`review_design`** — full-LN-context check of the new `refactor_sigma_separation_symmetric` signature.

5. **`verify_equivalence`** — focused equivalence check on the new signature vs LN+addition.

6. **`add_design_choice_comments`** — write the refactor-specific design rationale above the REPLACEMENT block.

7. **`new_manager`** — handoff to Manager B for the proof port.

### Phase 2 (Manager B) — proof port

8. **`spawn_agent_sub_task` → `write_tex_proof.md`** — write the twin file `tex/refactor_claim_3_22_proof_SigmaSeparationSymmetric.tex`. Mathematical content is identical to the ORIGINAL proof tex (since the math doesn't depend on the side-aware vs literal-stored-pair distinction except at directed self-loops, and the proof works at the structural-reversal level which is unaffected). Add a brief note that the side-aware predicates' reversal invariance follows from constructor-tag-flip + the explicit L-disjunct's Sym2-invariance.

9. **`verify_tex_statement_plus_proof`** — structural.

10. **`verify_tex_proof`** — mathematical.

11. **`spawn_agent_sub_task` → `prove_claim_in_lean.md`** — port every IsCollider/IsBlockableNonCollider/IsSigmaBlockedGiven-touching lemma to its `refactor_*` partner, wrapping each with `REFACTOR-BLOCK-ORIGINAL/REPLACEMENT` markers. Specifically:
    - `Walk.isCollider_cons_zero/cons_nil_eq/nil/cons_cons_one/cons_cons_succ_succ/length_false/out_of_range/comp_eq_of_lt/comp_succ_length_cons_cons/reverse` → `refactor_*` versions
    - `Walk.isNonCollider_reverse` → `refactor_*`
    - `Walk.isBlockableNonCollider_reverse` → `refactor_*`
    - `Walk.isSigmaBlockedGiven_reverse_forward/isSigmaBlockedGiven_reverse` → `refactor_*`
    - Main `sigma_separation_symmetric` body
    - NEW: `WalkStep.refactor_headAtTarget_reverse` and `WalkStep.refactor_headAtSource_reverse` (replacing `WalkStep.isInto_reverse` — the OLD lemma can stay as-is since `IsInto` is preserved post-cleanup).
    - HasBlockingLeftSlot/RightSlot lemmas DO NOT need refactor versions (those predicates are unchanged).

12. **`solved`** — final gate.

## Notes / pitfalls

- All proof helpers that mention OLD predicate names must get REPLACEMENT versions because the OLD `IsCollider`/`IsNonCollider`/`IsBlockableNonCollider`/`IsSigmaBlockedGiven`/`IsSigmaSeparated` get deleted at Phase 7 cleanup. Without REPLACEMENTs, those helpers will reference now-deleted symbols.
- The `IsInto`-based `WalkStep.isInto_reverse` lemma CAN stay as-is — `IsInto` is preserved post-cleanup (it's not refactored).
- The `Walk.reverse`/`WalkStep.reverse`/`comp_*`/etc. structural helpers DON'T need REPLACEMENT — they don't reference any refactored predicate.
- The MAIN theorem `sigma_separation_symmetric`'s signature uses `IsSigmaSeparated`. The REPLACEMENT signature uses `refactor_IsSigmaSeparated`.
- HasBlockingLeftSlot/RightSlot lemmas are NOT refactored — they pattern-match on WalkStep constructor tags directly and the `def_3_16` predicates that use them are refactored only at the `IsNonCollider` link, not the HasBlocking* layer.

## Action history

### 2026-06-20 — Manager B picks up (fresh manager, post-handoff)

Confirmed file state:
- ORIGINAL `sigma_separation_symmetric` block (lines 1120-1337): intact, builds.
- REPLACEMENT `refactor_sigma_separation_symmetric` (lines 1339-1569): signature ported, body `:= by sorry`. Compiles with `sorry`.
- Helper lemmas (lines 88-1118) all reference OLD `IsCollider/IsNonCollider/IsBlockableNonCollider/IsSigmaBlockedGiven` — these helpers will need REPLACEMENT versions in the prove_claim_in_lean phase (cleanup deletes the OLDs).
- Twin tex file `tex/refactor_claim_3_22_proof_SigmaSeparationSymmetric.tex` does NOT exist yet.

Upstream refactor partners confirmed in scope:
- `refactor_HeadAtSource` / `refactor_HeadAtTarget` / `refactor_IsCollider` / `refactor_IsNonCollider` in `CollidersAndNon.lean`.
- `refactor_IsBlockableNonCollider` in `BlockableAndUnblockable.lean`.
- `refactor_IsSigmaBlockedGiven` in `SigmaBlockedWalks.lean`.
- `refactor_IsISigmaSeparated` / `refactor_IsSigmaSeparated` in `ISigmaSeparation.lean`.

Next action: spawn `write_tex_proof` to author the twin tex proof.

### 2026-06-20 — `solved` bounced on marker-hygiene gate

`solved` was rejected by the marker-hygiene check with finding:
> post-cleanup synthesis predicts duplicate top-level declaration(s): ['Walk', 'WalkStep'].

**Root cause (regex limitation, not a real bug):** the gate's `_DECL_RE` regex captures only the FIRST word after `def/lemma/...`, so `lemma Walk.foo` registers as a `Walk` declaration. With 49 `lemma Walk.*` + 5 `lemma WalkStep.*` in this file, both names are counted as duplicates. The cleanup script's own version of the same check explicitly acknowledges this limitation and offers `--skip-dup-check` for exactly this case — but the solve-time gate doesn't have such a flag, so I must clear it by restructure.

Simulated the synthesis to confirm: `Walk` count=49, `WalkStep` count=5, no real duplicates (all `Walk.foo` / `WalkStep.foo` are distinct in Lean).

**Fix plan:**
1. Wrap dead-after-cleanup `Walk.*` helpers in DELETE markers (`Walk.isCollider_*` lines 277–469, `Walk.isNonCollider_reverse` 984, `Walk.isBlockableNonCollider_reverse` 1000, `Walk.isSigmaBlockedGiven_reverse_*` 1086, 1109). These reference the OLD `IsCollider`/`IsNonCollider`/`IsBlockableNonCollider`/`IsSigmaBlockedGiven` which post-cleanup is renamed to the SIDE-AWARE versions — the OLD proofs likely fail to typecheck against the new bodies. DELETE wrapping removes them at cleanup.
2. Convert all surviving `Walk.*` / `WalkStep.*` declarations (the structural reverse / comp / hasBlocking* helpers AND the NEW REPLACEMENT `_sa` lemmas) to live inside `namespace Walk` / `namespace WalkStep` blocks instead of dotted-prefix notation. Inside the namespace, declarations are `lemma foo` (no `Walk.` prefix), so the regex captures the actual unique lemma name.
3. Rename any inner-name collisions (e.g. `Walk.reverse_reverse` vs `WalkStep.reverse_reverse` both become `lemma reverse_reverse` in their respective namespaces — but the regex counts them as the same `name`; rename one of them).
4. `lake build` must remain clean.

Confirmed no external consumers of the to-be-deleted OLD helpers via grep (only this file's source + workspace + for-website.json reference them).

