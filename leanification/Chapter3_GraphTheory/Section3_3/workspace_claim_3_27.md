# Workspace for claim_3_27 — LabelRoman (refactor: collider_side_aware)

## Critical situation analysis (Manager A, fresh start)

### Prior state (pre-refactor)
- Original chapter row had `proven=disproven, solved=yes` (commit `fa84b62`, 2026-06-20).
- Prior disproof: `LabelRomanDisproof.lean` (599 lines) + `claim_3_27_disproof_LabelRoman.tex` (418 lines).
- BOTH files deleted in commit `e3634ef` (def_3_15 refactor) — see `git show e3634ef --stat`.
- The disproof was a concrete counter-example over `Bool`:
  - CDMG `G` with `V = {false, true}`, `E = {(false,true), (true,false), (true,true)}` (directed 2-cycle + self-loop at `true`), `L = ∅`.
  - Walk `π = (false, .backwardE h_ba, true, .forwardE h_bb, true)` — vertex sequence `[false, true, true]`.
  - Case (i) replacement: `σ_ij = (false, .forwardE h_ab, true)` (single directed edge).
  - Modified walk `π' = (false, .forwardE h_ab, true, .forwardE h_bb, true)`.
  - **Load-bearing fact**: `π'.IsCollider 1 = True` under the OLD `IsInto`-based reading, because `IsInto true` fires on BOTH `.forwardE h_ab` (target=true) AND on `.forwardE h_bb` (a self-loop, where source=target=true, so node-equality fires).
  - σ-blocked verdict at position 1 followed from `true ∉ AncSet ∅`.

### What the refactor changes
- New side-aware predicates:
  - `refactor_HeadAtSource(.forwardE _) = False`   (KEY)
  - `refactor_HeadAtTarget(.forwardE _) = True`
  - Both `True` for `.bidir _`; mirrored for `.backwardE _`.
- New `refactor_IsCollider` at position 1: `s₀.refactor_HeadAtTarget ∧ s₁.refactor_HeadAtSource`.
- For the old counter-example `π'`: at position 1, `s₀=.forwardE h_ab` → `HeadAtTarget=True`; `s₁=.forwardE h_bb` → `HeadAtSource=False`.
- ⇒ `π'.refactor_IsCollider 1 = False`.
- ⇒ The previous counter-example's σ-blocked verdict no longer holds.
- ⇒ The disproof is INVALIDATED by the refactor.

### Why the LN claim is now plausibly TRUE
The `collider_side_aware` refactor was explicitly designed to fix the self-loop misclassification that made the LN's `lem:replace_walk` false in the old encoding. The whole point of the refactor is to make the encoding match the LN's intuitive semantics, restoring the LN's claim to provability. This row should pivot to PROVE direction.

### Wording-check subtleties (working phase)
1. **`case_i_fork_at_vj_blocking_criteria_overlooked`** — assumes our σ-blocking convention is asymmetric (outgoing-only). I verified by reading `HasBlockingLeftSlot`/`HasBlockingRightSlot` in `BlockableAndUnblockable.lean:378,509`: yes, our convention IS asymmetric. BUT the subtlety's claimed corner case (v_j ∈ C, v_j ∈ Sc v_{j-1}, v_j ∉ Sc v_{j+1}) is EXCLUDED by the σ-open hypothesis on π: a fork at v_j with v_j ∈ C is blockable iff v_{j-1} ∉ Sc v_j ∨ v_{j+1} ∉ Sc v_j; in the subtlety's case, v_{j+1} ∉ Sc v_j, so π would NOT be σ-open at v_j on the fork. Contradiction. **So subtlety #1 is benign for us** — the proof's "same blocking criteria apply" is correct under our asymmetric convention.
2. **`vi_eq_vj_combined_node_open_not_verified`** — the canonical statement tex already addresses this in the "Addition to the LN" paragraph (length-zero replacement). Worth careful handling in the Lean proof.
3. **`shortest_qualifier_unused_in_proof`** — benign.

### Canonical statement tex
Already filled in at `tex/claim_3_27_statement_LabelRoman.tex` (122 lines). States the positive lemma with existential conclusion `∃ σ_ij π', (σ_ij ⊆ Sc(v_j)) ∧ π' is σ-open`. Includes the "Addition to the LN" paragraph for the `v_i = v_j` case. This is a PROVE-direction statement; equivalent for both old and new semantics.

### Files context
- Original `LabelRomanDisproof.lean` / disproof tex: deleted; no current file exists for this row.
- Canonical statement tex (prove direction): `tex/claim_3_27_statement_LabelRoman.tex` (filled, presumably already verified equivalent under the OLD semantics; should still be valid).
- Target Lean file (new): `Section3_3/LabelRoman.lean` (positive theorem). `main_lean_file` metadata in refactor_data.json points at stale `LabelRomanDisproof.lean`; the orchestrator can update on `mark_solved`.
- Proof tex (new): `tex/claim_3_27_proof_LabelRoman.tex` (currently does not exist; will be created by `write_tex_proof`).
- Upstream refactored predicates (live, REPLACEMENT blocks present):
  - `Section3_3/CollidersAndNon.lean`: `refactor_HeadAtSource/Target`, `refactor_IsCollider`, `refactor_IsNonCollider`.
  - `Section3_3/BlockableAndUnblockable.lean`: `refactor_IsBlockableNonCollider`, `refactor_IsUnblockableNonCollider`.
  - `Section3_3/SigmaBlockedWalks.lean`: `refactor_IsSigmaOpenGiven`, `refactor_IsSigmaBlockedGiven`.

### Plan sketch
- Dispatch `make_plan` worker to lay out the subtasks (LN tex statement verification, Lean theorem signature, structural lemmas, proof of each LN case).
- Then standard claim flow Manager A → handoff → Manager B:
  - Statement formalization in Lean (signature only, sorry body).
  - TeX proof (the LN's `\begin{proof}` block adapted).
  - Lean proof.

## History
- 2026-06-21 (this turn): manager analyzed the situation, decided to pivot from port-the-disproof to prove-the-claim. Reason: refactor invalidates the prior counter-example; LN claim is now provable under side-aware semantics.
