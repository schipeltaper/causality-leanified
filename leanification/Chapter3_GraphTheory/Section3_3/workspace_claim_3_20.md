# Workspace for claim_3_20 — AcyclicNonCollidersBlockable (refactor `blockable_noncollider_first`)

## Refactor context

- Role: DEPENDENT. Pulled in because `def_3_16` changed underneath us.
- Original Lean: `AcyclicNonCollidersBlockable.lean` — full theorem
  `acyclic_non_colliders_blockable` already on disk, statement +
  proof intact (must stay intact through Phase 7).
- Original tex statement: `tex/claim_3_20_statement_AcyclicNonCollidersBlockable.tex`
  — **stays unchanged** (no statement twin; only proof tex has a twin).
- Original tex proof: `tex/claim_3_20_proof_AcyclicNonCollidersBlockable.tex`
  — **untouched**; new proof written into the *twin*
  `tex/refactor_claim_3_20_proof_AcyclicNonCollidersBlockable.tex`.

## What changed underneath us (def_3_16)

Primary / derived split was *swapped*:

- **Old primary** `IsUnblockableNonCollider` (positive
  universal-implication form: every outgoing walk-edge lands in
  `G.Sc vk`). **Old derived** `IsBlockableNonCollider = IsNonCollider ∧
  ¬IsUnblockableNonCollider` (double-negated disjunction).
- **New primary** `refactor_IsBlockableNonCollider` (positive
  disjunction form: `k = 0 ∨ k = p.length ∨ (∃ outgoing walk-edge at
  k-1 to non-Sc) ∨ (∃ outgoing walk-edge at k to non-Sc)`). **New
  derived** `refactor_IsUnblockableNonCollider = IsNonCollider ∧
  ¬refactor_IsBlockableNonCollider`.

LN meaning of "blockable" is unchanged; only the Lean encoding flipped.

## Our row's signature change

Lean signature for the REPLACEMENT block — only the predicate name in
the conclusion (and the theorem name) change:

```lean
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: acyclic_non_colliders_blockable (was: refactor_acyclic_non_colliders_blockable)
theorem refactor_acyclic_non_colliders_blockable
    (G : CDMG Node) (hG : G.IsAcyclic)
    {u v : Node} (π : Walk G u v) (k : ℕ) :
    π.IsNonCollider k → π.refactor_IsBlockableNonCollider k
:= by ...
-- REFACTOR-BLOCK-REPLACEMENT-END: acyclic_non_colliders_blockable
```

The proof body is *structurally different*: now constructive (exhibit
disjunction witness) rather than negation-style contradiction. Plus
the helper lemmas `Walk.vertices_length_eq`, `Walk.vertices_head?_eq_source`,
`Walk.walkStep_at`, `Walk.walkStep_at_vertices` are reusable as-is
(they sit above the original theorem with no markers).

## New proof strategy (high level)

Given `π.IsNonCollider k`, exhibit a `refactor_IsBlockableNonCollider`
witness via case-split on `k`:

1. `k = 0` → first end-position disjunct (paired with the
   IsNonCollider conjunct).
2. `k = p.length` → second end-position disjunct.
3. `k` interior (`1 ≤ k ∧ k + 1 ≤ p.length`) → exhibit an
   `∃`-disjunct. From `IsNonCollider`'s `ah_π(k) ≤ 1` (def_3_15) at
   least one walk-incident edge is not into `v_k`; combined with the
   `WalkStep` relation this forces an outgoing directed walk-edge
   `(v_k, w) ∈ G.E`. Then `w ∉ Sc^G(v_k)`: if it were, we'd have a
   directed walk `w ⤳ v_k` (`w ∈ Anc^G(v_k)`), prepending `(v_k, w)`
   would give a non-trivial directed cycle at `v_k`, contradicting
   `hG : G.IsAcyclic`. (Same cycle-construction as the old proof's
   Step 2.4 — now used to derive `w ∉ G.Sc vk` rather than to derive
   `False` outright.)

## Plan

1. **Write tex proof twin.** Spawn `write_tex_proof.md` with refactor
   briefing + path to the twin + the strategy above.
2. **`verify_tex_statement_plus_proof`** on the twin (structural).
3. **`verify_tex_proof`** on the twin (mathematical).
4. **Spawn `prove_claim_in_lean.md`** to add the REPLACEMENT block in
   `AcyclicNonCollidersBlockable.lean`, alongside the existing
   original (which stays untouched). Theorem name
   `refactor_acyclic_non_colliders_blockable`; reuse the helper
   lemmas already in the file (no markers needed for those — they're
   proof-only).
5. **`review_design`** on the REPLACEMENT.
6. **`verify_equivalence`** (statement-level: new theorem matches
   LN + addition).
7. **`add_design_choice_comments`** on the new REPLACEMENT block.
8. **`solved`** → orchestrator runs `verify_row_solved` + hard sorry
   check + strict-equivalence gate.

## Notes

- `addition_to_the_LN` (the
  `acyclic_does_not_imply_directed_in_text` clause) is unaffected
  by the refactor; canonical statement tex stays unchanged.
- No tex statement twin needed (refactor briefing: only proof twins).
- The `def_3_16` REPLACEMENT block in `BlockableAndUnblockable.lean`
  declares both `refactor_IsBlockableNonCollider` and
  `refactor_IsUnblockableNonCollider`; we only reference the
  blockable one in this row's conclusion.
