# Workspace for claim_3_3 — AcyclicPreservedUnderDo (REFACTOR row)

## Status
DEPENDENT row in refactor `cdmg_typed_edges`; roots `def_3_1`, `def_3_4`.
Both roots solved. Direct upstream `def_3_10` (HardInterventionOn) solved
with REPLACEMENT block already in place — provides
`refactor_hardInterventionOn` on `refactor_CDMG`.

## Goal
Port the existing `AcyclicPreservedUnderDo.lean` declarations against the
refactor twins:
- `refactor_CDMG` (Sym2 L, no `hL_symm`)
- `refactor_Walk` / `refactor_WalkStep` (typed-inductive: `.forwardE`,
  `.backwardE`, `.bidir`)
- `refactor_IsDirectedWalk`, `refactor_length`, `refactor_IsAcyclic`,
  `refactor_IsTopologicalOrder`, `refactor_Pa`,
  `refactor_hardInterventionOn`.

The mathematical content is unchanged; only encoding shifts.

## Pre-refactor structure (in `namespace CDMG`)
Five private helpers + one main theorem:
1. `mem_of_mem_hardInterventionOn` — carrier-matching lift.
2. `Walk.liftWalkStep_of_hardInterventionOn` — WalkStep lift.
3. `Walk.liftFromHardIntervention` — recursive walk lift.
4. `Walk.isDirectedWalk_liftFromHardIntervention` — directedness preservation.
5. `Walk.length_liftFromHardIntervention` — length preservation.
6. `theorem acyclic_preserved_under_do` — main statement.

## Porting recipe (per declaration)

### Marker convention (from AcyclicIffTopologicalOrder.lean)
- Each declaration wrapped in its own ORIGINAL+REPLACEMENT pair.
- Marker name follows the convention `Walk.<name>` even though only `Walk`
  parses as the rename target — that's intentional; inner private-helper
  `refactor_<name>` survives unrenamed (fine because `private`).
- Public theorem uses flat marker name = decl name (no dots).
- ORIGINAL block: keep declaration verbatim inside `namespace CDMG`.
- REPLACEMENT block: identical structure inside `namespace refactor_CDMG`,
  with `refactor_` prefix on declarations and on every type/term that has
  a refactor twin.

### Per-declaration transformations
1. **`mem_of_mem_hardInterventionOn`**: signature/body almost unchanged.
   - `CDMG` → `refactor_CDMG`; `G.hardInterventionOn` → `G.refactor_hardInterventionOn`.
   - Proof: pure set-algebra on `J/V/W`; identical body.

2. **`Walk.liftWalkStep_of_hardInterventionOn`**: structural rewrite.
   - Now takes `refactor_WalkStep (G.refactor_hardInterventionOn W hW) u v`
     (an inductive `Type`, not a `Prop`) and returns `refactor_WalkStep G u v`.
   - Pattern-match: `.forwardE h` → `.forwardE ((Finset.mem_filter.mp h).1)`;
     `.backwardE h` similarly; `.bidir h` → `.bidir ((Finset.mem_filter.mp h).1)`
     (the L filter is `fun s => ∀ v ∈ s, v ∉ W`; `.1` of `mem_filter` extracts
     `s ∈ G.L`).

3. **`Walk.liftFromHardIntervention`**: recursive on new constructors.
   - `.nil w hw` → `.nil w (refactor_mem_of_mem_hardInterventionOn hw)`.
   - `.cons vMid s p` → `.cons vMid (lift_step s) (lift_walk p)`.

4. **`Walk.isDirectedWalk_liftFromHardIntervention`**: pattern-match on step.
   - `.nil _ _, _` → `trivial`.
   - `.cons _ (.forwardE _) p, hp` → recurse on tail.
   - `.cons _ (.backwardE _) _, hp` → `hp.elim` (hp : False def-equally).
   - `.cons _ (.bidir _) _, hp` → `hp.elim`.

5. **`Walk.length_liftFromHardIntervention`**: trivial structural recursion.

6. **`theorem acyclic_preserved_under_do`**: outer structure unchanged.
   - Uses `G.refactor_IsAcyclic`, `G.refactor_IsTopologicalOrder`,
     `G.refactor_Pa`.
   - `refactor_IsAcyclic` def: `∀ v ∈ G, ¬ ∃ p, p.refactor_IsDirectedWalk ∧ p.refactor_length ≥ 1`.
   - `refactor_IsTopologicalOrder` = `refactor_IsTotalOrder` (3-field) ∧
     parent precedence via `refactor_Pa`.
   - `refactor_Pa` unfolds to `{w | w ∈ G ∧ (w, v) ∈ G.E}` — same shape as
     pre-refactor (E unchanged structurally; just lifted through `refactor_CDMG`).
   - Use refactor twins of all helpers in the body.

## Steps
1. Spawn a port-Lean worker to wrap originals + add REPLACEMENT block,
   then run `lake build` to verify.
2. After PASS: dispatch design-comment enrichment (`add_design_choice_comments`
   for the refactor twin; the original comments are extensive and serve as
   the template).
3. `solved` → strict-equivalence gate (the row's `proven` is currently `n/a`
   — but on refactor rows the strict gate validates against the LN, so the
   `proven` field is set by the prior solved-version's value, which was
   `proven`).

## Notes
- Original tex statement + proof files are untouched (LN math unchanged).
  No tex twin needed for the proof since it's an LN-level proof; the
  refactor briefing says claim rows DO get a tex twin but the proof's math
  doesn't change — only Lean encoding does. So the tex twin would be
  identical to the original. Confirm with the briefing's wording on tex
  twin for refactor rows where the proof is LN-level.

  Actually re-reading the briefing: claim rows refactor MUST use a tex twin
  `refactor_<ref>_proof_<title>.tex`. Even if the math is identical, the
  twin must exist (cleanup renames it over the original). Will need to
  create that file.
