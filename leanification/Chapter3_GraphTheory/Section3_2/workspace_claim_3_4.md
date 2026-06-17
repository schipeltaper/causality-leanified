# Workspace for claim_3_4 — HardInterventionsCommute (REFACTOR row)

## Status
DEPENDENT row in refactor `cdmg_typed_edges`; root `def_3_1`. Upstream
`def_3_10` (HardInterventionOn) already has its REPLACEMENT block in place
in `HardInterventionOn.lean` — provides `refactor_hardInterventionOn` on
`refactor_CDMG`. We port this row onto that twin.

## Pre-refactor structure (in `namespace CDMG`, `HardInterventionsCommute.lean`)
Two declarations (currently NOT wrapped in REFACTOR-BLOCK markers):

1. `variable {Node : Type*} [DecidableEq Node]` — helper (3-dash markers present).
2. `private lemma subset_carrier_of_hardInterventionOn` — helper (3-dash markers present).
3. `theorem hardInterventionsCommute` — main statement (2-dash markers present).
   - Inline `cdmgExt` is destructuring on 9 CDMG fields (incl. `hL_symm`).
   - J/V/E branches: pure set-algebra on `Finset Node` and
     `Finset (Node × Node)` — unchanged by refactor.
   - L branches: filter predicate `e.1 ∉ W ∧ e.2 ∉ W` on
     `Finset (Node × Node)` — must change to `∀ v ∈ s, v ∉ W` on
     `Finset (Sym2 Node)`.

## Porting plan

### Step 1 — Wrap originals + add REPLACEMENT twin
Wrap the existing `subset_carrier_of_hardInterventionOn` (helper) and
`hardInterventionsCommute` (main theorem) with
`REFACTOR-BLOCK-ORIGINAL-BEGIN/END` markers (separate pairs per declaration,
mirroring `claim_3_3` / `AcyclicPreservedUnderDo.lean`). Marker name = Lean
declaration name (not the row title).

Add a `namespace refactor_CDMG` block containing:
- `variable {Node : Type*} [DecidableEq Node]` wrapped with 3-dash helper markers.
- `private instance` for `DecidablePred (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W)`
  — copy of the one in `HardInterventionOn.lean` (which is `private` there, so
  not exported). Without this, `change` on our explicit filter syntax for the
  L-branch will not elaborate.
- `private lemma refactor_subset_carrier_of_hardInterventionOn` — body
  identical to original (pure set-algebra on `J/V/W`; nothing about `L`).
- `theorem refactor_hardInterventionsCommute` — port of the main theorem:
  - `cdmgExt` inline helper: destructure 8 CDMG fields, not 9 (drop `hL_symm`).
  - J/V/E branches: identical.
  - L branches: rewrite using
    `change (G.L.filter (fun s => ∀ v ∈ s, v ∉ W₁)).filter (fun s => ∀ v ∈ s, v ∉ W₂) = G.L.filter (fun s => ∀ v ∈ s, v ∉ W₁ ∪ W₂)`
    then `Finset.filter_filter` + `Finset.filter_congr` + show the predicate
    equivalence
    `(∀ v ∈ s, v ∉ W₁) ∧ (∀ v ∈ s, v ∉ W₂) ↔ ∀ v ∈ s, v ∉ W₁ ∪ W₂`.
    Each `v ∉ W₁ ∧ v ∉ W₂ ↔ v ∉ W₁ ∪ W₂` follows from
    `Finset.mem_union, not_or`. The bounded-forall split is by
    `forall_and` (or pointwise destructuring).

Conjunction (b) (W₂ then W₁) is identical with W₁ ↔ W₂ swap plus a
`Finset.union_comm W₁ W₂` rewrite — same as the original.

### Step 2 — Tex twin
Write `tex/refactor_claim_3_4_proof_HardInterventionsCommute.tex`:
- Statement block identical to the original (LN statement unchanged).
- Proof body adapted: drop the "Remark on the Lean encoding of L" paragraph
  (the deviation that paragraph documented is structurally resolved by the
  `Sym2` encoding) and replace with a short note explaining the `∀ v ∈ s, v ∉ W`
  filter reads identically under the union step (no `hL_symm` invoked).
- All other math identical to the original.

### Step 3 — Verifiers
- `verify_tex_statement_plus_proof` on the twin tex file (structural).
- `verify_tex_proof` on the twin (semantic).
- `add_design_choice_comments` on the refactor twin Lean block.
- `solved` → strict-equivalence gate runs against LN.

## Notes / non-obvious bits

- **Decidability instance.** `HardInterventionOn.lean` has a `private instance`
  `refactor_hardInterventionOn_decidable_bAll` for
  `DecidablePred (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W)`. Because it's
  `private`, it does NOT propagate to importers. Our file needs its own
  identical `private instance` (anywhere before the proof block that uses
  the filter syntax via `change`).

- **No tex statement-side rewrite needed.** This is the proof side of an
  already-formalized claim (statement was verified during the original
  `claim_3_4` run). The refactor briefing only mentions a proof twin for
  claim rows.

- **The "L plays a role" caveat from `claim_3_3` does NOT apply here.**
  `claim_3_4` is about CDMG equality on all four fields including `L`, so
  the L-side is load-bearing. Under the pre-refactor encoding the registered
  deviation `hard_intervention_l_symmetrized_removal` had to be cited in the
  proof's remark paragraph; under the post-refactor `Sym2` encoding the
  deviation is structurally resolved at the `def_3_10` row and no remark is
  needed — both sides simply use the literal LN filter "any endpoint in W"
  applied via `Finset.filter`.

- **`addition_to_the_LN` review.** Refactor row inherits the original row's
  addition verbatim. The original additions are about "no disjointness
  between W₁ and W₂" and "overlap with J permitted" — both untouched by the
  refactor. No edits needed.
