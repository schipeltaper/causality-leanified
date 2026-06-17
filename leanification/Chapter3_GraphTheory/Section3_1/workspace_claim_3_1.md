# Workspace for claim_3_1 — CDMGRestrictions (REFACTOR row, dependent of def_3_1)

## Status
- Refactor: `cdmg_typed_edges`. Role: DEPENDENT. Root: def_3_1.
- Original Lean lives in `CDMGRestrictions.lean` — three theorems:
  `no_arrowhead_into_J`, `J_to_V_edge_admissible`, `J_nodes_not_adjacent`.
- Original tex proof at `tex/claim_3_1_proof_CDMGRestrictions.tex` (statement
  restated on top + 3-clause proof). Untouched throughout this row.
- Twin tex proof (target): `tex/refactor_claim_3_1_proof_CDMGRestrictions.tex` —
  does not yet exist; create with `write_tex_proof`.

## What changed in the root (def_3_1)
- `L : Finset (Node × Node)` → `Finset (Sym2 Node)`
- `hL_subset : ∀ ⦃e⦄, e ∈ L → e.1 ∈ V ∧ e.2 ∈ V`
  → `hL_subset : ∀ ⦃s⦄, s ∈ L → ∀ ⦃v⦄, v ∈ s → v ∈ V`
- `hL_irrefl : ∀ ⦃v1 v2⦄, (v1,v2) ∈ L → v1 ≠ v2`
  → `hL_irrefl : ∀ ⦃s⦄, s ∈ L → ¬ s.IsDiag`
- `hL_symm` field removed (Sym2 is definitionally symmetric).

Upstream notation defs (CDMGNotation.lean refactor blocks) already track this:
- `refactor_huh (G : refactor_CDMG Node) (v1 v2) : Prop := s(v1, v2) ∈ G.L`
- `refactor_hus := refactor_hut ∨ refactor_huh` (unchanged shape)
- `refactor_sus := refactor_tuh ∨ refactor_hut ∨ refactor_huh` (unchanged shape)

Upstream adjacency (EdgeRelations.lean):
- `refactor_adjacent := refactor_sus` (unchanged shape).

## Impact on the three theorems
1. `no_arrowhead_into_J` (uses `G.hus` and `G.hL_subset`):
   - Disjunction branch `(j, v) ∈ G.L` becomes `s(j, v) ∈ G.L`.
   - `obtain ⟨hjV, _⟩ := G.hL_subset h` →
     `have hjV : j ∈ G.V := G.hL_subset h (Sym2.mem_mk_left j v)` (or similar
     Mathlib API — leanifier will pick the canonical name).
2. `J_to_V_edge_admissible` (only touches `E` typing): **no change at all**.
3. `J_nodes_not_adjacent` (uses `G.adjacent` and `G.hL_subset`):
   - Same L-branch adaptation as (1).

## Plan (ordered)
1. `spawn_agent_sub_task` → `write_tex_proof` for the TWIN tex file
   `tex/refactor_claim_3_1_proof_CDMGRestrictions.tex`.
   - Restated statement: same three sub-claims, with the L-clauses updated
     to the Sym2 form (`s(j,v) ∉ L`, `s(j_1, j_2) ∉ L`) where appropriate,
     and the typing recital updated to mention `L ⊆ V × V / (swap)` as a
     Sym2 quotient with irreflexivity (and no separate symmetry axiom).
   - Proof body: structurally identical to original; only L-typing
     argument adapts to "every node of an L-edge lies in V" via Sym2
     membership.
2. `verify_tex_statement_plus_proof` (structural).
3. `verify_tex_proof` (mathematical).
4. `spawn_agent_sub_task` → `prove_claim_in_lean` for new
   `CDMGRestrictions.lean` block(s).
   - Wrap each existing theorem in `REFACTOR-BLOCK-ORIGINAL-BEGIN/END`
     and add corresponding `REFACTOR-BLOCK-REPLACEMENT-BEGIN/END` blocks
     immediately below, each with a `refactor_<name>` declaration over
     `refactor_CDMG Node` using `refactor_hus` / `refactor_adjacent`.
   - Preserve existing comment block context; adapt the L-step in
     the proofs of (i) and (iii).
5. `review_design` (MODE=normal — this is a port, equivalence to the
   already-reviewed pre-refactor design is the bar).
6. `verify_equivalence` (statement-vs-LN+addition for each new theorem).
7. `add_design_choice_comments` — capture the *why* of the L-step shift.
8. `solved`.

## Notes / risks
- Sym2 API names to double-check: `Sym2.mem_mk_left`, `Sym2.mem_mk_right`,
  `Sym2.mk_left_mem`, `Sym2.mk_right_mem`. Leanifier will resolve.
- The statement file `tex/claim_3_1_statement_CDMGRestrictions.tex` is NOT
  edited (only proof files are twinned). The twin proof's restated
  statement may lightly diverge from it — that's fine; main.tex does not
  include the statement file.
- The existing Lean's design-choice comments are very thorough and largely
  carry over verbatim; instruct leanifier to mirror them in the
  REPLACEMENT blocks and only annotate the L-step delta.

## prove_claim_in_lean (DEPENDENT port) — DONE
- Wrapped each original theorem in `CDMGRestrictions.lean` with
  `REFACTOR-BLOCK-ORIGINAL-BEGIN/END: <name>` markers using the exact
  Lean identifier (`no_arrowhead_into_J`, `J_to_V_edge_admissible`,
  `J_nodes_not_adjacent`).
- Added `namespace refactor_CDMG` with `refactor_<name>` replacement
  theorems wrapped in `REFACTOR-BLOCK-REPLACEMENT-BEGIN/END: <name>
  (was: refactor_<name>)` markers.
- Sym2 API used: `Sym2.mem_mk_left j v` (canonical Mathlib name confirmed
  in `Mathlib/Data/Sym/Sym2.lean:347`). Both `refactor_no_arrowhead_into_J`
  and `refactor_J_nodes_not_adjacent` extract `j ∈ G.V` via
  `G.hL_subset h (Sym2.mem_mk_left j v)` (resp. `(Sym2.mem_mk_left j₁ j₂)`).
- `refactor_J_to_V_edge_admissible` is identical to the original body
  (`Finset.mem_union_left _ hj, hv`) — clause is entirely about `E`
  typing, structurally invisible to the L-refactor.
- `lake build` passes cleanly (29s, 8287 jobs). No new warnings; the
  pre-existing `MarginalizingOutThe.lean` linter warnings are unaffected.
- No net-new helpers required — every port was a 1-line L-branch swap.
