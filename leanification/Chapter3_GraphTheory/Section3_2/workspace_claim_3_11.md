# Workspace for claim_3_11 — DisjointHardInterventions (SWIG analog)

## Row context
- **Refactor row**: `cdmg_typed_edges` (roots `def_3_1`, `def_3_4`)
- **Role**: DEPENDENT, caused by `def_3_1`
- **Main lean file**: `DisjointHardInterventionsSwig.lean`
- **Main tex proof**: `tex/claim_3_11_proof_DisjointHardInterventions.tex`
- **Refactor tex twin (to write)**: `tex/refactor_claim_3_11_proof_DisjointHardInterventions.tex`

## What changed upstream
`def_3_1` (CDMG) had its `L` field re-typed from `Finset (Node × Node)`
(with `hL_subset`, `hL_irrefl`, `hL_symm`) to `Finset (Sym2 Node)`
(with `Sym2.Mem`-based `hL_subset` and `¬ s.IsDiag`-based `hL_irrefl`;
no more `hL_symm` — definitional under `Sym2`).

## What this row's port needs
1. The theorem `disjointHardInterventionsAndNodeSplittingHardsCommute`
   signature does NOT mention `L` — its statement is unchanged.
2. The proof body uses `G.L.filter (fun e : Node × Node => …)` and
   `G.L.image (fun e : Node × Node => …)` — both broken under
   `Finset (Sym2 Node)` and need `Sym2.map`-style rewrites.
3. The inline `cdmgExt` helper destructures 9 fields including
   `hL_symm` — needs to drop `hL_symm`, drop `hL_subset` argument
   to match the new field shape.
4. The two non-`L` helpers (`subset_V_of_hardInterventionOn`,
   `image_unsplit_subset_carrier_of_nodeSplittingHard`) and
   `hardInterventionOn_isCADMG_of_isCADMG` don't touch `L` — unchanged.

## Direct model
The spl twin **claim_3_8** (`DisjointHardInterventions.lean`) was
just solved on this branch (commit 5457df2). Its refactor port is
the direct model — same L-section pattern, no SWIG/spl divergence
in the L-handling.

## Plan
1. Read claim_3_8 refactor tex twin + Lean to understand the model.
2. Read post-refactor `HardInterventionOn.lean` and `NodeSplittingHard.lean` for
   how `L` is now produced (Sym2 ops).
3. Dispatch `write_tex_proof` for the refactor tex twin (port,
   minimal divergence from existing proof — the L-section may
   need to discuss Sym2 framing of the registered deviation
   `hard_intervention_l_symmetrized_removal` now that symmetry is
   definitional).
4. verify_tex_statement_plus_proof + verify_tex_proof.
5. Port the Lean: REFACTOR-BLOCK-ORIGINAL/REPLACEMENT markers,
   `refactor_disjointHardInterventionsAndNodeSplittingHardsCommute`.
6. solved.

## Upstream refactor state (from Explore agent)

### def_3_10 (HardInterventionOn.lean, REPLACEMENT)
- L-field: `G.L.filter (fun s => ∀ v ∈ s, v ∉ W)` (endpoint-universal,
  symmetric definitionally).
- `refactor_hardInterventionOn` is the new name.
- Local instance `refactor_hardInterventionOn_decidable_bAll`
  (DecidablePred via `Sym2.recOnSubsingleton` + `Sym2.ball`) for the
  filter to elaborate.

### def_3_12 (NodeSplittingHard.lean, REPLACEMENT)
- L-field: `G.L.image (Sym2.map (refactor_toCopy0 W))`.
- `refactor_nodeSplittingHard` is the new name.
- Local `refactor_swig_toCopy0_inj` (four-case proof) used by
  `hL_irrefl`'s one-liner `Sym2.isDiag_map`.

### claim_3_8 (DisjointHardInterventions.lean, REPLACEMENT) — DIRECT MODEL
- Theorem: `refactor_disjointHardInterventionsAndNodeSplittingsCommute`
  over `refactor_CDMG Node`.
- Uses `refactor_subset_V_of_hardInterventionOn`,
  `refactor_image_unsplit_subset_carrier_of_nodeSplittingOn` (refactor
  versions of the helpers).
- L-section: `Finset.filter_image` + `Sym2.mem_map` + endpoint-universal
  predicate equivalence. **No mirror-pair logic, no symmetrisation.**
- `toCopy0_notMem_iff` lemma re-used (Node → Node, unchanged shape).

### def_3_11 (NodeSplittingOn.lean, REPLACEMENT)
- Same shape as def_3_12: `L := G.L.image (Sym2.map (refactor_toCopy0 W))`.

### Tex twin (refactor_claim_3_8_proof_DisjointHardInterventions.tex)
- L-axiom phrasing: "$L \subseteq V \times V$, irreflexive, symmetric"
  → "$L$ consists of unordered pairs of distinct vertices in $V$".
- L-section's "Registered two-sided removal of $L$" paragraph
  replaced with: under post-refactor `Sym2`, the LN's literal reading
  IS endpoint-universal; no symmetrisation step required.

## Implications for claim_3_11 port
- The theorem signature, the three helpers, and the J/V/E sections of
  the proof are essentially **mechanically portable** from `CDMG`/
  `hardInterventionOn`/`nodeSplittingHard` to `refactor_CDMG`/
  `refactor_hardInterventionOn`/`refactor_nodeSplittingHard`.
- The L-section needs the same Sym2 rewrite pattern claim_3_8 used.
- `cdmgExt` helper destructures 9 fields → 8 (drop `hL_symm`).
- Helpers need refactor twins (because their signatures mention
  the refactored types).
- `acyclic_preserved_under_do` (claim_3_3) presumably has a refactor
  version — the worker should look it up.

## Running log
- 2026-06-18: First turn. Workspace initialized. Explore agent run.
  About to dispatch refactor tex twin writer (Manager B style — this
  row is a refactor dep, the statement type doesn't change for the
  end-user but the proof body does).
- 2026-06-18: Refactor port complete. Wrapped originals in
  REFACTOR-BLOCK-ORIGINAL markers (variable_Node,
  hardInterventionOn_isCADMG_of_isCADMG, subset_V_of_hardInterventionOn,
  image_unsplit_subset_carrier_of_nodeSplittingHard,
  disjointHardInterventionsAndNodeSplittingHardsCommute). Added
  REFACTOR-BLOCK-REPLACEMENT twins in `namespace refactor_CDMG` —
  decidability instance, three helper twins, and the main theorem twin
  `refactor_disjointHardInterventionsAndNodeSplittingHardsCommute`.
  L-section uses `Sym2.map (refactor_toCopy0 W₂)` + endpoint-universal
  filter `∀ v ∈ s, v ∉ W₁`; closes via `Sym2.mem_map` + pointwise
  `toCopy0_notMem_iff`. Eight-field `cdmgExt` (no `hL_symm`). `lake build`
  clean.
