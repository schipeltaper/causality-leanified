# Workspace for claim_3_19 — MarginalizingOutThe (REFACTOR DEPENDENT, `cdmg_typed_edges`)

## TL;DR — what we're porting

Row `claim_3_19` is pulled into refactor `cdmg_typed_edges` because two roots changed
underneath it:

- `def_3_1` (CDMG): `L : Finset (Node × Node) + hL_symm` → `L : Finset (Sym2 Node)`, no `hL_symm`, `hL_irrefl` phrased as `¬ s.IsDiag`.
- `def_3_4` (Walks): `WalkStep` is now a typed inductive `.forwardE / .backwardE / .bidir`; `Walk.cons` drops the ordered-pair field and the Prop-witness, takes `s : refactor_WalkStep` instead. All walk predicates (`IsDirectedWalk`, `IsBifurcationWithSplit`, ...) case-split on the WalkStep constructor.

Mathematical content of the claim is unchanged. We're producing *replacement* artefacts that live alongside the originals; Phase 7 cleanup deletes originals and renames `refactor_*` → bare name.

**Sibling model (near-perfect): `refactor_addInterventionNodes_comm_swig` in `AddingInterventionNodesSwig.lean:1190-1453`. Same `refactor_eqViaNodeMap (LHS, RHS, bijection)` shape; same J/V/E mechanical port + Sym2-restructured L sub-goal.**

## Files to touch — and only these

- `leanification/Chapter3_GraphTheory/Section3_2/MarginalizingOutThe.lean` (append AFTER original; wrap original main theorem with ORIGINAL markers; wrap every `refactor_*` decl with REPLACEMENT markers).
- `leanification/Chapter3_GraphTheory/Section3_2/tex/refactor_claim_3_19_proof_MarginalizingOutThe.tex` (CREATE — proof content identical to original `tex/claim_3_19_proof_MarginalizingOutThe.tex`; statement file has NO twin under this refactor).

No other files. No upstream edits.

## Substantive shape changes from original → refactor port

The original main theorem and its 8 helpers live at `MarginalizingOutThe.lean:126-852`. Concrete substitutions:

1. **Operands of `refactor_eqViaNodeMap`** (line 598-606 original):
   - `G.hardInterventionOn W _` → `G.refactor_hardInterventionOn W _` (sig in `HardInterventionOn.lean:809`). L is now `G.L.filter (fun s => ∀ v ∈ s, v ∉ W)` on `Finset (Sym2 Node)`.
   - `(G.nodeSplittingHard hG W hW).marginalize (W.image .copy0) _` → `(G.refactor_nodeSplittingHard hG W hW).refactor_marginalize (W.image refactor_SplitNode.copy0) _`. Marginalize's L is `(filter …).image (fun e => s(e.1, e.2))` over `Sym2` (sig in `MarginalizationAK.lean:1015`).
   - `eqViaNodeMap LHS RHS (toCopy1 W)` → `refactor_eqViaNodeMap LHS RHS (refactor_toCopy1 W)`. L-conjunct now `LHS.L.image (Sym2.map (refactor_toCopy1 W)) = RHS.L` (def at `TwoDisjointNode.lean:984-990`).

2. **Helper signatures**: `CDMG → refactor_CDMG`, `SplitNode → refactor_SplitNode`, `IsCADMG → refactor_IsCADMG`, `hardInterventionOn → refactor_hardInterventionOn`, `nodeSplittingHard → refactor_nodeSplittingHard`, `marginalize → refactor_marginalize`, `toCopy0 → refactor_toCopy0`, `toCopy1 → refactor_toCopy1`, `MarginalizationΦE → refactor_MarginalizationΦE`, `MarginalizationΦL → refactor_MarginalizationΦL`. Mechanical rename throughout.

3. **Walks** — pattern shapes change:
   - `Walk G u v` → `refactor_Walk G u v` (def at `Walks.lean:1507-1511`).
   - `Walk.cons v (u, v) h p` (4 args: middle, pair, proof, tail) → `refactor_Walk.cons v s p` (3 args: middle, typed step, tail).
   - **WalkStep construction sites** (originals at lines 280, 375): the original built `Walk.cons v (u, v) (Or.inl ⟨rfl, Or.inl h_edge⟩) (Walk.nil v hv_in)` for an E-edge length-1 walk. New form: `refactor_Walk.cons v (refactor_WalkStep.forwardE h_edge) (refactor_Walk.nil v hv_in)`. For an L-edge: `refactor_Walk.cons v (refactor_WalkStep.bidir h_edge) (refactor_Walk.nil v hv_in)`. No `Or.inl ⟨rfl, …⟩` proof construction needed at WalkStep level — the typed inductive carries the membership witness directly.
   - `Walk.IsDirectedWalk` — pattern matches `.cons _ a _ p` with conjunction `a = (u, v) ∧ a ∈ G.E ∧ p.IsDirectedWalk` change to constructor case: `.cons _ (.forwardE _) p => p.refactor_IsDirectedWalk` (other constructors → False). Destructuring `obtain ⟨ha_eq, ha_E, hq_dir⟩` becomes a direct pattern match on `.forwardE _` followed by recursion.
   - `Walk.IsBifurcationWithSplit` (10-case definition at `Walks.lean:2444-2454`). At index 0 with cons-cons body, the original's "left-arm-E OR left-arm-L" disjunction splits into TWO constructor branches in the refactor: `.backwardE` and `.bidir` (both yield `p.refactor_IsDirectedWalk` on the tail in the cons-cons case). The `.forwardE` branch at index 0 cons-cons is `False` (it's not a valid left-arm direction).
   - `Walk.vertices` / `Walk.length` → `refactor_vertices` / `refactor_length` (same recursion, 3-arg cons pattern).
   - `WalkStep` (def_3_3 helper used as `Walk.IsDirectedWalk` unfolder via `obtain`) is replaced by direct constructor pattern matching — see `swig_bif_with_split_cons_form` adjustment in §Subtask sequence.

4. **Φ_E and Φ_L predicate signatures**: `refactor_MarginalizationΦE` (sig at `MarginalizationAK.lean:814-820`) and `refactor_MarginalizationΦL` (`MarginalizationAK.lean:836-842`) have the same shape as originals but retargeted on `refactor_Walk` / `refactor_IsDirectedWalk` / `refactor_IsBifurcation` / `refactor_vertices` / `refactor_length`. The symmetric `Or` over walk orientations in Φ_L is preserved (semantically meaningful even though no `hL_symm` field consumes it).

5. **Clause (d) L sub-goal**: substantive refactor.
   - Pre-rewrite LHS (the conjunct goal): `(G.refactor_hardInterventionOn W _).L.image (Sym2.map (refactor_toCopy1 W)) = (refactor_marginalize…).L`.
   - After `change` to unfold: `(G.L.filter (fun s => ∀ v ∈ s, v ∉ W)).image (Sym2.map (refactor_toCopy1 W)) = (((swig.V \ W^o) ×ˢ (swig.V \ W^o)).filter (fun e => e.1 ≠ e.2 ∧ swig.refactor_MarginalizationΦL W^o e.1 e.2)).image (fun e => s(e.1, e.2))`.
   - Strategy: `Finset.ext` + pointwise constructor-bidir. Forward: `Finset.mem_image.mp` extracts source `s : Sym2 Node` with `s ∈ G.L`, plus `∀ v ∈ s, v ∉ W` filter witness. To prove membership in the RHS image, we need a witness pair `(e.1, e.2) ∈ filter` with `s(e.1, e.2) = Sym2.map (refactor_toCopy1 W) s`. The natural choice: use `Sym2.ind` on `s` to write `s = s(a, b)`, then `Sym2.map (refactor_toCopy1 W) s(a, b) = s(refactor_toCopy1 W a, refactor_toCopy1 W b)`. Pick the witness pair `(refactor_toCopy1 W a, refactor_toCopy1 W b)`. From `∀ v ∈ s, v ∉ W` derive `a ∉ W ∧ b ∉ W` via `Sym2.mem_iff`, hence `refactor_toCopy1 W a = .unsplit a` and `refactor_toCopy1 W b = .unsplit b`. Build swig.L membership analogous to the original (via `Sym2.map_pair` + `Finset.mem_image`), then close on the Φ_L iff via `swig_marginalization_phi_L_W_copy0_iff` REFACTOR twin.
   - **Sym2 API we'll need**: `Sym2.ind` / `Sym2.inductionOn` (to destructure an unknown `Sym2`), `Sym2.mem_iff` (`v ∈ s(a, b) ↔ v = a ∨ v = b`), `Sym2.map` (pointwise lift), `Sym2.map_pair` (`Sym2.map f s(a, b) = s(f a, f b)`), `Sym2.mk_isDiag_iff` (`s(a, b).IsDiag ↔ a = b`). All used in similar shape inside `refactor_marginalize_hL_subset` (`MarginalizationAK.lean:910-924`) and `refactor_marginalize_hL_irrefl` (`MarginalizationAK.lean:934-945`) — read those for the canonical idiom.
   - **NOT a one-shot `Sym2.map_map` collapse** like sibling claim_3_15's clause (d). The sibling's clause (d) was image-of-image; this row's clause (d) is image-of-filter-of-image vs image-of-filter-of-product — fundamentally a `Finset.ext` argument that uses Φ_L iff to bridge the two encodings of "L-edge after marginalisation". The sibling pattern is *informational* (shows how `Sym2.map`/`Sym2.map_map`/`Sym2.map_congr` are used), not directly applicable to the proof skeleton.

6. **`marginalize`'s noncomputable propagates**: `refactor_marginalize` is `noncomputable` (uses classical decidability for Φ_E/Φ_L). The main theorem need not be `noncomputable`, but `set_option maxHeartbeats 800000 in` is preserved verbatim from the original.

## Marker plan

- **ORIGINAL block** — wrap *only* the main theorem `marginalize_swig_eq_doit` (statement + proof body, lines 598-852). Marker name uses the actual Lean identifier (NOT the row title `MarginalizingOutThe`):
  ```
  -- REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize_swig_eq_doit
  theorem marginalize_swig_eq_doit (G : CDMG Node) (hG : G.IsCADMG) ...
    := by
      refine ⟨?_, ?_, ?_, ?_⟩
      ...
  -- REFACTOR-BLOCK-ORIGINAL-END: marginalize_swig_eq_doit
  ```
  The 8 private helpers (lines 126-387) stay un-marked — they are `private` and only support the main theorem; the cleanup script's strict refusal rule applies to top-level `refactor_*` declarations, NOT to pre-existing `private` originals.

- **REPLACEMENT blocks** — every net-new `refactor_*` declaration needs its own marker pair (cleanup script REFUSES otherwise — privacy doesn't exempt). Concretely:
  - `refactor_subset_J_union_V_of_subset_V` (private)
  - `refactor_image_copy0_subset_nodeSplittingHard_V` (private)
  - `refactor_swig_edge_source_notMem_W_copy0` (private)
  - `refactor_swig_vertices_ne_nil` (private)
  - `refactor_swig_middle_vertex_mem_tail_dropLast` (private)
  - `refactor_swig_marginalization_phi_E_W_copy0_iff` (private)
  - `refactor_swig_bif_with_split_cons_form` (private)
  - `refactor_swig_marginalization_phi_L_W_copy0_iff` (private)
  - `refactor_marginalize_swig_eq_doit` (the main theorem)

  Each wrapped as e.g.:
  ```
  -- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marginalize_swig_eq_doit (was: refactor_marginalize_swig_eq_doit)
  theorem refactor_marginalize_swig_eq_doit ... := by ...
  -- REFACTOR-BLOCK-REPLACEMENT-END: marginalize_swig_eq_doit
  ```
  Use the actual Lean identifier on the BEGIN/END line (no `refactor_` prefix in the marker name; the `refactor_` is on the declaration, the cleanup script renames to the marker name).

## Subtask sequence (commits, in order)

Each numbered step is ~one commit. Build green after each step (`lake build` from repo root). Suggested ordering: tex twin first (zero Lean compilation risk), then Lean helpers small-to-large, then the main theorem (largest, depends on all helpers).

### 1. Create tex proof twin
Worker: `write_tex_proof` (or `expand_proof`).
File: `leanification/Chapter3_GraphTheory/Section3_2/tex/refactor_claim_3_19_proof_MarginalizingOutThe.tex`.
Content: byte-identical copy of `tex/claim_3_19_proof_MarginalizingOutThe.tex` (the proof's math is unchanged — only the Lean encoding changes; the tex describes the LN-level argument). No statement twin (refactor doesn't change the LN statement of `claim_3_19`).
Rationale: tex first because (i) zero Lean compile risk; (ii) gives the prover worker a reference document while assembling clause (d).

### 2. Add ORIGINAL markers around `marginalize_swig_eq_doit`
Worker: `formalize_claim_in_lean` (or a small inline edit).
Edit: wrap the existing `theorem marginalize_swig_eq_doit ... := by ...` (lines 598-852) with ORIGINAL-BEGIN / ORIGINAL-END markers. NO content change.
Verify: `lake build` still green; no rename, no semantic change.
Rationale: needed by Phase 7 cleanup; do it standalone so any later steps can be reverted without losing the markers.

### 3. Append imports & variable + small mechanical helpers
Worker: `formalize_claim_in_lean`.
Append AFTER the original (after end Causality of the ORIGINAL block, OR inside a fresh `namespace refactor_CDMG` block — pick the latter, mirroring sibling). Includes:
- `namespace refactor_CDMG` + `variable {Node : Type*} [DecidableEq Node]`. No marker on the `variable` line (sibling claim_3_15 does mark it, mirror that — but read sibling line 795-799 first; if our sibling adds a `variable_Node` REPLACEMENT, copy that pattern verbatim).
- `refactor_subset_J_union_V_of_subset_V` — straight rename, `CDMG → refactor_CDMG`. Body byte-identical.
- `refactor_image_copy0_subset_nodeSplittingHard_V` — rename + adjust the `change` target: `(G.V \ W).image refactor_SplitNode.unsplit ∪ W.image refactor_SplitNode.copy0`. Body byte-identical otherwise.
Both wrapped with REPLACEMENT markers individually.
Verify: `lake build` green.

### 4. Walk-structural helpers (`vertices_ne_nil`, `middle_vertex_mem_tail_dropLast`)
Worker: `formalize_claim_in_lean`.
- `refactor_swig_vertices_ne_nil`: rename `Walk → refactor_Walk`, `Walk.vertices → refactor_vertices`. The pattern matches change: `.cons _ _ _ _ => …` (4 args) becomes `.cons _ _ _ => …` (3 args). Each case body is `simp [refactor_vertices]`.
- `refactor_swig_middle_vertex_mem_tail_dropLast`: substantive shape adjustment. Original signature took two `c : Node × Node` ordered pairs and two `h : WalkStep` proofs (lines 230-234); refactor signature takes two `s : refactor_WalkStep` typed steps and drops the ordered pairs:
  ```
  refactor_swig_middle_vertex_mem_tail_dropLast
      {a b : refactor_SplitNode Node} (w : refactor_SplitNode Node)
      (s : refactor_WalkStep (G.refactor_nodeSplittingHard hG W hW) a w)
      {bMid : refactor_SplitNode Node}
      (s' : refactor_WalkStep (G.refactor_nodeSplittingHard hG W hW) w bMid)
      (r : refactor_Walk (G.refactor_nodeSplittingHard hG W hW) bMid b) :
      w ∈ (refactor_Walk.cons w s (refactor_Walk.cons bMid s' r))
            .refactor_vertices.tail.dropLast
  ```
  Body adjustment: `change w ∈ (a :: w :: r.refactor_vertices).tail.dropLast`, then `List.tail_cons`, `List.dropLast_cons_of_ne_nil hr_ne`, `List.mem_cons.mpr (Or.inl rfl)` — same proof, retargeted.
Both wrapped with REPLACEMENT markers. Build green.

### 5. Edge-source helper `refactor_swig_edge_source_notMem_W_copy0`
Worker: `formalize_claim_in_lean`.
Original at lines 201-212. Body uses `Walk.cons v (u, v) (Or.inl …) ...` and unfolds `toCopy1` to discriminate. The refactor version:
- Rename: `CDMG → refactor_CDMG`, `SplitNode → refactor_SplitNode`, `toCopy1 → refactor_toCopy1`, `nodeSplittingHard → refactor_nodeSplittingHard`. The `change e ∈ G.E.image (fun e => (refactor_toCopy1 W e.1, refactor_toCopy0 W e.2)) at he` is the unfolding.
- `obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he` then `unfold refactor_toCopy1 at hweq` then `split_ifs at hweq <;> contradiction`. Same recipe.
Wrapped with REPLACEMENT markers. Build green.

### 6. Φ_E iff helper `refactor_swig_marginalization_phi_E_W_copy0_iff`
Worker: `formalize_claim_in_lean`.
Original at lines 249-285. Substantive refactor:
- Pattern matches on `Walk.cons w a h q` (4 args) become `refactor_Walk.cons w s q` (3 args, where `s : refactor_WalkStep`).
- The `simp only [Walk.IsDirectedWalk] at hp_dir; obtain ⟨ha_eq, ha_E, hq_dir⟩` step becomes: case-split on `s` via `match s with | .forwardE h_edge => …` (or `cases s`). Only `.forwardE` survives (others give `False` from `refactor_IsDirectedWalk`); we have `h_edge : (u, v) ∈ swig.E` directly.
- The length-1 walk construction at the bottom: `Walk.cons v (u, v) (Or.inl ⟨rfl, Or.inl h_edge⟩) (Walk.nil v hv_in)` → `refactor_Walk.cons v (refactor_WalkStep.forwardE h_edge) (refactor_Walk.nil v hv_in)`. Where `h_edge : (u, v) ∈ swig.E`.
- The directed-walk Prop proof `⟨rfl, h_edge, trivial⟩` becomes `trivial` for the recursive case in the unfolded `refactor_IsDirectedWalk` (or `(.forwardE h_edge).rec` style if needed — but most likely just `trivial` since the unfold gives `(.nil _ _).refactor_IsDirectedWalk = True`).
- Length proof `0 + 1 ≥ 1; omega` should still work with `refactor_length`.
- The `simp [Walk.vertices, List.tail]` for the empty-intermediate check becomes `simp [refactor_vertices, List.tail]`.
Wrapped with REPLACEMENT markers. Build green.

### 7. Bif-with-split cons-form helper `refactor_swig_bif_with_split_cons_form`
Worker: `formalize_claim_in_lean`.
Original at lines 288-297. Signature drops one `c : Node × Node` and one `h : WalkStep` argument (replaced by typed `s`):
```
refactor_swig_bif_with_split_cons_form ... :
    ∀ {a b : refactor_SplitNode Node} (q : refactor_Walk (G.refactor_nodeSplittingHard hG W hW) a b) (i : ℕ),
      q.refactor_IsBifurcationWithSplit i →
      ∃ (mid : refactor_SplitNode Node)
        (s : refactor_WalkStep (G.refactor_nodeSplittingHard hG W hW) a mid)
        (r : refactor_Walk (G.refactor_nodeSplittingHard hG W hW) mid b),
        q = refactor_Walk.cons mid s r
  | _, _, .nil _ _, _, hSpl => by simp only [refactor_IsBifurcationWithSplit] at hSpl
  | _, _, .cons mid s r, _, _ => ⟨mid, s, r, rfl⟩
```
Wrapped with REPLACEMENT markers. Build green.

### 8. Φ_L iff helper `refactor_swig_marginalization_phi_L_W_copy0_iff`
Worker: `formalize_claim_in_lean` (heavier; may need `prove_claim_in_lean` follow-up).
Original at lines 304-387. The substantive port:
- Inner `bifSplitAux` induction:
  - Index 0 case: pattern matches on `.cons w c h q` (4-arg) → `.cons w s q` (3-arg). Then case-split on `s : refactor_WalkStep`:
    - `.forwardE h`: at index 0 with cons-cons body in `refactor_IsBifurcationWithSplit` is `False` (per `Walks.lean:2449`). With nil body also `False`. So `.forwardE` case absurd, close with `exact hSpl.elim` or similar.
    - `.backwardE h_edge`: at index 0 with nil body is `False`; with cons-cons body is `p.refactor_IsDirectedWalk`. Cons-cons subcase: need to derive contradiction — `w` (the middle vertex) is the source of the next edge in the IsDirectedWalk q, so `w ∉ W^o` by `refactor_swig_edge_source_notMem_W_copy0`, contradicting `hInter w ⟨…⟩`.
    - `.bidir h_L`: at index 0 with nil body is `True` AND nil body bidir case gives `(a, b) ∈ swig.L` directly. With cons-cons body is `p.refactor_IsDirectedWalk`; same contradiction shape as the backwardE cons-cons subcase.
  - Index `k + 1` case: `.cons w s q, k + 1` shape. Case-split on `s`:
    - `.forwardE h`: `False` per `Walks.lean:2452`. Absurd.
    - `.backwardE h_edge`: recurses to `q.refactor_IsBifurcationWithSplit k`. This is the inductive step — derive contradiction by extracting cons-form of `q` via `refactor_swig_bif_with_split_cons_form`, then `refactor_swig_middle_vertex_mem_tail_dropLast` + `refactor_swig_edge_source_notMem_W_copy0`.
    - `.bidir h`: `False` per `Walks.lean:2454`. Absurd.
- Outer `constructor` shape: the forward direction is the `bifSplitAux` induction; the reverse direction constructs the length-1 walk via `refactor_Walk.cons v (refactor_WalkStep.bidir h_L) (refactor_Walk.nil v hv_in)` (where `h_L : s(u, v) ∈ swig.L`).
- **Critical detail on reverse direction**: the original uses `Or.inl ⟨…, ⟨rfl, h_edge⟩⟩` to construct the bifurcation witness at index 0. In the refactor, the `refactor_IsBifurcationWithSplit (.cons _ (.bidir _) (.nil _ _)) 0 = True`, so the witness simplifies to `trivial` (or unfolds to a single `True`).
- The `hL_irrefl` invocation: original uses `(G.nodeSplittingHard …).hL_irrefl h_edge` which returned `u ≠ v`; refactor's signature returns `¬ s(u, v).IsDiag`. To get `u ≠ v` from `¬ s(u, v).IsDiag`, use `Sym2.mk_isDiag_iff` (`s(a, b).IsDiag ↔ a = b`) and contrapose. Alternative: derive `u ≠ v` inline via `fun h_eq => hL_irrefl _ ((Sym2.mk_isDiag_iff).mpr h_eq)`.
- The `hL_symm` invocation in the original outer constructor's reverse-walk branch (`(G.nodeSplittingHard hG W hW).hL_symm (bifSplitAux i p hi hp_inter)`) DISAPPEARS — under `Sym2`, `s(u, v) = s(v, u)` is definitional, so no symmetry call is needed. The two `Or` branches of Φ_L both yield the SAME `s(u, v)` membership in swig.L.
Wrapped with REPLACEMENT markers. Build green.

### 9. Main theorem `refactor_marginalize_swig_eq_doit`
Worker: `formalize_claim_in_lean` (statement + sorry body); then `prove_claim_in_lean` (body).
Signature:
```
set_option maxHeartbeats 800000 in
theorem refactor_marginalize_swig_eq_doit (G : refactor_CDMG Node) (hG : G.refactor_IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V) :
    refactor_eqViaNodeMap
        (G.refactor_hardInterventionOn W (refactor_subset_J_union_V_of_subset_V hW))
        ((G.refactor_nodeSplittingHard hG W hW).refactor_marginalize
            (W.image refactor_SplitNode.copy0)
            refactor_image_copy0_subset_nodeSplittingHard_V)
        (refactor_toCopy1 W) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- clause (a) J
  · -- clause (b) V
  · -- clause (c) E
  · -- clause (d) L
```
Wrapped with REPLACEMENT markers.

**Clauses (a) and (b)**: pure `Finset.image` chasing on J and V fields. Bodies port mechanically — every `Finset.image_congr`, `Finset.image_union`, `Finset.mem_sdiff`, `Finset.mem_image` step carries over. No Sym2 involvement (J / V are not on the L channel). The `unfold refactor_toCopy1` + `if_pos / if_neg` discriminator logic is byte-identical to the original `toCopy1`. Expect ~30 lines each, line-for-line port of original 624-680.

**Clause (c) E**: same logic as original (lines 684-757). Uses `refactor_swig_marginalization_phi_E_W_copy0_iff` (the helper from step 6). Pattern: forward direction lifts `e ∈ G.E.filter` through `Prod.map (refactor_toCopy1 W) (refactor_toCopy1 W)`; reverse pulls back. The `change` rewrite of swig.E reads `G.E.image (fun e => (refactor_toCopy1 W e.1, refactor_toCopy0 W e.2))`. Body byte-for-byte port of original; ~70 lines.

**Clause (d) L**: the substantive port. Detailed strategy in §5 above. Sketch of tactic skeleton:
```
· change (G.L.filter (fun s => ∀ v ∈ s, v ∉ W)).image (Sym2.map (refactor_toCopy1 W))
      = (((swig.V \ W^o) ×ˢ (swig.V \ W^o)).filter
            (fun e => e.1 ≠ e.2 ∧ swig.refactor_MarginalizationΦL (W.image .copy0) e.1 e.2)).image
            (fun e => s(e.1, e.2))
  have hC0eqC1 : ∀ {x : Node}, x ∉ W → refactor_toCopy0 W x = refactor_toCopy1 W x := …
  have hToCopy1_unsplit : ∀ {x : Node}, x ∉ W → refactor_toCopy1 W x = refactor_SplitNode.unsplit x := …
  apply Finset.ext
  intro s_lift
  constructor
  · -- (⇒) take a lifted G.L element, show it lies in RHS image
    intro h_lift
    obtain ⟨s_src, hs_src_filter, rfl⟩ := Finset.mem_image.mp h_lift
    obtain ⟨hs_src_L, hs_src_notW⟩ := Finset.mem_filter.mp hs_src_filter
    -- Destructure s_src via Sym2.ind: s_src = s(a, b)
    induction s_src using Sym2.ind with | _ a b =>
    -- Now s_lift = Sym2.map (refactor_toCopy1 W) s(a, b) = s(refactor_toCopy1 W a, refactor_toCopy1 W b)
    have ha_notW : a ∉ W := hs_src_notW a (Sym2.mem_mk_left a b)
    have hb_notW : b ∉ W := hs_src_notW b (Sym2.mem_mk_right a b)
    have hab_V : a ∈ G.V ∧ b ∈ G.V := ⟨G.hL_subset hs_src_L (Sym2.mem_mk_left a b),
                                         G.hL_subset hs_src_L (Sym2.mem_mk_right a b)⟩
    have ha_ne_b : a ≠ b := fun h_eq => G.hL_irrefl hs_src_L (Sym2.mk_isDiag_iff.mpr h_eq)
    -- Build swig.L membership of s(refactor_toCopy0 W a, refactor_toCopy0 W b) = s(.unsplit a, .unsplit b)
    have h_swig_L : s(refactor_toCopy0 W a, refactor_toCopy0 W b) ∈
                      (G.refactor_nodeSplittingHard hG W hW).L := by
      change s(refactor_toCopy0 W a, refactor_toCopy0 W b) ∈
              G.L.image (Sym2.map (refactor_toCopy0 W))
      refine Finset.mem_image.mpr ⟨s(a, b), hs_src_L, ?_⟩
      rfl  -- Sym2.map_pair
    -- Take the RHS witness pair (.unsplit a, .unsplit b)
    refine Finset.mem_image.mpr ⟨(refactor_SplitNode.unsplit a, refactor_SplitNode.unsplit b), ?_, ?_⟩
    · -- pair ∈ filter
      refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
      · -- (.unsplit a, .unsplit b) ∈ (swig.V \ W^o) ×ˢ (swig.V \ W^o)
        refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · -- .unsplit a ∈ swig.V = (G.V \ W).image .unsplit ∪ W.image .copy0
            refine Finset.mem_union_left _ ?_
            exact Finset.mem_image.mpr ⟨a, Finset.mem_sdiff.mpr ⟨hab_V.1, ha_notW⟩, rfl⟩
          · -- .unsplit a ∉ W.image .copy0  (constructor mismatch)
            intro hContra
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
            cases hweq
        · -- symmetric for b
          …
      · -- .unsplit a ≠ .unsplit b   (from ha_ne_b via injection)
        intro h_eq; injection h_eq with h_inj; exact ha_ne_b h_inj
      · -- swig.refactor_MarginalizationΦL (W.image .copy0) (.unsplit a) (.unsplit b)
        exact (refactor_swig_marginalization_phi_L_W_copy0_iff G hG W hW _ _).mpr h_swig_L
    · -- s_lift = s(.unsplit a, .unsplit b)
      -- s_lift = Sym2.map (refactor_toCopy1 W) s(a, b) = s(.unsplit a, .unsplit b) by hToCopy1_unsplit
      show Sym2.map (refactor_toCopy1 W) s(a, b) = s(refactor_SplitNode.unsplit a, refactor_SplitNode.unsplit b)
      rw [Sym2.map_pair_eq]  -- or simp only [Sym2.map_pair]
      rw [hToCopy1_unsplit ha_notW, hToCopy1_unsplit hb_notW]
  · -- (⇐) take a pair from RHS image, show it's the lift of a G.L element
    intro h_pair
    obtain ⟨pair, h_pair_filter, rfl⟩ := Finset.mem_image.mp h_pair
    obtain ⟨h_prod, h_pair_ne, h_pair_phi⟩ := Finset.mem_filter.mp h_pair_filter
    have h_swig_L : pair ∈ (G.refactor_nodeSplittingHard hG W hW).L :=
      (refactor_swig_marginalization_phi_L_W_copy0_iff G hG W hW _ _).mp h_pair_phi
    -- Wait — refactor_swig_marginalization_phi_L_W_copy0_iff takes (u v : Node) — pair has Sym2 type now? NO: pair has type
    -- refactor_SplitNode Node × refactor_SplitNode Node (it's from the FILTER over an ordered-pair product, NOT the image).
    -- The iff helper bridges Φ_L with L membership; signature should be on the ordered-pair carrier u, v.
    -- BUT the swig.L is now Finset (Sym2 (refactor_SplitNode Node)). So the membership in swig.L is s(pair.1, pair.2) ∈ swig.L, not pair ∈ swig.L.
    -- Re-examine: the iff helper takes (u v) and asserts Φ_L u v ↔ s(u, v) ∈ swig.L (under refactor). State it that way.
    ...
```

**IMPORTANT correction to helper #8's iff statement**: under refactor, the helper `refactor_swig_marginalization_phi_L_W_copy0_iff` should conclude `s(u, v) ∈ (G.refactor_nodeSplittingHard hG W hW).L` (not `(u, v) ∈ … .L` — `.L` is `Finset (Sym2 …)`). Re-state it:
```
refactor_swig_marginalization_phi_L_W_copy0_iff
    (G : refactor_CDMG Node) (hG : G.refactor_IsCADMG) (W : Finset Node) (hW : W ⊆ G.V)
    (u v : refactor_SplitNode Node) :
    (G.refactor_nodeSplittingHard hG W hW).refactor_MarginalizationΦL
        (W.image refactor_SplitNode.copy0) u v
      ↔ s(u, v) ∈ (G.refactor_nodeSplittingHard hG W hW).L
```
Similarly for the Φ_E helper, conclusion stays `(u, v) ∈ swig.E` (E carrier didn't change shape).

Wrapped with REPLACEMENT markers. Build green.

### 10. Final verification
- `lake build` from repo root (mandatory).
- Spot-check: original `marginalize_swig_eq_doit` still compiles (build is green proves it).
- Spot-check: every `refactor_*` declaration in the new file is inside a REPLACEMENT marker pair (`grep -n REFACTOR-BLOCK` to enumerate).
- The tex twin exists at `tex/refactor_claim_3_19_proof_MarginalizingOutThe.tex`.

## Worker dispatch sequence (manager calls)

1. `spawn_agent_sub_task` worker=`write_tex_proof` (or `expand_proof`) → create the tex twin (Step 1).
2. `spawn_agent_sub_task` worker=`formalize_claim_in_lean` → ORIGINAL markers + small helpers (Steps 2-3). Single commit batch.
3. `spawn_agent_sub_task` worker=`formalize_claim_in_lean` → walk-structural helpers (Step 4).
4. `spawn_agent_sub_task` worker=`formalize_claim_in_lean` → edge-source helper (Step 5).
5. `spawn_agent_sub_task` worker=`formalize_claim_in_lean` → Φ_E iff helper (Step 6).
6. `spawn_agent_sub_task` worker=`formalize_claim_in_lean` → bif cons-form helper (Step 7).
7. `spawn_agent_sub_task` worker=`formalize_claim_in_lean` → Φ_L iff helper, body via `prove_claim_in_lean` (Step 8). This is the second-heaviest worker (after the main theorem); separate it from helpers 4-7 so its build cycle is isolated.
8. `spawn_agent_sub_task` worker=`formalize_claim_in_lean` → main theorem signature with `sorry` body (Step 9 frontload).
9. `spawn_agent_sub_task` worker=`prove_claim_in_lean` → main theorem body, clauses (a)/(b)/(c)/(d) (Step 9 backfill). May need 2-3 turns; clause (d) is the heavy lift.
10. (Optional) `spawn_agent_sub_task` worker=`verify_*` → final pass.

If any helper's port turns out harder than scoped (e.g., the Φ_L helper triggers a Sym2 API gap), the manager can `make_plan` mid-stream to recursively split that helper.

## Risks / known pitfalls

- **`Sym2.map_pair`**: confirm the canonical Mathlib name. Candidates: `Sym2.map_pair_eq`, `Sym2.map_mk` (lifts to `s(f a, f b)`). Read `refactor_marginalize_hL_subset` in `MarginalizationAK.lean:910-924` — that helper uses `Finset.mem_image.mp hs` + `Sym2.mem_iff.mp hv` + `rcases ... | rfl | rfl`, which suggests Mathlib's preferred idiom is via `Sym2.mem_iff` rather than `Sym2.map_pair`. Sibling claim_3_15 used `Sym2.map_map` + `Sym2.map_congr` — different idiom because it had image-of-image, not image-of-filter-of-image. Plan to start clause (d) with the `Sym2.mem_iff` route (mirrors `refactor_marginalize_hL_subset`); if that hits a snag, fallback to `Sym2.ind` + explicit pair manipulation.
- **`Sym2.mem_mk_left` / `Sym2.mem_mk_right`**: canonical Mathlib names may be `Sym2.mem_mk_left`, `Sym2.mem_mk_right`. Or `Sym2.mk_has_mem_left` / `Sym2.mk_has_mem_right`. Worker should grep Mathlib for these.
- **`hL_symm` removal in `swig_marginalization_phi_L_W_copy0_iff` reverse direction**: original calls `swig.hL_symm` once. Under refactor, no field exists; the symmetry is definitional via `Sym2`. The worker MUST drop this call (not search for a replacement) — the `Or` branch of Φ_L that triggered it now collapses to the same `s(u, v)` membership in swig.L by `Sym2.eq_swap`.
- **Pattern match exhaustiveness on `refactor_IsBifurcationWithSplit`**: the 10-case definition (vs 4 in original) means more `match` branches in the bifSplitAux induction. Make sure to handle ALL of `.forwardE`, `.backwardE`, `.bidir` at both index `0` and `k + 1`, with both `.nil _ _` and `cons _ _ _` tails. The `.forwardE` branches at index 0 (both nil and cons-cons) are `False` — absurd hypothesis; close via `simp only [refactor_IsBifurcationWithSplit] at hSpl; exact hSpl.elim` or similar.
- **`Sym2.ind` vs `Sym2.inductionOn`**: pick whichever Mathlib offers. The induction principle for Sym2 may need `cases s_src using Sym2.ind with | _ a b => …` syntax — verify by grepping Mathlib.
- **`Finset.image_filter` vs filter-then-image**: should NOT need this rewriter; the LHS and RHS of clause (d) are both already in `image (filter …)` form, just with different filter+map content. `Finset.ext` + pointwise is the right shape.
- **`maxHeartbeats`**: the original uses `set_option maxHeartbeats 800000 in`. Keep it. Clause (d) may need a bump; if so, bump to 1_600_000 or 2_400_000.

## Mode

REFACTOR (not disprove), prove direction. **No `MODE: disprove` signal**.

## READY

READY: spawn `write_tex_proof` worker on `tex/refactor_claim_3_19_proof_MarginalizingOutThe.tex` (copy contents from `tex/claim_3_19_proof_MarginalizingOutThe.tex` verbatim).
