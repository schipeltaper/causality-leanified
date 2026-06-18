# Workspace for claim_3_16 — MargPreservesAncestors

## Initial state (2026-06-18)

**Refactor row.** Dependent in `cdmg_typed_edges`, pulled in by roots `def_3_1` (CDMG L now `Finset (Sym2 Node)`, no `hL_symm`, `hL_irrefl` via `¬ s.IsDiag`) and `def_3_4` (Walks now have typed `WalkStep` constructors `.forwardE`/`.backwardE`/`.bidir`; `Walk.cons` no longer carries `a : Node × Node`; many predicates rewritten).

**Scale.** Original `MargPreservesAncestors.lean` is 3855 lines:
- 5 main theorems (each `-- claim_3_16 -- start/end statement` wrapped):
  - `marginalize_preserves_ancestors` (sub-claim i, line 3326)
  - `marginalize_preserves_bifurcation` (sub-claim ii(a), line 3468)
  - `marginalize_preserves_bifurcation_with_source` (sub-claim ii(b), line 3562)
  - `marginalize_preserves_acyclic` (sub-claim iii(a), line 3655)
  - `marginalize_restricts_topological_order` (sub-claim iii(b), line 3815)
- 1 helper-marker block: `variable {Node : Type*} [DecidableEq Node]` (lines 110-112)
- ~70 helper lemmas/defs (no markers; proof-supporting only)

**Strategy.** PORT (not re-derive). The math is unchanged; only the encoding changes:
- `Walk.cons _ a hStep p` → `Walk.cons _ s p` where `s : WalkStep G u v` is `.forwardE h`/`.backwardE h`/`.bidir h`
- `(a, b) ∈ G.L` → `s(a, b) ∈ G.L` (Sym2 quotient)
- `G.hL_symm` invocations → delete (definitional under Sym2)
- `G.hL_irrefl` invocations → use `¬ s.IsDiag` form
- `Walk.IsDirectedWalk`, `Walk.IsBifurcation*`, etc. — pattern-match cases change (no `a` field, typed step branches)

**Tex twin.** Previous dependent claim rows in this refactor (e.g. `claim_3_15`) created `tex/refactor_claim_3_15_proof_*.tex` with only a small notational tweak to reflect L being `Sym2` quotient. Same expectation here — almost-verbatim copy with one notational sentence about L.

**Lean replacement file structure.** Use **same-file marker convention**:
- Every original declaration is wrapped in `-- REFACTOR-BLOCK-ORIGINAL-BEGIN/END: <FinalName>`.
- Each replacement gets `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN/END: <FinalName> (was: refactor_<FinalName>)` and is named `refactor_<FinalName>` so the build stays green.
- The 5 main theorems also have the `-- claim_3_16 -- start statement` / `-- claim_3_16 -- end statement` markers inside the replacement block (using their `refactor_` prefix for the declaration name).

**Ordering risk.** The file is bottom-up: helpers at the top, main theorems at the bottom. Replacement declarations need to come AFTER their dependencies' replacements. Since all dependencies live in this file, the replacement block must be a SECOND PASS over the file, with the replacements in the same order as the originals.

**Plan kicked off via `make_plan` next.**

## Plan (make_plan, 2026-06-18)

### Methodology

This row is a **dependent** in `cdmg_typed_edges`; the math is unchanged, only the encoding shifts. The whole file is one long bottom-up scaffold of walk surgery that culminates in five main theorems. We port the file **in-place** under same-file REFACTOR-BLOCK markers — every original `def` / `lemma` / `theorem` gets an ORIGINAL marker pair, every replacement gets a REPLACEMENT marker pair (with its identifier prefixed `refactor_*`). Because every declaration depends on the previously-declared helpers in the same file, the **replacement block must follow the original ordering**. We append all replacements as a *second pass* at the bottom of the file (after the original `end Causality`, opening a fresh `namespace Causality / CDMG` for the replacements), then close with another `end CDMG / end Causality`.

Net new declarations (no ORIGINAL counterpart) — e.g. `refactor_helper_lemma` we may need for a `Sym2`-irreflexivity helper — also get REPLACEMENT markers (no ORIGINAL pair).

### Refactor cheat-sheet (the *only* mechanical changes per batch)

| Pre-refactor pattern | Post-refactor replacement |
|---|---|
| `Walk G u v` (signature) | `refactor_Walk G u v` |
| `CDMG Node` (signature) | `refactor_CDMG Node` |
| `.cons v a hStep p` (pattern) | `.cons v s p` where `s : refactor_WalkStep G u v` |
| `.cons _ _ _ p` (4-arg skip) | `.cons _ _ p` (3-arg skip) |
| `.cons _ _ _ _` (full skip) | `.cons _ _ _` (full skip) |
| `Walk.cons w a hStep p` (constructor) | `refactor_Walk.cons w s p` |
| `(G.WalkStep u a v)` (Prop) | `refactor_WalkStep G u v` (Type, inductive) |
| `Or.inl ⟨ha_eq, Or.inl ha_E⟩` (forward-E witness) | `refactor_WalkStep.forwardE h_E` |
| `Or.inr ⟨ha_eq, ha_E⟩` (backward-E witness) | `refactor_WalkStep.backwardE h_E` |
| `Or.inl ⟨ha_eq, Or.inr ha_L⟩` (bidir witness) | `refactor_WalkStep.bidir h_L` |
| `obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir` (destructure IsDirectedWalk on cons) | drop — refactor_IsDirectedWalk on `.cons _ (.forwardE _) p` unfolds directly to `p.refactor_IsDirectedWalk`; pattern-match on the step at the cons level |
| `p.IsDirectedWalk` / `p.IsBifurcation` / etc. | `p.refactor_IsDirectedWalk` / `p.refactor_IsBifurcation` / etc. |
| `p.vertices` / `p.length` | `p.refactor_vertices` / `p.refactor_length` |
| `Walk.IsBifurcationWithSplit` on `.cons _ a _ (.nil _ _), 0` returning `a = (u, v) ∧ a ∈ G.L` | now `True` (when constructor is `.bidir _`); proof simplifies to `trivial` |
| `(u, v) ∈ G.L` (G.L : Finset (Node × Node)) | `s(u, v) ∈ G.L` (G.L : Finset (Sym2 Node)) |
| `G.hL_symm hLR` (returns `(v2, v1) ∈ G.L`) | **delete** — Sym2 swap is definitional |
| `G.hL_irrefl hLR` (returns `v1 ≠ v2`) | now returns `¬ s(v1, v2).IsDiag`; pull `v1 ≠ v2` out via `fun h => G.hL_irrefl hLR (Sym2.mk_isDiag_iff.mpr h)` (or define a small helper) |
| `G.hL_subset hLR` (returns `v1 ∈ G.V ∧ v2 ∈ G.V`) | now takes `s ∈ G.L` and `v ∈ s` to give `v ∈ G.V`; use `G.hL_subset hLR (Sym2.mem_mk_left v1 v2)` for v1 and `Sym2.mem_mk_right` for v2 |
| `Walk.edges` (deprecated/removed) | not used in this file — skip |
| `G.marginalize W hW` | `G.refactor_marginalize W hW` |
| `G.MarginalizationΦE` / `G.MarginalizationΦL` | `G.refactor_MarginalizationΦE` / `G.refactor_MarginalizationΦL` |
| Marg-E filter `(G.J ∪ (G.V \ W)) ×ˢ (G.V \ W).filter (… Φ_E …)` | same — E filter unchanged |
| Marg-L direct membership `(vL, vR) ∈ (G.marginalize …).L` (filter form) | now built via `.image (fun e => s(e.1, e.2))` over the filter; needs an `Finset.mem_image`-style proof to extract the ordered-pair witness, OR a derived `s(vL, vR) ∈ marg.L` for direct mem |
| Anc / IsAcyclic / IsTopologicalOrder | NOT yet refactored — they sit in unchanged `def_3_5` / `def_3_6` / `def_3_8`. Mismatch alert: the main theorems' conclusion `v₁ ∈ G.Anc v₂ ↔ v₁ ∈ (G.refactor_marginalize W hW).Anc v₂` — but `G.Anc` takes `CDMG Node`, NOT `refactor_CDMG Node`. **THIS IS THE CENTRAL OPEN PROBLEM** — see Risks section below. |

### Refactor risks / unresolved structural questions

**R1. The five main theorems mention `G.Anc`, `G.IsAcyclic`, `G.IsTopologicalOrder` — all rooted in `def_3_5` / `def_3_6` / `def_3_8`, which are NOT in the refactor root set.** This is a real problem because those defs take a `CDMG Node`, not a `refactor_CDMG Node`. Concretely:

  - `marginalize_preserves_ancestors`: signature `v₁ ∈ G.Anc v₂ ↔ v₁ ∈ (G.marginalize W hW).Anc v₂` — both sides reference `Anc` which lives in `FamilyRelationships.lean` (def_3_5), defined on `CDMG`. We need the analogous predicate on `refactor_CDMG`. Either:
    - **(a) escalate**: emit `refactor` with `NEW_ROOT_REF: def_3_5` (and probably also `def_3_6`, `def_3_8`). This restarts the whole refactor with a bigger root set. EXPENSIVE — loses all current progress including `claim_3_15`, `def_3_14` etc.
    - **(b) define refactor-side analogues locally** in this file: `refactor_Anc`, `refactor_IsAcyclic`, `refactor_IsTopologicalOrder` reaching only into the *un-refactored* CDMG types behind the scenes — NO, this doesn't typecheck because `Walk` is now `refactor_Walk` on the refactored side.
    - **(c) re-stage the main theorems against the refactor types only**: use `refactor_CDMG.Anc` (if it exists) or define inline an existential over `refactor_Walk … refactor_IsDirectedWalk` and prove against that.
    - **First action of Batch 0 below: read `FamilyRelationships.lean`, `Acyclicity.lean`, `TopologicalOrder.lean` to confirm whether they already carry `refactor_*` REPLACEMENT blocks or not.** If not, this row CANNOT proceed without one of (a)/(b)/(c).
    - **Likely answer (from sibling claim_3_13 / claim_3_14 / claim_3_15 having shipped successfully)**: these MUST have refactor-side analogues, because those rows depended on the same Anc/IsAcyclic/IsTopologicalOrder. Check siblings first.

**R2. `(vL, vR) ∈ marg.L` no longer typechecks** — marg.L is now `Finset (Sym2 Node)`. The original code repeatedly opens `Finset.mem_filter, Finset.mem_product` on the ordered-pair carrier. Under the refactor we need:

  - At construction sites: `s(vL_exit, vR_exit) ∈ marg.L` proved via `Finset.mem_image.mpr ⟨(vL_exit, vR_exit), …, rfl⟩`.
  - At consumption sites: from `s ∈ marg.L`, extract via `Finset.mem_image.mp` an ordered-pair `(e1, e2) : Node × Node` with `s = s(e1, e2)` and `(e1, e2) ∈ filter`.
  - A new helper lemma `refactor_marginalize_L_iff : s(vL, vR) ∈ (G.refactor_marginalize W hW).L ↔ (vL, vR) ∈ (((G.V \ W) ×ˢ (G.V \ W)).filter …)` may pay for itself across the ~8 sites that do this dance. Add as a **net-new helper** in Batch 1.

**R3. `Walk.IsBifurcationWithSplit` nil-tail at `i=0` returning `True` for bidir** — collapses several `⟨rfl, hLR⟩` proofs to `trivial`. Specifically `Walk.singleEdge_isBifurcation_of_bidir` (line 1561) and `Walk.isBifurcationWithSplit_mkBifurcationBidir` (line 1081). This is a NET SIMPLIFICATION — flag and exploit it.

**R4. `WalkStep.source_mem` (line 177)** has a proof that case-splits on the old `G.WalkStep` predicate's `Or.inl ⟨_, Or.inl ha_E⟩ | Or.inl ⟨_, Or.inr ha_L⟩ | Or.inr ⟨_, ha_E⟩`. Under the typed step it becomes a three-way `cases s with | forwardE h | backwardE h | bidir h => …`. Reads cleaner; **no logic change**, just constructor names.

**R5. The IsBifurcationWithSplit-style proofs of `Walk.exists_arms_of_bifurcation_directed_hinge_strong`, `Walk.exists_arms_of_bifurcation_bidir_hinge_strong`, `Walk.isBifurcationDirectedHinge_*`** all pattern-match deeply on `Walk.cons _ a hStep p, k`. The recursion shape is preserved under the refactor; only the destructuring of the cons-cell changes. Estimate: each gets +/- 30 lines of mechanical rewrites, no structural rework. **Watch for**: the `Or.inl ⟨h_E.1, h_E.2, hp'_dir⟩` proofs that derive a directed-hinge witness from a bidirected-hinge witness — these collapse cleanly under typed constructors.

### Declaration inventory

| # | Lines | Name | Kind | Porting class | Notes |
|---|---|---|---|---|---|
| 0 | 110–112 | `variable {Node} [DecidableEq Node]` | variable + marker | mechanical | wrap in REPLACEMENT only (no ORIGINAL marker needed — it's not a declaration); same as `MarginalizationAK.lean:797`'s `variable_Node` block |
| 1 | 133–136 | `Walk.comp` | def | mechanical | `Walk → refactor_Walk`; `.cons v a h p` pattern → `.cons v s p`; identifier→`refactor_Walk.refactor_comp` (or just `refactor_comp` if in namespace) |
| 2 | 138–144 | `Walk.length_comp` | lemma | mechanical | depends on (1); `Walk.length` → `Walk.refactor_length` (we don't redefine length — it's already refactored in Walks.lean); `Walk.comp` → `refactor_comp` |
| 3 | 146–152 | `Walk.isDirectedWalk_comp` | lemma | mechanical | depends on (1); `IsDirectedWalk` pattern destructuring `⟨h1, h2, h3⟩` changes: refactor IsDirectedWalk on `.cons _ (.forwardE _) p` unfolds directly to `p.refactor_IsDirectedWalk`, so we destructure with `cases hp` on `.forwardE` step pattern; ALSO needs `cases` on the cons-cell to extract |
| 4 | 156–159 | `Walk.vertices_ne_nil` | lemma | mechanical | `Walk.vertices` → `refactor_vertices`; `.cons _ _ _ _` → `.cons _ _ _` |
| 5 | 162–165 | `Walk.head_mem_vertices` | lemma | mechanical | same shape as (4) |
| 6 | 167–174 | `Walk.vertices_comp` | lemma | mechanical | depends on (1), (4); cons pattern shift |
| 7 | 177–190 | `WalkStep.source_mem` | lemma | **STRUCTURAL** | signature changes: takes `s : refactor_WalkStep G u v` not `(a, h) : (a) (h : G.WalkStep u a v)`; body becomes `cases s with | forwardE h | backwardE h | bidir h => …`; uses `G.hE_subset` for E cases, `G.hL_subset h (Sym2.mem_mk_left _ _)` for bidir case |
| 8 | 193–203 | `Walk.mem_of_mem_vertices` | lemma | mechanical | depends on (7); cons-cell destructure changes from `_ _ hStep p` to `_ s p`, then forward call to `WalkStep.refactor_source_mem` |
| 9 | 206–213 | `Walk.source_in_G_of_directedWalk_pos` | lemma | mechanical (small structural) | destructuring of `hp` changes — see note in cheat-sheet about IsDirectedWalk destructure |
| 10 | 216–231 | `Walk.target_in_GV_of_directedWalk_pos` | lemma | mechanical (small structural) | same as (9); `match q, hq_dir, hlen0 with | .nil _ _, _, _ => …` carries verbatim modulo step destructuring |
| 11 | 233–238 | `Walk.target_in_G_of_directedWalk_pos` | lemma | mechanical | depends on (10) |
| 12 | 242–248 | `mem_of_mem_marginalize` | lemma | mechanical | `G.marginalize` → `G.refactor_marginalize`; body shape unchanged (marg J/V fields unchanged) |
| 13 | 253–260 | `notW_of_mem_marginalize` | lemma | mechanical | same as (12) |
| 14 | 266–289 | `Walk.lt_of_directedWalk_pos` | lemma | mechanical (small structural) | IsDirectedWalk destructure as (9); `G.Pa` reference — see R1 (Pa is in def_3_5 / FamilyRelationships, may already be refactored) |
| 15 | 299–302 | `Walk.vertices_eq_head_cons_tail` | lemma | mechanical | trivial cons-skip pattern shift |
| 16 | 305–309 | `Walk.tail_vertices_ne_nil_of_pos` | lemma | mechanical | trivial cons-skip pattern shift |
| 17 | 326–457 | `expand_directed_walk_marginalize` | lemma | **HEAVY mechanical** | depends on (1)–(16); 130-line proof body with deep `induction p` + cons-cell destructure. Mostly mechanical (cons pattern shift, IsDirectedWalk destructure shift, `G.marginalize → G.refactor_marginalize`, `MarginalizationΦE` → `refactor_MarginalizationΦE`). Each WalkStep construction `Or.inl ⟨ha_eq, Or.inl h_edge_marg⟩` → `.forwardE h_edge_marg` |
| 18 | 472–536 | `find_first_non_W_directed` | lemma | **HEAVY mechanical** | depends on (1)–(16); 65-line proof; same patterns as (17). Pay attention to `Walk.cons vMid a hStep ...` rebuild → `refactor_Walk.cons vMid s_step ...` |
| 19 | 546–600 | `project_directed_walk_aux` | lemma | **HEAVY mechanical** | depends on (12)–(18); 55 lines. The marg-E construction `hStep_marg : (G.marg).WalkStep v₁ (v₁, m) m := Or.inl ⟨rfl, Or.inl h_edge_marg⟩` → `s_marg : refactor_WalkStep (G.refactor_marg) v₁ m := .forwardE h_edge_marg`. **Plus**: marg.L now Sym2-typed, so any `(v1, m) ∈ marg.E` reference is unchanged but membership *predicates* on marg.L change — careful audit needed |
| 20 | 605–610 | `project_directed_walk_marginalize` | lemma | mechanical (wrapper) | depends on (19) |
| 21 | 622–763 | `project_directed_walk_with_vertex_subset_aux` | lemma | **HEAVY mechanical** | depends on (12)–(18); 140-line proof body, mirrors (19) but with extra vertex-subset bookkeeping |
| 22 | 770–780 | `project_directed_walk_strong` | lemma | mechanical (wrapper) | depends on (21) |
| 23 | 783–787 | `Walk.length_pos_of_ne` | lemma | mechanical | cons-skip pattern shift |
| 24 | 796–802 | `Walk.reverseDirected` | def | **STRUCTURAL** | depends on (1), (7); the body builds `Walk.cons c a (Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩) (Walk.nil c (WalkStep.source_mem hStep))` → `refactor_Walk.cons c (.backwardE h_edge) (refactor_Walk.nil c (WalkStep.refactor_source_mem hStep))`. The `Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩` destructures into `(ha_eq, ha_E)` — under the refactor `hqv_dir` is now just the recursive `p.refactor_IsDirectedWalk` and the edge is read off the *step* `s`, not destructured from `hqv_dir`. **Watch carefully** — this is where the recursion shape changes the most. Specifically: `cases s with | forwardE h => Walk.cons c (.backwardE h) ...` |
| 25 | 804–812 | `Walk.length_reverseDirected` | lemma | mechanical | depends on (1), (24) |
| 26 | 814–827 | `Walk.vertices_reverseDirected` | lemma | mechanical | depends on (1), (24); `simp [Walk.vertices, …]` may need updates to `refactor_vertices` |
| 27 | 830–833 | `Walk.mkBifurcation` | def | mechanical | depends on (1), (24); wrapper, just type-retargets |
| 28 | 835–842 | `Walk.length_mkBifurcation` | lemma | mechanical | depends on (1), (27) |
| 29 | 844–851 | `Walk.vertices_mkBifurcation` | lemma | mechanical | depends on (1), (27) |
| 30 | 853–861 | `Walk.comp_assoc` | lemma | mechanical | depends on (1); cons-pattern shift |
| 31 | 863–871 | `Walk.isBifurcationDirectedHinge_cons_backward_of_directed` | lemma | **STRUCTURAL** | depends on (1); signature changes from `(a : Node × Node) (h : G.WalkStep u a v) (...) (ha_eq : a = (v, u)) (ha_mem : a ∈ G.E)` to taking `(h : (v, u) ∈ G.E)` directly + the WalkStep is the `.backwardE h` construction. Proof body shrinks because `.backwardE h` already pins the direction. |
| 32 | 873–904 | `Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux` | lemma | **HEAVY structural** | depends on (24), (30), (31); the `backStep` construction `Or.inr ⟨hqv_dir.1, hqv_dir.2.1⟩` becomes `.backwardE h_edge`; recursion structurally unchanged |
| 33 | 906–939 | `Walk.isBifurcationDirectedHinge_mkBifurcation` | lemma | **STRUCTURAL** | depends on (24), (27), (32); similar to (32) |
| 34 | 960–965 | `Walk.vertices_reverse_dropLast` | lemma | mechanical | independent — vertices-list manipulation |
| 35 | 968–973 | `Walk.mkBifurcationBidir` | def | **STRUCTURAL** | depends on (1), (24); body builds `Walk.cons vR (vL, vR) (Or.inl ⟨rfl, Or.inr hLR⟩) R` → `refactor_Walk.cons vR (.bidir hLR) R`. **Significantly simpler under typed steps.** Signature: `(hLR : (vL, vR) ∈ G.L)` → `(hLR : s(vL, vR) ∈ G.L)` |
| 36 | 975–984 | `Walk.length_mkBifurcationBidir` | lemma | mechanical | depends on (35) |
| 37 | 986–994 | `Walk.vertices_mkBifurcationBidir` | lemma | mechanical | depends on (35) |
| 38 | 997–1028 | `Walk.isBifurcationWithSplit_comp_reverseDirected_bidir_aux` | lemma | **STRUCTURAL** | depends on (24), (30); same backStep refactor as (32). Note: the `simp only [Walk.IsBifurcationWithSplit]` calls may unfold differently under the refactor; verify each. The `⟨hqv_dir.1, hqv_dir.2.1, hrest⟩` constructions need rephrasing because IsBifurcationWithSplit at `k+1` is now `p.refactor_IsBifurcationWithSplit k` directly (no extra conjuncts to bundle) |
| 39 | 1033–1063 | `Walk.isBifurcationWithSplit_comp_right_directed` | lemma | **HEAVY structural** | depends on (1), (3); match arms on `(0, .nil _ _, hM, .nil _ _, _)` etc. all need cons-pattern shift; the cons-cell predicate values also change (e.g. n=1 bidir at `i=0` is now `True` not `a = (u, v) ∧ a ∈ G.L`) — exploit simplification |
| 40 | 1067–1089 | `Walk.isBifurcationWithSplit_mkBifurcationBidir` | lemma | **STRUCTURAL** + simplification | depends on (35), (38); the `nil`-tail case where original returned `⟨rfl, hLR⟩` collapses to `trivial` under the new shape |
| 41 | 1096–1192 | `Walk.mkBifurcationBidir_isBifurcation` | lemma | **HEAVY mechanical** + Sym2 dance | depends on (35), (37), (40); 95-line proof body. Signature change: `(hLR : (vL, vR) ∈ G.L)` → `(hLR : s(vL, vR) ∈ G.L)`. Body is mostly list manipulation, but the IsBifurcation existential `L.length` index pinning the bidirected hinge no longer needs the `a = (u, v) ∧ a ∈ G.L` discharge. |
| 42 | 1206–1390 | `Walk.exists_arms_of_bifurcation_directed_hinge_strong` | lemma | **HEAVY structural** | depends on (1)–(33); 185-line proof body, deep `induction p` + cases on `i` + cases on `p'`. The `let forwardStep : G.WalkStep vMid a u := Or.inl ⟨ha_eq, Or.inl ha_mem⟩` constructions → `let s : refactor_WalkStep G vMid u := .forwardE h_E` (`h_E : (vMid, u) ∈ G.E`). The destructuring `obtain ⟨ha_eq, ha_mem, hp'_dir⟩ := h_unfold` for the directed-hinge predicate at `i = 0` also needs updates per new IsBifurcationDirectedHingeWithSplit shape. Big rewrite but no logic change |
| 43 | 1396–1505 | `Walk.mkBifurcation_isBifurcationSource` | lemma | **HEAVY mechanical** | depends on (24)–(33), (42); 110-line proof body; list-manipulation heavy; mechanical port |
| 44 | 1511–1531 | `Walk.isBifurcationDirectedHingeWithSplit_to_isBifurcationWithSplit` | lemma | **STRUCTURAL** | depends on (1); the cons-i=0-cons case `obtain ⟨ha_eq, ha_E, hp_dir⟩ := h; exact ⟨Or.inl ⟨ha_eq, ha_E⟩, hp_dir⟩` collapses because under typed steps both predicates' cons-i=0-cons case is `p.refactor_IsDirectedWalk` directly; the `Or.inl ⟨_, _⟩` disjunction is dissolved. Hence the proof becomes `exact h` (or near-trivial) for that branch. **Significant simplification.** |
| 45 | 1535–1540 | `Walk.isBifurcationSource_to_isBifurcation` | lemma | mechanical | depends on (44); destructure changes |
| 46 | 1545–1561 | `Walk.singleEdge_isBifurcation_of_bidir` | lemma | **STRUCTURAL** + simplification | depends on (1); signature `(hLR : (u, v) ∈ G.L)` → `(hLR : s(u, v) ∈ G.L)`; body's `let hStep` construction → typed step; the IsBifurcationWithSplit witness `exact ⟨rfl, hLR⟩` → `trivial` (per R3) |
| 47 | 1571–1770 | `Walk.exists_arms_of_bifurcation_bidir_hinge_strong` | lemma | **HEAVY structural** + Sym2 | depends on (1)–(46); 200-line proof body. The biggest single port in the file. Heavy use of `obtain ⟨ha_eq, ha_L⟩ := h_bif` (bidirected hinge); the resulting `(hLR : (u, v_nil) ∈ G.L)` → `(hLR : s(u, v_nil) ∈ G.L)`. The witness extraction from old `IsBifurcationWithSplit` shape disjunctions `h_alt : (a = (vMid, u) ∧ a ∈ G.E) ∨ (a = (u, vMid) ∧ a ∈ G.L)` collapses dramatically — under typed steps, the cons-cell's `s` IS the disjunction tag, so case-split on `s` (3 branches) instead of `h_alt` (2 branches). **One of the biggest simplifications.** |
| 48 | 1775–1838 | `marg_preserves_bifSource_forward` | lemma | mechanical | depends on (12)–(47); 65 lines, mostly list bookkeeping; mechanical port |
| 49 | 1843–1924 | `marg_preserves_bifSource_backward` | lemma | mechanical | depends on (12)–(48); 85 lines; mirrors (48) |
| 50 | 1932–1945 | `marg_bif_forward_dir_hinge_src_marg` | lemma | mechanical | depends on (44), (45), (48) |
| 51 | 1954–1969 | `marg_bif_backward_dir_hinge` | lemma | mechanical | depends on (8), (42), (44), (45), (49) |
| 52 | 1972–1979 | `Walk.vertices_getLast` | lemma | mechanical | independent recursion on Walk; cons-skip shift |
| 53 | 1983–1990 | `Walk.tail_getLast_of_pos` | lemma | mechanical | depends on (52); cons-skip shift |
| 54 | 1993–1998 | `Walk.length_pos_of_isBifurcation` | lemma | mechanical | depends on (1); cons-skip shift |
| 55 | 2005–2041 | `Walk.arm_dropLast_in_W` | lemma | mechanical | depends on (4), (15), (16), (52), (53), (54) |
| 56 | 2056–2388 | `marg_bif_backward_bidir_hinge` | lemma | **HEAVY mechanical** + Sym2 + delete hL_symm | depends on (1)–(55); 335 lines, the biggest single proof. **Contains line 2332 `G.hL_symm hMLR` → delete (use `hMLR` directly because Sym2 swap is definitional, `s(vMR, vML) = s(vML, vMR)`).** Many `Finset.mem_filter, Finset.mem_product` unfolds on marg.L need rewrites because marg.L is now Sym2-image. **Most Sym2-membership dancing happens here.** |
| 57 | 2399–2464 | `marg_bif_forward_bidir_both_notW` | lemma | **STRUCTURAL** + Sym2 + hL_irrefl | depends on (12)–(56); 65 lines. Contains line 2429 `G.hL_irrefl hLR_G` returning `vL ≠ vR` — now returns `¬ s(vL, vR).IsDiag`. Rewrite as: `have hvLvR_ne : vL ≠ vR := fun h => G.hL_irrefl hLR_G (Sym2.mk_isDiag_iff.mpr h)` or pull into a helper. The hStep construction `Or.inl ⟨rfl, Or.inr hLR_G⟩` → `.bidir hLR_G`. The single-edge walk → `refactor_Walk.cons vR (.bidir hLR_G) (refactor_Walk.nil vR hvR_g)`. The `(vL, vR) ∈ marg.L` membership via `Finset.mem_filter, Finset.mem_product` needs Sym2-image dance. |
| 58 | 2475–2517 | `marg_bif_forward_assemble_bidirected` | lemma | **STRUCTURAL** + Sym2 | depends on (12)–(57); same Sym2-image dance for marg.L membership |
| 59 | 2521–2813 | `marg_bif_forward_dir_hinge_src_W` | lemma | **HEAVY mechanical** + Sym2 | depends on (12)–(58); 295 lines; mostly list bookkeeping + mechanical port |
| 60 | 2823–3047 | `marg_bif_forward_bidir_finish` | lemma | **HEAVY mechanical** + Sym2 | depends on (12)–(59); 225 lines; mechanical |
| 61 | 3052–3191 | `marg_bif_forward_bidir_with_W` | lemma | **HEAVY mechanical** + Sym2 + hL_irrefl | depends on (12)–(60); 140 lines; contains line 3073 `G.hL_irrefl hLR_G` — same pattern as (57) |
| 62 | 3194–3218 | `marg_preserves_bif_forward` | lemma | mechanical (wrapper) | depends on (42), (47), (50), (57), (60), (61); the wrapper case-splits on hinge type |
| 63 | 3222–3231 | `marg_preserves_bif_backward` | lemma | mechanical (wrapper) | depends on (51), (56) |
| **T1** | 3325–3346 | `marginalize_preserves_ancestors` | theorem | mechanical PER R1 RESOLUTION | depends on (12), (17), (20). Body trivial; signature mentions `G.Anc` — **see Risks R1** |
| **T2** | 3467–3489 | `marginalize_preserves_bifurcation` | theorem | mechanical (wrapper) | depends on (62), (63) |
| **T3** | 3561–3580 | `marginalize_preserves_bifurcation_with_source` | theorem | mechanical (wrapper) | depends on (48), (49) |
| **T4** | 3654–3668 | `marginalize_preserves_acyclic` | theorem | mechanical PER R1 RESOLUTION | depends on (12), (17). Body short; signature mentions `G.IsAcyclic` and `(G.marginalize W hW).IsAcyclic` — **see Risks R1** |
| **T5** | 3814–3851 | `marginalize_restricts_topological_order` | theorem | mechanical PER R1 RESOLUTION | depends on (12), (14). Body moderate; signature mentions `G.IsTopologicalOrder` — **see Risks R1** |

### Batched plan (12 batches)

Each batch is a `prove_claim_in_lean`-style worker invocation that **ports a contiguous set of declarations** from the original to a same-file replacement block. Workers append their replacements at the bottom of the file inside REFACTOR-BLOCK-REPLACEMENT markers, preserving the original ordering. After each batch the manager runs `lake build`.

**Batch 0 (precondition probe, no Lean work).** Before any porting begins, audit the dependencies that this row's main theorems depend on but are not in the refactor root set: `def_3_5 / FamilyRelationships.lean` (`Anc`, `Pa`), `def_3_6 / Acyclicity.lean` (`IsAcyclic`), `def_3_8 / TopologicalOrder.lean` (`IsTopologicalOrder`). Specifically: do they have REFACTOR-BLOCK-REPLACEMENT blocks for `refactor_Anc`, `refactor_IsAcyclic`, `refactor_IsTopologicalOrder`? If YES → proceed with Batches 1–11 and use those refactor-side analogues in T1/T4/T5. If NO → **STOP and `refactor` to expand root set** (this is the only blocker). Sibling rows `claim_3_13` (extAcyclic/extRestrictsTopologicalOrder) and `claim_3_15` (uses IsAcyclic / IsTopologicalOrder) have already shipped, so the dependencies are almost certainly present — but verify before starting the heavy ports.
  - worker: research-only `Agent(subagent_type=Explore, prompt="check that refactor_Anc, refactor_IsAcyclic, refactor_IsTopologicalOrder exist in Section3_1/")`
  - inputs: paths to FamilyRelationships.lean, Acyclicity.lean, TopologicalOrder.lean
  - rationale: T1/T4/T5 require these. If missing, all subsequent porting is wasted.

**Batch 1: variable + walk-algebra primitives (declarations 0–11).**
  - worker: `prove_claim_in_lean` (or custom porting worker)
  - inputs: original lines 110–238, REFACTOR-BLOCK-REPLACEMENT marker convention; cheat-sheet for cons-pattern shift
  - **Net-new helper to add here**: `refactor_marginalize_L_iff` (R2 above) — single source of truth for the Sym2-image membership dance on marg.L. Wrap in its own REPLACEMENT block.
  - rationale: independent of marginalization; lifts walk-algebra into the refactor namespace. Build green check after this batch validates the typed-step destructuring patterns.
  - risk: low-to-moderate; declaration (7) `WalkStep.source_mem` is the only structural rewrite. Build should pass after batch.

**Batch 2: marg-membership + `lt_of_directedWalk_pos` + vertex-list helpers (declarations 12–16).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 242–309
  - rationale: thin helpers; sets up the marg-membership lemmas and the vertex-list lemmas everything downstream uses. (14) `lt_of_directedWalk_pos` references `G.Pa` — if R1's audit confirms `refactor_Pa` exists, port; otherwise inline a minimal substitute.
  - risk: low.

**Batch 3: `expand_directed_walk_marginalize` (declaration 17 — single 130-line lemma).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 326–457; the refactored marg-E and `refactor_MarginalizationΦE` from `MarginalizationAK.lean`
  - rationale: load-bearing for sub-claims i, iii(a), and ii(b)'s backward direction. Sole big lemma in this batch so we get an isolated build signal.
  - risk: moderate — many `Or.inl ⟨ha_eq, Or.inl h_E⟩` constructions and cons-cell destructures, but no genuine logic change.

**Batch 4: `find_first_non_W_directed` + the two project_directed_walk lemmas + wrapper (declarations 18–22).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 472–780
  - rationale: the dual to Batch 3 — projection from `G` to marg. Build separately so projection bugs don't mask in expansion bugs (or vice versa).
  - risk: moderate-to-high — 260+ lines of dense walk surgery. Likely the highest-risk single batch in the file for hidden defeq breakage from the encoding change.

**Batch 5: walk reversal + mkBifurcation core (declarations 23–33).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 783–939
  - rationale: introduces the typed-step construction patterns (`.forwardE` / `.backwardE` / `.bidir`) at a focused walk-construction level. The `Walk.reverseDirected` def is the centerpiece — gets the encoding-shift logic right once for the rest of the file.
  - risk: moderate; declarations 24 and 31–33 are structural rewrites but small.

**Batch 6: mkBifurcationBidir core + simplifications (declarations 34–41).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 960–1192
  - rationale: bidirected hinge constructions. Two simplification opportunities (R3): declaration 40's `nil`-case collapses to `trivial`, declaration 41's IsBifurcationWithSplit witness simplifies. Sym2 enters here via `hLR : s(vL, vR) ∈ G.L`.
  - risk: moderate; mostly mechanical with the simplifications noted.

**Batch 7: bifurcation arm extractors + small support lemmas (declarations 42–46).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 1206–1561
  - rationale: the two `exists_arms_of_bifurcation_*_hinge_strong` lemmas are central to all later bifurcation surgery. Declaration 47 splits off into Batch 8 because of its size.
  - risk: high — declaration 42 is 185 lines and contains the most cons-pattern manipulation in the file. Declaration 44 may genuinely simplify (per R3).

**Batch 8: `exists_arms_of_bifurcation_bidir_hinge_strong` (declaration 47 — single 200-line lemma).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 1571–1770
  - rationale: the largest single non-theorem in the file; the dual to declaration 42. Isolating it gives a clean build signal. Most of the `h_alt : disjunction` → 3-way constructor case-split simplification happens here.
  - risk: high — biggest single port.

**Batch 9: forward / backward source helpers (declarations 48–55).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 1775–2041
  - rationale: the four "marg_preserves_bifSource_*" + dir-hinge helpers + the small list-manipulation supports. All mechanical.
  - risk: moderate.

**Batch 10: backward bidirected-hinge (declaration 56 — single 335-line lemma).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 2056–2388
  - rationale: largest single lemma in the file. **Contains the `G.hL_symm` deletion (line 2332).** Many `Finset.mem_filter, Finset.mem_product` calls on marg.L need Sym2-image rewrites; this is where `refactor_marginalize_L_iff` (added in Batch 1) earns its keep.
  - risk: high — biggest port, most Sym2 dancing.

**Batch 11: forward bidirected case helpers + forward/backward wrappers (declarations 57–63).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 2399–3231 (skipping the in-between gaps that are already covered)
  - rationale: closes off the bifurcation forward direction across the five sub-cases (both vL/vR ∉ W, vL ∈ W and/or vR ∈ W, degenerate / non-degenerate). Contains the two `G.hL_irrefl` rewrites (lines 2429, 3073). Wrappers are trivial.
  - risk: moderate-to-high — lots of cumulative Sym2 + cons-pattern shifts.

**Batch 12: the five main theorems (T1–T5).**
  - worker: `prove_claim_in_lean`
  - inputs: original lines 3325–3851
  - rationale: ports the five top-level theorems. **All bodies are trivial wrappers** around the helpers above — the porting is essentially a name-prefix swap (`*` → `refactor_*`) on each declaration cited inside the body. Each theorem keeps its `-- claim_3_16 -- start/end statement` marker pair inside the REPLACEMENT block (just renamed to `refactor_marginalize_preserves_ancestors` etc.). **Assumes R1 audit succeeded; otherwise this batch cannot start.**
  - risk: low *if* R1 is resolved; otherwise the whole batch is blocked.

**Batch 13 (tex twin): create `tex/refactor_claim_3_16_proof_MargPreservesAncestors.tex`.**
  - worker: `write_tex_proof` (or hand-copy from sibling)
  - inputs: existing `tex/claim_3_16_proof_MargPreservesAncestors.tex`; the small notational tweak template demonstrated by sibling `tex/refactor_claim_3_15_proof_AddingInterventionNodes.tex` (one-line addition about L being `Sym2` quotient)
  - rationale: independent of the Lean ports; can run in parallel with Batches 1–12. **Mechanical.**
  - risk: low.

### Dependency-edge invariants

- Every batch's declaration set depends only on declarations in *prior* batches OR within the same batch (in declaration order).
- Batch 0 is a research probe with no Lean writes; everything else writes Lean.
- Batches 3, 4, 8, 10 are each single-lemma batches that isolate the highest-risk ports.
- Batch 13 (tex twin) is independent of the Lean batches and can run in parallel.
- Batch 12 (main theorems) depends on R1's audit (Batch 0) — DO NOT start Batch 12 if Batch 0 surfaced a missing `refactor_Anc` / `refactor_IsAcyclic` / `refactor_IsTopologicalOrder`.

### Manager dispatch sequence

```
Batch 0 → Batch 13 (tex twin, parallel from this point) ─┐
   ↓                                                     │
Batch 1 → 2 → 3 → 4 → 5 → 6 → 7 → 8 → 9 → 10 → 11 → 12 ─┘ → done
```

(or sequentially: 0, 1, 2, …, 12, 13 — order between 12 and 13 doesn't matter.)

### Estimated work

- ~3500 lines of Lean to port (the helpers + body) plus 540 lines of theorem statements / proofs at the bottom.
- Per Batch typical = 200–350 lines of port; high-risk batches (3, 4, 8, 10) = 130–335 lines each.
- Net file size after Phase 7 cleanup: roughly same as original (3855 lines). During the refactor window the file will roughly double in length (original + replacement blocks). Lake's recompilation cost will be the main cost driver per batch.

### Final reminders for the manager

- **Do NOT delete the original anywhere in this file** — Phase 7 cleanup handles the swap.
- **Every refactor_*** declaration MUST be wrapped in a REPLACEMENT marker block** — even net-new helpers like `refactor_marginalize_L_iff`. Otherwise cleanup refuses without `--auto-rename-strays`.
- **Inside each main theorem's REPLACEMENT block, keep the `-- claim_3_16 -- start/end statement` markers** so the statement-equivalence checker still finds them.
- **The tex twin (Batch 13) targets `tex/refactor_claim_3_16_proof_MargPreservesAncestors.tex`** — DO NOT edit the original `tex/claim_3_16_proof_MargPreservesAncestors.tex`.
- After Batch 12 completes, run the full `lake build` from repo root, then proceed to `verify_equivalence_strict` against the original LN block + addition.

## Progress log

- 2026-06-18 ~13:06 UTC: **Batches 1–12 all complete and build is GREEN** (8287 jobs, only style/warning lint, no errors). File is now 8002 lines with 139 REFACTOR-BLOCK markers (~70 ORIGINAL + ~70 REPLACEMENT pairs). Batch 12 turn 1 placed the 5 main theorems' replacement blocks just before `end refactor_CDMG`, each carrying their inner `-- claim_3_16 -- start/end statement` markers.
- Next: Batch 13 (tex twin — mechanical port from `tex/claim_3_16_proof_MargPreservesAncestors.tex` to `tex/refactor_claim_3_16_proof_MargPreservesAncestors.tex` with the one-line notational tweak about L being a `Sym2` quotient, mirroring sibling `refactor_claim_3_15_proof_AddingInterventionNodes.tex`).
