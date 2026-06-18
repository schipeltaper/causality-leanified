# Workspace for claim_3_17 — MarginalizationsCommute

This file is the manager's scratchpad for this row. Use it for:

- The plan (output of `make_plan` worker)
- A running list of what has been tried and why it didn't work
- Notes for the next manager (if you `new_manager`-handoff or
  the run ends and a future invocation picks this row up again)

It is YAML-untyped markdown — feel free to add sections.

## Plan

Port `MarginalizationsCommute.lean` (3639 lines, 18 top-level
declarations) against the `cdmg_typed_edges` refactor. ALL
upstream prerequisites are already in place:

- `Section3_1/Walks.lean` — fully refactored (`refactor_WalkStep`
  + 3-arg `refactor_Walk.cons`, all walk predicates rewritten).
- `Section3_2/MarginalizationAK.lean` — fully refactored
  (`refactor_marginalize.L : Finset (Sym2 Node)`; no
  `marginalize_hL_symm`, since `Sym2` is definitionally
  symmetric).
- `Section3_2/MargPreservesAncestors.lean` — fully refactored;
  every walk-algebra helper `MarginalizationsCommute.lean`
  consumes has a `refactor_*` twin (`refactor_comp`,
  `refactor_vertices_comp`, `refactor_isDirectedWalk_comp`,
  `refactor_expand_directed_walk_marginalize`,
  `refactor_find_first_non_W_directed`,
  `refactor_Walk.refactor_reverseDirected`, `refactor_mkBifurcation`,
  `refactor_mkBifurcationBidir`,
  `refactor_exists_arms_of_bifurcation_directed_hinge_strong`,
  `refactor_exists_arms_of_bifurcation_bidir_hinge_strong`,
  `refactor_mkBifurcation_isBifurcationSource`,
  `refactor_arm_dropLast_in_W`, `refactor_vertices_reverse_dropLast`,
  `refactor_isBifurcationSource_to_isBifurcation`,
  `refactor_length_pos_of_isBifurcation`,
  `refactor_target_in_GV_of_directedWalk_pos`,
  `refactor_target_in_G_of_directedWalk_pos`,
  `refactor_length_pos_of_ne`,
  `refactor_tail_vertices_ne_nil_of_pos`,
  `refactor_vertices_eq_head_cons_tail`,
  `refactor_vertices_ne_nil`, `refactor_head_mem_vertices`,
  `refactor_tail_getLast_of_pos`, `refactor_vertices_getLast`,
  `refactor_mem_of_mem_vertices`, `refactor_mem_of_mem_marginalize`,
  `refactor_notW_of_mem_marginalize`, and crucially the net-new
  `refactor_marginalize_L_iff`).
- No `refactor_edges` exists (the original `Walk.edges` returns
  `List (Node × Node)` and has no clean refactor — but
  `MarginalizationsCommute.lean` does NOT consume `Walk.edges`
  (grep confirms zero matches), so this is a non-issue.

The port is structurally mechanical for most declarations.
The risk concentrates in the L-field machinery (sites that
peel `(u, v) ∈ G.L` off `marg.L` inline, sites that use
`hL_symm`, sites that use `hL_subset`/`hL_irrefl`).
**Heads-up findings from reading the original:**

1. `marg.L` membership peeled inline at:
   - L815-819 in `forward_marg_to_g_bif_one_orientation`
     (`hLR_p_marg` → `Finset.mem_filter` + `Finset.mem_product`)
   - Equivalent unwraps in `marg_PhiL_iff` and
     `backward_marg_to_g_bif_bidir_hinge_one_orientation`.

   Under refactor, `marg.L : Finset (Sym2 Node)` is built as
   `(filter …).image (fun e => s(e.1, e.2))`, so direct
   `Finset.mem_filter` on `marg.L` is ill-typed. Use
   `refactor_marginalize_L_iff` (in
   `MargPreservesAncestors.lean` L4202) at all such sites —
   this is the **single source of truth** the upstream
   refactor explicitly added for this consumer.

2. `G.hL_symm hMLR_G` at L1627 (the "Inr + bid M-hinge"
   branch of `forward_marg_to_g_bif_one_orientation`)
   becomes a NO-OP under refactor. The witness
   `hMLR_G : s(vML, vMR) ∈ G.L` is orientation-free
   (`s(vML, vMR) = s(vMR, vML)` definitionally), so
   `mkBifurcationBidir` accepts it with either reading of
   the endpoints. **The "Inl + bid M-hinge" and "Inr + bid
   M-hinge" branches likely collapse into one under
   refactor.** Surface this when dispatching: the porter
   may be able to merge them, but a conservative port that
   keeps both branches but replaces `G.hL_symm hMLR_G` with
   `hMLR_G` (plus possibly a `Sym2.eq_swap.mp` rewrite if
   the elaborator wants the explicit orientation) is also
   acceptable and may be the safer first pass.

3. `(G.hL_subset hLR_G).1` / `.2` at L1952-1953 (extracting
   `vL_h ∈ G.V` and `vR_h ∈ G.V`) becomes
   `G.hL_subset hLR_G (Sym2.mem_mk_left vL_h vR_h)` and
   `G.hL_subset hLR_G (Sym2.mem_mk_right vL_h vR_h)` (the
   same `Sym2.Mem` idiom that MPA's
   `refactor_WalkStep.refactor_source_mem` uses).

4. `G.hL_irrefl hLR_G heq` at L1957 (where
   `heq : vL_h = vR_h`) becomes a `Sym2.IsDiag` discharge.
   The witness shape: `G.hL_irrefl hLR_G` now gives
   `¬ s(vL_h, vR_h).IsDiag`; from `vL_h = vR_h`, derive
   `s(vL_h, vR_h).IsDiag` via `Sym2.mk_isDiag_iff.mpr heq`
   (or the appropriate Mathlib name —
   `Sym2.IsDiag` characterization). Concrete idiom is
   `G.hL_irrefl hLR_G (Sym2.isDiag_iff_proj_eq.mpr heq)`
   (or `Sym2.mk_isDiag_iff` depending on Mathlib version);
   the porter will need to grep Mathlib for the exact name
   in the porter's environment.

5. `marg_L_field_eq` (the assembly lemma) compares two
   filtered ordered-pair Finsets; under refactor both
   `marg.L`s are `image`d on top of the filter. The
   equality becomes a `Finset.image_congr` over a
   `Finset.filter_congr` — same skeleton, one extra
   `Finset.image` layer.

6. `cdmgExt` (the main theorem's CDMG-extensionality
   helper at L3603-3607) destructures `CDMG` with 9
   fields (including `hL_symm`). Under refactor,
   `refactor_CDMG` has 8 fields (no `hL_symm`), so
   the pattern is one comma narrower:
   `⟨J₁, V₁, _, E₁, _, L₁, _, _⟩` instead of
   `⟨J₁, V₁, _, E₁, _, L₁, _, _, _⟩`.

7. `Walk.WalkStep`-construction sites at L206-207, L321-322
   (`hStepMarg : (G.marginalize S hS).WalkStep u (u, m) m
     := Or.inl ⟨rfl, Or.inl h_edge⟩`)
   become `refactor_WalkStep.forwardE h_edge` — drop the
   ordered-pair argument and pass the edge witness
   directly. The `.cons m (u, m) hStepMarg q_tail` calls
   correspondingly drop the `(u, m)` argument:
   `refactor_Walk.cons m (.forwardE h_edge) q_tail`.

8. `subset_sdiff_of_disjoint` (the marker-wrapped helper
   at L157-161) is type-agnostic in `Node`, `G` — it's
   pure `Finset`-set-difference. No structural change
   needed; only the `refactor_*` prefix on the
   declaration and the marker conventions matter. ALL
   call sites in this file (4 of them, inside the main
   theorem signature) reference the same helper.

9. The two `Walk.cons` building sites in
   `project_walk_marg_*_aux` (L244, L262, L367, L413)
   call `Walk.cons m (u, m) hStepMarg q_tail` (4 args).
   Under refactor this collapses to `.cons m s q_tail`
   (3 args; `s : refactor_WalkStep G u m`).

### Phase A — Tex twin + variable + subset_sdiff_of_disjoint

Set up the markers and the tex twin. Lowest risk, gets the
convention right.

A.1 **Tex twin.** Create
`Section3_2/tex/refactor_claim_3_17_proof_MarginalizationsCommute.tex`
identical in content to the existing
`tex/claim_3_17_proof_MarginalizationsCommute.tex` (the
mathematics doesn't change — the LN proof argues about
marginalization sets, never about ordered-vs-quotient
encoding of `L`).
- worker: `spawn_agent_sub_task` with the file-create task
  (a simple `cp`-equivalent + sanity-check). Could also
  be done directly by the manager via a single Bash call.
- inputs: source path
  `Section3_2/tex/claim_3_17_proof_MarginalizationsCommute.tex`,
  target path
  `Section3_2/tex/refactor_claim_3_17_proof_MarginalizationsCommute.tex`.
- rationale: tex twin is required by the refactor
  convention; doing it first front-loads the trivial
  bookkeeping.
- risk/effort: zero.

A.2 **Open a `namespace refactor_CDMG` block at the end of
`MarginalizationsCommute.lean`.** Mirror MPA's structure
(L3993 in MargPreservesAncestors.lean). Inside that block:
add a REPLACEMENT marker for the variable declaration, and
a marker-wrapped REPLACEMENT for `subset_sdiff_of_disjoint`.
- worker: `spawn_agent_sub_task` with
  `refactor_lean_code.md`.
- worker brief: add the namespace block and the two
  REPLACEMENT marker pairs, port the marker-wrapped
  `subset_sdiff_of_disjoint` helper (pure `Finset` proof,
  no CDMG/Walk dependency — body unchanged modulo
  `private lemma` → `private lemma refactor_subset_sdiff_of_disjoint`).
- inputs: original block L157-161; refactor-marker
  template; the file
  `/home/11716061/repo_scaffold2/leanification/Chapter3_GraphTheory/Section3_2/MarginalizationsCommute.lean`.
- prerequisites: nothing.
- rationale: this gets the marker convention and the
  namespace block in place; lake build confirms the
  rename + Finset-only helper compile cleanly.
- checkpoint: `lake build Chapter3_GraphTheory.Section3_2.MarginalizationsCommute` PASS.
- risk/effort: very low. A.1 and A.2 can be sent in
  parallel.

### Phase B — E-field machinery (5 lemmas, mechanical port)

B.1 Port `project_walk_marg_with_interior_aux`,
`project_walk_marg_with_interior`,
`project_walk_marg_full_aux`, `project_walk_marg_full`,
`mem_marg_of_notin_union_V`, `mem_marg_of_notin_union_VnoJ`,
`marg_PhiE_iff`, `marg_E_field_eq` (8 lemmas, ~360 lines
combined). All are E-field only — no `L` references.
- worker: `spawn_agent_sub_task` with `refactor_lean_code.md`.
- worker brief: port each lemma in order under the
  `namespace refactor_CDMG` block. Each gets its own
  REPLACEMENT marker (no ORIGINAL pair — these were
  `private lemma`s with no markers in the original; treat
  them as NET-NEW from the cleanup script's perspective,
  using the `REPLACEMENT-BEGIN: <name> (was: refactor_<name>)`
  form without a paired ORIGINAL).
- key substitutions:
  - `CDMG Node` → `refactor_CDMG Node`
  - `Walk G u v` → `refactor_Walk G u v`
  - `.marginalize` → `.refactor_marginalize`
  - `MarginalizationΦE` → `refactor_MarginalizationΦE`
  - `IsDirectedWalk` → `refactor_IsDirectedWalk`
  - `.vertices` → `.refactor_vertices`
  - `.length` → `.refactor_length`
  - `Walk.cons m (u, m) hStepMarg q_tail` (4 args, `hStepMarg : marg.WalkStep u (u, m) m := Or.inl ⟨rfl, Or.inl h_edge⟩`) → `refactor_Walk.cons m (.forwardE h_edge) q_tail` (3 args, `.forwardE` constructor takes the edge witness directly)
  - `find_first_non_W_directed`, `Walk.target_in_GV_of_directedWalk_pos`, `Walk.vertices_eq_head_cons_tail`, `Walk.tail_vertices_ne_nil_of_pos`, `Walk.head_mem_vertices`, `expand_directed_walk_marginalize`, `notW_of_mem_marginalize` → all `refactor_*` namespaced variants from MPA L3993+.
- inputs: original block L172-538; MPA refactor cookbook
  L3993-5170; the `MarginalizationsCommute.lean` file
  with the Phase A skeleton.
- prerequisites: Phase A complete.
- rationale: E-field is entirely structural and uses NO
  L-side hypotheses (`G.L`, `hL_subset`, `hL_symm`,
  `hL_irrefl`), so it's the closest thing to a pure
  mechanical rename in the file. Getting it green first
  isolates any pure-rename mistakes from the L-field
  Sym2 work that follows.
- checkpoint: `lake build` PASS on
  `Chapter3_GraphTheory.Section3_2.MarginalizationsCommute`.
- risk/effort: medium. ~360 lines, four induction-style
  proofs (the two `_aux` lemmas plus the `_full_aux` and
  `_full` companion lemmas have the most boilerplate).
  ONE `spawn_agent_sub_task` should suffice — these
  lemmas are tightly coupled (each consumes the
  previous one) and the porter will want them all in
  context. Note: `marg_PhiE_iff` and `marg_E_field_eq`
  use `Finset.filter_congr` / `Finset.mem_product`
  unchanged.

### Phase C — Small L-field setup (4 lemmas)

C.1 Port `mem_interior_of_arm_source`,
`vertices_tail_dropLast_mkBifurcation`,
`vertices_tail_dropLast_mkBifurcationBidir_Lpos`,
`find_first_non_W_directed_inclusive` (~158 lines
combined).
- worker: `spawn_agent_sub_task` with `refactor_lean_code.md`.
- key substitutions (in addition to Phase B's set):
  - `mkBifurcation` → `refactor_Walk.refactor_mkBifurcation`
  - `mkBifurcationBidir` → `refactor_Walk.refactor_mkBifurcationBidir`
  - `vertices_mkBifurcation` → `refactor_Walk.refactor_vertices_mkBifurcation`
  - `vertices_reverse_dropLast` → `refactor_Walk.refactor_vertices_reverse_dropLast`
  - For `vertices_tail_dropLast_mkBifurcationBidir_Lpos`'s
    L-edge hypothesis `(vL, vR) ∈ G.L` (ordered-pair),
    becomes `s(vL, vR) ∈ G.L` (Sym2). Use this
    consistently throughout the helper.
- inputs: original block L539-685.
- prerequisites: Phase B complete (these helpers feed
  into Phase D).
- rationale: bridges the algebra-of-walks side into the
  bif-with-bidir-hinge side; no inline Φ_L witness
  manipulation yet, just the new
  `mkBifurcationBidir`'s argument shape.
- checkpoint: `lake build` PASS.
- risk/effort: low. These lemmas are list-arithmetic
  about `vertices` / `dropLast` / `tail` and don't
  touch the L-field's filter structure.

### Phase D — The three giant case-analysis lemmas

This is where the bulk of the file (and the bulk of the
risk) lives. The three lemmas total ~2337 lines:
- `forward_marg_to_g_bif_one_orientation` (~1232 lines)
- `backward_marg_to_g_bif_bidir_hinge_one_orientation` (~641 lines)
- `backward_marg_to_g_bif_dir_hinge_cInS_betaNeGamma_one_orientation` (~464 lines)

Each is a 4-way case split (directed-vs-bidir hinge on
the bif × Inl-vs-Inr orientation of how `find_first_non_W`
attaches) further subdivided by length-≥1 cases on the
component arms. The porter needs to maintain the case
structure while shifting the L-witness shape from
ordered-pair to `Sym2`.

D.1 Port `forward_marg_to_g_bif_one_orientation`.
- worker: `spawn_agent_sub_task` with `refactor_lean_code.md`.
- worker brief: port the whole 1232-line lemma in ONE
  dispatch. Key shifts beyond Phases B/C:
  - The `hLR_p_marg : (vL_p, vR_p) ∈ marg.L` extraction
    chain (L815-819) replaces with one call to
    `refactor_marginalize_L_iff` (in MPA L4202). The
    result yields an `e : Node × Node` plus
    `s(vL_p, vR_p) = s(e.1, e.2)` — but since here
    `vL_p`, `vR_p` are bound by
    `exists_arms_of_bifurcation_bidir_hinge_strong`'s
    witness directly via the typed `.bidir _` constructor
    in the WalkStep, the porter should check whether the
    underlying source already gives `s(vL_p, vR_p) ∈ marg.L`
    in Sym2 form (it does — the refactored
    `refactor_exists_arms_of_bifurcation_bidir_hinge_strong`'s
    output is `hLR_p_marg : s(vL_p, vR_p) ∈ marg.L`, MPA
    L5973+).
  - For the "Inr + bid M-hinge" branch (L1619-1627):
    `G.hL_symm hMLR_G` becomes vacuous. The branch
    receives `hMLR_G : s(vML, vMR) ∈ G.L` and
    `mkBifurcationBidir` accepts `s(vMR, vML) ∈ G.L`
    via `s(vML, vMR) = s(vMR, vML)` (definitional or
    `Sym2.eq_swap`). The porter can either (a)
    use `hMLR_G` directly in the swapped slot (likely
    type-checks under definitional equality), or (b)
    add an explicit `Sym2.eq_swap` rewrite, or (c)
    flag that this branch may collapse together with
    the "Inl + bid M-hinge" branch.
  - `Walk.exists_arms_of_bifurcation_bidir_hinge_strong`
    → `refactor_Walk.refactor_exists_arms_of_bifurcation_bidir_hinge_strong`
    (MPA L5973+); same for the `directed_hinge_strong`
    sibling.
  - `Walk.mkBifurcationBidir` (4-arg with ordered-pair
    L-witness) → `refactor_Walk.refactor_mkBifurcationBidir`
    (4-arg with `Sym2`-witness).
  - `Walk.mkBifurcationBidir_isBifurcation` →
    `refactor_Walk.refactor_mkBifurcationBidir_isBifurcation`
    (MPA L5389).
  - `Walk.isDirectedWalk_comp` →
    `refactor_Walk.refactor_isDirectedWalk_comp`
    (MPA L4054).
  - `Walk.vertices_comp` → `refactor_Walk.refactor_vertices_comp` (MPA L4089).
  - `Walk.arm_dropLast_in_W` →
    `refactor_Walk.refactor_arm_dropLast_in_W`
    (MPA L6540).
  - `Walk.length_pos_of_ne` → `refactor_Walk.refactor_length_pos_of_ne` (MPA L4931).
  - `Walk.mkBifurcation_isBifurcationSource` →
    `refactor_Walk.refactor_mkBifurcation_isBifurcationSource`
    (MPA L5746).
  - `Walk.isBifurcationSource_to_isBifurcation` →
    `refactor_Walk.refactor_isBifurcationSource_to_isBifurcation`
    (MPA L5923).
- inputs: original block L696-1927; full MPA refactor
  helpers index.
- prerequisites: Phases A/B/C complete.
- rationale: This is the row's biggest single lemma.
  Doing it as ONE dispatch is risky (long; many
  branches), but splitting it would require the porter
  to coordinate symbolic substitution across multiple
  dispatch boundaries and is likely to introduce
  inconsistencies (e.g. one branch ports the
  Φ_L-witness extraction differently from another). One
  dispatch with the porter given the full lemma and
  the full helper-rename cookbook (this plan + MPA
  L3993+ in context) is the recommended approach.
- checkpoint: `lake build` PASS.
- risk/effort: HIGH. If the porter gets stuck, split the
  lemma by orientation (Inl vs Inr) and dispatch the
  two halves separately, but expect that the porter
  will need to do this lemma in a single context to
  keep variable-naming consistent.

D.2 Port `backward_marg_to_g_bif_bidir_hinge_one_orientation`.
- worker: `spawn_agent_sub_task` with `refactor_lean_code.md`.
- worker brief: port the 641-line lemma. Key risks:
  - L1952-1957: `(G.hL_subset hLR_G).1` / `.2` and
    `G.hL_irrefl hLR_G heq` rewrites.
    - `(G.hL_subset hLR_G).1` becomes
      `G.hL_subset hLR_G (Sym2.mem_mk_left vL_h vR_h)`.
    - `(G.hL_subset hLR_G).2` becomes
      `G.hL_subset hLR_G (Sym2.mem_mk_right vL_h vR_h)`.
    - `G.hL_irrefl hLR_G heq` becomes (something like)
      `G.hL_irrefl hLR_G (Sym2.mk_isDiag_iff.mpr heq)`
      — porter should grep Mathlib for the exact
      `Sym2.IsDiag` characterization in their build (it
      may be `Sym2.isDiag_iff_proj_eq` or similar; the
      `refactor_marginalize_hL_irrefl` proof in
      MarginalizationAK.lean is a working pattern to
      mirror — check MarginalizationAK.lean around the
      `refactor_marginalize_hL_irrefl` body for the
      exact idiom used in this codebase).
  - At the bidirected-hinge witness `hLR_G : s(vL_h, vR_h) ∈ G.L`,
    the refactored
    `refactor_exists_arms_of_bifurcation_bidir_hinge_strong`
    already gives the Sym2 form, so no extra unwrap is needed
    at the bif-arm-extraction step.
  - The `Walk.mkBifurcationBidir` constructor calls (and
    the `mkBifurcation` siblings for the β=γ branch)
    follow the same Sym2-witness shift as Phase D.1.
  - `Walk.reverseDirected` (used in the β≠γ assembly):
    `refactor_Walk.refactor_reverseDirected` (MPA L4940).
- inputs: original block L1928-2568.
- prerequisites: Phases A/B/C and D.1 complete (D.1 has
  shaken out the helper-rename and Sym2-witness
  conventions; D.2 reuses them).
- rationale: shorter and structurally simpler than D.1
  (one orientation, one hinge type) — but it's where
  `hL_subset` / `hL_irrefl` first appear.
- checkpoint: `lake build` PASS.
- risk/effort: medium-high. The `Sym2.IsDiag` idiom is
  the only genuinely novel piece beyond the
  Phase D.1 patterns.

D.3 Port `backward_marg_to_g_bif_dir_hinge_cInS_betaNeGamma_one_orientation`.
- worker: `spawn_agent_sub_task` with `refactor_lean_code.md`.
- worker brief: port the 464-line lemma. This is the
  "directed-hinge with source ∈ S, β ≠ γ" case for the
  backward direction. Closer to D.1's structural-only
  port than to D.2's L-symmetry plumbing — the bif this
  lemma constructs in `marg` has a *bidirected* hinge
  (built via `mkBifurcationBidir` on the contracted
  arms), so a single `marg.L` witness is needed; build it
  via `refactor_marginalize_L_iff.mpr`.
- inputs: original block L2569-3032.
- prerequisites: Phases A/B/C and D.1 complete (D.2 not
  strictly required, but its sym2-irrefl pattern may be
  useful when classifying β ≠ γ on the marg side).
- rationale: combinatorially the most intricate of the
  three (case-splits on every arm length combination),
  but uses fewer truly novel refactor patterns than
  D.1 / D.2.
- checkpoint: `lake build` PASS.
- risk/effort: high (size) but lower per-line risk than
  D.1/D.2.

Note: D.1, D.2, D.3 can in principle run in parallel
once Phases A/B/C are green AND the porter has fully
internalised the helper-rename cookbook from D.1. **For
the first attempt, dispatch D.1 alone**; once it passes,
D.2 and D.3 can be dispatched in parallel.

### Phase E — Assembly lemmas

E.1 Port `marg_PhiL_iff` and `marg_L_field_eq` (~557
lines combined). These two are the assembly of the
Phase D auxiliaries into a clean iff
(`marg.MarginalizationΦL T u v ↔ MarginalizationΦL (S ∪ T) u v`)
and an equality (`marg₁₂.L = marg₁₂'.L`).
- worker: `spawn_agent_sub_task` with `refactor_lean_code.md`.
- worker brief:
  - `marg_PhiL_iff` body uses the three Phase D auxiliaries
    plus inline Walk manipulation. Wire up the
    `refactor_*` calls; the `MarginalizationΦL` definition
    is itself an `Or` over two orientations of the bif, so
    the structure of the proof should be preserved
    one-to-one (4 inner branches → 4 inner branches with
    `refactor_*` renames).
  - `marg_L_field_eq` (L3430-3445) takes the iff and lifts
    it to a `Finset` equality. The big shift here: under
    refactor, `marg.L` is
    `((filter …).image (fun e => s(e.1, e.2)))`, so the
    equality of two `marg.L` Finsets becomes
    `Finset.image_congr` over a `Finset.filter_congr`. The
    inner `Finset.filter_congr` is the same as the
    original (compare iff on ordered pairs); the outer
    `Finset.image_congr` is one extra layer. Use
    `refactor_marginalize_L_iff` (MPA L4202) inside the
    `Finset.image` congruence to avoid re-deriving the
    membership chain.
- inputs: original block L3033-3445; Phase D outputs.
- prerequisites: Phase D complete.
- rationale: this is the "make it useful" layer that the
  main theorem consumes.
- checkpoint: `lake build` PASS.
- risk/effort: medium. The `Finset.image_congr` /
  `Finset.image` layer is genuinely new structure; the
  iff body is structural.

### Phase F — Main theorem

F.1 Port `marginalize_comm` (~50 lines) marker-wrapped as
`REFACTOR-BLOCK-REPLACEMENT-BEGIN: marginalize_comm (was: refactor_marginalize_comm)`.
This is the row's main `theorem`-level declaration and
the only place this row has an ORIGINAL/REPLACEMENT
*pair*. The ORIGINAL marker wraps the existing
`marginalize_comm` (need to add a
`REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize_comm` /
`-END` pair around L3591-3600); the REPLACEMENT goes
inside the `namespace refactor_CDMG` block at the file's
end.
- worker: `spawn_agent_sub_task` with `refactor_lean_code.md`.
- worker brief:
  - Wrap the existing `marginalize_comm` (the original) at
    L3591-3635 in
    `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: marginalize_comm` /
    `-- REFACTOR-BLOCK-ORIGINAL-END: marginalize_comm`.
  - Inside the `namespace refactor_CDMG` block add
    `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: marginalize_comm (was: refactor_marginalize_comm)` /
    `-- REFACTOR-BLOCK-REPLACEMENT-END: marginalize_comm`.
  - Inside the REPLACEMENT block, declare
    `theorem refactor_marginalize_comm
      (G : refactor_CDMG Node) (W₁ W₂ : Finset Node)
      (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V)
      (hDisj : Disjoint W₁ W₂) : … ∧ … := by …`.
  - `cdmgExt` rewrite: destructure pattern shifts from
    9 to 8 fields (no `hL_symm`):
    `⟨J₁, V₁, _, E₁, _, L₁, _, _⟩` instead of
    `⟨J₁, V₁, _, E₁, _, L₁, _, _, _⟩`.
  - All other plumbing (`hL_field_eq` closure over
    `marg_L_field_eq`; the two `cdmgExt` calls; the
    `Finset.union_comm` / `sdiff_sdiff_left` rewrites)
    ports verbatim.
- inputs: original block L3447-3635; Phase E outputs.
- prerequisites: Phase E complete.
- rationale: this is the LN-spec assertion; with E in
  place, this should be a near-mechanical assembly.
- checkpoint: `lake build` PASS.
- risk/effort: low (modulo the `cdmgExt` destructure).

F.2 Run the strict-equivalence solved-gate.
- worker: the manager's standard `solved` action ⇒
  `verify_row_solved` chain.
- inputs: row state with formalized=yes, proven=yes.
- prerequisites: F.1 complete and `lake build` clean.
- rationale: gate-validates the
  `refactor_marginalize_comm` declaration against the LN
  block (rewritten canonical statement +
  `addition_to_the_LN`, which is empty for this row per
  `refactor_data.json`).
- checkpoint: `verify_row_solved` PASS.
- risk/effort: low — the `Sym2` encoding doesn't change
  the LN-level statement of the lemma, so the strict
  gate is the same logical check.

### Summary of dispatch order

1. Phase A.1 (tex twin) — manager `cp`, ~30 seconds.
2. Phase A.2 + Phase B (in parallel) — two
   `spawn_agent_sub_task` calls.
3. Phase C — one `spawn_agent_sub_task`.
4. Phase D.1 — one `spawn_agent_sub_task`. Wait for green.
5. Phase D.2 + Phase D.3 (in parallel) — two
   `spawn_agent_sub_task` calls.
6. Phase E — one `spawn_agent_sub_task`.
7. Phase F.1 — one `spawn_agent_sub_task`.
8. Phase F.2 — manager `solved`.

Total expected dispatches: ~8 (most of them low-risk),
with the bulk of the wall-clock time concentrated in
Phases D.1–D.3 (the three giant case-analysis lemmas).

### Cross-cutting reminders for every porter dispatch

- Every `refactor_*` declaration must be marker-wrapped.
  Net-new declarations (everything except
  `subset_sdiff_of_disjoint` and `marginalize_comm`)
  use the `REPLACEMENT-BEGIN: <FinalName> (was: refactor_<FinalName>)`
  form WITHOUT a paired ORIGINAL block.
- The two `ORIGINAL`/`REPLACEMENT` PAIRED markers in
  this file are: `subset_sdiff_of_disjoint` (Phase A)
  and `marginalize_comm` (Phase F).
- All ports live INSIDE
  `namespace Causality / namespace CDMG / namespace refactor_CDMG`
  (mirror the MPA structure at L3993).
- Don't touch the originals or rename them. Cleanup
  does that at Phase 7.
- After each phase: `lake build
  Chapter3_GraphTheory.Section3_2.MarginalizationsCommute`
  must pass. If it fails, fix the issue before
  dispatching the next phase.
- `refactor_marginalize_L_iff` (MPA L4202) is the
  canonical iff for Sym2-image membership on `marg.L`
  — use it instead of peeling `Finset.mem_filter` +
  `Finset.mem_product` inline.
