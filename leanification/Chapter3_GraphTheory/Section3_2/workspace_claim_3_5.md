# Workspace for claim_3_5 — BifurcationAlternative

## Status snapshot (manager turn 1)

- Row kind: **DEPENDENT** in refactor `cdmg_typed_edges`.
- Roots: `def_3_1` (CDMG → refactor_CDMG with `L : Finset (Sym2 Node)`) and
  `def_3_4` (Walk + WalkStep + all walk predicates retyped). Both root rows
  are solved (per refactor_data.json).
- Tex proof file `tex/claim_3_5_proof_BifurcationAlternative.tex` is already
  rigorous and self-contained (LN proof + expansion). Refactor twin file is
  **not** needed: a refactor port of a claim only needs a tex twin if the
  proof reasoning itself changes; here the math is identical and only the
  underlying Lean encoding changes. (Tex-side cleanup is no-op.)
- Existing Lean file: `BifurcationAlternative.lean` (2167 lines, 35 helper
  decls). All currently target the **OLD** untyped `Walk` + `WalkStep` shape
  and the `Finset (Node × Node)` form of `L`.

## Structural map of existing BifurcationAlternative.lean (from explorer)

- Imports (1–5): CDMG, CDMGNotation, Walks, FamilyRelationships,
  HardInterventionOn. `namespace Causality` then `namespace CDMG`.
- Helper variable block at 109–111: wrapped `-- claim_3_5 --- start/end
  helper`. (`variable {Node : Type*} [DecidableEq Node]`.)
- Main theorem `bifurcationAlternative` at 1881–1890, wrapped
  `-- claim_3_5 -- start/end statement`. Proof body 1891–2067.
- 35 private helper lemmas/defs grouped into 7 subtasks:
  1. **Walk lift from G_{do(W)}** (142–233): `mem_of_mem_hardInterventionOn`,
     `Walk.liftWalkStep_of_hardInterventionOn`, `Walk.liftFromHardIntervention`,
     plus IsDirectedWalk/length/vertices preservation.
  2. **Walk composition** (266–426): `Walk.comp`, `length_comp`,
     `isDirectedWalk_comp`, `vertices_comp`, head/tail-of-vertices aux.
  3. **Walk lift to G_{do(W)}** (448–644): `Walk.liftTo_hardInterventionOn`,
     directedness preservation, avoidance predicate, `WalkStep.source_mem`.
  4. **Walk truncation** (679–866): `Walk.truncateAtFirst`, length/directedness
     /vertices lemmas, `exists_directed_walk_v_not_in_dropLast`.
  5. **Bifurcation walk construction** (1012–1104): `Walk.reverseDirected`,
     `Walk.mkBifurcation`, length/vertices lemmas.
  6/7. **Bifurcation predicates & arm extraction** (1207–1508): `comp_assoc`,
     `isBifurcationDirectedHinge_cons_backward_of_directed`, …,
     **`exists_arms_of_bifurcation_directed_hinge`** (the central decomposer
     that turns `IsBifurcationDirectedHingeWithSplit i` into a pair of
     directed walks `L : Walk G c v`, `R : Walk G c w`).
- Reference density (OLD shapes):
  - `IsDirectedWalk`: 58 hits (most inside helper recursion).
  - `.vertices`: 249 hits (`dropLast`, `tail`, `head`, `append` operations).
  - `.length`: 127 hits.
  - `.cons _ a _ p` style pattern matches: ~35.
  - `Anc` (from FamilyRelationships, refactor-side untouched): 41.

## What the port boils down to

The mathematical content is unchanged: the LN proof is identical and the
tex proof is unchanged. The port is **syntactic + structural**, not
mathematical:

1. `CDMG Node` → `refactor_CDMG Node` everywhere a CDMG is named.
2. `Walk G u v` → `refactor_Walk G u v`. Recursors / pattern matches on
   `.cons v a h p` become `.cons v s p` with `s : refactor_WalkStep G u v`.
3. Pattern matches on the step:
   - **OLD:** `obtain ⟨ha, hL⟩ | ⟨ha', hE⟩ := hStep` against
     `WalkStep G u a v := (a = (u,v) ∧ (a ∈ G.E ∨ a ∈ G.L)) ∨ (a = (v,u) ∧ a ∈ G.E)`.
   - **NEW:** `match s with | .forwardE h => _ | .backwardE h => _ | .bidir h => _`
     against the typed inductive `refactor_WalkStep`.
4. Walk-derived names:
   - `IsDirectedWalk` → `refactor_IsDirectedWalk`
   - `IsBifurcationDirectedHingeWithSplit` →
     `refactor_IsBifurcationDirectedHingeWithSplit`
   - `IsBifurcationSource` → `refactor_IsBifurcationSource`
   - `vertices` → `refactor_vertices`
   - `length` → `refactor_length`
5. `G.L` is now `Finset (Sym2 Node)` rather than `Finset (Node × Node)` —
   but this proof works **only with directed walks** (the bifurcation
   restricted to a directed hinge + two directed arms in the intervened
   CDMGs), so the L-channel never appears structurally in the proof. The
   Sym2 change is essentially neutral here.
6. `hL_symm` is gone — but again, never used in this proof.
7. Markers: wrap the entire current contents block (helper variable + 35
   helpers + main theorem) in `REFACTOR-BLOCK-ORIGINAL` markers, then add a
   parallel `REFACTOR-BLOCK-REPLACEMENT` block below containing the
   `refactor_`-prefixed versions of every declaration. Phase 7 will swap.

## Tex twin: not needed

The proof's reasoning is unchanged (same shortest-walk truncation +
concatenation + reversal, same five-clause verification of def 3.4). No
tex twin is required for this row — only the Lean port.

## Convention check from prior solved refactor rows

`HardInterventionsCommute.lean` (solved) and `AcyclicPreservedUnderDo.lean`
(solved) demonstrate the pattern:
- ORIGINAL block stays in place verbatim (consumers still reference it).
- REPLACEMENT block below uses `refactor_<name>` names + REFACTOR-BLOCK
  markers; design-choice docstrings sit above the start marker.
- Net-new helper lemmas added for the port also get REPLACEMENT markers
  (no ORIGINAL pair required for those).
- Replacement decls live inside `namespace refactor_CDMG` (so the upstream
  `refactor_Walk` / `refactor_Anc` / `refactor_hardInterventionOn` resolve
  by dot notation as `p.refactor_IsDirectedWalk`, `G.refactor_Anc v`, etc.).

## Step-by-step subtask plan (turn 1 → solve)

The plan below is what the manager should dispatch sequentially. Each
step lists the worker, inputs, what to write, and rationale. Rough sizes
in parentheses reflect line-count for the corresponding ORIGINAL block.

### Step 0 — Baseline + verify nothing structural references L bidirected

worker: read-only sanity check (the manager itself, no worker needed)
inputs: existing BifurcationAlternative.lean (2167 lines)
do:
- Run `lake build` once to confirm the file builds green at HEAD.
- Grep the file for `\.bidir|G\.L|hL_symm|L\.filter|Or\.inr` outside the
  step-3 `WalkStep.source_mem` `hL_subset` branch — confirm the proof
  body never branches on the L channel structurally. (Spot-check
  already shows: only `WalkStep.source_mem`'s third disjunct touches
  `hL_subset`. Everything else is forward/backward `E`-based.)
- Confirm namespace structure: original lives in `namespace Causality
  / namespace CDMG`; the REPLACEMENT will live in `namespace Causality
  / namespace refactor_CDMG`.

(No tool dispatch needed; this is manager-level orientation.)

### Step 1 — Wrap ORIGINAL block with REFACTOR-BLOCK markers (one pair per top-level decl)

worker: `prove_claim_in_lean` (single dispatch, mechanical edit)
inputs: BifurcationAlternative.lean lines 109–2067
do:
- Add `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: <lean_decl_name>` immediately
  before each of the 36 top-level decls (variable block, 35 helpers,
  main theorem), and matching `-- REFACTOR-BLOCK-ORIGINAL-END: <name>`
  immediately after each.
- The 36 names to use (Lean identifiers, NOT row title): `variable`
  marker uses identifier-free wrapping per HardInterventionsCommute.lean
  precedent — actually, the variable block has no decl name; check the
  AcyclicPreservedUnderDo.lean precedent: the variable block sits
  OUTSIDE the REFACTOR-BLOCK pairs (cleanup just keeps it). Follow that
  convention — wrap only the 35 helpers + main theorem (36 pairs).
- Per-decl names: `mem_of_mem_hardInterventionOn`,
  `Walk.liftWalkStep_of_hardInterventionOn`,
  `Walk.liftFromHardIntervention`,
  `Walk.isDirectedWalk_liftFromHardIntervention`,
  `Walk.length_liftFromHardIntervention`,
  `Walk.vertices_liftFromHardIntervention`,
  `Walk.comp`, `Walk.length_comp`, `Walk.isDirectedWalk_comp`,
  `Walk.vertices_ne_nil`, `Walk.vertices_comp`,
  `Walk.head_mem_vertices`, `Walk.vertices_eq_head_cons_tail`,
  `Walk.vertices_directed_avoid_of_hardInterventionOn`,
  `Walk.liftTo_hardInterventionOn`,
  `Walk.isDirectedWalk_liftTo_hardInterventionOn`,
  `WalkStep.source_mem`, `Walk.truncateAtFirst`,
  `Walk.truncateAtFirst_target_eq`, `Walk.length_truncateAtFirst_le`,
  `Walk.isDirectedWalk_truncateAtFirst`,
  `Walk.mem_vertices_of_mem_dropLast`,
  `Walk.length_truncateAtFirst_lt_of_mem_dropLast`,
  `exists_directed_walk_v_not_in_dropLast`,
  `Walk.reverseDirected`, `Walk.length_reverseDirected`,
  `Walk.vertices_reverseDirected`, `Walk.mkBifurcation`,
  `Walk.length_mkBifurcation`, `Walk.vertices_mkBifurcation`,
  `Walk.comp_assoc`,
  `Walk.isBifurcationDirectedHinge_cons_backward_of_directed`,
  `Walk.isBifurcationDirectedHinge_comp_reverseDirected_aux`,
  `Walk.isBifurcationDirectedHinge_mkBifurcation`,
  `Walk.exists_arms_of_bifurcation_directed_hinge`,
  `bifurcationAlternative`.
rationale: cleanup script needs marker pairs around each ORIGINAL decl
to delete them at Phase 7 and rename `refactor_X → X` whole-word
across files.

### Step 2 — Open REPLACEMENT namespace + variable block

worker: `prove_claim_in_lean` (mechanical, one dispatch)
inputs: end of file (after `end CDMG`), before final `end Causality`
do:
- Append `namespace refactor_CDMG` then a `variable {Node : Type*}
  [DecidableEq Node]` line. No marker pair needed for the variable
  declaration (matches the upstream Walks.lean / FamilyRelationships.lean
  convention for refactor namespaces).
rationale: scaffolding for all subsequent REPLACEMENT decls.

### Step 3 — Port subtask 1 (Walk lift from G_do, 6 helpers, ~95 lines)

worker: `prove_claim_in_lean`
inputs: ORIGINAL lines 142–233; refactor twins in `AcyclicPreservedUnderDo.lean`
  lines 446–568 give the first 5 helpers verbatim (already-solved
  reference port).
do: for each of the 6 helpers, add REPLACEMENT marker pair + design-choice
docstring + `refactor_`-prefixed body. Specifically:
- `refactor_mem_of_mem_hardInterventionOn` — body identical to twin in
  AcyclicPreservedUnderDo.lean:454–467 (verbatim copy).
- `refactor_Walk.refactor_liftWalkStep_of_hardInterventionOn` — typed-step
  version; matches twin in AcyclicPreservedUnderDo.lean:486–493.
- `refactor_Walk.refactor_liftFromHardIntervention` — matches twin in
  AcyclicPreservedUnderDo.lean:510–521 (note cons-cell takes 3 args
  `vMid s p` not 4 `vMid a h p`).
- `refactor_Walk.refactor_isDirectedWalk_liftFromHardIntervention` —
  matches twin in AcyclicPreservedUnderDo.lean:536–547 (per-case split on
  `.forwardE / .backwardE / .bidir`; the latter two close by `hp.elim`).
- `refactor_Walk.refactor_length_liftFromHardIntervention` — twin in
  AcyclicPreservedUnderDo.lean ~ lines 552–568 area; cons case uses
  `.cons _ _ p` 3-arg pattern.
- `refactor_Walk.refactor_vertices_liftFromHardIntervention` — **NEW** for
  this row (no twin). Body mirrors the original 227–233:
  `| _, _, .nil _ _ => rfl` and `| u, _, .cons _ _ p => congrArg (u :: ·) ih`
  (3-arg cons pattern).
risk: low. The first 5 are direct copies; #6 is a 4-line mechanical
adaptation. **Pure mechanical port.**

### Step 4 — Port subtask 2 (Walk composition, 5 helpers, ~160 lines)

worker: `prove_claim_in_lean`
inputs: ORIGINAL lines 266–326; sibling refactor port in
`AcyclicIffTopologicalOrder.lean` (the OLD `Walk.comp` lives there as the
canonical sibling, so check whether a refactor twin already exists there).
do: add 5 REPLACEMENT marker pairs:
- `refactor_Walk.refactor_comp` — recursive `def`, cons cell signature
  `.cons _ s p` (3-arg). Body: `| _, _, _, .nil _ _, q => q` /
  `| _, _, _, .cons v s p, q => .cons v s (p.refactor_comp q)`.
- `refactor_Walk.refactor_length_comp` — proof uses `refactor_length`,
  case-split on `.cons _ _ p` (3-arg). Mechanical.
- `refactor_Walk.refactor_isDirectedWalk_comp` — **non-trivial**: OLD
  proof obtained `⟨h1, h2, h3⟩` from `hp_dir`; NEW proof must case-split on
  the typed step `s`. The `.forwardE` case recurses; `.backwardE` and
  `.bidir` close by `hp.elim` (since `refactor_IsDirectedWalk` returns
  `False` on those branches). Same shape as
  AcyclicPreservedUnderDo.lean:536–547.
- `refactor_Walk.refactor_vertices_ne_nil` — mechanical, both arms reduce
  by `simp [refactor_vertices]`.
- `refactor_Walk.refactor_vertices_comp` — proof same as OLD modulo
  `vertices_comp → refactor_vertices_comp`, `vertices → refactor_vertices`,
  `cons _ a _ _` → `cons _ _ _` (3-arg). The `simp` call closes the same way.
risk: low. The `isDirectedWalk_comp` proof needs an honest step-case split
but the result is mechanical once you follow the pattern from
AcyclicPreservedUnderDo.

### Step 5 — Port subtask 3 (Walk lift to G_do, 5 helpers, ~200 lines)

worker: `prove_claim_in_lean`
inputs: ORIGINAL lines 414–546.
do: add 5 REPLACEMENT marker pairs:
- `refactor_Walk.refactor_head_mem_vertices` — mechanical (`simp
  [refactor_vertices]` closes both arms).
- `refactor_Walk.refactor_vertices_eq_head_cons_tail` — mechanical (both
  arms close by `rfl`).
- `refactor_Walk.refactor_vertices_directed_avoid_of_hardInterventionOn`
  — **non-trivial pattern-match rewrite**: OLD proof obtains `⟨ha_eq, ha_E,
  hp'_dir⟩ := hp_dir` and reads `vMid ∉ W` off `Finset.mem_filter.mp ha_E`
  using `ha_eq`. NEW: case-split on `s`, only `.forwardE h` survives
  `refactor_IsDirectedWalk`; `h : (u, vMid) ∈ G.refactor_hardInterventionOn
  W hW |>.E` already filters with `e.2 ∉ W`, so `vMid ∉ W` reads off
  `(Finset.mem_filter.mp h).2` directly — no `ha_eq` rewrite needed.
  `.backwardE` and `.bidir` close by `hp_dir.elim`.
- `refactor_Walk.refactor_liftTo_hardInterventionOn` — **most intricate
  port**: OLD `def` builds `hStepNew : G.WalkStep u a vMid` via `Or.inl
  ⟨..., Or.inl (Finset.mem_filter.mpr ...)⟩`. NEW must build
  `refactor_WalkStep (G.refactor_hardInterventionOn W hW) u vMid` via the
  `.forwardE` constructor: extract `h_E : (u, vMid) ∈ G.E` from the
  `refactor_IsDirectedWalk`'s `.forwardE _` step, then `.forwardE
  (Finset.mem_filter.mpr ⟨h_E, hvMid_notW⟩)`. The `cons` pattern signature
  becomes `.cons vMid s p'` (3-arg), and the recursion call passes the
  filtered step through. Helper computations `hvMid_V`, `hvMid_inHard`,
  `hp'_avoid` carry over verbatim modulo renames.
- `refactor_Walk.refactor_isDirectedWalk_liftTo_hardInterventionOn` —
  parallel rewrite: OLD case-split `⟨hp_dir.1, ?_, ?_⟩` becomes a
  structural match on the step's typed constructor; only `.forwardE`
  produces non-trivial content, recursing on `refactor_IsDirectedWalk`.
risk: medium. `liftTo_hardInterventionOn` is the deepest re-port because
the WalkStep is now data, not propositional. Careful with the `Finset.mem_filter.mpr`
packaging of the filter predicate.

### Step 6 — Port subtask 4 (Truncation, 8 helpers, ~225 lines)

worker: `prove_claim_in_lean`
inputs: ORIGINAL lines 644–901.
do: add 8 REPLACEMENT marker pairs:
- `refactor_WalkStep.refactor_source_mem` — **significant rewrite**.
  OLD body: `rcases h with ⟨ha_eq, ha_or⟩ | ⟨ha_eq, ha_E⟩`, then nested
  `rcases ha_or with ha_E | ha_L`, three case-conclusions via
  `G.hE_subset / G.hL_subset`. NEW body: pattern-match `h` against
  `.forwardE h | .backwardE h | .bidir h`; in each case extract `u`'s
  membership from the appropriate `G.hE_subset` / `G.hL_subset` projection
  (now applied to the typed witness directly without `rw [ha_eq]`).
  Under the refactor `G.hL_subset` takes a Sym2-membership shape:
  `hL_subset : ∀ s ∈ G.L, ∀ v ∈ s, v ∈ G.V`. For the `.bidir h` arm with
  `h : s(u, v) ∈ G.L`, conclude `u ∈ G.V` via
  `G.hL_subset h (Sym2.mem_mk_left u v)` (use `Sym2.mem_mk_left` /
  `Sym2.mem_mk_right` for "v ∈ s(u, v)"), then `Finset.mem_union_right`.
- `refactor_Walk.refactor_truncateAtFirst` — recursive `def`. Same shape
  as OLD modulo cons-cell becoming 3-arg (`vMid s p'` not `vMid a hStep
  p'`), and the by_cases on `t = u` is unchanged. The two-arm conditional
  builds `Walk.nil u (WalkStep.refactor_source_mem s)` or recurses; both
  arms now thread `s` instead of `(a, hStep)`.
- `refactor_Walk.refactor_truncateAtFirst_target_eq` — mechanical rewrite
  of the corresponding original.
- `refactor_Walk.refactor_length_truncateAtFirst_le` — mechanical.
- `refactor_Walk.refactor_isDirectedWalk_truncateAtFirst` —
  `obtain ⟨ha_eq, ha_E, hp_dir⟩ := hp_dir` → case-split `s`, only
  `.forwardE` survives and recurses.
- `refactor_Walk.refactor_mem_vertices_of_mem_dropLast` — mechanical
  one-liner (`List.mem_of_mem_dropLast`).
- `refactor_Walk.refactor_length_truncateAtFirst_lt_of_mem_dropLast` —
  mechanical port, uses `refactor_vertices_ne_nil` instead of `vertices_ne_nil`.
- `refactor_exists_directed_walk_v_not_in_dropLast` — the
  `Classical.dec` / `Nat.find` / `Nat.find_spec` / `Nat.find_min`
  machinery is identical; rename `Walk` / `IsDirectedWalk` / `length` /
  `vertices` → refactor-prefixed.
risk: medium. `WalkStep.source_mem` for the `.bidir` arm needs careful
handling of `hL_subset`'s new signature (`Sym2.Mem`-based instead of
ordered-pair). Worth a quick check of the canonical `Sym2.mem_mk_left`
API name in current mathlib.

### Step 7 — Port subtask 5 (Bifurcation walk construction, 6 helpers, ~110 lines)

worker: `prove_claim_in_lean`
inputs: ORIGINAL lines 1012–1111.
do: add 6 REPLACEMENT marker pairs:
- `refactor_Walk.refactor_reverseDirected` — **non-trivial rewrite**.
  OLD recursion builds the backward step via `Or.inr ⟨hqv_dir.1,
  hqv_dir.2.1⟩` (the disjunctive `WalkStep` shape's backward arm). NEW:
  case-split on the typed step `s` (only `.forwardE h_E` survives
  directedness); build `backStep : refactor_WalkStep G vMid c` as
  `.backwardE h_E` directly — the typed inductive's `.backwardE` already
  takes `h : (v, u) ∈ G.E`, matching `h_E : (c, vMid) ∈ G.E` from
  `.forwardE h_E`. Then `comp` the recursive reverse with a length-1
  backward walk built via `.cons c (.backwardE h_E) (.nil c
  (WalkStep.refactor_source_mem s))`. The two non-`.forwardE` cases of
  `s` in the cons branch close by `hqv_dir.elim` (since
  `refactor_IsDirectedWalk` returns `False` on `.backwardE` / `.bidir`).
- `refactor_Walk.refactor_length_reverseDirected` — mechanical, using
  `refactor_length_comp` and the same recursion shape.
- `refactor_Walk.refactor_vertices_reverseDirected` — same mechanical
  rewrite plus `refactor_vertices_comp`, `refactor_vertices_eq_head_cons_tail`.
- `refactor_Walk.refactor_mkBifurcation` — one-liner:
  `(refactor_reverseDirected qv hqv_dir).refactor_comp qw`.
- `refactor_Walk.refactor_length_mkBifurcation` — mechanical.
- `refactor_Walk.refactor_vertices_mkBifurcation` — mechanical.
risk: medium. `reverseDirected`'s `cons` case is the key spot where the
typed-step constructor swap (`Or.inr → .backwardE`) lands; the rest
threads through `refactor_comp` mechanically.

### Step 8 — Port subtask 6/7 (Bifurcation predicates + arm extraction, 5 helpers, ~310 lines)

worker: `prove_claim_in_lean` (likely dispatched as **two sub-dispatches**:
  first 8a covers 6a/6b/6c, second 8b covers the big extractor)
inputs: ORIGINAL lines 1207–1678.

**8a — `comp_assoc` + the three directed-hinge realisation lemmas:**
- `refactor_Walk.refactor_comp_assoc` — mechanical (3-arg cons pattern).
- `refactor_Walk.refactor_isBifurcationDirectedHinge_cons_backward_of_directed`
  — **rewrite needed**. OLD signature takes `(a : Node × Node) (h :
  G.WalkStep u a v)` — the `a` and the proposition. NEW signature drops
  `a`, takes `(s : refactor_WalkStep G u v)` and an explicit
  `h_back : ∃ h_E, s = .backwardE h_E`-style witness (or, cleaner: take
  `h_E : (v, u) ∈ G.E` as an extra arg and build `s := .backwardE h_E`
  inside the proof, dropping the original `ha_eq / ha_mem` data).
  Recommended signature:
  `refactor_isBifurcationDirectedHinge_cons_backward_of_directed
   {G u v w} (h_E : (v, u) ∈ G.E) (p : refactor_Walk G v w)
   (hp_dir : p.refactor_IsDirectedWalk) (hp_nonempty : p.refactor_length ≥ 1) :
   (refactor_Walk.cons v (.backwardE h_E) p)
       .refactor_IsBifurcationDirectedHingeWithSplit 0`.
  Proof: case-split `p` as in OLD — `.nil` contradicts `hp_nonempty`;
  `.cons _ _ _` lands directly in the predicate's third clause
  (`.cons _ (.backwardE _) (p@(.cons _ _ _)), 0 => p.refactor_IsDirectedWalk`),
  closed by `hp_dir`.
- `refactor_Walk.refactor_isBifurcationDirectedHinge_comp_reverseDirected_aux`
  — **non-trivial parametrised port**. OLD built `backStep` via `Or.inr`;
  NEW builds `backStep` as `.backwardE hqv_dir.h_E` where
  `hqv_dir.h_E` is the directed-walk witness extracted by case-splitting
  `s : refactor_WalkStep G c vMid`. The `cons` cell signature change
  (3-arg) propagates through; the `IsBifurcationDirectedHingeWithSplit`
  unfolding now uses the typed-step predicate (each clause's pattern
  match is on the constructor, not on `Or.inr ⟨...⟩`). The
  `refactor_comp_assoc` rewrite step is unchanged in spirit; the
  re-association consumes the same intermediate shape.
- `refactor_Walk.refactor_isBifurcationDirectedHinge_mkBifurcation` —
  consumer-facing wrapper. `match qv, hqv_dir, hqv_pos` becomes a
  `cases qv` + step case-split: `.nil _ _` contradicts `hpos`;
  `.cons vMid s qv'` requires `s = .forwardE h_E` (other constructors
  killed by `hqv_dir.elim` on `refactor_IsDirectedWalk`). Then build
  `backStep := .backwardE h_E` and call the base case (Helper 1) +
  the parametrised aux (Helper 2). Index arithmetic via `omega`
  unchanged.

**8b — the big arm extractor `exists_arms_of_bifurcation_directed_hinge`
  (~170 lines):**
- `refactor_Walk.refactor_exists_arms_of_bifurcation_directed_hinge` —
  **biggest port in this file**. Structural induction on `p` with `i`
  generalised; case-splits per the predicate's clauses.
  Key transformations:
  - Outer `induction p with | nil ... | @cons u w vMid a hStep p' ih =>`
    becomes `| @cons u w vMid s p' ih =>` (3-arg cons).
  - The base-case "cons _ a _ (.cons _ _ _ _), 0" branch unfolds the
    predicate as `a = (vMid, u) ∧ a ∈ G.E ∧ ...IsDirectedWalk` in OLD;
    in NEW the predicate's `.cons _ (.backwardE _) (p@(.cons _ _ _)), 0`
    clause directly returns `p.refactor_IsDirectedWalk`, but the OUTER
    cons step `s` MUST also be `.backwardE h_E` for the clause to fire
    — so a precondition that the `.forwardE / .bidir` constructors of
    `s` immediately produce `h_hinge.elim` (since the predicate's
    corresponding clauses return `False`). Case-split `s` first, then
    in the `.backwardE h_E` branch:
    - `forwardStep` (used to build `L`'s single forward edge from
      `vMid` to `u`) was OLD `Or.inl ⟨ha_eq, Or.inl ha_mem⟩`; NEW it is
      `.forwardE h_E` directly (the typed `.backwardE h_E`'s `h_E :
      (vMid, u) ∈ G.E` is the same data needed for `.forwardE` going
      the other way — note the **endpoint-index flip**: `.backwardE` on
      step `u → vMid` carries `(vMid, u) ∈ G.E`, and `.forwardE` on
      step `vMid → u` ALSO carries `(vMid, u) ∈ G.E`. Same proof term,
      different constructor wrapping).
    - All vertex-list bookkeeping (`hxv` case-split, `dropLast_cons_of_ne_nil`)
      ports mechanically with the `vertices → refactor_vertices` rename.
  - The `succ k` branch's `cases p'` and `obtain ⟨ha_eq, ha_mem,
    h_rec⟩ := h_hinge` similarly become: case-split `s` (only
    `.backwardE h_E` survives, the others kill via `h_hinge.elim`),
    then the recursion clause of the predicate
    `.cons _ (.backwardE _) p, k + 1 => p.refactor_IsBifurcationDirectedHingeWithSplit k`
    gives `h_hinge : p'.refactor_IsBifurcationDirectedHingeWithSplit k`
    directly (no `obtain` needed; the clause is already a single
    proposition).
  - The `forwardStep`, `single`, `L'.refactor_comp single` chain all
    port mechanically; `Walk.length_comp` → `refactor_length_comp`, etc.

  Recommendation: dispatch 8b as its own worker turn — it's by far the
  largest single helper (170 lines of OLD) and the predicate-clause
  matching is the riskiest piece. Pre-state the signature in the worker
  prompt to anchor the worker.

risk: high. Touching the directed-hinge predicate's clause-by-clause
case structure is the most error-prone spot. The predicate's new shape
(case-split on every constructor of `s` even in the `nil`-tail branch)
means OLD's `obtain ⟨_, _, h_rec⟩ := h_hinge` must be replaced by case-
splitting `s` first.

### Step 9 — Port the main theorem `bifurcationAlternative` (~190 lines body)

worker: `prove_claim_in_lean`
inputs: ORIGINAL lines 1881–2163.
do: add REPLACEMENT marker pair around the new
`refactor_bifurcationAlternative` theorem.
- Signature: same shape with all `CDMG → refactor_CDMG`, `Walk →
  refactor_Walk`, `Anc → refactor_Anc`, `hardInterventionOn →
  refactor_hardInterventionOn`, `IsBifurcationSource →
  refactor_IsBifurcationSource` substitutions. Three explicit binders
  `(hv : v ∈ G) (hw : w ∈ G) (hc : c ∈ G)` unchanged.
- (⇒) direction (1900–1990): same flow. `obtain ⟨huv_ne, hu_tail,
  hv_drop, i, h_hinge, h_src⟩ := h_bif` → unchanged because
  `refactor_IsBifurcationSource`'s 4-conjunct shape is identical. Then
  `refactor_exists_arms_of_bifurcation_directed_hinge` replaces the OLD
  call. The `liftTo_hardInterventionOn` invocations (final `refine` arms)
  rename to `refactor_liftTo_hardInterventionOn` /
  `refactor_isDirectedWalk_liftTo_hardInterventionOn`.
- (⇐) direction (1991–2163): same flow but every helper renamed. Key
  pieces:
  - `exists_directed_walk_v_not_in_dropLast` →
    `refactor_exists_directed_walk_v_not_in_dropLast`.
  - `Walk.vertices_directed_avoid_of_hardInterventionOn` → refactor
    twin.
  - The inline `hvert_len_succ` lemma (lines 2012–2020) — `induction q
    with | nil _ _ => rfl | cons _ _ _ q' ih =>` becomes `cons _ _ q' ih`
    (3-arg).
  - All `Walk.cons`-pattern `cases q_v_Gdow with | nil ... | cons _ _ _ _`
    case-splits become 3-arg `cons _ _ _`.
  - `Walk.length_liftFromHardIntervention` /
    `Walk.vertices_liftFromHardIntervention` → refactor-prefixed.
  - `Walk.isBifurcationDirectedHinge_mkBifurcation` → refactor twin
    (whose signature matches OLD modulo refactor names).
  - The final 4 `refine ⟨..., ?_, ?_, qv.length - 1, ?_, ?_⟩` arms
    discharge the 4 conjuncts of `refactor_IsBifurcationSource` — the
    clause shape is unchanged, only the helpers it calls are renamed.
risk: medium-low. The proof flow is identical; this is essentially a
massive rename pass with the `cons _ _ _ _` → `cons _ _ _` adjustment
in every `cases`/`induction`.

### Step 10 — Verifier chain + design comments + solved

worker(s) sequentially:
1. `review_design` — read the refactor's overall structure, confirm the
   design-choice docstrings on the major new declarations
   (`refactor_bifurcationAlternative`, `refactor_mkBifurcation`,
   `refactor_exists_arms_of_bifurcation_directed_hinge`,
   `refactor_liftTo_hardInterventionOn`) explain why the typed-step
   port works the same as the OLD untyped one. Tex twin not needed,
   so design review focuses on Lean side.
2. `verify_equivalence` — confirm `refactor_bifurcationAlternative`
   matches the LN block's content (same iff, same three conjuncts,
   same intervention pattern) under the new types.
3. `verify_equivalence_strict` — the solved-gate runs this anyway, but
   dispatch it explicitly here so the manager catches any issue before
   the gate. If it fails, that's a signal that some refactor name didn't
   resolve, or that a helper's signature changed in a way that breaks
   strict equivalence.
4. `add_design_choice_comments` — add the load-bearing comments to the
   new REPLACEMENT decls (mirror the pattern from
   AcyclicPreservedUnderDo.lean's REPLACEMENT block). Focus on the
   spots where the port made a non-obvious choice (e.g. the
   `Sym2.mem_mk_left` call in `refactor_WalkStep.refactor_source_mem`'s
   bidir arm).
5. `solved` — emit terminal action. The solved-gate runs
   `verify_row_solved` which re-runs strict equivalence and the build.

## Run history

_(turn 1 — orienting, dispatching make_plan)_
_(turn 1 — plan worker: appended 10-step subtask plan above; reports
back to manager)_
