# Workspace for claim_3_18 — MarginalizationAndIntervention

This file is the manager's scratchpad for this row. Use it for:

- The plan (output of `make_plan` worker)
- A running list of what has been tried and why it didn't work
- Notes for the next manager (if you `new_manager`-handoff or
  the run ends and a future invocation picks this row up again)

It is YAML-untyped markdown — feel free to add sections.

---

# claim_3_18 — Refactor porting plan (DEPENDENT row, refactor `cdmg_typed_edges`)

**Row.** `claim_3_18` (Lemma: *Marginalization and intervention commute*),
section 3.2, three theorems in one Lean file.

**Refactor roots.** `def_3_1` (`CDMG` → `refactor_CDMG`: `L : Finset (Sym2 Node)`,
no `hL_symm`, `hL_irrefl` via `¬ s.IsDiag`) and `def_3_4` (typed
`refactor_WalkStep` with constructors `.forwardE / .backwardE / .bidir`).

**Target file.** `Section3_2/MarginalizationAndIntervention.lean`
(currently 4644 lines, 110 declarations). The file imports
`refactor_CDMG`, `refactor_marginalize`, `refactor_hardInterventionOn`,
`refactor_extendingCDMGsWith`, `refactor_nodeSplittingOn`, `refactor_Walk`,
`refactor_IsDirectedWalk`, `refactor_IsBifurcation`, etc. from the
already-refactored upstream files (verified on disk).

**Target tex twin.** `tex/refactor_claim_3_18_proof_MarginalizationAndIntervention.tex`
(write the proof there; the existing
`tex/claim_3_18_proof_MarginalizationAndIntervention.tex` stays untouched
until Phase 7 cleanup).

**Upstream refactored APIs (verified in place).**

| Upstream | File | After-refactor shape |
|---|---|---|
| `refactor_CDMG` | `Section3_1/CDMG.lean:189-393` | `L : Finset (Sym2 Node)`; no `hL_symm`; `hL_irrefl s = ¬ s.IsDiag` |
| `refactor_WalkStep` | `Section3_1/Walks.lean:1364-1371` | `.forwardE h / .backwardE h / .bidir h` (typed channel) |
| `refactor_Walk` | `Section3_1/Walks.lean:1505-1512` | `.cons v s p` (no stored ordered pair `a`; just the typed step `s`) |
| `refactor_IsDirectedWalk` | `Walks.lean:2031-2039` | `.forwardE _ → p.rec ; .backwardE/.bidir → False` |
| `refactor_IsBifurcationWithSplit` | `Walks.lean:2442-2456` | 10-branch pattern-match (3 step tags × 3 tail/k shapes + nil) |
| `refactor_IsBifurcation` | `Walks.lean:2523-2531` | 4-conjunct (uses `refactor_vertices`, `refactor_IsBifurcationWithSplit`) |
| `refactor_marginalize` | `Section3_2/MarginalizationAK.lean:1011-1029` | `L := ((G.V\W)×ˢ(G.V\W)).filter (e.1≠e.2 ∧ Φ_L W).image (fun e => s(e.1,e.2))` |
| `refactor_hardInterventionOn` | `Section3_2/HardInterventionOn.lean:809-820` | `L := G.L.filter (fun s => ∀ v∈s, v∉W)`; no symmetric ordered-pair pattern |
| `refactor_extendingCDMGsWith` | `Section3_2/ExtendingCDMGsWith.lean:1065-1078` | `L := G.L.image (Sym2.map IntExtNode.unsplit)` |
| `refactor_nodeSplittingOn` | `Section3_2/NodeSplittingOn.lean:1581-1597` | `L := G.L.image (Sym2.map (refactor_toCopy0 W))`; carrier is `refactor_CDMG (refactor_SplitNode Node)` (note: `refactor_SplitNode`, NOT `SplitNode`) |
| `refactor_SplitNode` + `refactor_toCopy0/1` | `NodeSplittingOn.lean:703 / 770 / 783` | constructors `.unsplit / .copy0 / .copy1` (same shape; renamed carrier) |
| Walk utilities (`refactor_vertices_eq_head_cons_tail`, `refactor_tail_vertices_ne_nil_of_pos`, `refactor_vertices_ne_nil`, `refactor_head_mem_vertices`, `refactor_length_pos_of_isBifurcation`, `refactor_tail_getLast_of_pos`, `refactor_vertices_getLast`) | `MargPreservesAncestors.lean:4072-6526` | available as `refactor_Walk.refactor_<name>` |

---

## 1. Inventory of the 110 declarations

(All counts grouped by part. Line numbers refer to the *current* file
state; the replacement clones will be appended after each ORIGINAL block.)

### Shared helpers (lines 97-272, 4 lemmas)

| # | Line | Name | Role |
|---|---|---|---|
| H1 | 126 | `subset_sdiff_of_disjoint` | Generic Finset helper |
| H2 | 169 | `subset_carrier_of_marginalize` | Pre-image of marg carrier (used by Parts i/ii) |
| H3 | 209 | `image_unsplit_subset_extendingCDMGsWith_V` | Image lift for Part ii |
| H4 | 258 | `image_unsplit_subset_nodeSplittingOn_V_of_disjoint` | Image lift for Part iii |

### Part i — hard intervention (lines 274-827, 17 declarations)

Walk surgery (proof-only):
| # | Line | Name | Role |
|---|---|---|---|
| Pi1 | 285 | `mem_doit_of_mem_G` | carrier ascent (G → doit) |
| Pi2 | 296 | `mem_G_of_mem_doit` | carrier descent (doit → G) |
| Pi3 | 307 | `walkStep_ofDoit` | WalkStep descent doit → G |
| Pi4 | 318 | `walk_ofDoit` (def) | Walk descent doit → G |
| Pi5 | 324 | `walk_ofDoit_length` | length preservation |
| Pi6 | 333 | `walk_ofDoit_vertices` | vertices preservation |
| Pi7 | 342 | `walk_ofDoit_isDirectedWalk` | IsDirectedWalk pres. on descent |
| Pi8 | 352 | `walk_ofDoit_isBifurcationWithSplit` | BifurcationWithSplit pres. |
| Pi9 | 377 | `walk_ofDoit_isBifurcation` | IsBifurcation pres. (wrapper) |
| Pi10 | 387 | `walkStep_toDoit` | WalkStep ascent G → doit (general) |
| Pi11 | 408 | `walkStep_toDoit_dir` | WalkStep ascent (.forwardE-only) |
| Pi12 | 430 | `lift_dir_walk_to_doit` | Walk ascent (directed) by induction |
| Pi13 | 462 | `lift_bifWithSplit_to_doit_aux` | Walk ascent (BifurcationWithSplit) |

Φ iff lemmas:
| # | Line | Name | Role |
|---|---|---|---|
| Pi14 | 540 | `doit_marg_PhiE_iff` | Φ_E iff doit ↔ G |
| Pi15 | 571 | `doit_marg_PhiL_iff` | Φ_L iff doit ↔ G |

Field equality and main theorem:
| # | Line | Name | Role |
|---|---|---|---|
| Pi16 | 641 | `doit_marg_E_field_eq` | E-field equality |
| Pi17 | 701 | `doit_marg_L_field_eq` | L-field equality (Sym2-image now) |
| **Pi18** | **802** | **`marginalize_hardInterventionOn_comm`** | **MAIN THEOREM (Part i)** |

### Part ii — adding intervention nodes (lines 898-1771, 26 declarations)

Walk-surgery ascent (G → ext):
| # | Line | Name | Role |
|---|---|---|---|
| Pii1 | 898 | `mem_ext_of_mem_G_unsplit` | carrier ascent through `.unsplit` |
| Pii2 | 911 | `walkStep_toExt` | WalkStep ascent G → ext |
| Pii3 | 935 | `walk_toExt` (def) | Walk ascent G → ext |
| Pii4 | 946 | `walk_toExt_length` | length pres. |
| Pii5 | 954 | `walk_toExt_vertices` | vertices pres. (with `.map .unsplit`) |
| Pii6 | 963 | `walk_toExt_isDirectedWalk` | IsDirectedWalk pres. on ascent |
| Pii7 | 976 | `walk_toExt_isBifurcationWithSplit` | BifurcationWithSplit pres. |
| Pii8 | 1015 | `walk_toExt_isBifurcation` | IsBifurcation pres. |

Walk-surgery descent (ext → G, `.unsplit`-pinned):
| # | Line | Name | Role |
|---|---|---|---|
| Pii9 | 1066 | `walkStep_ofExt_unsplit` | WalkStep descent through `.unsplit_pair` |
| Pii10 | 1139 | `image_unsplit_sdiff` | image-sdiff identity |
| Pii11 | 1157 | `mem_G_of_unsplit_mem_ext` | carrier descent through `.unsplit` |
| Pii12 | 1178 | `list_unsplit_tail` | list utility |
| Pii13 | 1185 | `list_unsplit_dropLast` | list utility |
| Pii14 | 1196 | `list_unsplit_tail_dropLast` | list utility |
| Pii15 | 1204 | `a_in_G_E_of_lifted_in_ext` | E-edge descent through `.unsplit`-pair |
| Pii16 | 1229 | `a_in_G_L_of_lifted_in_ext` | L-edge descent (now `Sym2`!) |
| Pii17 | 1248 | `pair_eq_of_unsplit_eq` | pair-equality helper |
| Pii18 | 1262 | `walk_ofExt_unsplit_full` | full Walk descent (heavy) |
| Pii19 | 1373 | `all_unsplit_of_interior_W_image` | interior-vertex tagging |

Φ iff for Part ii:
| # | Line | Name | Role |
|---|---|---|---|
| Pii20 | 1402 | `ext_marg_PhiE_iff_unsplit` | Φ_E iff ext ↔ G |
| Pii21 | 1435 | `ext_marg_PhiL_iff_unsplit` | Φ_L iff ext ↔ G |
| Pii22 | 1511 | `walk_intCopy_target_unsplit` | intervention-walk transfer-edge handler |

Field equality and main theorem:
| # | Line | Name | Role |
|---|---|---|---|
| Pii23 | 1566 | `ext_marg_E_field_eq` | E-field equality |
| Pii24 | 1693 | `ext_marg_L_field_eq` | L-field equality (Sym2.map on both sides) |
| **Pii25** | **1746** | **`marginalize_extendingCDMGsWith_comm`** | **MAIN THEOREM (Part ii)** |

### Part iii — node-splitting (lines 1838-4640, 56 declarations + 1 main theorem)

(Largest sub-block; subdivided into 6 sub-phases below for ordering.)

**iii.A — Carrier helpers / sdiff / constructor disjointness (lines 1838-2052):**

| # | Line | Name |
|---|---|---|
| Piii1 | 1838 | `image_split_unsplit_sdiff` |
| Piii2 | 1860 | `unsplit_image_disjoint_copy0` |
| Piii3 | 1869 | `unsplit_image_disjoint_copy1` |
| Piii4 | 1879 | `mem_G_of_unsplit_mem_split` |
| Piii5 | 1903 | `toCopy0_unsplit_of_notW` |
| Piii6 | 1907 | `toCopy1_unsplit_of_notW` |
| Piii7 | 1913 | `lifted_edge_in_split_E` |
| Piii8 | 1933 | `mem_split_of_mem_G_unsplit` |
| Piii9 | 1948 | `mem_split_of_mem_W₁_copy0` |
| Piii10 | 1960 | `mem_split_of_mem_W₁_copy1` |
| Piii11 | 1973 | `lifted_E_in_split_E_generic` |
| Piii12 | 1983 | `lifted_L_in_split_L_generic` |
| Piii13 | 1992 | `unsplit_notW₁_of_unsplit_mem_split` |
| Piii14 | 2021 | `mem_W₁_of_copy0_mem_split` |
| Piii15 | 2038 | `mem_W₁_of_copy1_mem_split` |

**iii.B — Walk ascent G → split, `.unsplit`-tagged (lines 2060-2256):**

| # | Line | Name |
|---|---|---|
| Piii16 | 2060 | `walkStep_toSplit` |
| Piii17 | 2100 | `walk_toSplit_unsplit` (def) |
| Piii18 | 2120 | `walk_toSplit_unsplit_length` |
| Piii19 | 2129 | `walk_toSplit_unsplit_vertices` |
| Piii20 | 2139 | `walk_toSplit_unsplit_isDirectedWalk` |
| Piii21 | 2158 | `walk_toSplit_unsplit_isBifurcationWithSplit` |
| Piii22 | 2225 | `walk_toSplit_unsplit_isBifurcation` |

**iii.C — Walk descent split → G, `.unsplit`-pinned (lines 2266-2570):**

| # | Line | Name |
|---|---|---|
| Piii23 | 2266 | `node_of_toCopy1_unsplit` |
| Piii24 | 2275 | `node_of_toCopy0_unsplit` |
| Piii25 | 2290 | `walkStep_ofSplit_unsplit` (heavy) |
| Piii26 | 2357 | `list_split_unsplit_tail` |
| Piii27 | 2363 | `list_split_unsplit_dropLast` |
| Piii28 | 2373 | `list_split_unsplit_tail_dropLast` |
| Piii29 | 2379 | `pair_eq_of_split_unsplit_eq` |
| Piii30 | 2392 | `a_in_G_E_of_lifted_in_split` |
| Piii31 | 2413 | `a_in_G_L_of_lifted_in_split` (Sym2!) |
| Piii32 | 2431 | `walk_ofSplit_unsplit_full` (very heavy) |
| Piii33 | 2543 | `all_unsplit_of_interior_W_image_split` |

**iii.D — toCopy0/1 walk-surgery (Part iii E-field, lines 2580-3604):**

| # | Line | Name |
|---|---|---|
| Piii34 | 2580 | `mem_split_of_mem_G_toCopy0` |
| Piii35 | 2590 | `toCopy0_inj_node` |
| Piii36 | 2602 | `mem_split_V_marg_of_mem_V_W₂_toCopy0` |
| Piii37 | 2632 | `toCopy0_ne_copy1` |
| Piii38 | 2640 | `exists_underlying_of_mem_split_V_marg_not_copy1` |
| Piii39 | 2676 | `exists_lifted_dir_walk_to_split_endTarget` (heavy) |
| Piii40 | 2799 | `exists_lifted_bifWithSplit_to_split` (very heavy) |
| Piii41 | 3076 | `exists_lifted_bif_to_split` |
| Piii42 | 3147 | `walk_copy0_target_copy1` (heavy) |
| Piii43 | 3216 | `walk_G_lift_to_split` (heavy) |
| Piii44 | 3316 | `walk_split_descend_to_G` (heavy) |
| Piii45 | 3487 | `split_marg_PhiE_iff` |
| Piii46 | 3516 | `walk_target_copy1_source_copy0` (heavy) |
| Piii47 | 3606 | `split_marg_E_field_eq` (huge) |

**iii.E — Part iii L-field helpers (lines 3937-4463):**

| # | Line | Name |
|---|---|---|
| Piii48 | 3937 | `pair_eq_of_toCopy0_eq` |
| Piii49 | 3945 | `toCopy1_eq_toCopy0_imp_notW` |
| Piii50 | 3959 | `a_in_G_E_of_toCopy0_lifted_in_split` |
| Piii51 | 3980 | `a_in_G_L_of_toCopy0_lifted_in_split` (Sym2!) |
| Piii52 | 3996 | `walkStep_ofSplit_toCopy0` (heavy) |
| Piii53 | 4060 | `mem_G_of_toCopy0_mem_split` |
| Piii54 | 4069 | `list_toCopy0_tail` |
| Piii55 | 4075 | `list_toCopy0_dropLast` |
| Piii56 | 4088 | `walk_ofSplit_toCopy0_full` (very heavy) |
| Piii57 | 4181 | `all_toCopy0_of_interior_W_image_split` |
| Piii58 | 4210 | `split_marg_PhiL_iff` |
| Piii59 | 4290 | `not_bif_source_copy1` (very heavy; **HIGH RISK**) |
| Piii60 | 4389 | `not_bif_target_copy1_aux` (very heavy; **HIGH RISK**) |
| Piii61 | 4454 | `not_bif_target_copy1` |

**iii.F — L-field equality and main theorem:**

| # | Line | Name |
|---|---|---|
| Piii62 | 4466 | `split_marg_L_field_eq` (huge; Sym2 on both sides) |
| **Piii63** | **4578** | **`marginalize_nodeSplittingOn_comm`** (MAIN THEOREM, Part iii) |

---

## 2. Per-declaration refactor verdict

Three buckets:

* **MECHANICAL** — pure name-retarget (`CDMG → refactor_CDMG`,
  `marginalize → refactor_marginalize`, `Walk → refactor_Walk`,
  `vertices → refactor_vertices`, `length → refactor_length`,
  `IsDirectedWalk → refactor_IsDirectedWalk`, …, plus
  `SplitNode → refactor_SplitNode` / `toCopy0/1 → refactor_toCopy0/1`
  for Part iii). No constructor case-splits, no Sym2 dance, body
  ports byte-identical modulo renames.
* **STRUCTURAL** — needs body rewrite because the underlying type
  changed materially. Two shape changes:
  1. WalkStep destructure: any `rcases h with ⟨ha, hOr⟩ | ⟨ha, hE⟩`
     (the old ordered-pair-plus-Prop `WalkStep` disjunction) and
     `match _, p, h with | … .cons _ a hStep p, … =>` (the old 4-arg
     cons pattern) becomes `cases s with | forwardE h_E | backwardE h_E | bidir hL`
     (case-split on the typed `refactor_WalkStep` constructor) and
     `cons _ s p` (3-arg cons pattern). Cons constructions
     `Walk.cons v a hStep` become `refactor_Walk.cons v (.forwardE h_E)`
     (or `.backwardE` / `.bidir`); the `IsDirectedWalk` triple
     `⟨ha, hE, hRec⟩` collapses to just `hRec`. The `walkStep_*`
     helpers — both ascent and descent — collapse from a 2-disjunct
     case split to a 3-constructor `cases s` pattern.
  2. L-membership reshape: any `a ∈ G.L` test on an ordered pair
     becomes `s(u, v) ∈ G.L` on a `Sym2 Node`. Filter / image / sdiff
     calls over `G.L` retarget accordingly. For the
     `hardInterventionOn` filter, `Finset.mem_filter` of the L-filter
     reshapes from `⟨hL, hu, hv⟩` (one membership + two
     not-in-W conjuncts on the ordered pair) to `⟨hL, h_ball⟩` where
     `h_ball : ∀ v ∈ s, v ∉ W`. For `extendingCDMGsWith`, the lift
     is `Sym2.map IntExtNode.unsplit` (acts via `Sym2.map_pair`); for
     `nodeSplittingOn`, the lift is `Sym2.map (refactor_toCopy0 W)`.
* **GLUE/NEW** — a small helper anticipated to need adding (e.g.\ an
  `s(u,v) ↔ ordered-pair` Sym2 bridge or a `Sym2.map` membership
  helper).

### Shared helpers

| # | Verdict | Notes |
|---|---|---|
| H1 `subset_sdiff_of_disjoint` | **MECHANICAL** | already ported as `refactor_subset_sdiff_of_disjoint` in MarginalizationsCommute; copy verbatim and re-prove under `refactor_` prefix. |
| H2 `subset_carrier_of_marginalize` | **MECHANICAL** | `marginalize → refactor_marginalize`; carrier `J ∪ (V\W)` unchanged. |
| H3 `image_unsplit_subset_extendingCDMGsWith_V` | **MECHANICAL** | `extendingCDMGsWith.V = G.V.image IntExtNode.unsplit` unchanged. |
| H4 `image_unsplit_subset_nodeSplittingOn_V_of_disjoint` | **MECHANICAL +** | rename `SplitNode → refactor_SplitNode`; `nodeSplittingOn.V` shape unchanged. |

### Part i (hard intervention)

| # | Verdict | Notes |
|---|---|---|
| Pi1 `mem_doit_of_mem_G` | **MECHANICAL** | hardInterventionOn.J/V unchanged. |
| Pi2 `mem_G_of_mem_doit` | **MECHANICAL** | same. |
| Pi3 `walkStep_ofDoit` | **STRUCTURAL** | rewrite as `cases s with | forwardE hE => …forwardE _, Finset.mem_filter.mp hE.1… | backwardE hE => … | bidir hL => …`. For `.bidir`, the L-filter under `hardInterventionOn` is `G.L.filter (fun s => ∀ v∈s, v∉W)`, so the L-edge witness extracts via `Finset.mem_filter.mp h |>.1`. |
| Pi4 `walk_ofDoit` (def) | **STRUCTURAL** | `Walk.cons v a hStep p → refactor_Walk.cons v (walkStep_ofDoit_refactor hStep) p` — pass a single typed step through. |
| Pi5 `walk_ofDoit_length` | **MECHANICAL** | structural recursion on `refactor_Walk`. |
| Pi6 `walk_ofDoit_vertices` | **MECHANICAL** | same. |
| Pi7 `walk_ofDoit_isDirectedWalk` | **STRUCTURAL** | recurse on `s with | .forwardE _ => …` (only branch that survives); `.backwardE / .bidir` discharge from `hp_dir.elim`. |
| Pi8 `walk_ofDoit_isBifurcationWithSplit` | **STRUCTURAL** | 10-branch pattern-match analogous to the new `refactor_IsBifurcationWithSplit`; admit only `.bidir _, (.nil _ _), 0`, `.backwardE _, (.cons …), 0`, `.bidir _, (.cons …), 0`, `.backwardE _, _, k+1`. |
| Pi9 `walk_ofDoit_isBifurcation` | **MECHANICAL** | wrapper over Pi8 + vertex rewrites. |
| Pi10 `walkStep_toDoit` | **STRUCTURAL** | rewrite as `cases h with | forwardE h_E => …forwardE …Finset.mem_filter.mpr ⟨h_E, hv⟩… | backwardE h_E => …backwardE …Finset.mem_filter.mpr ⟨h_E, hu⟩… | bidir hL => …bidir …Finset.mem_filter.mpr ⟨hL, fun v hv_s => …⟩…`. **The bidir branch is the key Sym2 shift**: the L-filter predicate is `fun s => ∀ v ∈ s, v ∉ W` (no longer the asymmetric `e.1 ∉ W ∧ e.2 ∉ W` on ordered pairs). Need to discharge `∀ v ∈ s(u,v_mid), v ∉ W` from `hu : u ∉ W` and `hv : v_mid ∉ W`. Use `Sym2.mem_iff.mp` → case-split on `v = u ∨ v = v_mid`. |
| Pi11 `walkStep_toDoit_dir` | **STRUCTURAL** | specialisation of Pi10 to the `.forwardE` branch. Much shorter than the general one. |
| Pi12 `lift_dir_walk_to_doit` | **STRUCTURAL** | induction with `cons` destructure; case-split on `s : refactor_WalkStep` and re-cons with the lifted step. |
| Pi13 `lift_bifWithSplit_to_doit_aux` | **STRUCTURAL** | the heaviest helper. Original has `match i, p', hSpl with | 0, .nil _ _, hSpl => … | 0, .cons _ _ _ _, hSpl => … | k+1, _, hSpl => …`. Port: nested `match` whose inner cases now case-split on `s : refactor_WalkStep` (only the surviving constructors per the new `refactor_IsBifurcationWithSplit` branches). |
| Pi14 `doit_marg_PhiE_iff` | **MECHANICAL** | pure plumbing over Pi4 / Pi5 / Pi6 / Pi12. |
| Pi15 `doit_marg_PhiL_iff` | **MECHANICAL** | pure plumbing over Pi9 / Pi13 + `refactor_length_pos_of_isBifurcation`. |
| Pi16 `doit_marg_E_field_eq` | **STRUCTURAL (light)** | filter equality. The E side is unchanged structurally (E is still `Finset (Node×Node)`). Body retargets `MarginalizationΦE → refactor_MarginalizationΦE` etc. Carrier `J / V` rewrites are unchanged. |
| Pi17 `doit_marg_L_field_eq` | **STRUCTURAL (Sym2)** | L on the LHS is `((refactor_marginalize on doit-CDMG).L) = ((((G.V\W₁)\W₂)×ˢ((G.V\W₁)\W₂)).filter (… ∧ Φ_L)).image (fun e => s(e.1, e.2))`; L on the RHS is `((refactor_hardInterventionOn (marg G)).L) = ((((G.V\W₂)×ˢ(G.V\W₂)).filter (… ∧ Φ_L)).image (fun e => s(e.1, e.2))).filter (fun s => ∀ v ∈ s, v ∉ W₁)`. Pattern: peel the outer `Finset.image (Sym2.mk)` on both sides, reduce to ordered-pair filter equality, close via Pi15. The **Sym2 dance**: extract pre-image via `Finset.mem_image.mp`, get `Sym2.mk e_1 e_2 = s`, then route through `Finset.mem_filter`, etc. See `refactor_marg_L_field_eq` in `MarginalizationsCommute.lean:7049-7068` for the **canonical template** (`congr 1; apply Finset.filter_congr` after peeling `image`). |
| Pi18 `marginalize_hardInterventionOn_comm` | **STRUCTURAL** | The local `cdmgExt` `have`-lemma rintro destructures 9-field `CDMG` → 8-field `refactor_CDMG` (drop `hL_symm` slot). The four-field check `J / V / E / L` is unchanged. |

### Part ii (adding intervention nodes)

| # | Verdict | Notes |
|---|---|---|
| Pii1 `mem_ext_of_mem_G_unsplit` | **MECHANICAL** | ext.J/V shape unchanged. |
| Pii2 `walkStep_toExt` | **STRUCTURAL** | `cases h with | forwardE hE => …forwardE …Finset.mem_union_left …Finset.mem_image.mpr⟨(u,v),hE,rfl⟩… | backwardE hE => … | bidir hL => …bidir …Finset.mem_image.mpr⟨_,hL,?⟩…`. **Sym2 shift on bidir**: `extendingCDMGsWith.L = G.L.image (Sym2.map IntExtNode.unsplit)`. Need `s(.unsplit u, .unsplit v) ∈ G.L.image (Sym2.map .unsplit)` from `s(u,v) ∈ G.L` — use `Sym2.map_pair_eq` lemma (or `Finset.mem_image.mpr ⟨s(u,v), hL, rfl⟩` and `Sym2.map_mk`). |
| Pii3 `walk_toExt` (def) | **STRUCTURAL** | recursion shape change. Note: the original passed `a = (a.1, a.2)` to `Walk.cons`; the refactor passes just the typed step. The step's endpoints `(.unsplit u, .unsplit v)` come from the typed step's indices, NOT from a stored ordered pair. |
| Pii4 `walk_toExt_length` | **MECHANICAL** | |
| Pii5 `walk_toExt_vertices` | **MECHANICAL** | |
| Pii6 `walk_toExt_isDirectedWalk` | **STRUCTURAL** | recurse on `s`; only `.forwardE` survives. |
| Pii7 `walk_toExt_isBifurcationWithSplit` | **STRUCTURAL** | 10-branch port analogous to Pi8. |
| Pii8 `walk_toExt_isBifurcation` | **MECHANICAL** | wrapper. |
| Pii9 `walkStep_ofExt_unsplit` | **STRUCTURAL** | the heaviest of Part ii. The descent has to read off the channel from `s : refactor_WalkStep`, AND for the `.bidir` branch test whether `s(u', v')` lifts from `G.L` (via `Sym2.map IntExtNode.unsplit`) or is a fresh transfer edge. Since `extendingCDMGsWith.L = G.L.image (Sym2.map .unsplit)`, every `.bidir` step in ext lifts from a `.bidir` step in G — *no transfer-edge case to rule out at L*. The E side still needs to exclude the transfer edge `(.intCopy w, .unsplit w)` when both endpoints are `.unsplit`-tagged. Total structural rewrite. |
| Pii10 `image_unsplit_sdiff` | **MECHANICAL** | |
| Pii11 `mem_G_of_unsplit_mem_ext` | **STRUCTURAL (light)** | extendingCDMGsWith.J shape unchanged. |
| Pii12-14 list utilities | **MECHANICAL** | three list lemmas. |
| Pii15 `a_in_G_E_of_lifted_in_ext` | **STRUCTURAL** | E-edge filter unchanged in shape; port mechanically modulo `WalkStep` references. |
| Pii16 `a_in_G_L_of_lifted_in_ext` | **STRUCTURAL (Sym2)** | **KEY Sym2 RESHAPE**. Original: `(a ∈ ext.L) → (a.1, a.2) ∈ G.L.image .unsplit_pair → exists a' ∈ G.L`. New: `(s ∈ ext.L) ↔ ∃ s' ∈ G.L, s = Sym2.map .unsplit s'`. Use `Finset.mem_image.mp` over `Sym2.map IntExtNode.unsplit`. |
| Pii17 `pair_eq_of_unsplit_eq` | **MECHANICAL** | constructor injectivity. |
| Pii18 `walk_ofExt_unsplit_full` | **STRUCTURAL (heavy)** | full Walk descent — recurses through ascent-back logic with the new WalkStep destructure. |
| Pii19 `all_unsplit_of_interior_W_image` | **MECHANICAL** | |
| Pii20 `ext_marg_PhiE_iff_unsplit` | **MECHANICAL** | |
| Pii21 `ext_marg_PhiL_iff_unsplit` | **MECHANICAL** | |
| Pii22 `walk_intCopy_target_unsplit` | **STRUCTURAL (heavy)** | transfer-edge walk surgery; rewrite the step-construction at the transfer-edge entry. |
| Pii23 `ext_marg_E_field_eq` | **STRUCTURAL** | filter / image equality on E; port over the new constructors. |
| Pii24 `ext_marg_L_field_eq` | **STRUCTURAL (Sym2)** | Sym2 image dance: peel `.image (Sym2.mk)` on inner-marg side and `.image (Sym2.map IntExtNode.unsplit)` on outer-ext side. Reduce to ordered-pair filter equality + iff via Pii21. **Probably needs a new GLUE helper**: `Sym2.map_image_filter` style — see GLUE/NEW below. |
| Pii25 `marginalize_extendingCDMGsWith_comm` | **STRUCTURAL** | cdmgExt destructure shrinks 9→8 fields. |

### Part iii (node-splitting)

| # | Verdict | Notes |
|---|---|---|
| Piii1 `image_split_unsplit_sdiff` | **MECHANICAL** | `SplitNode → refactor_SplitNode`. |
| Piii2-3 disjointness lemmas | **MECHANICAL** | rename. |
| Piii4 `mem_G_of_unsplit_mem_split` | **STRUCTURAL (light)** | nodeSplittingOn.V shape unchanged. |
| Piii5-6 `toCopy{0,1}_unsplit_of_notW` | **MECHANICAL** | rename `toCopy0/1 → refactor_toCopy0/1`. |
| Piii7 `lifted_edge_in_split_E` | **MECHANICAL** | E-shape unchanged. |
| Piii8-10 `mem_split_of_*` | **STRUCTURAL (light)** | nodeSplittingOn.V shape unchanged. |
| Piii11 `lifted_E_in_split_E_generic` | **MECHANICAL** | E-shape unchanged. |
| Piii12 `lifted_L_in_split_L_generic` | **STRUCTURAL (Sym2)** | **KEY Sym2**: nodeSplittingOn.L is now `G.L.image (Sym2.map refactor_toCopy0)`. Original: `(u, v) ∈ G.L → (toCopy0 u, toCopy0 v) ∈ split.L`. New: `s(u, v) ∈ G.L → s(toCopy0 u, toCopy0 v) = Sym2.map toCopy0 s(u,v) ∈ split.L`. |
| Piii13-15 various `mem_*` | **STRUCTURAL (light)** | |
| Piii16 `walkStep_toSplit` | **STRUCTURAL** | port the WalkStep ascent. |
| Piii17 `walk_toSplit_unsplit` (def) | **STRUCTURAL** | recursion shape change. |
| Piii18-19 length / vertices | **MECHANICAL** | |
| Piii20-22 isDirectedWalk / isBifurcationWithSplit / isBifurcation | **STRUCTURAL** | port branches; only the surviving cases (per the new pattern-matches). |
| Piii23-24 `node_of_toCopy{0,1}_unsplit` | **MECHANICAL** | |
| Piii25 `walkStep_ofSplit_unsplit` | **STRUCTURAL (heavy)** | the heaviest descent step on Part iii. Branches on `s : refactor_WalkStep` and reasons about whether the typed step came from a lifted G-step or is a transfer edge `(.copy0 w, .copy1 w)` (E only — the L side is symmetric under `Sym2`, so the analogous L-channel transfer-edge analysis doesn't apply). |
| Piii26-28 list utilities | **MECHANICAL** | |
| Piii29 `pair_eq_of_split_unsplit_eq` | **MECHANICAL** | |
| Piii30 `a_in_G_E_of_lifted_in_split` | **STRUCTURAL** | port. |
| Piii31 `a_in_G_L_of_lifted_in_split` | **STRUCTURAL (Sym2)** | port through `Sym2.map`. |
| Piii32 `walk_ofSplit_unsplit_full` | **STRUCTURAL (very heavy)** | |
| Piii33 `all_unsplit_of_interior_W_image_split` | **MECHANICAL** | |
| Piii34-38 toCopy0 carrier / injective helpers | **MECHANICAL** | |
| Piii39 `exists_lifted_dir_walk_to_split_endTarget` | **STRUCTURAL (heavy)** | |
| Piii40 `exists_lifted_bifWithSplit_to_split` | **STRUCTURAL (very heavy)** | the centerpiece bifurcation ascent. |
| Piii41 `exists_lifted_bif_to_split` | **MECHANICAL** | wrapper. |
| Piii42 `walk_copy0_target_copy1` | **STRUCTURAL (heavy)** | |
| Piii43 `walk_G_lift_to_split` | **STRUCTURAL (heavy)** | |
| Piii44 `walk_split_descend_to_G` | **STRUCTURAL (heavy)** | |
| Piii45 `split_marg_PhiE_iff` | **MECHANICAL** | wrapper. |
| Piii46 `walk_target_copy1_source_copy0` | **STRUCTURAL (heavy)** | |
| Piii47 `split_marg_E_field_eq` | **STRUCTURAL (huge)** | E-field equality through the image lift. ~300 lines of filter / image equality. |
| Piii48-49 pair / not-W helpers | **MECHANICAL** | |
| Piii50 `a_in_G_E_of_toCopy0_lifted_in_split` | **STRUCTURAL** | |
| Piii51 `a_in_G_L_of_toCopy0_lifted_in_split` | **STRUCTURAL (Sym2)** | |
| Piii52 `walkStep_ofSplit_toCopy0` | **STRUCTURAL (heavy)** | |
| Piii53 `mem_G_of_toCopy0_mem_split` | **STRUCTURAL (light)** | |
| Piii54-55 list utilities | **MECHANICAL** | |
| Piii56 `walk_ofSplit_toCopy0_full` | **STRUCTURAL (very heavy)** | |
| Piii57 `all_toCopy0_of_interior_W_image_split` | **MECHANICAL** | |
| Piii58 `split_marg_PhiL_iff` | **MECHANICAL** | wrapper. |
| Piii59 `not_bif_source_copy1` | **STRUCTURAL (very heavy; HIGH RISK)** | reasons about `a.1 = .copy1 w` ordered-pair equation under the typed WalkStep refactor. Need to re-derive the source-copy0/target-copy1 analysis through the new step constructors. The "transfer edge `(w^0, w^1)`" identification reads off `.forwardE h` whose witness `h : (u,v) ∈ split.E = G.E.image (toCopy1 _, toCopy0 _) ∪ W₁.image (toCopy0, toCopy1)`; ascertain via `Finset.mem_union` on the witness. |
| Piii60 `not_bif_target_copy1_aux` | **STRUCTURAL (very heavy; HIGH RISK)** | dual to Piii59. |
| Piii61 `not_bif_target_copy1` | **MECHANICAL** | wrapper. |
| Piii62 `split_marg_L_field_eq` | **STRUCTURAL (huge, Sym2)** | the largest L-field equality in the file. Outer image dance on both sides; inner filter equality; relies on `not_bif_source_copy1` / `not_bif_target_copy1` to exclude `.copy1`-source/target cases. |
| Piii63 `marginalize_nodeSplittingOn_comm` | **STRUCTURAL** | cdmgExt destructure shrinks 9→8 fields. |

### GLUE/NEW additions anticipated

| Name | Purpose | When |
|---|---|---|
| `refactor_Sym2_mem_image_map_iff` | bridge `s ∈ T.image (Sym2.map f) ↔ ∃ s', s' ∈ T ∧ s = Sym2.map f s'` (mostly Mathlib's `Finset.mem_image`, but might want a Sym2-flavoured rewrite). | If body of Pii16 / Piii31 / Piii51 doesn't reduce cleanly. |
| `refactor_Sym2_map_unsplit_inj` / `refactor_Sym2_map_toCopy0_inj` | injectivity of `Sym2.map .unsplit` / `Sym2.map (refactor_toCopy0 W)`. Mathlib provides `Sym2.map_injective : Function.Injective f → Function.Injective (Sym2.map f)`. Probably no need — use Mathlib directly. | If body of `a_in_G_L_of_lifted_*` blows up. |
| `refactor_Sym2_ball_iff` | `(∀ v ∈ s, P v) ↔ Sym2.ball s P` style; probably already in Mathlib as `Sym2.ball`. | At Pi10 bidir branch (the `hardInterventionOn` L-filter is `fun s => ∀ v ∈ s, v ∉ W`). The `Sym2.ball` Mathlib def is already used by the decidability instance in `HardInterventionOn.lean:780-783`; we can lean on the existing instance. |

**Most-likely outcome**: zero new GLUE lemmas. The reference patterns
in `MarginalizationsCommute.lean` show that direct `Finset.mem_image.mp / mpr`
+ `Sym2.mk` destructure suffices in every case — see lines 7054-7068
for the canonical pattern.

---

## 3. Phased ordering

Each phase is closable by `lake build`. Recommended split:
**three big dispatches**, one per Part, each broken into in-Phase
sub-phases. NOT all three at once — Part iii alone is ~57 ports and
needs its own dispatch; bundling Part i (17 ports) + Part ii (26 ports)
into one is feasible but loses the per-Part build-incrementalism.

**Recommended: 3 separate `spawn_agent_sub_task` calls**, one per Part,
serialised (not parallel) because Part ii reuses H2 and Part iii
reuses H1 — they all depend on the four shared helpers being ported
first. Inside each Part dispatch, the worker proceeds through the
sub-phases below in order.

### Phase 0 — Shared helpers (4 lemmas, ~80 lines)

Bundle with Phase i (no per-Part overhead). The four shared helpers
(H1-H4) port mechanically; `lake build` after they're added validates
that the refactor types are properly imported.

### Phase i — Hard intervention (Part i; 17 decls + main thm = 18 ports)

* **i.A**: walk-surgery helpers Pi1-Pi13 (13 lemmas / defs)
* **i.B**: Φ iff Pi14-Pi15 (2 lemmas)
* **i.C**: field equality Pi16-Pi17 (2 lemmas)
* **i.D**: main theorem Pi18

Build after each sub-phase. Risk: low — mirror of
`MarginalizationsCommute.lean` Phase B-F (lines 3669-7136) style.

### Phase ii — Adding intervention nodes (Part ii; 24 decls + main thm = 25 ports)

* **ii.A**: walk ascent Pii1-Pii8 (8 lemmas / defs)
* **ii.B**: walk descent and list/edge helpers Pii9-Pii19 (11 lemmas / defs)
* **ii.C**: Φ iff and walk_intCopy_target_unsplit Pii20-Pii22 (3 lemmas)
* **ii.D**: field equality Pii23-Pii24 (2 lemmas)
* **ii.E**: main theorem Pii25

Build after each sub-phase. Risk: moderate (Pii16, Pii24 are the
first Sym2-dance L-field touches).

### Phase iii — Node-splitting (Part iii; 56 decls + main thm = 57 ports)

* **iii.A**: carrier helpers / sdiff / constructor disjointness Piii1-Piii15 (15 lemmas)
* **iii.B**: walk ascent G → split Piii16-Piii22 (7 decls)
* **iii.C**: walk descent split → G via `.unsplit` Piii23-Piii33 (11 decls)
* **iii.D**: toCopy0/1 walk-surgery + E-field equality Piii34-Piii47 (14 decls, including the huge Piii47)
* **iii.E**: L-field helpers Piii48-Piii61 (14 decls, including the HIGH-RISK Piii59 / Piii60)
* **iii.F**: L-field equality Piii62 + main theorem Piii63

Build after each sub-phase. Risk: high (Piii25, Piii32, Piii40,
Piii44, Piii47, Piii56, Piii59, Piii60, Piii62 are the heavies; the
last two are the highest-risk decls in the whole file).

**Recommendation: dispatch Phase iii as its OWN
`spawn_agent_sub_task` call**, post-Phase ii completion, so the
worker has fresh context for the largest sub-block. Optionally split
into iii.A-D ("E-field") and iii.E-F ("L-field") sub-dispatches; the
boundary at Piii48 is a natural cut (everything before is shared
plumbing + E-field; everything after is L-field-specific).

---

## 4. Top three risk items

### Risk 1 — Piii59 / Piii60 (`not_bif_source_copy1` / `not_bif_target_copy1_aux`)

These reason about *the asymmetric transfer-edge pattern*
`W₁.image (fun w => (refactor_SplitNode.copy0 w, refactor_SplitNode.copy1 w))`.
The original walks through `a.1 = .copy1 w` / `a.2 = .copy1 w` from
the cons-cell's stored ordered pair, then case-splits whether `a`
came from `G.E.image (toCopy1, toCopy0)` (a lifted E-edge) or from
the W₁-transfer image (the fresh `(c0, c1)` edge). Under the refactor:

* the stored ordered pair `a` is gone — read endpoints off the typed
  step's indices instead;
* the `.forwardE h` witness gives `h : (u, v) ∈ split.E`, where
  `split.E = G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪ W₁.image (…)`;
* destructure `h` via `Finset.mem_union` → two sub-cases as before,
  but now both sub-cases reason about `(u, v) = lifted_edge_or_transfer`
  with the WalkStep's indices `u`, `v` pinned by the type, not by a
  stored ordered pair.

The contradiction proofs `cases toCopy0_ne_copy1 h` etc. should port
mechanically, but the surrounding case-split scaffolding (in
particular the `match i, p', hSpl with` outer nested-`match` for
`refactor_IsBifurcationWithSplit` k=0 trivial-tail vs cons-tail) is
where the most line-count expansion will happen. The original
manages with ~200 lines combined; expect 250-350 ported lines.

**Mitigation**: pattern after `MargPreservesAncestors.lean` decls 38-41
(`refactor_marg_bif_*_dir_hinge_src_*`, lines 6446-6497) which port
the analogous asymmetric directed-hinge logic; sample those before
attempting Piii59 / Piii60.

### Risk 2 — Piii62 (`split_marg_L_field_eq`, ~115 lines)

The most-complex single field equality:

* LHS is `((((G.V\W₁).image .unsplit ∪ W₁.image .copy0 ∪ W₁.image .copy1) \ W₂.image .unsplit) ×ˢ …).filter (e.1 ≠ e.2 ∧ split.Φ_L (W₂.image .unsplit) e.1 e.2).image (Sym2.mk)`
* RHS is `((((G.V \ W₂) ×ˢ (G.V \ W₂)).filter (e.1 ≠ e.2 ∧ G.Φ_L W₂ e.1 e.2)).image (Sym2.mk)).image (Sym2.map refactor_toCopy0)` (RHS-of-nodeSplittingOn-applied-to-marg, so the image lift comes AFTER the inner Sym2.mk image).

Sanity-check the RHS shape carefully when porting; the original takes
a different path via `exists_underlying_of_mem_split_V_marg_not_copy1`
to land in `Finset.image.mpr ⟨(u,v), …⟩` on the RHS, which works for
the ordered-pair RHS but needs reworking for the **two-image-layer**
RHS in the refactor (outer `Sym2.map toCopy0` wrapped around inner
`Sym2.mk`).

**Mitigation**: read `MarginalizationsCommute.lean:7049-7068`
(`refactor_marg_L_field_eq`) carefully — it's the canonical
"two-image-layer L-field equality" pattern (`(filter).image (Sym2.mk)`
on each side). The technique is: `congr 1` peels the outer image
layer, reducing to ordered-pair filter equality, then
`Finset.filter_congr` reduces to the inner-iff. For Piii62 we have
*three* nested image-or-image layers; peel one at a time. **Likely
needs >150 ported lines.**

### Risk 3 — Walk-step ascent Pi10 (`walkStep_toDoit`) bidir branch

The original's `.bidir` branch test (`hL : (a ∈ G.L)`) ported as a
single ordered-pair filter (`(a ∈ G.L.filter …) → a.1 ∉ W ∧ a.2 ∉ W`).
The new test is `s(u, v) ∈ G.L.filter (fun s => ∀ v ∈ s, v ∉ W)`,
which expects a `∀ v ∈ s, v ∉ W` discharge. The right argument
order is:

```
refine Finset.mem_filter.mpr ⟨hL, ?_⟩
intro w hw
rcases Sym2.mem_iff.mp hw with rfl | rfl
· exact hu
· exact hv
```

Easy in isolation, but the wider lemma threads this through ~80 lines
of dependent helpers (Pi13 specifically) where any case-split mismatch
on the inner WalkStep cascades. Test that decidability of
`hardInterventionOn`'s L-filter (the `Sym2.ball` route per
`HardInterventionOn.lean:780-783`) resolves automatically at call
sites where `Finset.mem_filter.mpr` is applied to an L-filter; if not,
the `private instance refactor_hardInterventionOn_decidable_bAll` will
need an explicit reference.

**Mitigation**: write Pi10 + Pi11 first (the two lightest WalkStep
helpers), spot-build, then push through to Pi12 / Pi13. Pi10's bidir
branch is the litmus test for the whole Sym2 mechanic on the
hard-intervention side.

---

## 5. First worker recommendation

**Dispatch: Phase 0 + Phase i bundled, single worker.**

```
ROLE: prove_claim_in_lean worker
TARGET FILE: leanification/Chapter3_GraphTheory/Section3_2/MarginalizationAndIntervention.lean
SCOPE: Append REFACTOR-BLOCK-REPLACEMENT-BEGIN/END marker pairs around
       new clones of H1-H4 (shared helpers) and Pi1-Pi18 (Part i).
       Do NOT modify any ORIGINAL declaration; wrap each one with
       REFACTOR-BLOCK-ORIGINAL-BEGIN/END markers and append the
       refactor_<name> twin BELOW the marker pair.

READ FIRST (in order):
  1. workspace_claim_3_18.md — this plan.
  2. claude.md at repo root.
  3. Section3_2/MarginalizationsCommute.lean lines 3592-7140 (the
     entire REPLACEMENT half) — canonical template for
     `refactor_subset_sdiff_of_disjoint`, the `refactor_marg_*_iff`
     iff lemmas, and the `refactor_marg_*_field_eq` patterns.
  4. Section3_2/MargPreservesAncestors.lean lines 4348-4517
     (`refactor_expand_directed_walk_marginalize`) — canonical
     template for typed-WalkStep cons / Walk recursion.
  5. Section3_2/HardInterventionOn.lean lines 700-823 — the
     `refactor_hardInterventionOn` definition + the L-filter
     decidability instance (`Sym2.ball`).
  6. Section3_1/CDMG.lean lines 189-393 — `refactor_CDMG` structure
     to know the 8-field destructure pattern for `cdmgExt`.
  7. Section3_1/Walks.lean lines 1364-1512 — `refactor_WalkStep`
     + `refactor_Walk` to know the constructor patterns.

DO NOT delete or rename anything. Just APPEND.

After each sub-phase (i.A, i.B, i.C, i.D) run `lake build` from the
repo root. If build fails, fix the most recent block before moving
on. Do NOT batch multiple sub-phases into a single uncompiled blob.

For the tex twin, ALSO create
  leanification/Chapter3_GraphTheory/Section3_2/tex/refactor_claim_3_18_proof_MarginalizationAndIntervention.tex
as a near-verbatim copy of the existing
  leanification/Chapter3_GraphTheory/Section3_2/tex/claim_3_18_proof_MarginalizationAndIntervention.tex
(the mathematical proof is unchanged — only the Lean encoding
differs; the tex doesn't need to mention `refactor_*` names). This
twin will replace the original at Phase 7 cleanup.

Expected output: ~600-900 ported lines (Phase 0 + Phase i combined),
single Lean file modification, single tex twin file creation. Budget
~3-5 turns.
```

After Phase i lands cleanly, dispatch Phase ii as a separate
`spawn_agent_sub_task`. After Phase ii lands cleanly, dispatch Phase
iii (potentially as two sub-dispatches: iii.A-D, then iii.E-F).

**Note on `add_design_choice_comments`**: every original ORIGINAL
block already has design-choice prose; the refactor blocks should
inherit verbatim but can add short *refactor-deltas* (e.g.\ "Body
identical modulo `Walk → refactor_Walk` retarget and `cons` cell
shrinkage from 4-arg to 3-arg") in the prose above each
`REFACTOR-BLOCK-REPLACEMENT-BEGIN` marker. The
`MarginalizationsCommute.lean` and `MargPreservesAncestors.lean`
reference files demonstrate this convention. Full `add_design_choice_comments`
worker dispatch is NOT separately needed for this row — the per-block
refactor-delta prose, written inline by `prove_claim_in_lean`, is
the LN-faithful equivalent.

---

## 6. Cross-references and naming conventions

* Every new top-level declaration MUST be wrapped in
  `-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: <FinalName> (was: refactor_<FinalName>)`
  / `-- REFACTOR-BLOCK-REPLACEMENT-END: <FinalName>` markers (the
  cleanup script greps for these and renames `refactor_<FinalName>`
  → `<FinalName>` at Phase 7).
* Every original declaration MUST be wrapped in
  `-- REFACTOR-BLOCK-ORIGINAL-BEGIN: <FinalName>` /
  `-- REFACTOR-BLOCK-ORIGINAL-END: <FinalName>` markers (the cleanup
  script greps and removes these blocks at Phase 7).
* The three main theorems' `<FinalName>` values are:
  - `marginalize_hardInterventionOn_comm`
  - `marginalize_extendingCDMGsWith_comm`
  - `marginalize_nodeSplittingOn_comm`
* The `<FinalName>` for ALL refactor twins should match the original
  Lean declaration name; the cleanup script does a whole-word rename
  globally, so consistent naming across all 110 ports is essential.
* Net-new helpers (no ORIGINAL block) ALSO need REPLACEMENT-only
  marker blocks. Don't leave any `refactor_*` declaration unwrapped.
* The `private` keyword is preserved on private lemmas. The new
  refactor twins are also `private` — the `private` keyword goes
  inside the REPLACEMENT block.

## 7. Build verification gates

After every sub-phase, run from the repo root:

```
cd /home/11716061/repo_scaffold2 && lake build
```

Hard requirement: `lake build` must succeed before declaring the
sub-phase complete. The build dependency chain pulls in every
upstream refactored file already on disk; the new refactor twins
must resolve to those upstreams (not the originals). Any
`unknown identifier 'refactor_*'` error means a typo in a name or a
missing import / namespace.

`MarginalizationsCommute.lean` and `MargPreservesAncestors.lean` are
both fully refactored already, so the only NEW errors the build
should surface are inside our new replacement blocks.
