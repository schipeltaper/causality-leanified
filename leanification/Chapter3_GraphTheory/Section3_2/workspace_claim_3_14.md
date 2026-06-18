# Workspace for claim_3_14 — AddingInterventionNodes (refactor port)

This is a **DEPENDENT** row in refactor `cdmg_typed_edges`. Root
`def_3_1` changed the bidirected-edge field of `CDMG` from
`Finset (Node × Node)` (with `hL_symm`, `hL_irrefl` on ordered pairs)
to `Finset (Sym2 Node)` (with `hL_irrefl : ¬ s.IsDiag` and `hL_subset`
quantified via `Sym2.Mem`; **no `hL_symm` field**). Mathematics is
unchanged; only the Lean encoding migrates. The existing proven file
`AddingInterventionNodes.lean` (1029 lines, on main) needs replacement
blocks added alongside the originals. Phase 7 cleanup renames the
replacements over the originals.

---

## 1. Upstream survey

All five upstream pieces have already been refactored on this branch.

| Upstream piece | File | Refactor lives in `namespace …` | Post-refactor signature / L-shape | Notes |
|---|---|---|---|---|
| `def_3_1` `CDMG` → `refactor_CDMG` | `Section3_1/CDMG.lean` L383–392 | `Causality` | `structure refactor_CDMG (Node : Type*) [DecidableEq Node]` with 8 fields: `J, V, hJV_disj, E, hE_subset, L : Finset (Sym2 Node), hL_subset : ∀ ⦃s⦄, s ∈ L → ∀ ⦃v⦄, v ∈ s → v ∈ V, hL_irrefl : ∀ ⦃s⦄, s ∈ L → ¬ s.IsDiag`. **NO `hL_symm`** | One fewer field than original |
| `def_3_13` `extendingCDMGsWith` → `refactor_extendingCDMGsWith` | `Section3_2/ExtendingCDMGsWith.lean` L1065–1077 | `Causality.CDMG` (NOT `refactor_CDMG`!) | `(G : refactor_CDMG Node) (W : Finset Node) (hW : W ⊆ G.J ∪ G.V) : refactor_CDMG (IntExtNode Node)`. J/V/E unchanged. **`L := G.L.image (Sym2.map IntExtNode.unsplit)`** | Four private helpers `refactor_extendingCDMGsWith_h{JV_disj,E_subset,L_subset,L_irrefl}` (one fewer than pre-refactor — no `_hL_symm`). The `_hL_subset` quantifies via `Sym2.Mem`; `_hL_irrefl` uses `Sym2.isDiag_map` for the pullback |
| `def_3_10` `hardInterventionOn` → `refactor_hardInterventionOn` | `Section3_2/HardInterventionOn.lean` L809–820 | `Causality.refactor_CDMG` | `(G : refactor_CDMG Node) (W : Finset Node) (hW : W ⊆ G.J ∪ G.V) : refactor_CDMG Node`. J/V/E unchanged. **`L := G.L.filter (fun s => ∀ v ∈ s, v ∉ W)`** | Plus a `private instance refactor_hardInterventionOn_decidable_bAll (W) : DecidablePred (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W)` at L780 — needed for the `Finset.filter` to elaborate. `private` does not block typeclass search across files. |
| `claim_3_7` `eqViaNodeMap` → `refactor_eqViaNodeMap` | `Section3_2/TwoDisjointNode.lean` L984–989 | `Causality.refactor_CDMG` | `{α β} [DecidableEq α] [DecidableEq β] (G : refactor_CDMG α) (G' : refactor_CDMG β) (f : α → β) : Prop` — four `Finset.image f`-equalities on J/V/E/L. The L-equality on the Sym2 side reads as `G.L.image (Sym2.map f) = G'.L` (rather than `G.L.image (Prod.map f f)`) | Used by our (a) theorem — confirm signature shape on lines 984–989 before authoring |
| `IntExtNode` | `Section3_2/ExtendingCDMGsWith.lean` L246–248 | `Causality.CDMG` | **UNCHANGED** — same `inductive IntExtNode (Node : Type*)` with `.unsplit (v : Node)` and `.intCopy (w : Node)`, `deriving DecidableEq` | No `refactor_IntExtNode`. The same constructor disjointness / injectivity lemmas apply verbatim |

### Namespace gotcha (load-bearing)

`refactor_extendingCDMGsWith` lives in `namespace CDMG`, **NOT** in
`namespace refactor_CDMG`. So dot notation
`G.refactor_extendingCDMGsWith W hW` (where `G : refactor_CDMG Node`)
**does not resolve** — Lean searches `refactor_CDMG.refactor_extendingCDMGsWith`,
which does not exist. The fix used by `AcyclicHardInterventionTopologicalOrder.lean`
(L866–882) is:

```lean
namespace refactor_CDMG
open CDMG     -- bring `refactor_extendingCDMGsWith` and `IntExtNode` into scope
```

Then function-style `refactor_extendingCDMGsWith G W hW` works.
`refactor_hardInterventionOn` and `refactor_eqViaNodeMap` *are* in
`namespace refactor_CDMG`, so dot notation `G.refactor_hardInterventionOn`
and `refactor_eqViaNodeMap … … …` (function-style, since `eqViaNodeMap`
takes two different graphs) work directly.

**Recommended namespace layout for the refactor blocks in
`AddingInterventionNodes.lean`:** mirror the precedent —
put new declarations in `namespace refactor_CDMG` (a sibling block
after the existing `namespace CDMG` … `end CDMG`), with an `open CDMG`
to bring `refactor_extendingCDMGsWith` and `IntExtNode` into scope.

---

## 2. Existing file inventory (1029 lines)

The file currently contains 7 top-level / helper items, all using
pre-refactor `CDMG`. Listing with line ranges and the marker shape
each item needs in the refactor block.

| # | Item | Lines | Kind | Pre-refactor markers | Replacement marker name (for cleanup) |
|---|---|---|---|---|---|
| 0 | `variable {Node : Type*} [DecidableEq Node]` | 83 | variable | none (currently unwrapped — but the original file does need it wrapped *if* the existing file has no `variable_Node` marker; check before editing) | `variable_Node` (helper-style markers) |
| 1 | `image_unsplit_subset_extendingCDMGsWith_carrier` | 157–174 | private lemma | helper (`--- start helper / --- end helper`) | `image_unsplit_subset_extendingCDMGsWith_carrier` |
| 2 | `subset_carrier_of_hardInterventionOn` | 217–229 | private lemma | helper | `subset_carrier_of_hardInterventionOn` |
| 3 | `flattenIntExt` | 295–300 | def | helper | `flattenIntExt` |
| 4 | `addInterventionNodesAndHardInterventionOn` | 363–369 | def | helper | `addInterventionNodesAndHardInterventionOn` |
| 5 | `addInterventionNodes_comm_disjoint` (sub-claim (a)) | 512–528 (sig); 529–713 (proof body) | theorem | **statement** (`-- start statement / -- end statement`) | `addInterventionNodes_comm_disjoint` |
| 6 | `addInterventionNodes_comm_hardIntervention` (sub-claim (b)) | 833–844 (sig); 845–1025 (proof body) | theorem | **statement** | `addInterventionNodes_comm_hardIntervention` |

**Action needed first:** grep the file for existing
`REFACTOR-BLOCK-ORIGINAL-BEGIN:` markers — if none exist yet, the
worker must add ORIGINAL-BEGIN/END marker pairs around each item
above before adding the REPLACEMENT blocks. (The existing
`---  helper` / `-- statement` markers are the website-extraction
markers, NOT the refactor cleanup markers — both must coexist on
the originals.)

---

## 3. Declaration-by-declaration porting checklist

For each item the refactor block sits in `namespace refactor_CDMG`
(after `open CDMG` so `refactor_extendingCDMGsWith` and `IntExtNode`
resolve function-style).

### (0) `variable_Node` block

Mechanical. The variable line is identical; only the marker wrapper
differs.

```lean
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: variable_Node (was: refactor_variable_Node)
-- claim_3_14 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_14 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: variable_Node
```

### (1) `image_unsplit_subset_extendingCDMGsWith_carrier` → `refactor_…`

Signature change: `{G : CDMG Node}` → `{G : refactor_CDMG Node}`;
inside the proof, the `change` target's union-of-`Finset.image`
expression refers to `(G.extendingCDMGsWith W hW).J ∪ … .V` which
post-refactor becomes
`(refactor_extendingCDMGsWith G W hW).J ∪ (refactor_extendingCDMGsWith G W hW).V` —
**but the J/V fields of `refactor_extendingCDMGsWith` are unchanged
from `extendingCDMGsWith`** (only L migrates). So the `change` line
is literally identical except the function name is `refactor_extendingCDMGsWith`,
not `G.extendingCDMGsWith`. Proof body (lines 164–174) is otherwise
verbatim. Wrap with helper markers around the existing `private lemma`
shell.

```lean
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: image_unsplit_subset_extendingCDMGsWith_carrier (was: refactor_image_unsplit_subset_extendingCDMGsWith_carrier)
-- claim_3_14 --- start helper
private lemma refactor_image_unsplit_subset_extendingCDMGsWith_carrier
    {G : refactor_CDMG Node} {W : Finset Node} (hW : W ⊆ G.J ∪ G.V)
    {S : Finset Node} (hS : S ⊆ G.J ∪ G.V) :
    S.image IntExtNode.unsplit ⊆
      (refactor_extendingCDMGsWith G W hW).J ∪ (refactor_extendingCDMGsWith G W hW).V
-- claim_3_14 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change IntExtNode.unsplit v ∈
    (G.J.image IntExtNode.unsplit ∪ (W \ G.J).image IntExtNode.intCopy)
      ∪ G.V.image IntExtNode.unsplit
  -- … body verbatim from original L164–174
-- REFACTOR-BLOCK-REPLACEMENT-END: image_unsplit_subset_extendingCDMGsWith_carrier
```

### (2) `subset_carrier_of_hardInterventionOn` → `refactor_…`

Same mechanical port. Signature change `CDMG → refactor_CDMG`; call
`refactor_hardInterventionOn` instead of `hardInterventionOn`.
`refactor_hardInterventionOn` IS in `namespace refactor_CDMG`, so dot
notation `G.refactor_hardInterventionOn W hW` works (and the
`change` target `v ∈ (G.J ∪ W) ∪ (G.V \ W)` is identical because
J/V are unchanged). Proof body verbatim.

### (3) `flattenIntExt` → `refactor_flattenIntExt`

**Pure verbatim port.** The carrier `IntExtNode (IntExtNode Node)` is
unchanged (no `refactor_IntExtNode`), so the four pattern-match
clauses are literally identical. Only the name changes for the marker
+ cleanup rename.

```lean
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: flattenIntExt (was: refactor_flattenIntExt)
-- claim_3_14 --- start helper
def refactor_flattenIntExt : IntExtNode (IntExtNode Node) → IntExtNode Node
  | .unsplit (.unsplit v) => IntExtNode.unsplit v
  | .unsplit (.intCopy w) => IntExtNode.intCopy w
  | .intCopy (.unsplit v) => IntExtNode.intCopy v
  | .intCopy (.intCopy w) => IntExtNode.intCopy w
-- claim_3_14 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: flattenIntExt
```

### (4) `addInterventionNodesAndHardInterventionOn` → `refactor_…`

Compose `refactor_hardInterventionOn` on the result of
`refactor_extendingCDMGsWith`. Both function calls use the *unchanged*
`IntExtNode` carrier so the body shape is mechanical:

```lean
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: addInterventionNodesAndHardInterventionOn (was: refactor_addInterventionNodesAndHardInterventionOn)
-- claim_3_14 --- start helper
def refactor_addInterventionNodesAndHardInterventionOn (G : refactor_CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V) :
    refactor_CDMG (IntExtNode Node) :=
  (refactor_extendingCDMGsWith G W₁ hW₁).refactor_hardInterventionOn
      (W₂.image IntExtNode.unsplit)
      (refactor_image_unsplit_subset_extendingCDMGsWith_carrier hW₁ hW₂)
-- claim_3_14 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: addInterventionNodesAndHardInterventionOn
```

Note `refactor_extendingCDMGsWith G W₁ hW₁` is function-style (because
it's in `namespace CDMG`, see gotcha §1); then
`.refactor_hardInterventionOn` is dot-notation chaining because
`refactor_hardInterventionOn` IS in `namespace refactor_CDMG`.

### (5) `addInterventionNodes_comm_disjoint` (sub-claim (a)) → `refactor_…`

Signature change: `CDMG → refactor_CDMG`, `eqViaNodeMap → refactor_eqViaNodeMap`,
`G.extendingCDMGsWith → refactor_extendingCDMGsWith G`,
`image_unsplit_subset_extendingCDMGsWith_carrier → refactor_image_unsplit_subset_extendingCDMGsWith_carrier`,
`flattenIntExt → refactor_flattenIntExt`.

Statement shape unchanged: conjunction of two `refactor_eqViaNodeMap`
equalities (iter₁₂ → joint, iter₂₁ → joint).

**Proof body — substantive change in the L-component subgoals (4 and 8).**
The first three subgoals per direction (J, V, E components) are
*unchanged* because the refactor only touches L. Lines 626–660 (a-1)
and 673–706 (a-2) carry over verbatim including the precomputed
collapses `h_uu_collapse`, `h_iu_collapse`, `h_ui_collapse`,
`h_E_lift_uu_collapse`, `h_W_transfer_inner_collapse`,
`h_W_transfer_outer_collapse`, `h_sdiff`, `h_sdiff_union`,
`h_sdiff_union'` — all of these operate on J/V/E carriers and are
independent of the L encoding.

The L subgoals (lines 662–668 and 707–713) change shape. Original:

```lean
-- L subgoal (iter₁₂):
· change ((G.L.image
            (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
            (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))).image
          (Prod.map flattenIntExt flattenIntExt)
        = G.L.image (fun e : Node × Node => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
  exact h_E_lift_uu_collapse G.L
```

Post-refactor (iter₁₂, using `Sym2.map`):

```lean
· change ((G.L.image (Sym2.map IntExtNode.unsplit)).image
              (Sym2.map IntExtNode.unsplit)).image
          (Sym2.map refactor_flattenIntExt)
        = G.L.image (Sym2.map IntExtNode.unsplit)
  exact h_L_lift_uu_collapse G.L
```

where `h_L_lift_uu_collapse` is a **new** auxiliary collapse on `Sym2`:

```lean
have h_L_lift_uu_collapse : ∀ (S : Finset (Sym2 Node)),
    ((S.image (Sym2.map IntExtNode.unsplit)).image
        (Sym2.map IntExtNode.unsplit)).image
      (Sym2.map refactor_flattenIntExt)
    = S.image (Sym2.map IntExtNode.unsplit) := by
  intro S
  rw [Finset.image_image, Finset.image_image]
  -- After two `Finset.image_image` rewrites we have
  --     S.image ((Sym2.map refactor_flattenIntExt) ∘
  --              (Sym2.map IntExtNode.unsplit) ∘
  --              (Sym2.map IntExtNode.unsplit))
  -- which by `Sym2.map_comp` (or `Sym2.map_map`) equals
  --     S.image (Sym2.map (refactor_flattenIntExt ∘ .unsplit ∘ .unsplit))
  -- and that composition collapses to `IntExtNode.unsplit` by `funext + rfl`
  -- (because `refactor_flattenIntExt (.unsplit (.unsplit v)) = .unsplit v`).
  -- Two ways to close:
  --   (A) Show `Sym2.map g ∘ Sym2.map f = Sym2.map (g ∘ f)` (Mathlib's `Sym2.map_map`);
  --       then reduce the composition to `IntExtNode.unsplit` by `congr; funext v; rfl`.
  --   (B) `ext s; induction s using Sym2.inductionOn` (or `Sym2.ind`) — destructure
  --       `s = s(a, b)`, push `Sym2.map_pair`, close by `rfl`.
  -- (A) is shorter; (B) is more bullet-proof if `Sym2.map_map` is not in scope.
  sorry  -- worker fills in the closer
```

A similar `h_L_lift_uu_collapse G.L` discharges the iter₂₁ L
subgoal verbatim (same shape, the joint RHS `G.L.image (Sym2.map IntExtNode.unsplit)`
is symmetric in `W₁` / `W₂`).

**Note:** `Sym2.map_map` (also called `Sym2.map_comp` in some
Mathlib versions) is the key Mathlib lemma: `Sym2.map g (Sym2.map f s) = Sym2.map (g ∘ f) s`.
If it is not available, fall back to (B) via
`Sym2.inductionOn` / `Sym2.ind` / `Sym2.recOnSubsingleton`.

### (6) `addInterventionNodes_comm_hardIntervention` (sub-claim (b)) → `refactor_…`

Signature change: same identifier renames as (5), plus the LHS uses
`refactor_extendingCDMGsWith` and `refactor_hardInterventionOn`, the
middle uses `refactor_hardInterventionOn` and `refactor_extendingCDMGsWith`,
and the RHS is `refactor_addInterventionNodesAndHardInterventionOn`.

**Substantive proof-body changes:**

#### (6a) `cdmgExt` extensionality helper — drops one field

Original (L852–857):

```lean
have cdmgExt : ∀ {G₁' G₂' : CDMG (IntExtNode Node)},
    G₁'.J = G₂'.J → G₁'.V = G₂'.V → G₁'.E = G₂'.E → G₁'.L = G₂'.L → G₁' = G₂' := by
  rintro ⟨J₁, V₁, hJV₁, E₁, hE₁, L₁, hL₁, hLi₁, hLs₁⟩
         ⟨J₂, V₂, hJV₂, E₂, hE₂, L₂, hL₂, hLi₂, hLs₂⟩ hJ hV hE hL
  obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL
  rfl
```

Post-refactor (`refactor_CDMG` has 8 fields, no `hL_symm`):

```lean
have cdmgExt : ∀ {G₁' G₂' : refactor_CDMG (IntExtNode Node)},
    G₁'.J = G₂'.J → G₁'.V = G₂'.V → G₁'.E = G₂'.E → G₁'.L = G₂'.L → G₁' = G₂' := by
  rintro ⟨J₁, V₁, hJV₁, E₁, hE₁, L₁, hL₁, hLi₁⟩      -- 8 binders, was 9
         ⟨J₂, V₂, hJV₂, E₂, hE₂, L₂, hL₂, hLi₂⟩
         hJ hV hE hL
  obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL
  rfl
```

#### (6b) J / V / E component proofs — verbatim

The `h_W₁_sdiff_collapse` helper, the `refine ⟨rfl, ?_⟩` step, and
the J / V / E component goal-rewrites (lines 858–983) are all on
J/V/E carriers and port verbatim.

#### (6c) L-component proof — substantive rewrite

This is the load-bearing change. Original (lines 989–1025) handles
the goal

```lean
(G.L.filter (fun e : Node × Node => e.1 ∉ W₂ ∧ e.2 ∉ W₂)).image
    (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
  = (G.L.image (fun e => (.unsplit e.1, .unsplit e.2))).filter
      (fun e => e.1 ∉ W₂.image .unsplit ∧ e.2 ∉ W₂.image .unsplit)
```

via a two-direction `ext ⟨a, b⟩; simp [Finset.mem_image, Finset.mem_filter]; constructor; …`
unfold, using `.unsplit`-injectivity (`injection hweq with hwe`) to
move `W₂`-membership across the lift.

**Post-refactor the goal becomes:**

```lean
(G.L.filter (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₂)).image
    (Sym2.map IntExtNode.unsplit)
  = (G.L.image (Sym2.map IntExtNode.unsplit)).filter
      (fun s : Sym2 (IntExtNode Node) => ∀ v ∈ s, v ∉ W₂.image IntExtNode.unsplit)
```

derived from:
- middle.L = `(G.refactor_hardInterventionOn W₂ hW₂).L.image (Sym2.map .unsplit)`
  - = `(G.L.filter (fun s => ∀ v ∈ s, v ∉ W₂)).image (Sym2.map .unsplit)`
- mixed.L = `((refactor_extendingCDMGsWith G W₁ hW₁).refactor_hardInterventionOn …).L`
  - = `((G.L.image (Sym2.map .unsplit))).filter (fun s => ∀ v ∈ s, v ∉ W₂.image .unsplit)`

**Proof recipe (filter/image-swap on Sym2):**

```lean
ext s
simp only [Finset.mem_image, Finset.mem_filter]
constructor
· rintro ⟨s', ⟨hs'L, hs'W⟩, rfl⟩
  refine ⟨⟨s', hs'L, rfl⟩, ?_⟩
  intro v hv
  -- hv : v ∈ Sym2.map .unsplit s'
  -- by Sym2.mem_map, ∃ u ∈ s', .unsplit u = v
  obtain ⟨u, huS', rfl⟩ := Sym2.mem_map.mp hv
  -- hs'W u huS' : u ∉ W₂
  intro h_in
  -- h_in : .unsplit u ∈ W₂.image .unsplit  → ∃ w ∈ W₂, .unsplit w = .unsplit u → w = u (by .unsplit injectivity) → u ∈ W₂ → contradict
  obtain ⟨w, hwW₂, hwEq⟩ := Finset.mem_image.mp h_in
  injection hwEq with hweq
  exact hs'W u huS' (hweq ▸ hwW₂)
· rintro ⟨⟨s', hs'L, rfl⟩, hsW⟩
  refine ⟨s', ⟨hs'L, ?_⟩, rfl⟩
  intro u huS'
  -- hsW : ∀ v ∈ Sym2.map .unsplit s', v ∉ W₂.image .unsplit
  -- specialise at v := .unsplit u (∈ Sym2.map .unsplit s' by Sym2.mem_map)
  have h_in : IntExtNode.unsplit u ∈ Sym2.map IntExtNode.unsplit s' :=
    Sym2.mem_map.mpr ⟨u, huS', rfl⟩
  intro huW₂
  exact hsW _ h_in (Finset.mem_image.mpr ⟨u, huW₂, rfl⟩)
```

This is the *whole* L-component proof under Sym2 — substantially
shorter than the original (no need to handle `e.1` and `e.2`
separately, because `Sym2.mem_map` quantifies over both endpoints in
one stroke).

**Key Mathlib lemma:** `Sym2.mem_map : v ∈ Sym2.map f s ↔ ∃ w ∈ s, f w = v`
(in `Mathlib.Data.Sym.Sym2.Init` / `Mathlib.Data.Sym.Sym2`).

#### (6d) Decidability of the L-filter predicate

The middle term `(G.refactor_hardInterventionOn W₂ hW₂)` uses a
filter predicate `(fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₂)`. Lean
needs `DecidablePred` for `Finset.filter` to elaborate. The required
instance is `refactor_hardInterventionOn_decidable_bAll` declared
`private` in `HardInterventionOn.lean` L780–783. **`private` does not
hide instances from typeclass search across files** in Lean 4, so this
should propagate; but if elaboration fails, the worker can either
(i) `open private refactor_hardInterventionOn_decidable_bAll` (not
recommended — relies on `private`-name) or (ii) redeclare a local
instance using the same body:

```lean
private instance refactor_addInt_decidable_bAll (W : Finset Node) :
    DecidablePred (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W) := fun s =>
  s.recOnSubsingleton fun _ _ => decidable_of_iff' _ Sym2.ball
```

When the outer call lifts to `Sym2 (IntExtNode Node)`, the same
instance applies because `IntExtNode Node` has `DecidableEq` from
`def_3_13`'s `deriving DecidableEq`.

---

## 4. Tex twin plan

The existing tex proof at `tex/claim_3_14_proof_AddingInterventionNodes.tex`
is encoding-agnostic — the statement block restates the LN's
ordered-pair-L axioms (`$L \subseteq V \times V$, $L$ irreflexive, $L$
symmetric`) verbatim, and the proof reasons at the level of "remove
every bidirected edge incident to $W_2$" / "the symmetrisation noted
in the bullet on $G_{\doit(W)}$". Sym2-vs-ordered-pair is a Lean
detail, not an LN one.

**Plan:** create `tex/refactor_claim_3_14_proof_AddingInterventionNodes.tex`
as a **near-verbatim copy** of the original proof file. No mathematical
content changes. The cleanup script (Phase 7) renames the twin over
the original.

Optional sub-changes the worker may consider, all *optional* and not
required:
- Replace the `% Proof body adapted from the LN's \Claude{...} block …`
  preamble comment with a one-line note "Refactor-twin of the
  Sym2-encoding port; mathematics unchanged from the original".
- Leave every `\lC (v_1, v_2) \in L \st …\rC` removal phrasing as-is.
  The Sym2 encoding's "remove every unordered pair touching $W_2$"
  realises this set exactly; no LN-level rewording is needed.

**Recommendation:** do not change anything substantive in the tex —
the original already passed `verify_tex_proof` for the LN content,
and a near-verbatim twin will pass again.

---

## 5. Recommended next worker

**Option A (recommended): split into two parallel workers.**

1. **tex twin worker** (cheap, low-risk):
   - Worker: `write_tex_proof` or a generic file-copy task
   - Input: read `tex/claim_3_14_proof_AddingInterventionNodes.tex`
   - Output: write near-verbatim copy at `tex/refactor_claim_3_14_proof_AddingInterventionNodes.tex`
   - Optional: replace the LN-cite preamble comment with the
     refactor-twin marker line above.

2. **Lean port worker** (substantive):
   - Worker: `prove_claim_in_lean.md` (dispatched on this row's
     existing file `AddingInterventionNodes.lean`)
   - Input: this plan in full, plus pointers to the upstream
     refactored decls (line numbers in §1).
   - Output: 7 REFACTOR-BLOCK-REPLACEMENT marker pairs (one per item
     in §2's inventory), all inside a new `namespace refactor_CDMG`
     (`open CDMG`) block appended after the existing `end CDMG`.

These are independent files, so they parallelize. Both should complete
before triggering the strict-equivalence solved-gate.

**Option B (fallback if dispatcher only takes one worker):** a single
`prove_claim_in_lean.md` worker that does both — feasible because the
tex twin is trivial, but the Lean port alone is the substantive
content.

---

## 6. Risk flags

1. **Namespace gotcha (high priority).** `refactor_extendingCDMGsWith`
   is in `namespace CDMG`. Inside `namespace refactor_CDMG`, dot
   notation `G.refactor_extendingCDMGsWith` does NOT resolve. The
   precedent (`AcyclicHardInterventionTopologicalOrder.lean` L866–882)
   is `open CDMG` + function-style calls. Apply the same fix here.

2. **`cdmgExt` field count.** The inline `cdmgExt` extensionality
   helper (L852–857) destructures 9 fields per CDMG (one of which is
   `hL_symm`). Post-refactor `refactor_CDMG` has 8 fields. **Cut the
   last binder in each `rintro` pattern** — see §3(6a).

3. **`Sym2.map_map` availability.** The new `h_L_lift_uu_collapse`
   helper needs either `Sym2.map_map` (or `Sym2.map_comp`) from
   Mathlib, or an `ext s; induction s using Sym2.inductionOn` fallback.
   Worker should attempt `Sym2.map_map` first; if it's not in the
   imported Mathlib subset, fall back to induction.

4. **`Sym2.mem_map`.** The L-component (b-2) proof leans on
   `Sym2.mem_map : v ∈ Sym2.map f s ↔ ∃ w ∈ s, f w = v`. This is in
   Mathlib's `Sym2` API; confirm at use site that the lemma name is
   `Sym2.mem_map` (not `Sym2.mem_map_iff` or similar).

5. **L-filter predicate decidability.** The `refactor_hardInterventionOn`
   filter `(fun s => ∀ v ∈ s, v ∉ W)` requires a `DecidablePred`
   instance. The upstream `refactor_hardInterventionOn_decidable_bAll`
   (HardInterventionOn.lean L780) is `private`. In Lean 4, `private`
   does NOT hide *instances* from typeclass search across files —
   typeclass search is name-blind — so this should propagate.
   **Falsifiable assumption:** if elaboration fails on the
   `refactor_addInterventionNodesAndHardInterventionOn` def with a
   `DecidablePred` error, redeclare a local copy of the instance as
   shown in §3(6d).

6. **`.refactor_hardInterventionOn` chained dot-notation.** Inside
   `refactor_addInterventionNodesAndHardInterventionOn`, the expression
   `(refactor_extendingCDMGsWith G W₁ hW₁).refactor_hardInterventionOn …`
   should resolve cleanly because `refactor_hardInterventionOn` IS in
   `namespace refactor_CDMG` and the receiver
   `refactor_extendingCDMGsWith G W₁ hW₁ : refactor_CDMG (IntExtNode Node)`.
   Worth double-checking at the call site.

7. **`hL_subset` shape change cascades into the helper's `change`
   targets.** None of this row's 7 items destructure or directly invoke
   `hL_subset` / `hL_irrefl` (the proofs work at the level of `Finset`
   data fields, not the CDMG axiom fields). So the migration of these
   axioms' shapes (Sym2.Mem / ¬ IsDiag) is *contained* upstream —
   does not enter this row's proof bodies. Good news.

8. **Filter predicate phrasing identity.** Pre-refactor, the
   L-filter for hard intervention was `(fun e => e.1 ∉ W ∧ e.2 ∉ W)`
   (two-sided exclusion to preserve symmetry under removal).
   Post-refactor it's `(fun s => ∀ v ∈ s, v ∉ W)` (single
   universal quantifier over both endpoints of the unordered pair).
   These are LN-equivalent — both say "no endpoint of the bidirected
   edge is in `W`" — but the *Lean shape* is different. The (b-2)
   L-component proof shape changes accordingly (see §3(6c)).

9. **Net-new helper marker requirement.** The new `h_L_lift_uu_collapse`
   is an *inline* `have` inside the (a) proof body, NOT a top-level
   `private lemma`. So it does NOT need a REPLACEMENT marker block.
   Marker blocks are only required for top-level `def` / `theorem` /
   `lemma` (per the briefing's "cleanup REFUSES if it finds a
   top-level `refactor_*` declaration that isn't inside any
   REPLACEMENT marker"). Inline `have`s are fine to introduce freely.

10. **Existing ORIGINAL marker check.** Before authoring REPLACEMENT
    blocks, worker should grep for existing
    `REFACTOR-BLOCK-ORIGINAL-BEGIN:` lines in
    `AddingInterventionNodes.lean`. If absent, the worker must add
    ORIGINAL-BEGIN/END marker pairs around each of the 7 original
    items first. (Comparison: `ExtendingCDMGsWith.lean` and
    `HardInterventionOn.lean` both have ORIGINAL markers wrapping the
    pre-refactor declarations; cleanup needs these to know what to
    delete.)

---

## 7. Notes from the row briefing (carry-over)

- `addition_to_the_LN` clarification
  `[doit_overloaded_for_node_addition_vs_hard_intervention]` is the
  disambiguation paragraph in the rewritten tex statement (L36–41).
  Already incorporated in the proven version's docstrings; no change
  needed for the port.
- LN wording-check subtleties
  `ad_hoc_mixed_doit_notation_g_doit_iw1_comma_w2` and
  `w_subseteq_j_makes_both_operations_near_identity` are encoding-
  independent (LN-level) — the port carries them over via the existing
  docstrings unchanged.

---

## 8. Time / effort estimate

Total port: ~30–60 minutes of focused work.
- (0)–(4) helpers: ~10 min mechanical edits (rename + marker
  wrappers).
- (5) sub-claim (a): ~10–15 min (proof body verbatim except for the
  two L subgoals + the new `h_L_lift_uu_collapse`).
- (6) sub-claim (b): ~15–25 min (J/V/E verbatim; cdmgExt drops a
  field; L-component proof is rewritten under Sym2 — substantively
  shorter than the original).
- Tex twin: ~5 min file copy.
