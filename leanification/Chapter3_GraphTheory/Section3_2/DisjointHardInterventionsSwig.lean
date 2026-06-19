import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGTypes
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.AcyclicPreservedUnderDo
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard

namespace Causality

/-!
# Disjoint hard interventions and node-splitting hard interventions
  commute (`claim_3_11`)

This file formalises the LN lemma `claim_3_11`
(`DisjointHardInterventions`, the SWIG analog of `claim_3_8`) in
section 3.2 of `graphs.tex`:

> Let `G = (J, V, E, L)` be a CADMG and `W₁ ⊆ J ∪ V`, `W₂ ⊆ V` two
> disjoint subsets of nodes of `G`.  Then
> `(G_{doit(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{doit(W₁)}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_11_statement_DisjointHardInterventions.tex`, verified
equivalent to the LN block (`addition_to_the_LN` empty).

## Carrier reading (load-bearing for this row's Lean signature)

`def_3_10` (`hardInterventionOn`) preserves the node carrier
(`Node → Node`) while `def_3_12` (`nodeSplittingHard`, SWIG) lifts
the carrier (`Node → SplitNode Node`).  Both sides of the asserted
equality therefore land in `CDMG (SplitNode Node)`:

* LHS `(G.hardInterventionOn W₁ hW₁).nodeSplittingHard _ W₂ _` — the
  inner hard intervention keeps the carrier as `Node`; the outer
  `nodeSplittingHard` lifts to `SplitNode Node`.
* RHS `(G.nodeSplittingHard hG W₂ hW₂).hardInterventionOn
  (W₁.image .unsplit) _` — the inner `nodeSplittingHard` lifts to
  `SplitNode Node`, and the outer hard intervention operates on the
  lifted carrier.  `W₁` is lifted to the split-graph carrier via
  `.image SplitNode.unsplit`, faithful to the tex spec's "Carrier
  reading of the equality" paragraph: every `w ∈ W₁` satisfies
  `w ∈ J ∪ V` (by `hW₁`) and `w ∉ W₂` (by disjointness), so `w`
  injects as its unsplit copy `.unsplit w` in the split-graph
  carrier.

Both sides have the same Lean type `CDMG (SplitNode Node)`, so the
equality is a *literal* `=` of CDMGs — mirroring the literal-`=`
pattern of `claim_3_8` (`DisjointHardInterventions`), the
node-splitting-not-SWIG analog of this row.  No `eqViaNodeMap` /
`flattenSplit` workaround is needed (contrast with `claim_3_10`'s
iterated-SWIG case, where two stacked `nodeSplittingHard`s produce
`CDMG (SplitNode (SplitNode Node))` and a carrier-relabelling is
unavoidable).

## CADMG hypothesis `(hG : G.IsCADMG)` on the signature

Unlike `claim_3_8` (whose `nodeSplittingOn` takes no acyclicity
precondition), `def_3_12`'s `nodeSplittingHard` requires
`(hG : G.IsCADMG)` on its signature (cf.\
`NodeSplittingHard.lean`'s design bullet (d)).  The RHS's inner
`nodeSplittingHard hG W₂ hW₂` is fed `hG` directly; the LHS's outer
`nodeSplittingHard ...` needs an `IsCADMG` witness on
`G.hardInterventionOn W₁ hW₁`, supplied by `claim_3_3`
(`acyclic_preserved_under_do`): if `G.IsAcyclic` (= `G.IsCADMG` by
`def_3_7` item i), then so is `G.hardInterventionOn W₁ hW₁`.  The
private wrapper `hardInterventionOn_isCADMG_of_isCADMG` below
extracts that conjunct cleanly so the main signature reads without
`.1` projections.

The body is filled in by `prove_claim_in_lean` (Manager B),
following the to-be-written tex proof at
`tex/claim_3_11_proof_DisjointHardInterventions.tex`.
-/

namespace CDMG

-- ## Design choice — statement context (refactor twin)
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1`'s refactor twin `CDMG` (`CDMG.lean`).  The
--   signature references `CDMG Node`,
--   `G.hardInterventionOn` (`def_3_10` twin), and
--   `G.nodeSplittingHard` (`def_3_12` twin), each of which
--   depends on `[DecidableEq Node]` through `Finset`-backed membership
--   and image operations.  The split-graph carrier
--   `SplitNode Node` inherits `[DecidableEq (SplitNode
--   Node)]` automatically via the `deriving DecidableEq` clause on
--   `SplitNode` (`NodeSplittingOn.lean`).
-- claim_3_11 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_11 --- end helper

-- ## Local decidability instance for the L-filter predicate
--
-- Required by the L-branch `change` step in the main theorem below,
-- which writes the L-component of the iterated intervention as
-- `… .filter (fun s : Sym2 _ => ∀ v ∈ s, v ∉ W)` — the endpoint-
-- universal filter shape pinned by `def_3_10`'s refactor twin's
-- L-field assignment (itself the canonical `Sym2.Mem` reading of
-- the LN's "remove every bidirected edge touching $W$" clause, see
-- `def_3_1`'s replacement design choice on `hL_subset` for the
-- `Sym2.Mem`-vs-destructure rationale).  `[DecidableEq Node]` alone
-- is not enough: universal quantification on `Sym2`'s underlying-
-- pair components requires the Mathlib `Sym2.ball` pattern to land
-- on a decidable conjunction, which Mathlib does not auto-derive at
-- this use site.
--
-- Private polymorphic copy of the
-- `hardInterventionOn_decidable_bAll` instance declared in
-- `HardInterventionOn.lean`.  That instance is declared `private`
-- at the def-site, so it does not propagate by `import`; we supply
-- our own local copy here.  Polymorphic over the ambient node type
-- so that the *same* instance covers both the LHS's inner
-- `hardInterventionOn` on `Sym2 Node` (the
-- hard-intervention applied first, on the unsplit carrier) *and*
-- the RHS's outer `hardInterventionOn` on the lifted
-- carrier `Sym2 (SplitNode Node)` (the hard-intervention
-- applied second, after `nodeSplittingHard`).
--
-- *Implementation.*  Identical to the def-site version: every
-- `s : Sym2 α` is `s(a, b)` for some `a, b`; Mathlib's `Sym2.ball`
-- reduces `∀ v ∈ s(a, b), v ∉ W` to `a ∉ W ∧ b ∉ W`; conjunction of
-- decidable propositions is decidable.  `recOnSubsingleton`
-- discharges the quotient-respecting obligation that the resulting
-- `Decidable` is independent of the chosen `(a, b)` representative.
--
-- *Naming.*  Distinct name from the sibling instance in
-- `DisjointHardInterventions.lean` (which uses
-- `disjointHardInterventions_decidable_bAll`, without the
-- `Swig`) keeps the renamed post-cleanup symbol unique across the
-- two twin files in the spl / SWIG pair.
set_option linter.style.longLine false in
private instance disjointHardInterventionsSwig_decidable_bAll
    {α : Type*} [DecidableEq α] (W : Finset α) :
    DecidablePred (fun s : Sym2 α => ∀ v ∈ s, v ∉ W) := fun s =>
  s.recOnSubsingleton fun _ _ => decidable_of_iff' _ Sym2.ball

-- ## Private helper — `IsCADMG` witness for the inner hard
-- intervention (refactor twin)
--
-- Port of `hardInterventionOn_isCADMG_of_isCADMG`.  The LHS's outer
-- `nodeSplittingHard ?hG W₂ ?hW₂` needs a
-- `IsCADMG` witness on
-- `G.hardInterventionOn W₁ hW₁` (because `def_3_12`'s
-- refactor twin requires acyclicity of its input).  `claim_3_3`'s
-- refactor twin `acyclic_preserved_under_do` provides
-- exactly this — as the first conjunct of an
-- `(acyclic) ∧ (∀ lt, topological_order ↦ …)` pair.  This wrapper
-- projects the first conjunct cleanly so the main signature reads
-- without `.1` clutter.  Not LN content (acyclicity preservation is
-- `claim_3_3`), so no helper markers — matches the original's
-- unmarked convention.
private lemma hardInterventionOn_isCADMG_of_isCADMG
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    (G.hardInterventionOn W hW).IsCADMG :=
  (acyclic_preserved_under_do G W hW hG).1

-- ## Helper — `W₂` sits inside the carrier of the inner hard
--   intervention (refactor twin)
--
-- Port of `subset_V_of_hardInterventionOn`.  Mechanical rename:
-- `CDMG → CDMG`,
-- `hardInterventionOn → hardInterventionOn`.  The V-side of
-- the post-refactor `hardInterventionOn` is structurally
-- identical to the pre-refactor `hardInterventionOn` (the refactor
-- only touches `L`), so the proof body carries over verbatim with
-- the rename.
set_option linter.style.longLine false in
-- claim_3_11 --- start helper
private lemma subset_V_of_hardInterventionOn
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.J ∪ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂ ⊆ (G.hardInterventionOn W₁ hW₁).V
-- claim_3_11 --- end helper
:= by
  intro v hv
  change v ∈ G.V \ W₁
  exact Finset.mem_sdiff.mpr ⟨hW₂ hv, Finset.disjoint_right.mp hDisj hv⟩

-- ## Helper — `W₁.image .unsplit` sits inside the carrier of the
--   inner SWIG (refactor twin)
--
-- Port of `image_unsplit_subset_carrier_of_nodeSplittingHard`.
-- Mechanical renames: `CDMG → CDMG`,
-- `SplitNode → SplitNode`,
-- `nodeSplittingHard → nodeSplittingHard`.  The J/V
-- partition of `nodeSplittingHard` is structurally
-- identical to the pre-refactor `nodeSplittingHard` (the refactor
-- only touches `L`), so the proof body carries over verbatim with
-- the rename.
set_option linter.style.longLine false in
-- claim_3_11 --- start helper
private lemma image_unsplit_subset_carrier_of_nodeSplittingHard
    {G : CDMG Node} {hG : G.IsCADMG}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.J ∪ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₁.image SplitNode.unsplit ⊆
      (G.nodeSplittingHard hG W₂ hW₂).J ∪
        (G.nodeSplittingHard hG W₂ hW₂).V
-- claim_3_11 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  rcases Finset.mem_union.mp (hW₁ hv) with hJ | hV
  · -- `v ∈ G.J` → `.unsplit v ∈ G.J.image .unsplit` ⊆ `J_{swig(W₂)}`.
    refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · -- `v ∈ G.V`: disjointness gives `v ∉ W₂`, so `v ∈ G.V \ W₂` and
    -- `.unsplit v` lands in `(G.V \ W₂).image .unsplit ⊆ V_{swig(W₂)}`.
    have hv_notW₂ : v ∉ W₂ := Finset.disjoint_left.mp hDisj hv
    refine Finset.mem_union_right _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hV, hv_notW₂⟩, rfl⟩

-- ref: claim_3_11 — refactor twin
--
-- For any `G : CDMG Node` (`hG : G.IsCADMG`) and
-- any two subsets `W₁ ⊆ G.J ∪ G.V`, `W₂ ⊆ G.V` with
-- `Disjoint W₁ W₂`, the LN equality
--   `(G_{doit(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{doit(W₁)}`
-- holds as a literal `=` of `CDMG`s over the split-graph
-- carrier `SplitNode Node`.
--
-- The mathematical content is unchanged from the pre-refactor
-- sibling `disjointHardInterventionsAndNodeSplittingHardsCommute`
-- (same file, pre-refactor `namespace CDMG` block above).  Under
-- the `cdmg_typed_edges` refactor (driving rationale at
-- `leanification/refactors/refactor_cdmg_typed_edges.md`) only the
-- L-field's *encoding* changes — from
-- `Finset (Node × Node) + hL_symm` to `Finset (Sym2 Node)` — so
-- the J / V / E sub-goals port verbatim under a rename pass while
-- the L sub-goal is restructured around `Sym2`-quotient API.  The
-- mathematical sibling on the spl side is `claim_3_8`'s refactor
-- twin `disjointHardInterventionsAndNodeSplittingsCommute`
-- in `DisjointHardInterventions.lean`; this SWIG twin diverges
-- only in the upstream operator (`nodeSplittingHard` vs
-- `nodeSplittingOn`) and the extra `hG : G.IsCADMG`
-- precondition that `def_3_12` levies on its input.
--
-- ## Refactor port — proof structure
--
-- * **J / V / E sub-goals port mechanically under the rename
--   pass.**  The post-refactor `hardInterventionOn` and
--   `nodeSplittingHard` leave J / V / E structurally
--   unchanged (the refactor only restructures `L`).  Each sub-goal
--   is the pre-refactor tactic block with the rename
--   `CDMG → CDMG`, `SplitNode → SplitNode`,
--   `toCopy0 → toCopy0`, `toCopy1 → toCopy1`:
--   `Finset.image_union` + `Finset.union_right_comm` for `J`,
--   elementwise `ext` for `V` (under set-difference and constructor
--   mismatch), and a `Finset.filter_image` rewrite for `E` (closed
--   pointwise via the inline `toCopy0_notMem_iff` helper on the
--   head `e.2` of each generator).  The `toCopy0_notMem_iff` helper
--   itself is unchanged from the pre-refactor sibling — it operates
--   on `Node` and `SplitNode Node`, not on the L-field's
--   typing — so the directed-edge sub-goal reuses it without
--   modification.
--
-- * **L sub-goal restructured around `Sym2.map` and the endpoint-
--   universal filter — the central encoding payoff of the
--   refactor.**  Pre-refactor `L` was carried as
--   `Finset (Node × Node)` and was discharged via two patterns
--   that the refactor structurally eliminates:
--
--   - The node-splitting lift was
--     `Prod.map (toCopy0 W₂) (toCopy0 W₂)` on ordered pairs (per
--     `def_3_12`'s pre-refactor L-field), with separate
--     destructuring of `e.1` and `e.2`.
--   - The hard-intervention removal clause was the *two-sided*
--     filter `fun e => e.1 ∉ W₁ ∧ e.2 ∉ W₁` — the
--     `hard_intervention_l_symmetrized_removal` deviation
--     registered at `def_3_10` to keep the survivor set closed
--     under `hL_symm`.
--
--   Post-refactor (matching `def_3_10`'s and `def_3_12`'s
--   refactor twins):
--
--   - **The lift is `Sym2.map (toCopy0 W₂)`** — Mathlib's
--     canonical lift of a node-level relabelling
--     `Node → SplitNode Node` through the swap quotient
--     (`Sym2.map f s(a, b) = s(f a, f b)`).  This is *the*
--     structural image-of-`L` under SWIG node-splitting: item iv
--     of `def_3_12`'s LN block collapses to a single
--     `Finset.image (Sym2.map (toCopy0 W₂)) G.L` with
--     no `Sym2.lift`-of-`Sym2.mk` boilerplate and crucially no
--     ordered-pair destructure that would force a choice of
--     representative under the swap quotient.  See
--     `NodeSplittingHard.lean`'s `nodeSplittingHard`
--     design bullet on `Sym2.map` vs `Sym2.lift`+pair-rebuild for
--     the def-site rationale; here we simply consume that shape.
--   - **The hard-intervention removal clause is the *endpoint-
--     universal* filter `fun s : Sym2 _ => ∀ v ∈ s, v ∉ W₁`**
--     (matching `def_3_10`'s refactor twin L-field assignment).
--     "Every node mentioned by `s` lies outside `W₁`" is the
--     canonical `Sym2.Mem` idiom pinned by `def_3_1`'s replacement
--     design choice on `hL_subset`: destructuring through
--     `Sym2.mk` to a `v.1 ∉ W₁ ∧ v.2 ∉ W₁` conjunction would
--     force a choice of representative that, under the swap
--     quotient, has no canonical value, and would re-introduce
--     the orientation asymmetry the refactor is designed to
--     dissolve.  The two-sided removal deviation is now
--     structurally subsumed: the LN's literal "remove every
--     bidirected edge touching $W$" reading translates directly
--     to the endpoint-universal form, with no ordered-pair
--     "second component" to single out and no `hL_symm`
--     invocation to close under.  See the rewritten tex twin's
--     "Refactor-context note on the removal clause of $\doit$ for
--     $L$" paragraph for the prose justification.
--
--   With those two encoding shifts in place, the L sub-goal
--   closes via the same three-step pattern as the pre-refactor
--   sibling, just on the `Sym2` carriers: `change` writes the
--   underlying form; `Finset.filter_image` swaps the filter
--   inside the image; `Finset.filter_congr` reduces to the
--   per-element predicate equivalence
--     `(∀ v ∈ s, v ∉ W₁) ↔
--        (∀ v ∈ Sym2.map (toCopy0 W₂) s,
--           v ∉ W₁.image SplitNode.unsplit)`,
--   which **closes via `Sym2.mem_map` plus the existing
--   `toCopy0_notMem_iff` helper**.  `Sym2.mem_map` (Mathlib:
--   `v ∈ Sym2.map f s ↔ ∃ v₀ ∈ s, f v₀ = v`) unfolds image-side
--   membership to a node-level disjunction over the underlying
--   pair, and `toCopy0_notMem_iff` (the *same* iff used by the
--   directed-edge sub-goal for the head of each generator)
--   discharges the pointwise step on each endpoint of the
--   unordered pair.  No fresh helper, no two-sided destructure —
--   the L sub-goal reduces to two applications of an iff that was
--   already in the proof's working memory.  Mirrors `claim_3_8`'s
--   refactor twin L-section exactly.
--
-- * **`cdmgExt` destructures 8 fields, not 9 — a *structural*
--   consequence of the `Sym2` encoding, not a missing field.**
--   The post-refactor `CDMG` has eight fields
--   (`J`, `V`, `hJV_disj`, `E`, `hE_subset`, `L`, `hL_subset`,
--   `hL_irrefl`) — one fewer than the pre-refactor nine, because
--   the LN's `(v₁, v₂) ∈ L ⟹ (v₂, v₁) ∈ L` symmetry implication
--   is *vacuous* under `Sym2`'s quotient typing
--   (`s(v₁, v₂) = s(v₂, v₁)` holds by construction), so
--   `hL_symm` is dropped at the structure level.  See `def_3_1`'s
--   replacement design choice on the `L` field (the `Sym2`
--   encoding commitment) for the foundational justification, and
--   the refactor rationale doc's "Drop `hL_symm` (free under
--   `Sym2`)" bullet.  A future reader scanning the eight-field
--   `rintro ⟨J₁, V₁, hJV₁, E₁, hE₁, L₁, hL₁, hLi₁⟩ ...` pattern
--   against the pre-refactor nine-field one should read the
--   discrepancy as structural, *not* as an accidentally dropped
--   field.
--
-- * **Local `private instance
--   disjointHardInterventionsSwig_decidable_bAll`
--   (declared above this comment block).**  Needed to make the
--   `Finset.filter` over the endpoint-universal predicate
--   `fun s : Sym2 _ => ∀ v ∈ s, v ∉ W` elaborate at the L-branch
--   `change` step.  Polymorphic over the ambient node type so the
--   same instance covers both the LHS's inner
--   `hardInterventionOn` on `Sym2 Node` and the RHS's
--   outer one on `Sym2 (SplitNode Node)`.  See the
--   instance's own comment block above for the full rationale and
--   the cross-reference to the def-site `private` instance in
--   `HardInterventionOn.lean`.
--
-- * **Literal `=` of `CDMG`s over
--   `SplitNode Node`, NOT
--   `eqViaNodeMap` / `flattenSplit`.**  Both
--   sides apply a single SWIG on `W₂` and a single hard
--   intervention on `W₁`, and `hardInterventionOn`
--   preserves the node carrier
--   (`CDMG α → CDMG α`), so both sides land in
--   `CDMG (SplitNode Node)` — no carrier
--   mismatch arises and the asserted equality is a literal `=`
--   between two terms of identical Lean type.  Contrast with
--   `claim_3_10`'s refactor twin (when ported), where iterating
--   `nodeSplittingHard` twice produces
--   `CDMG (SplitNode (SplitNode Node))`
--   on both sides with disagreeing constructor wrappings of the
--   same underlying node (`.unsplit (.copy0 w)` vs
--   `.copy0 (.unsplit w)`), forcing the
--   `eqViaNodeMap` / `flattenSplit` workaround.
--   Mirrors the literal-`=` pattern of the pre-refactor
--   `disjointHardInterventionsAndNodeSplittingHardsCommute`.
set_option linter.style.longLine false in
-- claim_3_11 -- start statement
theorem disjointHardInterventionsAndNodeSplittingHardsCommute
    (G : CDMG Node) (hG : G.IsCADMG)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (G.hardInterventionOn W₁ hW₁).nodeSplittingHard
        (hardInterventionOn_isCADMG_of_isCADMG hG hW₁) W₂
        (subset_V_of_hardInterventionOn hW₁ hW₂ hDisj)
      = (G.nodeSplittingHard hG W₂ hW₂).hardInterventionOn
          (W₁.image SplitNode.unsplit)
          (image_unsplit_subset_carrier_of_nodeSplittingHard
            hW₁ hW₂ hDisj)
-- claim_3_11 -- end statement
-- TeX proof: refactor_claim_3_11_proof_DisjointHardInterventions.tex
:= by
  -- `CDMG` extensionality: two `CDMG`s over the
  -- split-graph carrier are equal once their four data fields
  -- `(J, V, E, L)` agree.  Eight-field destructuring (the pre-
  -- refactor `hL_symm` field is gone — swap-symmetry is definitional
  -- on `Sym2`).
  have cdmgExt : ∀ {G₁ G₂ : CDMG (SplitNode Node)},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨J₁, V₁, hJV₁, E₁, hE₁, L₁, hL₁, hLi₁⟩
           ⟨J₂, V₂, hJV₂, E₂, hE₂, L₂, hL₂, hLi₂⟩ hJ hV hE hL
    obtain rfl := hJ
    obtain rfl := hV
    obtain rfl := hE
    obtain rfl := hL
    rfl
  -- Key membership lemma: under disjointness, the `toCopy0
  -- W₂`-lift of a `Node` lies outside `W₁.image .unsplit` iff the
  -- original `Node` lies outside `W₁`.  Implements the tex proof's
  -- "$v_k^o \notin W_1 \Leftrightarrow v_k \notin W_1$" cross-check
  -- (used both in the *directed edges* section for the `e.2` head of
  -- each generator, and twice in the *bidirected edges* section for
  -- the two endpoints of each unordered-pair generator).
  have toCopy0_notMem_iff : ∀ (v : Node),
      toCopy0 W₂ v ∉ W₁.image SplitNode.unsplit ↔
        v ∉ W₁ := by
    intro v
    unfold toCopy0
    by_cases hvW₂ : v ∈ W₂
    · rw [if_pos hvW₂]
      refine ⟨fun _ hW₁ => Finset.disjoint_left.mp hDisj hW₁ hvW₂,
              fun _ hMem => ?_⟩
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hMem
      cases hweq
    · rw [if_neg hvW₂]
      refine ⟨fun h hW₁ => h (Finset.mem_image.mpr ⟨v, hW₁, rfl⟩),
              fun h hMem => ?_⟩
      obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hMem
      cases hweq
      exact h hw
  refine cdmgExt ?_ ?_ ?_ ?_
  -- ===== Node sets: `J` =====
  -- LHS `J`: `(G.J ∪ W₁).image .unsplit ∪ W₂.image .copy1` (after
  -- unfolding `nodeSplittingHard` applied to
  -- `G.hardInterventionOn W₁ hW₁`).
  -- RHS `J`: `(G.J.image .unsplit ∪ W₂.image .copy1) ∪ W₁.image .unsplit`
  -- (after unfolding `hardInterventionOn` applied to
  -- `G.nodeSplittingHard hG W₂ hW₂`).  Per the tex's
  -- "Input nodes" section: rewrite `(G.J ∪ W₁).image` via
  -- `Finset.image_union` to
  -- `G.J.image .unsplit ∪ W₁.image .unsplit`, then swap the last
  -- two summands via `Finset.union_right_comm`.
  · change (G.J ∪ W₁).image SplitNode.unsplit
            ∪ W₂.image SplitNode.copy1
          = (G.J.image SplitNode.unsplit
              ∪ W₂.image SplitNode.copy1)
              ∪ W₁.image SplitNode.unsplit
    rw [Finset.image_union, Finset.union_right_comm]
  -- ===== Node sets: `V` =====
  -- LHS `V`: `((G.V \ W₁) \ W₂).image .unsplit ∪ W₂.image .copy0`.
  -- RHS `V`: `((G.V \ W₂).image .unsplit ∪ W₂.image .copy0)
  --             \ W₁.image .unsplit`.
  -- We prove the equality directly via element-wise `ext`, mirroring
  -- the pre-refactor V section.
  · change ((G.V \ W₁) \ W₂).image SplitNode.unsplit
            ∪ W₂.image SplitNode.copy0
          = ((G.V \ W₂).image SplitNode.unsplit
              ∪ W₂.image SplitNode.copy0)
            \ W₁.image SplitNode.unsplit
    ext x
    constructor
    · -- LHS → RHS direction.
      intro hx
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · -- `x` is in the inner V (RHS-pre-sdiff).
        rcases Finset.mem_union.mp hx with hx1 | hx2
        · -- `x = .unsplit v`, `v ∈ (G.V \ W₁) \ W₂` ⊆ `G.V \ W₂`.
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
          obtain ⟨hv_VW₁, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
          obtain ⟨hv_V, _⟩ := Finset.mem_sdiff.mp hv_VW₁
          refine Finset.mem_union_left _ ?_
          exact Finset.mem_image.mpr
            ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₂⟩, rfl⟩
        · -- `x = .copy0 w`, lands directly in the right summand of inner V.
          refine Finset.mem_union_right _ ?_
          exact hx2
      · -- `x ∉ W₁.image .unsplit`: case on which piece of LHS V holds x.
        rcases Finset.mem_union.mp hx with hx1 | hx2
        · -- `x = .unsplit v`, `v ∉ W₁` from `v ∈ G.V \ W₁`.
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
          obtain ⟨hv_VW₁, _⟩ := Finset.mem_sdiff.mp hv
          obtain ⟨_, hv_notW₁⟩ := Finset.mem_sdiff.mp hv_VW₁
          intro h
          obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
          cases hweq
          exact hv_notW₁ hw
        · -- `x = .copy0 w`: constructor mismatch with `.unsplit`.
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx2
          intro h
          obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
          cases hweq
    · -- RHS → LHS direction.
      intro hx
      obtain ⟨hx_inner, hx_notW₁'⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp hx_inner with hx1 | hx2
      · -- `x = .unsplit v`, `v ∈ G.V \ W₂`, and `v ∉ W₁` from
        -- `hx_notW₁'` (`.unsplit v ∉ W₁.image .unsplit` by injectivity).
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨hv_V, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
        have hv_notW₁ : v ∉ W₁ := fun h =>
          hx_notW₁' (Finset.mem_image.mpr ⟨v, h, rfl⟩)
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₁⟩, hv_notW₂⟩
      · -- `x = .copy0 w`, lands directly in the right summand of LHS V.
        refine Finset.mem_union_right _ ?_
        exact hx2
  -- ===== Directed edges: `E` =====
  -- LHS `E`: `(G.E.filter (e.2 ∉ W₁)).image
  --             (toCopy1 W₂ ·.1, toCopy0 W₂ ·.2)`.
  -- RHS `E`: `(G.E.image (toCopy1 W₂ ·.1, toCopy0 W₂ ·.2)).filter
  --             (e.2 ∉ W₁.image .unsplit)`.
  -- Per the tex's "Directed edges" section: `Finset.filter_image`
  -- swaps to a pre-image-filter form, and the filter predicate
  -- matches `e.2 ∉ W₁` via `toCopy0_notMem_iff` applied to `e.2`.
  -- The SWIG construction introduces NO transfer-edge piece, so the
  -- directed-edge case is one image-filter rewrite simpler than
  -- claim_3_8's E section — no `Finset.filter_union` pre-rewrite, no
  -- second-summand vacuous-filter argument.
  · change (G.E.filter (fun e : Node × Node => e.2 ∉ W₁)).image
            (fun e : Node × Node =>
              (toCopy1 W₂ e.1, toCopy0 W₂ e.2))
          = (G.E.image
              (fun e : Node × Node =>
                (toCopy1 W₂ e.1,
                  toCopy0 W₂ e.2))).filter
              (fun e : SplitNode Node × SplitNode Node =>
                e.2 ∉ W₁.image SplitNode.unsplit)
    rw [Finset.filter_image]
    congr 1
    refine Finset.filter_congr ?_
    intro e he
    exact (toCopy0_notMem_iff e.2).symm
  -- ===== Bidirected edges: `L` =====
  -- LHS `L`: `(G.L.filter (∀ v ∈ s, v ∉ W₁)).image
  --             (Sym2.map (toCopy0 W₂))`.
  -- RHS `L`: `(G.L.image (Sym2.map (toCopy0 W₂))).filter
  --             (∀ v ∈ s, v ∉ W₁.image .unsplit)`.
  --
  -- Per the tex twin's "Bidirected edges" section: post-refactor, the
  -- LN's literal one-sided removal clause translates directly to the
  -- endpoint-universal form "every endpoint of the unordered pair
  -- lies outside `W₁`".  `Finset.filter_image` swaps the filter
  -- inside the image; `Finset.filter_congr` reduces to a per-element
  -- predicate equivalence, which closes via `Sym2.mem_map`
  -- (unfolds `v ∈ Sym2.map f s` to `∃ v₀ ∈ s, f v₀ = v`) plus
  -- pointwise `toCopy0_notMem_iff`.
  · change (G.L.filter (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₁)).image
            (Sym2.map (toCopy0 W₂))
          = (G.L.image (Sym2.map (toCopy0 W₂))).filter
              (fun s : Sym2 (SplitNode Node) =>
                ∀ v ∈ s, v ∉ W₁.image SplitNode.unsplit)
    rw [Finset.filter_image]
    congr 1
    refine Finset.filter_congr ?_
    intro s hs
    constructor
    · -- `(∀ v ∈ s, v ∉ W₁) → ∀ v ∈ Sym2.map f s, v ∉ W₁.image .unsplit`.
      intro h v hv
      obtain ⟨v₀, hv₀, rfl⟩ := Sym2.mem_map.mp hv
      exact (toCopy0_notMem_iff v₀).mpr (h v₀ hv₀)
    · -- `(∀ v ∈ Sym2.map f s, v ∉ W₁.image .unsplit) → ∀ v ∈ s, v ∉ W₁`.
      intro h v hv
      exact (toCopy0_notMem_iff v).mp
        (h (toCopy0 W₂ v) (Sym2.mem_map.mpr ⟨v, hv, rfl⟩))

end CDMG

end Causality
