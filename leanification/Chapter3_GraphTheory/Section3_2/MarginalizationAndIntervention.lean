import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_2.MarginalizationAK
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn
import Chapter3_GraphTheory.Section3_2.ExtendingCDMGsWith
import Chapter3_GraphTheory.Section3_2.MargPreservesAncestors

namespace Causality

/-!
# Marginalization and intervention commute (`claim_3_18`)

This file formalises the LN lemma `claim_3_18`
(`\label{marginalization-and-intervention-commute}` in `graphs.tex`).
Per the row's `addition_to_the_LN` the LN block bundles three
distinct commutativity claims under one `\begin{Lem}` heading — one
per intervention operator (hard intervention, adding intervention
nodes, node-splitting), each commuting with marginalization
(`def_3_14`).  The authoritative spec is the rewritten canonical tex
statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_18_statement_MarginalizationAndIntervention.tex`, verified
equivalent to the LN block plus the operator's
`addition_to_the_LN` clarification
`[trailing_similar_statement_two_unstated_claims]`.  The rewritten
tex spells the lemma out as a three-part enumerate with a single
equation per part:

* (i)  *(hard intervention)*       `(G_{doit(W₁)})^{∖W₂}    = (G^{∖W₂})_{doit(W₁)}`;
* (ii) *(adding intervention nodes)* `(G_{doit(I_{W₁})})^{∖W₂} = (G^{∖W₂})_{doit(I_{W₁})}`;
* (iii) *(node-splitting)*           `(G_{spl(W₁)})^{∖W₂}     = (G^{∖W₂})_{spl(W₁)}`.

The typing on `W₁` varies by part — `W₁ ⊆ J ∪ V` for (i) and (ii)
matching `def_3_10` / `def_3_13`, `W₁ ⊆ V` for (iii) matching
`def_3_11`.  `W₂ ⊆ V` in all three parts (so the inner / outer
marginalization is well-typed), and the disjointness side condition
`Disjoint W₁ W₂` is in force throughout.  The result-carrier varies
by part: `CDMG Node` for (i), `CDMG (IntExtNode Node)` for (ii),
`CDMG (SplitNode Node)` for (iii) — each side of each equation lives
in the same carrier (no `eqViaNodeMap` workaround needed; see the
"Carrier matching" paragraphs in the design blocks below).

The bodies of the three theorems are filled in by `prove_claim_in_lean`
(Manager B), following the to-be-written tex proofs at
`tex/claim_3_18_proof_MarginalizationAndIntervention.tex`.
-/

namespace CDMG

-- ## Design choice — row-level shape (three theorems in one file)
--
-- *Three separate theorems, not one parametric "for every intervention
--   operator" statement.*  The row's `addition_to_the_LN` clause
--   `[trailing_similar_statement_two_unstated_claims]` factors the LN's
--   single Lemma into three sub-claims with **different result
--   carriers** — `CDMG Node` for Part (i), `CDMG (IntExtNode Node)` for
--   Part (ii), `CDMG (SplitNode Node)` for Part (iii).  Lean has no
--   natural way to host a parametric quantification over "intervention
--   operator" that lets the return type vary by operator (each
--   operator's signature already fixes its return carrier), so the
--   three-theorem shape mirrors the addition's enumeration verbatim —
--   and the addition is the spec we must satisfy.  Bundling into one
--   conjunction would over-couple the three parts and obstruct
--   selective downstream citation: chapter 5's ID-algorithm
--   manipulation `G_{\doit(C)}^{\sm B}` (`id-algorithm.tex` 159-161,
--   485-498) cites only Part (i), and counterfactuals at
--   `counterfactuals.tex` 238-241 rest on the same Part (i) shape.
--   Contrast `claim_3_17` (MarginalizationsCommute), which the LN
--   states as a triple equality `=…=…` and is therefore formalized as
--   a single conjunctive theorem.
--
-- *One Lean file, not three per-part files.*  The three parts share
--   the same upstream-def chain (`def_3_1`, `def_3_10` / `_11` / `_13`,
--   `def_3_14`), the same shared lift helpers below
--   (`subset_sdiff_of_disjoint`, `subset_carrier_of_marginalize`, and
--   the two `image_unsplit_subset_*` helpers), and the same proof-
--   strategy template (CDMG-`ext` field-by-field).  Splitting per-part
--   would re-import the same chain three times and scatter the lift
--   helpers across files.  Split decision is deferred to a post-proof
--   refactor if the file passes ~3000 lines (cf.
--   `MarginalizationsCommute.lean` at 3639 lines).

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited from `def_3_1`
--   (`CDMG.lean`), `def_3_10` (`HardInterventionOn.lean`), `def_3_11`
--   (`NodeSplittingOn.lean`), `def_3_13` (`ExtendingCDMGsWith.lean`),
--   and `def_3_14` (`MarginalizationAK.lean`); load-bearing because the
--   signatures of all three theorems below construct `Finset`-backed
--   subsets of `G.J ∪ G.V` / `G.V`, applications of `Finset.image`
--   under `IntExtNode.unsplit` / `SplitNode.unsplit`, and the
--   marginalize / hardInterventionOn / extendingCDMGsWith /
--   nodeSplittingOn operators (each of which carries a `[DecidableEq]`
--   constraint into its return type's `CDMG` structure).  Stronger
--   instances (`Fintype`, `LinearOrder`) are not needed at the
--   statement level and are deferred to the proof body's use sites.
-- claim_3_18 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_18 --- end helper

-- ## Helper — `S ⊆ U \ T` from `S ⊆ U` and `Disjoint S T`
--
-- Used twice in the statement signatures: Part (i)'s LHS inner
-- `marginalize W₂` (needs `W₂ ⊆ (G.hardInterventionOn W₁ hW₁).V =
-- G.V \ W₁`) and Part (iii)'s RHS outer `nodeSplittingOn W₁` (needs
-- `W₁ ⊆ (G.marginalize W₂ hW₂).V = G.V \ W₂`).  The lemma is the
-- direct `.mpr` of mathlib's `Finset.subset_sdiff` and lives here so
-- the theorem signatures stay free of inline term-mode plumbing.
--
-- ## Design choice
--
-- *Re-prove locally rather than import from `MarginalizationsCommute.lean`.*
--   The sibling row's `subset_sdiff_of_disjoint` (claim_3_17) is
--   `private` to that file; per the per-row scope discipline
--   (`claude.md` rule 4) we re-prove it here under the same name
--   rather than promote it to a chapter-wide public helper.  The proof
--   is a one-liner Mathlib iff direction, so the duplication has
--   near-zero maintenance cost.
--
-- *Disjointness orientation `Disjoint S T`, matching the mathlib
--   iff.*  At the call sites the caller's `hDisj : Disjoint W₁ W₂`
--   (LN-symmetric phrasing) is composed with `.symm` when the
--   operator's argument order flips — see the call sites in Parts (i)
--   and (iii).
-- claim_3_18 --- start helper
private lemma subset_sdiff_of_disjoint {S T : Finset Node}
    {U : Finset Node} (hS : S ⊆ U) (hDisj : Disjoint S T) :
    S ⊆ U \ T
-- claim_3_18 --- end helper
:= Finset.subset_sdiff.mpr ⟨hS, hDisj⟩

-- ## Helper — `S ⊆ G.J ∪ (G.V ∖ W)` from `S ⊆ G.J ∪ G.V` and `Disjoint S W`
--
-- Used twice in the statement signatures: Part (i)'s RHS outer
-- `hardInterventionOn W₁` and Part (ii)'s RHS outer
-- `extendingCDMGsWith W₁`, both applied to `G.marginalize W₂ hW₂`.
-- The outer constructor in each case requires `W₁ ⊆
-- (G.marginalize W₂ hW₂).J ∪ (G.marginalize W₂ hW₂).V`, which
-- unfolds (per `def_3_14`'s items i / ii) to `W₁ ⊆ G.J ∪ (G.V ∖ W₂)`.
-- This lemma discharges that subset from the available hypotheses
-- `hW₁ : W₁ ⊆ G.J ∪ G.V`, `hW₂ : W₂ ⊆ G.V`, and `hDisj : Disjoint W₁
-- W₂` via a per-element case split on `v ∈ G.J ∨ v ∈ G.V`.
--
-- ## Design choice
--
-- *Stand-alone helper, not an inline `by`-block in the theorem
--   signature.*  Mirrors the helper pattern in the sibling
--   `MarginalizationsCommute.lean` (`subset_sdiff_of_disjoint`),
--   `HardInterventionsCommute.lean` (`subset_carrier_of_hard…`), and
--   `AddingInterventionNodes.lean`
--   (`image_unsplit_subset_extendingCDMGsWith_carrier`): keeps the
--   rendered theorem on the website free of bookkeeping clutter, and
--   shares the lift between Parts (i) and (ii) at one definition
--   site.
--
-- *Disjointness orientation `Disjoint S W`* (`S` first, marginalize-
--   out `W` second).  Matches the LN's symmetric phrasing and the
--   natural call-site `subset_carrier_of_marginalize hW₂ hW₁ hDisj`
--   with `S := W₁`, `W := W₂`, `hDisj := claim_3_18's hDisj : Disjoint
--   W₁ W₂`.
--
-- *Implicit `G`, `W`, `S`; explicit `hW`, `hS`, `hDisj`.*  At the call
--   site `subset_carrier_of_marginalize hW₂ hW₁ hDisj`, the implicit
--   arguments are synthesised from the goal type, and the call reads
--   left-to-right as "the inner marginalization is on `W₂` via `hW₂`;
--   the transported set is `W₁` via `hW₁`; the disjointness witness
--   is `hDisj`".
-- claim_3_18 --- start helper
private lemma subset_carrier_of_marginalize {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.V) {S : Finset Node} (hS : S ⊆ G.J ∪ G.V)
    (hDisj : Disjoint S W) :
    S ⊆ (G.marginalize W hW).J ∪ (G.marginalize W hW).V
-- claim_3_18 --- end helper
:= by
  intro v hv
  change v ∈ G.J ∪ (G.V \ W)
  rcases Finset.mem_union.mp (hS hv) with hJ | hV
  · exact Finset.mem_union_left _ hJ
  · refine Finset.mem_union_right _ ?_
    exact Finset.mem_sdiff.mpr ⟨hV, Finset.disjoint_left.mp hDisj hv⟩

-- ## Helper — `S.image .unsplit ⊆ (G.extendingCDMGsWith W hW).V`
--
-- Used once in the statement signatures: Part (ii)'s LHS inner
-- `marginalize (W₂.image .unsplit)` applied to
-- `G.extendingCDMGsWith W₁ hW₁`.  The marginalization requires
-- `W₂.image .unsplit ⊆ (G.extendingCDMGsWith W₁ hW₁).V`, which
-- unfolds (per `def_3_13` item ii) to `W₂.image .unsplit ⊆
-- G.V.image .unsplit`.  This lemma is the per-element witness from
-- `S ⊆ G.V`: `v ∈ S → v ∈ G.V → .unsplit v ∈ G.V.image .unsplit`.
--
-- ## Design choice
--
-- *Stand-alone helper, not an inline `by`-block in the theorem
--   signature.*  Same rationale as `subset_carrier_of_marginalize`
--   above.  Mirrors `image_unsplit_subset_extendingCDMGsWith_V` from
--   `AddingInterventionNodesSwig.lean` (privately re-defined; we
--   re-prove locally per the per-row scope discipline).
--
-- *No disjointness consumed.*  The `Finset.image .unsplit` lift only
--   needs the per-element membership `v ∈ G.V`; it does not interact
--   with the `W` of `extendingCDMGsWith` because `(extendingCDMGsWith
--   W hW).V` does not depend on `W` (only `J` does, via the
--   `intCopy`-image addition).  `hW` is bound on the signature for
--   uniformity with the call site `image_unsplit_subset_extendingCDMGs
--   With_V hW₁ hW₂`; the `set_option` keeps the linter quiet.
-- claim_3_18 --- start helper
set_option linter.unusedVariables false in
private lemma image_unsplit_subset_extendingCDMGsWith_V {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V)
    {S : Finset Node} (hS : S ⊆ G.V) :
    S.image IntExtNode.unsplit ⊆ (G.extendingCDMGsWith W hW).V
-- claim_3_18 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change IntExtNode.unsplit v ∈ G.V.image IntExtNode.unsplit
  exact Finset.mem_image.mpr ⟨v, hS hv, rfl⟩

-- ## Helper — `S.image .unsplit ⊆ (G.nodeSplittingOn W₁ hW₁).V`
--
-- Used once in the statement signatures: Part (iii)'s LHS inner
-- `marginalize (W₂.image .unsplit)` applied to
-- `G.nodeSplittingOn W₁ hW₁`.  The marginalization requires
-- `W₂.image .unsplit ⊆ (G.nodeSplittingOn W₁ hW₁).V`, which
-- unfolds (per `def_3_11` item ii) to
-- `W₂.image .unsplit ⊆ (G.V \ W₁).image .unsplit ∪ W₁.image .copy0 ∪
--    W₁.image .copy1`.  This lemma routes the lift through the
-- `(G.V \ W₁).image .unsplit` piece: from `v ∈ S ⊆ G.V` and `Disjoint
-- S W₁` we get `v ∈ G.V \ W₁`, and `.unsplit v` lands in the
-- corresponding image piece.
--
-- ## Design choice
--
-- *Stand-alone helper, not an inline `by`-block in the theorem
--   signature.*  Same rationale as the sibling helpers above.
--   Mirrors `image_unsplit_subset_carrier_of_nodeSplittingOn` from
--   `DisjointHardInterventions.lean` (privately re-defined; we
--   re-prove locally per the per-row scope discipline) but lifts to
--   `(...).V` rather than `(...).J ∪ (...).V` because our lifted set
--   `W₂` lives in `G.V` (not `G.J ∪ G.V`).
--
-- *Disjointness consumed.*  Unlike `image_unsplit_subset_extendingCDMGs
--   With_V`, this lift needs `Disjoint S W₁` to route the lifted
--   `.unsplit v` through the `(G.V \ W₁).image .unsplit` piece of
--   `(G.nodeSplittingOn W₁ hW₁).V`.  Without disjointness, a `v ∈ S
--   ∩ W₁` would have `.unsplit v` *not* in `(G.V \ W₁).image .unsplit`
--   (it would belong to `W₁.image .copy0 / .copy1` after the lift
--   through `toCopy0 / toCopy1`, but the bare `.unsplit v` lifted from
--   `S` does not factor through `toCopy{0,1}`).
--
-- *Disjointness orientation `Disjoint S W₁`* (`S` first, split-on
--   `W₁` second).  Matches `subset_carrier_of_marginalize`'s
--   convention and the natural call-site
--   `image_unsplit_subset_nodeSplittingOn_V_of_disjoint hW₁ hW₂
--   hDisj.symm` (with claim_3_18's `hDisj : Disjoint W₁ W₂`).
-- claim_3_18 --- start helper
private lemma image_unsplit_subset_nodeSplittingOn_V_of_disjoint
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V)
    {S : Finset Node} (hS : S ⊆ G.V) (hDisj : Disjoint S W₁) :
    S.image SplitNode.unsplit ⊆ (G.nodeSplittingOn W₁ hW₁).V
-- claim_3_18 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change SplitNode.unsplit v ∈
    (G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_union_left _ ?_
  exact Finset.mem_image.mpr ⟨v,
    Finset.mem_sdiff.mpr ⟨hS hv, Finset.disjoint_left.mp hDisj hv⟩, rfl⟩

-- ## Walk surgery for hard intervention (proof-only helpers for Part i).
--
-- The `hardInterventionOn` operator removes edges via `Finset.filter`:
--   `E_{doit(W)} := G.E.filter (e.2 ∉ W)`, `L_{doit(W)} := G.L.filter (e.1 ∉ W ∧ e.2 ∉ W)`.
-- A walk in `G.hardInterventionOn W hW` therefore canonically casts down to
-- a walk in `G` (each filtered-edge membership implies the original membership).
-- The reverse cast — a walk in `G` becomes a walk in `G.hardInterventionOn W hW`
-- — needs a per-edge filter-survival side condition; for directed walks it
-- collapses to "every head (every tail vertex) lies outside `W`", and for
-- general walks (bifurcations) it strengthens to "every vertex lies outside `W`".

private lemma mem_doit_of_mem_G {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {v : Node} (hv : v ∈ G) :
    v ∈ G.hardInterventionOn W hW := by
  change v ∈ (G.J ∪ W) ∪ (G.V \ W)
  change v ∈ G.J ∪ G.V at hv
  rcases Finset.mem_union.mp hv with hJ | hV
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
  · by_cases hW' : v ∈ W
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hW')
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, hW'⟩)

private lemma mem_G_of_mem_doit {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {v : Node}
    (hv : v ∈ G.hardInterventionOn W hW) : v ∈ G := by
  change v ∈ (G.J ∪ W) ∪ (G.V \ W) at hv
  change v ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp hv with h | h
  · rcases Finset.mem_union.mp h with hJ | hW'
    · exact Finset.mem_union_left _ hJ
    · exact hW hW'
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp h).1

private lemma walkStep_ofDoit {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {u v : Node} {a : Node × Node}
    (h : (G.hardInterventionOn W hW).WalkStep u a v) : G.WalkStep u a v := by
  rcases h with ⟨ha, hOr⟩ | ⟨ha, hE⟩
  · refine Or.inl ⟨ha, ?_⟩
    rcases hOr with hE | hL
    · exact Or.inl (Finset.mem_filter.mp hE).1
    · exact Or.inr (Finset.mem_filter.mp hL).1
  · exact Or.inr ⟨ha, (Finset.mem_filter.mp hE).1⟩

/-- Cast a walk in `G.hardInterventionOn W hW` to a walk in `G`. -/
private def walk_ofDoit {G : CDMG Node} {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node}, Walk (G.hardInterventionOn W hW) u v → Walk G u v
  | _, _, .nil v hv => Walk.nil v (mem_G_of_mem_doit (hW := hW) hv)
  | _, _, .cons v a hStep p =>
      Walk.cons v a (walkStep_ofDoit (hW := hW) hStep) (walk_ofDoit hW p)

private lemma walk_ofDoit_length {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      (walk_ofDoit hW p).length = p.length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ p => by
      change (walk_ofDoit hW p).length + 1 = p.length + 1
      rw [walk_ofDoit_length hW p]

private lemma walk_ofDoit_vertices {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      (walk_ofDoit hW p).vertices = p.vertices
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ p => by
      change _ :: (walk_ofDoit hW p).vertices = _ :: p.vertices
      rw [walk_ofDoit_vertices hW p]

private lemma walk_ofDoit_isDirectedWalk {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      p.IsDirectedWalk → (walk_ofDoit hW p).IsDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons _ _ _ p, hDir => by
      obtain ⟨ha, hE, hRec⟩ := hDir
      exact ⟨ha, (Finset.mem_filter.mp hE).1,
        walk_ofDoit_isDirectedWalk hW p hRec⟩

private lemma walk_ofDoit_isBifurcationWithSplit {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v) (i : ℕ),
      p.IsBifurcationWithSplit i → (walk_ofDoit hW p).IsBifurcationWithSplit i
  | _, _, .nil _ _, _, h => h.elim
  | _, _, .cons _ _ _ (.nil _ _), 0, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
      obtain ⟨ha, hL⟩ := hSpl
      simp only [walk_ofDoit, Walk.IsBifurcationWithSplit]
      exact ⟨ha, (Finset.mem_filter.mp hL).1⟩
  | _, _, .cons _ _ _ (.cons _ _ _ _), 0, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
      obtain ⟨hOr, hDir⟩ := hSpl
      simp only [walk_ofDoit, Walk.IsBifurcationWithSplit]
      refine ⟨?_, walk_ofDoit_isDirectedWalk hW _ hDir⟩
      rcases hOr with ⟨ha, hE⟩ | ⟨ha, hL⟩
      · exact Or.inl ⟨ha, (Finset.mem_filter.mp hE).1⟩
      · exact Or.inr ⟨ha, (Finset.mem_filter.mp hL).1⟩
  | _, _, .cons _ _ _ p, k+1, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
      obtain ⟨ha, hE, hRec⟩ := hSpl
      simp only [walk_ofDoit, Walk.IsBifurcationWithSplit]
      exact ⟨ha, (Finset.mem_filter.mp hE).1,
        walk_ofDoit_isBifurcationWithSplit hW p k hRec⟩

private lemma walk_ofDoit_isBifurcation {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) {u v : Node}
    (p : Walk (G.hardInterventionOn W hW) u v)
    (hp : p.IsBifurcation) : (walk_ofDoit hW p).IsBifurcation := by
  obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hp
  refine ⟨hne, ?_, ?_, i, walk_ofDoit_isBifurcationWithSplit hW p i hi⟩
  · rw [walk_ofDoit_vertices hW p]; exact hu_tail
  · rw [walk_ofDoit_vertices hW p]; exact hv_drop

-- WalkStep G → G_{doit}, both endpoints constraint.
private lemma walkStep_toDoit {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {u v : Node} {a : Node × Node}
    (h : G.WalkStep u a v) (hu : u ∉ W) (hv : v ∉ W) :
    (G.hardInterventionOn W hW).WalkStep u a v := by
  rcases h with ⟨ha, hOr⟩ | ⟨ha, hE⟩
  · refine Or.inl ⟨ha, ?_⟩
    rcases hOr with hE | hL
    · refine Or.inl ?_
      change a ∈ G.E.filter _
      refine Finset.mem_filter.mpr ⟨hE, ?_⟩
      rw [ha]; exact hv
    · refine Or.inr ?_
      change a ∈ G.L.filter _
      refine Finset.mem_filter.mpr ⟨hL, ?_⟩
      rw [ha]; exact ⟨hu, hv⟩
  · refine Or.inr ⟨ha, ?_⟩
    change a ∈ G.E.filter _
    refine Finset.mem_filter.mpr ⟨hE, ?_⟩
    rw [ha]; exact hu

-- WalkStep G → G_{doit}, directed (forward-E) case: only head matters.
private lemma walkStep_toDoit_dir {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {u v : Node} {a : Node × Node}
    (ha : a = (u, v)) (haE : a ∈ G.E) (hv : v ∉ W) :
    (G.hardInterventionOn W hW).WalkStep u a v := by
  refine Or.inl ⟨ha, Or.inl ?_⟩
  change a ∈ G.E.filter _
  refine Finset.mem_filter.mpr ⟨haE, ?_⟩
  rw [ha]; exact hv

-- ## Predicate iff lemmas for Part (i): Φ_E and Φ_L through doit + marg.
--
-- Each direction is handled separately:
--   * `(⇒)` direction uses `walk_ofDoit` (a structurally simple downward cast,
--     no side conditions).
--   * `(⇐)` direction lifts the walk from `G` back into `G.hardInterventionOn W₁ hW₁`,
--     done inline via `induction` on the walk (this avoids a separate
--     `walk_toDoit` def whose `by`-block body would block subsequent reduction
--     for preservation lemmas).

/-- Lift a directed walk in `G` to a directed walk in
`G.hardInterventionOn W hW`, preserving length and vertices.  Side condition:
all tail vertices (= all heads of directed edges) lie outside `W`. -/
private lemma lift_dir_walk_to_doit {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {a b : Node} (r : Walk G a b),
      r.IsDirectedWalk →
      (∀ x ∈ r.vertices.tail, x ∉ W) →
      ∃ s : Walk (G.hardInterventionOn W hW) a b,
        s.IsDirectedWalk ∧ s.length = r.length ∧ s.vertices = r.vertices := by
  intro a b r
  induction r with
  | nil v hv =>
      intro _ _
      refine ⟨Walk.nil v (mem_doit_of_mem_G (hW := hW) hv), trivial, rfl, rfl⟩
  | @cons u' w' vMid a' hStep p' ih =>
      intro hr_dir hNotW
      obtain ⟨ha', hE', hRecDir'⟩ := hr_dir
      have hvMid_notW : vMid ∉ W :=
        hNotW vMid (Walk.head_mem_vertices p')
      have h_inner : ∀ x ∈ p'.vertices.tail, x ∉ W := fun x hx =>
        hNotW x (List.mem_of_mem_tail hx)
      obtain ⟨s', hs'_dir, hs'_len, hs'_vs⟩ := ih hRecDir' h_inner
      refine ⟨Walk.cons vMid a'
        (walkStep_toDoit_dir (hW := hW) ha' hE' hvMid_notW) s', ?_, ?_, ?_⟩
      · refine ⟨ha', ?_, hs'_dir⟩
        change a' ∈ G.E.filter _
        refine Finset.mem_filter.mpr ⟨hE', ?_⟩
        rw [ha']; exact hvMid_notW
      · show s'.length + 1 = p'.length + 1
        rw [hs'_len]
      · show u' :: s'.vertices = u' :: p'.vertices
        rw [hs'_vs]

/-- Lift IsBifurcationWithSplit through the doit-cast. -/
private lemma lift_bifWithSplit_to_doit_aux {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {a b : Node} (r : Walk G a b) (i : ℕ),
      (∀ x ∈ r.vertices, x ∉ W) →
      r.IsBifurcationWithSplit i →
      ∃ s : Walk (G.hardInterventionOn W hW) a b,
        s.IsBifurcationWithSplit i ∧ s.vertices = r.vertices := by
  intro a b r
  induction r with
  | nil _ _ => intro i _ h; exact h.elim
  | @cons u' w' vMid a' hStep p' ih =>
      intro i hNotW hSpl
      have hu'_notW : u' ∉ W := hNotW u' List.mem_cons_self
      have hvMid_notW : vMid ∉ W :=
        hNotW vMid (List.mem_cons_of_mem _ (Walk.head_mem_vertices p'))
      have h_inner_all : ∀ x ∈ p'.vertices, x ∉ W := fun x hx =>
        hNotW x (List.mem_cons_of_mem _ hx)
      -- Case analysis on (i, p')
      match i, p', hSpl, ih with
      | 0, .nil v hv, hSpl, _ =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
          obtain ⟨ha', hL⟩ := hSpl
          have hv_notW : v ∉ W :=
            hNotW v (List.mem_cons_of_mem _ List.mem_cons_self)
          refine ⟨Walk.cons v a'
            (walkStep_toDoit (hW := hW) hStep hu'_notW hvMid_notW)
            (Walk.nil v (mem_doit_of_mem_G (hW := hW) hv)), ?_, rfl⟩
          show _ = _ ∧ _ ∈ (G.hardInterventionOn W hW).L
          refine ⟨ha', ?_⟩
          change a' ∈ G.L.filter _
          refine Finset.mem_filter.mpr ⟨hL, ?_⟩
          rw [ha']; exact ⟨hu'_notW, hvMid_notW⟩
      | 0, .cons vMidInner aInner hStepInner pInner, hSpl, _ =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
          obtain ⟨hOr, hDir⟩ := hSpl
          obtain ⟨haInner, hEInner, hRecDirInner⟩ := hDir
          have hvMidInner_notW : vMidInner ∉ W :=
            h_inner_all vMidInner
              (List.mem_cons_of_mem _ (Walk.head_mem_vertices pInner))
          have h_innerInner : ∀ x ∈ pInner.vertices.tail, x ∉ W := fun x hx =>
            h_inner_all x (List.mem_cons_of_mem _ (List.mem_of_mem_tail hx))
          obtain ⟨s'', hs''_dir, _, hs''_vs⟩ :=
            lift_dir_walk_to_doit hW pInner hRecDirInner h_innerInner
          refine ⟨Walk.cons vMid a'
            (walkStep_toDoit (hW := hW) hStep hu'_notW hvMid_notW)
            (Walk.cons vMidInner aInner
              (walkStep_toDoit_dir (hW := hW) haInner hEInner hvMidInner_notW)
              s''), ?_, ?_⟩
          · simp only [Walk.IsBifurcationWithSplit]
            refine ⟨?_, haInner, ?_, hs''_dir⟩
            · rcases hOr with ⟨ha', hE'⟩ | ⟨ha', hL'⟩
              · refine Or.inl ⟨ha', ?_⟩
                change a' ∈ G.E.filter _
                refine Finset.mem_filter.mpr ⟨hE', ?_⟩
                rw [ha']; exact hu'_notW
              · refine Or.inr ⟨ha', ?_⟩
                change a' ∈ G.L.filter _
                refine Finset.mem_filter.mpr ⟨hL', ?_⟩
                rw [ha']; exact ⟨hu'_notW, hvMid_notW⟩
            · change aInner ∈ G.E.filter _
              refine Finset.mem_filter.mpr ⟨hEInner, ?_⟩
              rw [haInner]; exact hvMidInner_notW
          · simp only [Walk.vertices]
            rw [hs''_vs]
      | k+1, _, hSpl, ih =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
          obtain ⟨ha', hE', hRec⟩ := hSpl
          obtain ⟨s', hs'_split, hs'_vs⟩ := ih k h_inner_all hRec
          refine ⟨Walk.cons vMid a'
            (walkStep_toDoit (hW := hW) hStep hu'_notW hvMid_notW) s', ?_, ?_⟩
          · simp only [Walk.IsBifurcationWithSplit]
            refine ⟨ha', ?_, hs'_split⟩
            change a' ∈ G.E.filter _
            refine Finset.mem_filter.mpr ⟨hE', ?_⟩
            rw [ha']; exact hu'_notW
          · simp only [Walk.vertices]
            rw [hs'_vs]

private lemma doit_marg_PhiE_iff {G : CDMG Node} (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂)
    {u v : Node} (hv_notW₁ : v ∉ W₁) :
    (G.hardInterventionOn W₁ hW₁).MarginalizationΦE W₂ u v ↔
      G.MarginalizationΦE W₂ u v := by
  constructor
  · rintro ⟨p, hp_dir, hp_pos, hp_inter⟩
    refine ⟨walk_ofDoit hW₁ p,
      walk_ofDoit_isDirectedWalk hW₁ p hp_dir, ?_, ?_⟩
    · rw [walk_ofDoit_length hW₁ p]; exact hp_pos
    · rw [walk_ofDoit_vertices hW₁ p]; exact hp_inter
  · rintro ⟨q, hq_dir, hq_pos, hq_inter⟩
    have hNotW : ∀ x ∈ q.vertices.tail, x ∉ W₁ := by
      intro x hx
      have h_tail_ne : q.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos q hq_pos
      have h_x_drop_or_last : x ∈ q.vertices.tail.dropLast ∨ x = v := by
        rw [← List.dropLast_append_getLast h_tail_ne] at hx
        rcases List.mem_append.mp hx with h_drop | h_last
        · exact Or.inl h_drop
        · refine Or.inr ?_
          rw [List.mem_singleton] at h_last
          rw [h_last, Walk.tail_getLast_of_pos q hq_pos]
      rcases h_x_drop_or_last with h_drop | h_last
      · exact Finset.disjoint_right.mp hDisj (hq_inter x h_drop)
      · rw [h_last]; exact hv_notW₁
    obtain ⟨s, hs_dir, hs_len, hs_vs⟩ := lift_dir_walk_to_doit hW₁ q hq_dir hNotW
    refine ⟨s, hs_dir, ?_, ?_⟩
    · rw [hs_len]; exact hq_pos
    · rw [hs_vs]; exact hq_inter

private lemma doit_marg_PhiL_iff {G : CDMG Node} (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂)
    {u v : Node} (hu_notW₁ : u ∉ W₁) (hv_notW₁ : v ∉ W₁) :
    (G.hardInterventionOn W₁ hW₁).MarginalizationΦL W₂ u v ↔
      G.MarginalizationΦL W₂ u v := by
  constructor
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · refine Or.inl ⟨walk_ofDoit hW₁ p,
        walk_ofDoit_isBifurcation hW₁ p hp_bif, ?_⟩
      rw [walk_ofDoit_vertices hW₁ p]; exact hp_inter
    · refine Or.inr ⟨walk_ofDoit hW₁ p,
        walk_ofDoit_isBifurcation hW₁ p hp_bif, ?_⟩
      rw [walk_ofDoit_vertices hW₁ p]; exact hp_inter
  · -- The lift direction for the L iff requires lifting a bifurcation walk to
    -- the doit-CDMG, with the side condition "every vertex of the walk is outside W₁".
    -- Implemented via a helper that walks IsBifurcationWithSplit through the lift.
    rintro (⟨q, hq_bif, hq_inter⟩ | ⟨q, hq_bif, hq_inter⟩)
    · have hNotW : ∀ x ∈ q.vertices, x ∉ W₁ := by
        intro x hx
        rw [Walk.vertices_eq_head_cons_tail q] at hx
        rcases List.mem_cons.mp hx with h_eq_u | h_in_tail
        · rw [h_eq_u]; exact hu_notW₁
        · have h_pos : q.length ≥ 1 := Walk.length_pos_of_isBifurcation hq_bif
          have h_tail_ne : q.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos q h_pos
          have h_x_drop_or_last : x ∈ q.vertices.tail.dropLast ∨ x = v := by
            rw [← List.dropLast_append_getLast h_tail_ne] at h_in_tail
            rcases List.mem_append.mp h_in_tail with h_drop | h_last
            · exact Or.inl h_drop
            · refine Or.inr ?_
              rw [List.mem_singleton] at h_last
              rw [h_last, Walk.tail_getLast_of_pos q h_pos]
          rcases h_x_drop_or_last with h_drop | h_last
          · exact Finset.disjoint_right.mp hDisj (hq_inter x h_drop)
          · rw [h_last]; exact hv_notW₁
      obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hq_bif
      obtain ⟨s, hs_split, hs_vs⟩ :=
        lift_bifWithSplit_to_doit_aux hW₁ q i hNotW hi
      refine Or.inl ⟨s, ⟨hne, ?_, ?_, i, hs_split⟩, ?_⟩
      · rw [hs_vs]; exact hu_tail
      · rw [hs_vs]; exact hv_drop
      · rw [hs_vs]; exact hq_inter
    · have hNotW : ∀ x ∈ q.vertices, x ∉ W₁ := by
        intro x hx
        rw [Walk.vertices_eq_head_cons_tail q] at hx
        rcases List.mem_cons.mp hx with h_eq_v | h_in_tail
        · rw [h_eq_v]; exact hv_notW₁
        · have h_pos : q.length ≥ 1 := Walk.length_pos_of_isBifurcation hq_bif
          have h_tail_ne : q.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos q h_pos
          have h_x_drop_or_last : x ∈ q.vertices.tail.dropLast ∨ x = u := by
            rw [← List.dropLast_append_getLast h_tail_ne] at h_in_tail
            rcases List.mem_append.mp h_in_tail with h_drop | h_last
            · exact Or.inl h_drop
            · refine Or.inr ?_
              rw [List.mem_singleton] at h_last
              rw [h_last, Walk.tail_getLast_of_pos q h_pos]
          rcases h_x_drop_or_last with h_drop | h_last
          · exact Finset.disjoint_right.mp hDisj (hq_inter x h_drop)
          · rw [h_last]; exact hu_notW₁
      obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hq_bif
      obtain ⟨s, hs_split, hs_vs⟩ :=
        lift_bifWithSplit_to_doit_aux hW₁ q i hNotW hi
      refine Or.inr ⟨s, ⟨hne, ?_, ?_, i, hs_split⟩, ?_⟩
      · rw [hs_vs]; exact hu_tail
      · rw [hs_vs]; exact hv_drop
      · rw [hs_vs]; exact hq_inter

-- ## Field-equality lemmas for Part (i).

private lemma doit_marg_E_field_eq {G : CDMG Node} (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    ((G.hardInterventionOn W₁ hW₁).marginalize W₂
        (subset_sdiff_of_disjoint hW₂ hDisj.symm)).E
      = ((G.marginalize W₂ hW₂).hardInterventionOn W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)).E := by
  apply Finset.ext
  intro e
  -- LHS: filter over (G.J ∪ W₁ ∪ ((G.V \ W₁) \ W₂)) ×ˢ ((G.V \ W₁) \ W₂)
  --   with predicate Φ_E_doit W₂.
  -- RHS: filter over (G.J ∪ (G.V \ W₂)) ×ˢ (G.V \ W₂) with predicate Φ_E_G W₂,
  --   then filter `e.2 ∉ W₁`.
  change
    e ∈ (((G.J ∪ W₁) ∪ ((G.V \ W₁) \ W₂)) ×ˢ ((G.V \ W₁) \ W₂)).filter
          (fun e => (G.hardInterventionOn W₁ hW₁).MarginalizationΦE W₂ e.1 e.2)
    ↔ e ∈ (((G.J ∪ (G.V \ W₂)) ×ˢ (G.V \ W₂)).filter
              (fun e => G.MarginalizationΦE W₂ e.1 e.2)).filter
            (fun e => e.2 ∉ W₁)
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_product, Finset.mem_product]
  constructor
  · rintro ⟨⟨hu, hv⟩, hPhi⟩
    have hv_W₂_notW₁ : e.2 ∈ G.V ∧ e.2 ∉ W₁ ∧ e.2 ∉ W₂ := by
      have h1 := Finset.mem_sdiff.mp hv
      have h2 := Finset.mem_sdiff.mp h1.1
      exact ⟨h2.1, h2.2, h1.2⟩
    have hv_RHS : e.2 ∈ G.V \ W₂ :=
      Finset.mem_sdiff.mpr ⟨hv_W₂_notW₁.1, hv_W₂_notW₁.2.2⟩
    have hu_RHS : e.1 ∈ G.J ∪ (G.V \ W₂) := by
      rcases Finset.mem_union.mp hu with hJW₁ | hVW
      · rcases Finset.mem_union.mp hJW₁ with hJ | hW₁'
        · exact Finset.mem_union_left _ hJ
        · -- e.1 ∈ W₁ ⊆ G.J ∪ G.V; if in G.J done; if in G.V then ∉ W₂
          rcases Finset.mem_union.mp (hW₁ hW₁') with hJ | hV
          · exact Finset.mem_union_left _ hJ
          · refine Finset.mem_union_right _ ?_
            refine Finset.mem_sdiff.mpr ⟨hV, ?_⟩
            exact Finset.disjoint_left.mp hDisj hW₁'
      · have h1 := Finset.mem_sdiff.mp hVW
        have h2 := Finset.mem_sdiff.mp h1.1
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h2.1, h1.2⟩)
    refine ⟨⟨⟨hu_RHS, hv_RHS⟩,
        (doit_marg_PhiE_iff W₁ W₂ hW₁ hW₂ hDisj hv_W₂_notW₁.2.1).mp hPhi⟩,
      hv_W₂_notW₁.2.1⟩
  · rintro ⟨⟨⟨hu, hv⟩, hPhi⟩, hv_notW₁⟩
    have hv_LHS : e.2 ∈ (G.V \ W₁) \ W₂ := by
      have h1 := Finset.mem_sdiff.mp hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨h1.1, hv_notW₁⟩, h1.2⟩
    have hu_LHS : e.1 ∈ (G.J ∪ W₁) ∪ ((G.V \ W₁) \ W₂) := by
      rcases Finset.mem_union.mp hu with hJ | hVW
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
      · have h1 := Finset.mem_sdiff.mp hVW
        by_cases hW₁' : e.1 ∈ W₁
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hW₁')
        · refine Finset.mem_union_right _ ?_
          refine Finset.mem_sdiff.mpr ⟨?_, h1.2⟩
          exact Finset.mem_sdiff.mpr ⟨h1.1, hW₁'⟩
    refine ⟨⟨hu_LHS, hv_LHS⟩,
      (doit_marg_PhiE_iff W₁ W₂ hW₁ hW₂ hDisj hv_notW₁).mpr hPhi⟩

private lemma doit_marg_L_field_eq {G : CDMG Node} (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    ((G.hardInterventionOn W₁ hW₁).marginalize W₂
        (subset_sdiff_of_disjoint hW₂ hDisj.symm)).L
      = ((G.marginalize W₂ hW₂).hardInterventionOn W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)).L := by
  apply Finset.ext
  intro e
  change
    e ∈ (((G.V \ W₁) \ W₂) ×ˢ ((G.V \ W₁) \ W₂)).filter
          (fun e => e.1 ≠ e.2 ∧
            (G.hardInterventionOn W₁ hW₁).MarginalizationΦL W₂ e.1 e.2)
    ↔ e ∈ (((G.V \ W₂) ×ˢ (G.V \ W₂)).filter
              (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W₂ e.1 e.2)).filter
            (fun e => e.1 ∉ W₁ ∧ e.2 ∉ W₁)
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_product, Finset.mem_product]
  constructor
  · rintro ⟨⟨hu, hv⟩, hNe, hPhi⟩
    have hu_W₂_notW₁ : e.1 ∈ G.V ∧ e.1 ∉ W₁ ∧ e.1 ∉ W₂ := by
      have h1 := Finset.mem_sdiff.mp hu
      have h2 := Finset.mem_sdiff.mp h1.1
      exact ⟨h2.1, h2.2, h1.2⟩
    have hv_W₂_notW₁ : e.2 ∈ G.V ∧ e.2 ∉ W₁ ∧ e.2 ∉ W₂ := by
      have h1 := Finset.mem_sdiff.mp hv
      have h2 := Finset.mem_sdiff.mp h1.1
      exact ⟨h2.1, h2.2, h1.2⟩
    refine ⟨⟨⟨Finset.mem_sdiff.mpr ⟨hu_W₂_notW₁.1, hu_W₂_notW₁.2.2⟩,
        Finset.mem_sdiff.mpr ⟨hv_W₂_notW₁.1, hv_W₂_notW₁.2.2⟩⟩,
      hNe,
      (doit_marg_PhiL_iff W₁ W₂ hW₁ hW₂ hDisj hu_W₂_notW₁.2.1 hv_W₂_notW₁.2.1).mp hPhi⟩,
      hu_W₂_notW₁.2.1, hv_W₂_notW₁.2.1⟩
  · rintro ⟨⟨⟨hu, hv⟩, hNe, hPhi⟩, hu_notW₁, hv_notW₁⟩
    have hu_LHS : e.1 ∈ (G.V \ W₁) \ W₂ := by
      have h1 := Finset.mem_sdiff.mp hu
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨h1.1, hu_notW₁⟩, h1.2⟩
    have hv_LHS : e.2 ∈ (G.V \ W₁) \ W₂ := by
      have h1 := Finset.mem_sdiff.mp hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨h1.1, hv_notW₁⟩, h1.2⟩
    refine ⟨⟨hu_LHS, hv_LHS⟩, hNe,
      (doit_marg_PhiL_iff W₁ W₂ hW₁ hW₂ hDisj hu_notW₁ hv_notW₁).mpr hPhi⟩

-- ref: claim_3_18 (part i / 3 — hard intervention)
-- For any CDMG `G : CDMG Node`, subsets `W₁ ⊆ G.J ∪ G.V` and
-- `W₂ ⊆ G.V` with `Disjoint W₁ W₂`, marginalization and hard
-- intervention commute as a literal `=` of CDMGs over the original
-- `Node` carrier:
--   `(G_{doit(W₁)})^{∖W₂} = (G^{∖W₂})_{doit(W₁)}`.
/-
LN tex (rewritten canonical statement for `claim_3_18`, part (i)):

  For every `W₁ ⊆ J ∪ V` and `W₂ ⊆ V` with `W₁ ∩ W₂ = ∅`:
    `(G_{doit(W₁)})^{∖W₂} = (G^{∖W₂})_{doit(W₁)}`.

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CDMG and `W_1 ⊆ J ∪ V` and `W_2 ⊆ V`
  two disjoint subsets of nodes from `G`.  Then we have:
    `(G_{doit(W_1)})^{∖W_2} = (G^{∖W_2})_{doit(W_1)}`.
-/
-- ## Design choice
--
-- *Literal `=` of CDMGs over `Node`, NOT `eqViaNodeMap`.*  Both sides
--   live in `CDMG Node`: `hardInterventionOn` preserves the node
--   carrier (`CDMG α → CDMG α`), and `marginalize` likewise preserves
--   it.  So the LHS `(G.hardInterventionOn W₁ hW₁).marginalize W₂ _`
--   and the RHS `(G.marginalize W₂ hW₂).hardInterventionOn W₁ _` are
--   two CDMGs of identical Lean type, and the asserted equality is a
--   literal `=`.  Matches `claim_3_4` (HardInterventionsCommute) and
--   `claim_3_17` (MarginalizationsCommute) — the carrier-preservation
--   pattern of the original-`Node`-carrier operators.
--
-- *Inner-`marginalize` carrier transport via `subset_sdiff_of_disjoint`.*
--   The LHS's outer `.marginalize W₂` needs a subset proof against
--   the inner-intervened CDMG's `V`, not against `G.V`.  The helper
--   `subset_sdiff_of_disjoint hW₂ hDisj.symm` transports the
--   hypothesis from `W₂ ⊆ G.V` to `W₂ ⊆ G.V \ W₁ =
--   (G.hardInterventionOn W₁ hW₁).V`, consuming `Disjoint W₂ W₁`
--   (the symmetric of the LN's `Disjoint W₁ W₂`).
--
-- *Outer-`hardInterventionOn` carrier transport via
--   `subset_carrier_of_marginalize`.*  The RHS's outer
--   `.hardInterventionOn W₁` needs a subset proof against the
--   marginalized CDMG's `J ∪ V = G.J ∪ (G.V \ W₂)`.  The helper
--   `subset_carrier_of_marginalize hW₂ hW₁ hDisj` discharges this from
--   `hW₁ : W₁ ⊆ G.J ∪ G.V` and `Disjoint W₁ W₂`.
--
-- *Disjointness binder `Disjoint W₁ W₂` (LN-symmetric phrasing).*
--   Matches the LN block's "two disjoint subsets of nodes from `G`"
--   and the sibling rows' (claim_3_17, claim_3_4, claim_3_8)
--   convention.  At the lift-helper call sites the orientation is
--   composed with `.symm` as needed.
--
-- *CDMG equality (`=`) is read field-wise.*  Equality of two `CDMG`s
--   unfolds via the `structure` injectivity from `def_3_1` to the
--   conjunction of equalities on the four data fields `J`, `V`, `E`,
--   `L` (the five propositional fields are determined by the data
--   and discharged by proof irrelevance).  We do not bake the
--   field-wise unpacking into the statement; it is deferred to the
--   proof per the rewritten tex's closing remark.
-- claim_3_18 -- start statement
theorem marginalize_hardInterventionOn_comm (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (G.hardInterventionOn W₁ hW₁).marginalize W₂
        (subset_sdiff_of_disjoint hW₂ hDisj.symm)
      = (G.marginalize W₂ hW₂).hardInterventionOn W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)
-- claim_3_18 -- end statement
:= by
  have cdmgExt : ∀ {G₁ G₂ : CDMG Node},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨_, _, _, _, _, _, _, _, _⟩
           ⟨_, _, _, _, _, _, _, _, _⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL; rfl
  refine cdmgExt ?_ ?_ ?_ ?_
  · -- J: both sides = G.J ∪ W₁
    rfl
  · -- V: (G.V \ W₁) \ W₂ = (G.V \ W₂) \ W₁
    change (G.V \ W₁) \ W₂ = (G.V \ W₂) \ W₁
    ext x
    simp only [Finset.mem_sdiff]
    tauto
  · -- E: filter equality via Φ_E iff
    exact doit_marg_E_field_eq W₁ W₂ hW₁ hW₂ hDisj
  · -- L: filter equality via Φ_L iff
    exact doit_marg_L_field_eq W₁ W₂ hW₁ hW₂ hDisj

-- ref: claim_3_18 (part ii / 3 — adding intervention nodes)
-- For any CDMG `G : CDMG Node`, subsets `W₁ ⊆ G.J ∪ G.V` and
-- `W₂ ⊆ G.V` with `Disjoint W₁ W₂`, marginalization and the
-- intervention-node extension commute as a literal `=` of CDMGs over
-- the extended carrier `IntExtNode Node`:
--   `(G_{doit(I_{W₁})})^{∖W₂} = (G^{∖W₂})_{doit(I_{W₁})}`.
/-
LN tex (rewritten canonical statement for `claim_3_18`, part (ii)):

  For every `W₁ ⊆ J ∪ V` and `W₂ ⊆ V` with `W₁ ∩ W₂ = ∅`:
    `(G_{doit(I_{W₁})})^{∖W₂} = (G^{∖W₂})_{doit(I_{W₁})}`.

LN block (verbatim, for backup): the LN's lemma block (graphs.tex,
`\label{marginalization-and-intervention-commute}`) closes with
"A similar statement holds for marginalizations and adding
intervention nodes, ..."; per the row's `addition_to_the_LN` clause
`[trailing_similar_statement_two_unstated_claims]`, that trailer is
authoritative and asserts this part (ii).
-/
-- ## Design choice
--
-- *Literal `=` of CDMGs over `IntExtNode Node`, NOT `eqViaNodeMap`.*
--   Carrier analysis: the LHS's outermost operator is `marginalize`
--   applied to `G.extendingCDMGsWith W₁ hW₁ : CDMG (IntExtNode Node)`,
--   which preserves the carrier — so LHS : `CDMG (IntExtNode Node)`.
--   The RHS's outermost operator is `extendingCDMGsWith` applied to
--   `G.marginalize W₂ hW₂ : CDMG Node`, which carries to `CDMG
--   (IntExtNode Node)` — so RHS : `CDMG (IntExtNode Node)` also.  Both
--   sides have identical Lean type, so the asserted equality is a
--   literal `=` (no `flattenIntExt` workaround needed, unlike
--   `claim_3_14`'s iterated extension).
--
-- *Inner-`marginalize` lifted set `W₂.image IntExtNode.unsplit`.*  The
--   inner CDMG `G.extendingCDMGsWith W₁ hW₁` lives over `IntExtNode
--   Node`, so the LHS marginalization's `W` argument must inhabit
--   `Finset (IntExtNode Node)`.  The natural lift of `W₂ : Finset
--   Node` is `W₂.image IntExtNode.unsplit`, which targets the
--   `G.V.image IntExtNode.unsplit = (G.extendingCDMGsWith W₁ hW₁).V`
--   slice.  The subset proof is discharged by
--   `image_unsplit_subset_extendingCDMGsWith_V hW₁ hW₂` (no
--   disjointness needed for this lift).
--
-- *Outer-`extendingCDMGsWith` carrier transport via
--   `subset_carrier_of_marginalize`.*  Same helper as Part (i)'s RHS:
--   `extendingCDMGsWith` requires its `W₁` argument to sit in
--   `(G.marginalize W₂ hW₂).J ∪ (G.marginalize W₂ hW₂).V = G.J ∪
--   (G.V \ W₂)`, discharged by `subset_carrier_of_marginalize hW₂ hW₁
--   hDisj`.
--
-- *Why the LHS marginalizes by `W₂.image .unsplit` and the RHS
--   extends by the *original* `W₁`.*  This mirrors the LN's "$I_{W_1}$"
--   semantics: the intervention symbol set lives over the *original*
--   nodes `W₁`, so `extendingCDMGsWith W₁ _` is applied with the bare
--   `W₁ : Finset Node` on the RHS.  The LHS's inner extension already
--   produced the `IntExtNode`-carrier CDMG; from there the only thing
--   that can be marginalized are `IntExtNode`-flavoured nodes — and
--   the natural lift of "marginalize the original `W₂`" is the
--   `.unsplit`-image.  No new "intervention copy" element of
--   `W₂` is ever marginalized, only the original-side copies.
--   `verify_equivalence_strict` is the natural place to gate this
--   carrier-matching choice during Phase A.
-- ## Walk surgery for `extendingCDMGsWith` (proof-only helpers for Part ii).
--
-- Extension adds nodes and edges (no edge removal): every walk in `G` lifts to
-- a walk in `G.extendingCDMGsWith W hW` via the `.unsplit` constructor.  The
-- reverse cast — descending a walk in the extension back to a walk in `G` —
-- needs a per-vertex side condition that no vertex is `.intCopy`-tagged,
-- equivalently no edge is the fresh transfer edge `(.intCopy w, .unsplit w)`.

private lemma mem_ext_of_mem_G_unsplit {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) {v : Node} (hv : v ∈ G) :
    IntExtNode.unsplit v ∈ G.extendingCDMGsWith W hW := by
  change _ ∈ ((G.J.image IntExtNode.unsplit ∪
      (W \ G.J).image IntExtNode.intCopy) ∪ G.V.image IntExtNode.unsplit)
  change v ∈ G.J ∪ G.V at hv
  rcases Finset.mem_union.mp hv with hJ | hV
  · refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · refine Finset.mem_union_right _ ?_
    exact Finset.mem_image.mpr ⟨v, hV, rfl⟩

private lemma walkStep_toExt {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {u v : Node} {a : Node × Node}
    (h : G.WalkStep u a v) :
    (G.extendingCDMGsWith W hW).WalkStep
      (IntExtNode.unsplit u) (IntExtNode.unsplit a.1, IntExtNode.unsplit a.2)
      (IntExtNode.unsplit v) := by
  rcases h with ⟨ha, hOr⟩ | ⟨ha, hE⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rw [ha]
    · rcases hOr with hE | hL
      · refine Or.inl ?_
        change _ ∈ G.E.image _ ∪ _
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨a, hE, rfl⟩
      · refine Or.inr ?_
        change _ ∈ G.L.image _
        exact Finset.mem_image.mpr ⟨a, hL, rfl⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rw [ha]
    · change _ ∈ G.E.image _ ∪ _
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr ⟨a, hE, rfl⟩

/-- Lift a walk in `G` to a walk in `G.extendingCDMGsWith W hW` via `.unsplit`. -/
private def walk_toExt {G : CDMG Node} {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node}, Walk G u v →
      Walk (G.extendingCDMGsWith W hW)
        (IntExtNode.unsplit u) (IntExtNode.unsplit v)
  | _, _, .nil v hv =>
      Walk.nil (IntExtNode.unsplit v) (mem_ext_of_mem_G_unsplit hW hv)
  | _, _, .cons v a hStep p =>
      Walk.cons (IntExtNode.unsplit v)
        (IntExtNode.unsplit a.1, IntExtNode.unsplit a.2)
        (walkStep_toExt (hW := hW) hStep) (walk_toExt hW p)

private lemma walk_toExt_length {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk G u v), (walk_toExt hW p).length = p.length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ p => by
      change (walk_toExt hW p).length + 1 = p.length + 1
      rw [walk_toExt_length hW p]

private lemma walk_toExt_vertices {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk G u v),
      (walk_toExt hW p).vertices = p.vertices.map IntExtNode.unsplit
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ p => by
      change _ :: (walk_toExt hW p).vertices = _ :: _
      rw [walk_toExt_vertices hW p]

private lemma walk_toExt_isDirectedWalk {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → (walk_toExt hW p).IsDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons _ _ _ p, hDir => by
      obtain ⟨ha, hE, hRec⟩ := hDir
      refine ⟨?_, ?_, walk_toExt_isDirectedWalk hW p hRec⟩
      · rw [ha]
      · change _ ∈ G.E.image _ ∪ _
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨_, hE, rfl⟩

private lemma walk_toExt_isBifurcationWithSplit {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk G u v) (i : ℕ),
      p.IsBifurcationWithSplit i →
        (walk_toExt hW p).IsBifurcationWithSplit i
  | _, _, .nil _ _, _, h => h.elim
  | _, _, .cons _ _ _ (.nil _ _), 0, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
      obtain ⟨ha, hL⟩ := hSpl
      simp only [walk_toExt, Walk.IsBifurcationWithSplit]
      refine ⟨?_, ?_⟩
      · rw [ha]
      · change _ ∈ G.L.image _
        exact Finset.mem_image.mpr ⟨_, hL, rfl⟩
  | _, _, .cons _ _ _ (.cons _ _ _ _), 0, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
      obtain ⟨hOr, hDir⟩ := hSpl
      simp only [walk_toExt, Walk.IsBifurcationWithSplit]
      refine ⟨?_, walk_toExt_isDirectedWalk hW _ hDir⟩
      rcases hOr with ⟨ha, hE⟩ | ⟨ha, hL⟩
      · refine Or.inl ⟨?_, ?_⟩
        · rw [ha]
        · change _ ∈ G.E.image _ ∪ _
          refine Finset.mem_union_left _ ?_
          exact Finset.mem_image.mpr ⟨_, hE, rfl⟩
      · refine Or.inr ⟨?_, ?_⟩
        · rw [ha]
        · change _ ∈ G.L.image _
          exact Finset.mem_image.mpr ⟨_, hL, rfl⟩
  | _, _, .cons _ _ _ p, k+1, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
      obtain ⟨ha, hE, hRec⟩ := hSpl
      simp only [walk_toExt, Walk.IsBifurcationWithSplit]
      refine ⟨?_, ?_, walk_toExt_isBifurcationWithSplit hW p k hRec⟩
      · rw [ha]
      · change _ ∈ G.E.image _ ∪ _
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨_, hE, rfl⟩

private lemma walk_toExt_isBifurcation {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) {u v : Node}
    (p : Walk G u v) (hp : p.IsBifurcation) :
    (walk_toExt hW p).IsBifurcation := by
  obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hp
  refine ⟨?_, ?_, ?_, i, walk_toExt_isBifurcationWithSplit hW p i hi⟩
  · intro heq
    apply hne
    have : IntExtNode.unsplit u = IntExtNode.unsplit v := heq
    injection this
  · rw [walk_toExt_vertices hW p]
    intro h
    rw [show (p.vertices.map IntExtNode.unsplit).tail
            = p.vertices.tail.map IntExtNode.unsplit from
        by cases p.vertices with
        | nil => rfl
        | cons _ _ => rfl] at h
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h
    have : a = u := by injection ha_eq
    exact hu_tail (this ▸ ha_in)
  · rw [walk_toExt_vertices hW p]
    intro h
    have hMap : ∀ (l : List Node),
        (l.map IntExtNode.unsplit).dropLast = l.dropLast.map IntExtNode.unsplit := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
          cases xs with
          | nil => rfl
          | cons y ys =>
              simp only [List.map_cons, List.dropLast_cons₂]
              change _ :: ((y :: ys).map _).dropLast
                = _ :: ((y :: ys).dropLast).map IntExtNode.unsplit
              rw [ih]
    rw [hMap p.vertices] at h
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h
    have : a = v := by injection ha_eq
    exact hv_drop (this ▸ ha_in)

-- ## Walk descent: extension to G, when source is `.unsplit` and walk avoids fresh edges.
--
-- Given `p : Walk extension x y` with `x = .unsplit u`, every step's source is
-- the previous walk vertex.  If the walk's source is `.unsplit`-tagged AND
-- every intermediate is `.unsplit`-tagged (e.g., all interior vertices lie in
-- `W₂.image .unsplit`), then no fresh edge `(.intCopy w, .unsplit w)` can
-- appear (its source `.intCopy w` would have to equal a `.unsplit`-tagged
-- vertex, contradicting constructor disjointness).
-- We package this as a recursive lemma that, given proofs that all of `p`'s
-- vertices are `.unsplit`-tagged, descends `p` to a walk in `G`.

private lemma walkStep_ofExt_unsplit {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {u v : Node} {a : IntExtNode Node × IntExtNode Node}
    (h : (G.extendingCDMGsWith W hW).WalkStep
      (IntExtNode.unsplit u) a (IntExtNode.unsplit v)) :
    ∃ a' : Node × Node, G.WalkStep u a' v ∧
      a = (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2) := by
  rcases h with ⟨ha, hOr⟩ | ⟨ha, hE⟩
  · -- a = (.unsplit u, .unsplit v) ∧ (a ∈ ext.E ∨ a ∈ ext.L)
    rcases hOr with hE_ext | hL_ext
    · -- a ∈ G.E.image .unsplit_pair ∪ fresh image
      change a ∈ G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
              ∪ (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w))
              at hE_ext
      rcases Finset.mem_union.mp hE_ext with hImg | hFresh
      · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hImg
        -- ha'_eq : (.unsplit a'.1, .unsplit a'.2) = a
        refine ⟨a', Or.inl ⟨?_, Or.inl ha'_in⟩, ha'_eq.symm⟩
        -- Need a' = (u, v).  From ha : a = (.unsplit u, .unsplit v) and ha'_eq.
        have ha_eq : a = (IntExtNode.unsplit u, IntExtNode.unsplit v) := ha
        rw [ha_eq] at ha'_eq
        have h1 : IntExtNode.unsplit a'.1 = IntExtNode.unsplit u := by
          exact congrArg Prod.fst ha'_eq
        have h2 : IntExtNode.unsplit a'.2 = IntExtNode.unsplit v := by
          exact congrArg Prod.snd ha'_eq
        have ha1 : a'.1 = u := by injection h1
        have ha2 : a'.2 = v := by injection h2
        ext <;> [exact ha1; exact ha2]
      · -- a is a fresh edge, but a = (.unsplit u, .unsplit v) — contradiction
        obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hFresh
        -- hw_eq : (.intCopy w, .unsplit w) = a = (.unsplit u, .unsplit v)
        have : a = (IntExtNode.unsplit u, IntExtNode.unsplit v) := ha
        rw [this] at hw_eq
        have : IntExtNode.intCopy w = IntExtNode.unsplit u := by
          exact congrArg Prod.fst hw_eq
        cases this
    · -- a ∈ G.L.image .unsplit_pair
      change a ∈ G.L.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
        at hL_ext
      obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hL_ext
      refine ⟨a', Or.inl ⟨?_, Or.inr ha'_in⟩, ha'_eq.symm⟩
      have ha_eq : a = (IntExtNode.unsplit u, IntExtNode.unsplit v) := ha
      rw [ha_eq] at ha'_eq
      have h1 : IntExtNode.unsplit a'.1 = IntExtNode.unsplit u :=
        congrArg Prod.fst ha'_eq
      have h2 : IntExtNode.unsplit a'.2 = IntExtNode.unsplit v :=
        congrArg Prod.snd ha'_eq
      have ha1 : a'.1 = u := by injection h1
      have ha2 : a'.2 = v := by injection h2
      ext <;> [exact ha1; exact ha2]
  · -- a = (.unsplit v, .unsplit u) ∧ a ∈ ext.E
    change a ∈ G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
            ∪ (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w))
            at hE
    rcases Finset.mem_union.mp hE with hImg | hFresh
    · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hImg
      refine ⟨a', Or.inr ⟨?_, ha'_in⟩, ha'_eq.symm⟩
      have ha_eq : a = (IntExtNode.unsplit v, IntExtNode.unsplit u) := ha
      rw [ha_eq] at ha'_eq
      have h1 : IntExtNode.unsplit a'.1 = IntExtNode.unsplit v :=
        congrArg Prod.fst ha'_eq
      have h2 : IntExtNode.unsplit a'.2 = IntExtNode.unsplit u :=
        congrArg Prod.snd ha'_eq
      have ha1 : a'.1 = v := by injection h1
      have ha2 : a'.2 = u := by injection h2
      ext <;> [exact ha1; exact ha2]
    · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hFresh
      have : a = (IntExtNode.unsplit v, IntExtNode.unsplit u) := ha
      rw [this] at hw_eq
      have : IntExtNode.intCopy w = IntExtNode.unsplit v :=
        congrArg Prod.fst hw_eq
      cases this

-- ## Image-sdiff identity for injective `.unsplit`.
private lemma image_unsplit_sdiff {S T : Finset Node} :
    S.image IntExtNode.unsplit \ T.image IntExtNode.unsplit
      = (S \ T).image IntExtNode.unsplit := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, hAS, rfl⟩, h_notT⟩
    refine ⟨a, ⟨hAS, ?_⟩, rfl⟩
    intro hAT
    exact h_notT ⟨a, hAT, rfl⟩
  · rintro ⟨a, ⟨hAS, hANotT⟩, rfl⟩
    refine ⟨⟨a, hAS, rfl⟩, ?_⟩
    rintro ⟨b, hBT, hEq⟩
    apply hANotT
    have : b = a := by injection hEq
    exact this ▸ hBT

-- ## `.unsplit v ∈ ext` ⟹ `v ∈ G` (carrier descent through `.unsplit`).
private lemma mem_G_of_unsplit_mem_ext {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) {v : Node}
    (hv : IntExtNode.unsplit v ∈ G.extendingCDMGsWith W hW) : v ∈ G := by
  change v ∈ G.J ∪ G.V
  change IntExtNode.unsplit v ∈
    ((G.J.image IntExtNode.unsplit ∪ (W \ G.J).image IntExtNode.intCopy)
     ∪ G.V.image IntExtNode.unsplit) at hv
  rcases Finset.mem_union.mp hv with hJI | hV
  · rcases Finset.mem_union.mp hJI with hJ | hI
    · obtain ⟨j, hjJ, hjEq⟩ := Finset.mem_image.mp hJ
      have hju : j = v := by injection hjEq
      subst hju
      exact Finset.mem_union_left _ hjJ
    · obtain ⟨_, _, hwEq⟩ := Finset.mem_image.mp hI
      cases hwEq
  · obtain ⟨v', hvV, hvEq⟩ := Finset.mem_image.mp hV
    have hvu : v' = v := by injection hvEq
    subst hvu
    exact Finset.mem_union_right _ hvV

-- ## List utility: `(l.map .unsplit).tail = l.tail.map .unsplit`.
private lemma list_unsplit_tail (l : List Node) :
    (l.map IntExtNode.unsplit).tail = l.tail.map IntExtNode.unsplit := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

-- ## List utility: `(l.map .unsplit).dropLast = l.dropLast.map .unsplit`.
private lemma list_unsplit_dropLast :
    ∀ (l : List Node),
      (l.map IntExtNode.unsplit).dropLast = l.dropLast.map IntExtNode.unsplit
  | [] => rfl
  | _ :: [] => rfl
  | x :: y :: rest => by
      change IntExtNode.unsplit x :: (((y :: rest).map IntExtNode.unsplit).dropLast)
          = IntExtNode.unsplit x :: ((y :: rest).dropLast.map IntExtNode.unsplit)
      rw [list_unsplit_dropLast (y :: rest)]

-- ## List utility: `(l.map .unsplit).tail.dropLast = l.tail.dropLast.map .unsplit`.
private lemma list_unsplit_tail_dropLast (l : List Node) :
    (l.map IntExtNode.unsplit).tail.dropLast
      = l.tail.dropLast.map IntExtNode.unsplit := by
  rw [list_unsplit_tail, list_unsplit_dropLast]

-- ## Two helpers: a `.unsplit_pair`-lifted edge in `ext.E` / `ext.L` lifts back
-- to a `G.E` / `G.L` edge.  Fresh edges cannot contribute (their source is
-- `.intCopy`, not `.unsplit`).
private lemma a_in_G_E_of_lifted_in_ext {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {a' : Node × Node}
    {a : IntExtNode Node × IntExtNode Node}
    (ha_eq : a = (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2))
    (ha_E : a ∈ (G.extendingCDMGsWith W hW).E) : a' ∈ G.E := by
  change a ∈ G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
          ∪ (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w))
          at ha_E
  rcases Finset.mem_union.mp ha_E with hLift | hFresh
  · obtain ⟨e', he'E, he'_eq⟩ := Finset.mem_image.mp hLift
    rw [ha_eq] at he'_eq
    have h1 : IntExtNode.unsplit e'.1 = IntExtNode.unsplit a'.1 :=
      congrArg Prod.fst he'_eq
    have h2 : IntExtNode.unsplit e'.2 = IntExtNode.unsplit a'.2 :=
      congrArg Prod.snd he'_eq
    have he1 : e'.1 = a'.1 := by injection h1
    have he2 : e'.2 = a'.2 := by injection h2
    have heq : e' = a' := Prod.ext he1 he2
    rw [← heq]; exact he'E
  · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hFresh
    rw [ha_eq] at hw_eq
    have hcontra : IntExtNode.intCopy w = IntExtNode.unsplit a'.1 :=
      congrArg Prod.fst hw_eq
    cases hcontra

private lemma a_in_G_L_of_lifted_in_ext {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {a' : Node × Node}
    {a : IntExtNode Node × IntExtNode Node}
    (ha_eq : a = (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2))
    (ha_L : a ∈ (G.extendingCDMGsWith W hW).L) : a' ∈ G.L := by
  change a ∈ G.L.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
    at ha_L
  obtain ⟨e', he'L, he'_eq⟩ := Finset.mem_image.mp ha_L
  rw [ha_eq] at he'_eq
  have h1 : IntExtNode.unsplit e'.1 = IntExtNode.unsplit a'.1 :=
    congrArg Prod.fst he'_eq
  have h2 : IntExtNode.unsplit e'.2 = IntExtNode.unsplit a'.2 :=
    congrArg Prod.snd he'_eq
  have he1 : e'.1 = a'.1 := by injection h1
  have he2 : e'.2 = a'.2 := by injection h2
  have heq : e' = a' := Prod.ext he1 he2
  rw [← heq]; exact he'L

-- ## Helper: equality of pairs through `.unsplit`.
private lemma pair_eq_of_unsplit_eq {a : Node × Node} {u v : Node}
    (h : (IntExtNode.unsplit a.1, IntExtNode.unsplit a.2)
        = (IntExtNode.unsplit u, IntExtNode.unsplit v)) :
    a = (u, v) := by
  have h1 : IntExtNode.unsplit a.1 = IntExtNode.unsplit u := congrArg Prod.fst h
  have h2 : IntExtNode.unsplit a.2 = IntExtNode.unsplit v := congrArg Prod.snd h
  have ha1 : a.1 = u := by injection h1
  have ha2 : a.2 = v := by injection h2
  exact Prod.ext ha1 ha2

-- ## Walk descent: ext → G, when source/target are `.unsplit` and all
-- vertices are `.unsplit`-tagged.  Returns the descended walk `q` plus
-- length / vertex-list / edge-list / `IsDirectedWalk` / `IsBifurcationWithSplit`
-- preservation, in a single unified existence statement.
private lemma walk_ofExt_unsplit_full {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {x y : IntExtNode Node} (p : Walk (G.extendingCDMGsWith W hW) x y),
      (∀ z ∈ p.vertices, ∃ z' : Node, z = IntExtNode.unsplit z') →
      ∀ (u v : Node), x = IntExtNode.unsplit u → y = IntExtNode.unsplit v →
      ∃ q : Walk G u v, q.length = p.length ∧
        q.vertices.map IntExtNode.unsplit = p.vertices ∧
        q.edges.map (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
          = p.edges ∧
        (p.IsDirectedWalk → q.IsDirectedWalk) ∧
        (∀ i, p.IsBifurcationWithSplit i → q.IsBifurcationWithSplit i) := by
  intro x y p
  induction p with
  | nil w hw =>
      intro _ u v hxu hyv
      have hu_eq_v : IntExtNode.unsplit u = (IntExtNode.unsplit v : IntExtNode Node) := by
        rw [← hxu, hyv]
      have huv : u = v := by injection hu_eq_v
      subst huv
      subst hxu
      have hu_in_G : u ∈ G := mem_G_of_unsplit_mem_ext hW hw
      refine ⟨Walk.nil u hu_in_G, rfl, rfl, rfl, fun _ => trivial, ?_⟩
      intro i h
      exact h.elim
  | @cons x' y' mid a hStep p' ih =>
      intro h_all u v hxu hyv
      subst hxu
      have hmid_in : mid ∈ (Walk.cons (G := G.extendingCDMGsWith W hW) mid a hStep p').vertices := by
        show mid ∈ (IntExtNode.unsplit u :: p'.vertices)
        exact List.mem_cons_of_mem _ (Walk.head_mem_vertices p')
      obtain ⟨m', hmid_eq⟩ := h_all mid hmid_in
      subst hmid_eq
      have h_all_p' : ∀ z ∈ p'.vertices, ∃ z' : Node, z = IntExtNode.unsplit z' := by
        intro z hz
        exact h_all z (List.mem_cons_of_mem _ hz)
      obtain ⟨a', hStepG, ha_eq⟩ := walkStep_ofExt_unsplit (hW := hW) hStep
      obtain ⟨q', hq'_len, hq'_vs, hq'_es, hq'_dir, hq'_bif⟩ :=
        ih h_all_p' m' v rfl hyv
      refine ⟨Walk.cons m' a' hStepG q', ?_, ?_, ?_, ?_, ?_⟩
      · -- length
        change q'.length + 1 = p'.length + 1
        rw [hq'_len]
      · -- vertices.map
        show IntExtNode.unsplit u :: (q'.vertices.map IntExtNode.unsplit)
              = IntExtNode.unsplit u :: p'.vertices
        rw [hq'_vs]
      · -- edges.map
        show (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2)
              :: (q'.edges.map (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)))
            = a :: p'.edges
        rw [hq'_es]; rw [← ha_eq]
      · -- IsDirectedWalk preservation
        intro hp_dir
        simp only [Walk.IsDirectedWalk] at hp_dir
        obtain ⟨ha_p, ha_E, hp'_dir⟩ := hp_dir
        refine ⟨?_, ?_, hq'_dir hp'_dir⟩
        · -- a' = (u, m')
          have hpair : (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2)
                  = (IntExtNode.unsplit u, IntExtNode.unsplit m') := by
            rw [← ha_eq]; exact ha_p
          exact pair_eq_of_unsplit_eq hpair
        · -- a' ∈ G.E: descend a ∈ ext.E via ha_eq.
          exact a_in_G_E_of_lifted_in_ext (hW := hW) ha_eq ha_E
      · -- IsBifurcationWithSplit preservation
        intro i hPi
        match i, p', hPi, q', hq'_len, hq'_dir, hq'_bif with
        | 0, .nil _ _, hPi, .nil _ _, _, _, _ =>
            simp only [Walk.IsBifurcationWithSplit] at hPi
            obtain ⟨ha_uv, ha_L⟩ := hPi
            simp only [Walk.IsBifurcationWithSplit]
            refine ⟨?_, ?_⟩
            · have hpair : (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2)
                          = (IntExtNode.unsplit u, IntExtNode.unsplit m') := by
                rw [← ha_eq]; exact ha_uv
              exact pair_eq_of_unsplit_eq hpair
            · exact a_in_G_L_of_lifted_in_ext (hW := hW) ha_eq ha_L
        | 0, .nil _ _, _, .cons _ _ _ _, hlen, _, _ =>
            simp [Walk.length] at hlen
        | 0, .cons _ _ _ _, _, .nil _ _, hlen, _, _ =>
            simp [Walk.length] at hlen
        | 0, .cons _ _ _ _, hPi, .cons _ _ _ _, _, hq'_dir, _ =>
            simp only [Walk.IsBifurcationWithSplit] at hPi
            obtain ⟨ha_or, hp'_dir⟩ := hPi
            simp only [Walk.IsBifurcationWithSplit]
            refine ⟨?_, hq'_dir hp'_dir⟩
            rcases ha_or with ⟨ha_vu, ha_E⟩ | ⟨ha_uv, ha_L⟩
            · refine Or.inl ⟨?_, ?_⟩
              · have hpair : (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2)
                            = (IntExtNode.unsplit m', IntExtNode.unsplit u) := by
                  rw [← ha_eq]; exact ha_vu
                exact pair_eq_of_unsplit_eq hpair
              · exact a_in_G_E_of_lifted_in_ext (hW := hW) ha_eq ha_E
            · refine Or.inr ⟨?_, ?_⟩
              · have hpair : (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2)
                            = (IntExtNode.unsplit u, IntExtNode.unsplit m') := by
                  rw [← ha_eq]; exact ha_uv
                exact pair_eq_of_unsplit_eq hpair
              · exact a_in_G_L_of_lifted_in_ext (hW := hW) ha_eq ha_L
        | k + 1, _, hPi, _, _, _, hq'_bif =>
            simp only [Walk.IsBifurcationWithSplit] at hPi
            obtain ⟨ha_vu, ha_E, hPi_rest⟩ := hPi
            simp only [Walk.IsBifurcationWithSplit]
            refine ⟨?_, ?_, hq'_bif k hPi_rest⟩
            · have hpair : (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2)
                          = (IntExtNode.unsplit m', IntExtNode.unsplit u) := by
                rw [← ha_eq]; exact ha_vu
              exact pair_eq_of_unsplit_eq hpair
            · exact a_in_G_E_of_lifted_in_ext (hW := hW) ha_eq ha_E

-- ## Helper: walk in ext from .unsplit u to .unsplit v with interior in
-- W₂.image .unsplit ⟹ all vertices are .unsplit-tagged.
private lemma all_unsplit_of_interior_W_image
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {x y : IntExtNode Node}
    (p : Walk (G.extendingCDMGsWith W hW) x y)
    (hp_pos : p.length ≥ 1)
    {u v : Node} (hxu : x = IntExtNode.unsplit u) (hyv : y = IntExtNode.unsplit v)
    {W₂ : Finset Node}
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast, z ∈ W₂.image IntExtNode.unsplit) :
    ∀ z ∈ p.vertices, ∃ z' : Node, z = IntExtNode.unsplit z' := by
  intro z hz
  rw [Walk.vertices_eq_head_cons_tail p] at hz
  rcases List.mem_cons.mp hz with h_eq | h_in_tail
  · exact ⟨u, h_eq.trans hxu⟩
  · have h_tail_ne : p.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos p hp_pos
    have h_drop_or_last : z ∈ p.vertices.tail.dropLast ∨ z = y := by
      rw [← List.dropLast_append_getLast h_tail_ne] at h_in_tail
      rcases List.mem_append.mp h_in_tail with h_drop | h_last
      · exact Or.inl h_drop
      · refine Or.inr ?_
        rw [List.mem_singleton] at h_last
        rw [h_last, Walk.tail_getLast_of_pos p hp_pos]
    rcases h_drop_or_last with h_drop | h_last
    · have h_in_image := hp_inter z h_drop
      obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp h_in_image
      exact ⟨w, hw_eq.symm⟩
    · exact ⟨v, h_last.trans hyv⟩

-- ## Φ_E iff for Part (ii), .unsplit-source case.
private lemma ext_marg_PhiE_iff_unsplit {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.J ∪ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂)
    {u v : Node} :
    (G.extendingCDMGsWith W₁ hW₁).MarginalizationΦE (W₂.image IntExtNode.unsplit)
        (IntExtNode.unsplit u) (IntExtNode.unsplit v) ↔
      G.MarginalizationΦE W₂ u v := by
  constructor
  · rintro ⟨p, hp_dir, hp_pos, hp_inter⟩
    have h_all := all_unsplit_of_interior_W_image (W := W₁) (hW := hW₁)
      p hp_pos (u := u) (v := v) rfl rfl (W₂ := W₂) hp_inter
    obtain ⟨q, hq_len, hq_vs, _, hq_dir, _⟩ :=
      walk_ofExt_unsplit_full hW₁ p h_all u v rfl rfl
    refine ⟨q, hq_dir hp_dir, ?_, ?_⟩
    · rw [hq_len]; exact hp_pos
    · intro x hx
      have hxL : IntExtNode.unsplit x ∈ p.vertices.tail.dropLast := by
        rw [← hq_vs, list_unsplit_tail_dropLast]
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      have h_in_image := hp_inter (IntExtNode.unsplit x) hxL
      obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp h_in_image
      have hwx : w = x := by injection hw_eq
      exact hwx ▸ hwW₂
  · rintro ⟨q, hq_dir, hq_pos, hq_inter⟩
    refine ⟨walk_toExt hW₁ q, walk_toExt_isDirectedWalk hW₁ q hq_dir, ?_, ?_⟩
    · rw [walk_toExt_length hW₁ q]; exact hq_pos
    · intro x hx
      rw [walk_toExt_vertices hW₁ q, list_unsplit_tail_dropLast] at hx
      obtain ⟨a, haIn, haEq⟩ := List.mem_map.mp hx
      rw [← haEq]
      exact Finset.mem_image.mpr ⟨a, hq_inter a haIn, rfl⟩

-- ## Φ_L iff for Part (ii), .unsplit-endpoints case.
private lemma ext_marg_PhiL_iff_unsplit {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.J ∪ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂)
    {u v : Node} :
    (G.extendingCDMGsWith W₁ hW₁).MarginalizationΦL (W₂.image IntExtNode.unsplit)
        (IntExtNode.unsplit u) (IntExtNode.unsplit v) ↔
      G.MarginalizationΦL W₂ u v := by
  constructor
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · -- walk u → v in ext
      have hp_pos : p.length ≥ 1 := Walk.length_pos_of_isBifurcation hp_bif
      have h_all := all_unsplit_of_interior_W_image (W := W₁) (hW := hW₁)
        p hp_pos (u := u) (v := v) rfl rfl (W₂ := W₂) hp_inter
      obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hp_bif
      obtain ⟨q, _, hq_vs, _, _, hq_bif⟩ :=
        walk_ofExt_unsplit_full hW₁ p h_all u v rfl rfl
      refine Or.inl ⟨q, ⟨?_, ?_, ?_, i, hq_bif i hi⟩, ?_⟩
      · intro heq; apply hne; rw [heq]
      · intro h
        apply hu_tail
        rw [← hq_vs, list_unsplit_tail]
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      · intro h
        apply hv_drop
        rw [← hq_vs, list_unsplit_dropLast]
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      · intro x hx
        have hx_in : IntExtNode.unsplit x ∈ p.vertices.tail.dropLast := by
          rw [← hq_vs, list_unsplit_tail_dropLast]
          exact List.mem_map.mpr ⟨x, hx, rfl⟩
        have h_in_image := hp_inter (IntExtNode.unsplit x) hx_in
        obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp h_in_image
        have hwx : w = x := by injection hw_eq
        exact hwx ▸ hwW₂
    · -- walk v → u in ext
      have hp_pos : p.length ≥ 1 := Walk.length_pos_of_isBifurcation hp_bif
      have h_all := all_unsplit_of_interior_W_image (W := W₁) (hW := hW₁)
        p hp_pos (u := v) (v := u) rfl rfl (W₂ := W₂) hp_inter
      obtain ⟨hne, hv_tail, hu_drop, i, hi⟩ := hp_bif
      obtain ⟨q, _, hq_vs, _, _, hq_bif⟩ :=
        walk_ofExt_unsplit_full hW₁ p h_all v u rfl rfl
      refine Or.inr ⟨q, ⟨?_, ?_, ?_, i, hq_bif i hi⟩, ?_⟩
      · intro heq; apply hne; rw [heq]
      · intro h
        apply hv_tail
        rw [← hq_vs, list_unsplit_tail]
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      · intro h
        apply hu_drop
        rw [← hq_vs, list_unsplit_dropLast]
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      · intro x hx
        have hx_in : IntExtNode.unsplit x ∈ p.vertices.tail.dropLast := by
          rw [← hq_vs, list_unsplit_tail_dropLast]
          exact List.mem_map.mpr ⟨x, hx, rfl⟩
        have h_in_image := hp_inter (IntExtNode.unsplit x) hx_in
        obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp h_in_image
        have hwx : w = x := by injection hw_eq
        exact hwx ▸ hwW₂
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · refine Or.inl ⟨walk_toExt hW₁ p, walk_toExt_isBifurcation hW₁ p hp_bif, ?_⟩
      intro x hx
      rw [walk_toExt_vertices hW₁ p, list_unsplit_tail_dropLast] at hx
      obtain ⟨a, haIn, haEq⟩ := List.mem_map.mp hx
      rw [← haEq]
      exact Finset.mem_image.mpr ⟨a, hp_inter a haIn, rfl⟩
    · refine Or.inr ⟨walk_toExt hW₁ p, walk_toExt_isBifurcation hW₁ p hp_bif, ?_⟩
      intro x hx
      rw [walk_toExt_vertices hW₁ p, list_unsplit_tail_dropLast] at hx
      obtain ⟨a, haIn, haEq⟩ := List.mem_map.mp hx
      rw [← haEq]
      exact Finset.mem_image.mpr ⟨a, hp_inter a haIn, rfl⟩

-- ## Helper: a directed walk in ext from `.intCopy w` (for `w ∈ W \ G.J`)
-- with interior in `W₂.image .unsplit` (and `Disjoint W W₂`) has its target
-- forced to be `.unsplit w` (i.e., is the single fresh edge).
private lemma walk_intCopy_target_unsplit {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {W₂ : Finset Node} (hDisj : Disjoint W W₂)
    {w : Node} (hwWJ : w ∈ W \ G.J)
    {y : IntExtNode Node}
    (p : Walk (G.extendingCDMGsWith W hW) (IntExtNode.intCopy w) y)
    (hp_dir : p.IsDirectedWalk)
    (hp_pos : p.length ≥ 1)
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast, z ∈ W₂.image IntExtNode.unsplit) :
    y = IntExtNode.unsplit w := by
  cases p with
  | nil _ _ => simp [Walk.length] at hp_pos
  | @cons _ _ mid a hStep p' =>
      simp only [Walk.IsDirectedWalk] at hp_dir
      obtain ⟨ha_eq, ha_E, _⟩ := hp_dir
      change a ∈ G.E.image _ ∪ (W \ G.J).image _ at ha_E
      rcases Finset.mem_union.mp ha_E with hLift | hFresh
      · obtain ⟨e', _, he'_eq⟩ := Finset.mem_image.mp hLift
        rw [ha_eq] at he'_eq
        have hcontra : IntExtNode.unsplit e'.1 = IntExtNode.intCopy w :=
          congrArg Prod.fst he'_eq
        cases hcontra
      · obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hFresh
        rw [ha_eq] at hw'_eq
        have h1 : IntExtNode.intCopy w' = IntExtNode.intCopy w :=
          congrArg Prod.fst hw'_eq
        have h2 : IntExtNode.unsplit w' = mid :=
          congrArg Prod.snd hw'_eq
        have hww' : w' = w := by injection h1
        -- Rewrite mid to be .unsplit w (without subst, to avoid w-direction issues).
        rw [hww'] at h2
        have hmid : mid = IntExtNode.unsplit w := h2.symm
        subst hmid
        cases p' with
        | nil _ _ => rfl
        | @cons _ _ mid2 a2 hStep2 p2 =>
            have h_pv_ne : p2.vertices ≠ [] := Walk.vertices_ne_nil p2
            have h_w_inter : IntExtNode.unsplit w ∈
                (Walk.cons (G := G.extendingCDMGsWith W hW)
                  (IntExtNode.unsplit w) a hStep
                  (Walk.cons mid2 a2 hStep2 p2)).vertices.tail.dropLast := by
              change IntExtNode.unsplit w ∈ (IntExtNode.intCopy w
                :: IntExtNode.unsplit w :: p2.vertices).tail.dropLast
              rw [show (IntExtNode.intCopy w :: IntExtNode.unsplit w
                          :: p2.vertices : List _).tail
                      = IntExtNode.unsplit w :: p2.vertices from rfl]
              rw [List.dropLast_cons_of_ne_nil h_pv_ne]
              exact List.mem_cons_self
            have h_in_image := hp_inter (IntExtNode.unsplit w) h_w_inter
            obtain ⟨w''', hw'''W₂, hw'''_eq⟩ := Finset.mem_image.mp h_in_image
            have hww''' : w''' = w := by injection hw'''_eq
            rw [hww'''] at hw'''W₂
            exact absurd hw'''W₂ (Finset.disjoint_left.mp hDisj
              (Finset.mem_sdiff.mp hwWJ).1)

-- ## E-field equality for Part (ii).
private lemma ext_marg_E_field_eq {G : CDMG Node} (W₁ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    ((G.extendingCDMGsWith W₁ hW₁).marginalize (W₂.image IntExtNode.unsplit)
        (image_unsplit_subset_extendingCDMGsWith_V hW₁ hW₂)).E
      = ((G.marginalize W₂ hW₂).extendingCDMGsWith W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)).E := by
  apply Finset.ext
  intro e
  change
    e ∈ (((G.J.image IntExtNode.unsplit ∪ (W₁ \ G.J).image IntExtNode.intCopy)
            ∪ (G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit))
          ×ˢ (G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit)).filter
        (fun e => (G.extendingCDMGsWith W₁ hW₁).MarginalizationΦE
                    (W₂.image IntExtNode.unsplit) e.1 e.2)
    ↔ e ∈ (((G.J ∪ (G.V \ W₂)) ×ˢ (G.V \ W₂)).filter
              (fun e => G.MarginalizationΦE W₂ e.1 e.2)).image
            (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
        ∪ (W₁ \ G.J).image
            (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w))
  rw [image_unsplit_sdiff]
  rw [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, h2⟩, hPhi⟩
    obtain ⟨v, hvVW₂, hv_eq⟩ := Finset.mem_image.mp h2
    rcases Finset.mem_union.mp h1 with h1JI | h1V
    · rcases Finset.mem_union.mp h1JI with h1J | h1I
      · -- e.1 = .unsplit u with u ∈ G.J. Lifted.
        obtain ⟨u, huJ, hu_eq⟩ := Finset.mem_image.mp h1J
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨(u, v), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_union_left _ huJ, hvVW₂⟩, ?_⟩
          rw [show e.1 = IntExtNode.unsplit u from hu_eq.symm,
              show e.2 = IntExtNode.unsplit v from hv_eq.symm] at hPhi
          exact (ext_marg_PhiE_iff_unsplit hW₁ hDisj).mp hPhi
        · -- (.unsplit u, .unsplit v) = e
          exact Prod.ext hu_eq hv_eq
      · -- e.1 = .intCopy w fresh. Must be fresh-edge walk.
        obtain ⟨w, hwWJ, hw_eq⟩ := Finset.mem_image.mp h1I
        refine Finset.mem_union_right _ ?_
        refine Finset.mem_image.mpr ⟨w, hwWJ, ?_⟩
        -- Destructure e to get fresh vars, then substitute via hw_eq, hv_eq.
        obtain ⟨ec1, ec2⟩ := e
        change IntExtNode.intCopy w = ec1 at hw_eq
        change IntExtNode.unsplit v = ec2 at hv_eq
        subst hw_eq
        -- Now ec1 = .intCopy w; hPhi about (.intCopy w, ec2).
        obtain ⟨p, hp_dir, hp_pos, hp_inter⟩ := hPhi
        -- p : Walk ext (.intCopy w) ec2.  Use the helper.
        have hec2 : ec2 = IntExtNode.unsplit w :=
          walk_intCopy_target_unsplit (hW := hW₁) hDisj hwWJ p hp_dir hp_pos hp_inter
        subst hec2
        -- Goal: (.intCopy w, .unsplit w) = (.intCopy w, .unsplit w)
        rfl
    · -- e.1 = .unsplit u with u ∈ G.V \ W₂.
      obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp h1V
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_image.mpr ⟨(u, v), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_union_right _ hu, hvVW₂⟩, ?_⟩
        rw [show e.1 = IntExtNode.unsplit u from hu_eq.symm,
            show e.2 = IntExtNode.unsplit v from hv_eq.symm] at hPhi
        exact (ext_marg_PhiE_iff_unsplit hW₁ hDisj).mp hPhi
      · exact Prod.ext hu_eq hv_eq
  · intro h_union
    rcases Finset.mem_union.mp h_union with h_lifted | h_fresh
    · obtain ⟨⟨u, v⟩, hUV_mem, hUV_eq⟩ := Finset.mem_image.mp h_lifted
      rw [Finset.mem_filter, Finset.mem_product] at hUV_mem
      obtain ⟨⟨hu_in, hv_in⟩, hPhi⟩ := hUV_mem
      have h1_eq : e.1 = IntExtNode.unsplit u :=
        congrArg Prod.fst hUV_eq.symm
      have h2_eq : e.2 = IntExtNode.unsplit v :=
        congrArg Prod.snd hUV_eq.symm
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rcases Finset.mem_union.mp hu_in with huJ | huVW₂
        · refine Finset.mem_union_left _ ?_
          refine Finset.mem_union_left _ ?_
          rw [h1_eq]
          exact Finset.mem_image.mpr ⟨u, huJ, rfl⟩
        · refine Finset.mem_union_right _ ?_
          rw [h1_eq]
          exact Finset.mem_image.mpr ⟨u, huVW₂, rfl⟩
      · rw [h2_eq]
        exact Finset.mem_image.mpr ⟨v, hv_in, rfl⟩
      · rw [h1_eq, h2_eq]
        exact (ext_marg_PhiE_iff_unsplit hW₁ hDisj).mpr hPhi
    · obtain ⟨w, hwWJ, hw_eq⟩ := Finset.mem_image.mp h_fresh
      have hwW₁ : w ∈ W₁ := (Finset.mem_sdiff.mp hwWJ).1
      have hwNJ : w ∉ G.J := (Finset.mem_sdiff.mp hwWJ).2
      have hwV : w ∈ G.V := by
        rcases Finset.mem_union.mp (hW₁ hwW₁) with hJ | hV
        · exact absurd hJ hwNJ
        · exact hV
      have hwNW₂ : w ∉ W₂ := Finset.disjoint_left.mp hDisj hwW₁
      have h1_eq : e.1 = IntExtNode.intCopy w :=
        congrArg Prod.fst hw_eq.symm
      have h2_eq : e.2 = IntExtNode.unsplit w :=
        congrArg Prod.snd hw_eq.symm
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h1_eq]
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, hwWJ, rfl⟩
      · rw [h2_eq]
        exact Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hwV, hwNW₂⟩, rfl⟩
      · rw [h1_eq, h2_eq]
        have h_fresh_edge : (IntExtNode.intCopy w, IntExtNode.unsplit w)
            ∈ (G.extendingCDMGsWith W₁ hW₁).E := by
          change _ ∈ G.E.image _ ∪ (W₁ \ G.J).image _
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwWJ, rfl⟩
        have h_unsplitw_in : IntExtNode.unsplit w ∈ G.extendingCDMGsWith W₁ hW₁ := by
          change _ ∈ (G.extendingCDMGsWith W₁ hW₁).J ∪ (G.extendingCDMGsWith W₁ hW₁).V
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwV, rfl⟩
        have hStep : (G.extendingCDMGsWith W₁ hW₁).WalkStep (IntExtNode.intCopy w)
            (IntExtNode.intCopy w, IntExtNode.unsplit w) (IntExtNode.unsplit w) :=
          Or.inl ⟨rfl, Or.inl h_fresh_edge⟩
        refine ⟨Walk.cons (IntExtNode.unsplit w)
                  (IntExtNode.intCopy w, IntExtNode.unsplit w)
                  hStep (Walk.nil (IntExtNode.unsplit w) h_unsplitw_in),
                ⟨rfl, h_fresh_edge, trivial⟩, by change 1 ≥ 1; omega, ?_⟩
        intro x hx
        simp [Walk.vertices, List.tail, List.dropLast] at hx

-- ## L-field equality for Part (ii).
private lemma ext_marg_L_field_eq {G : CDMG Node} (W₁ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    ((G.extendingCDMGsWith W₁ hW₁).marginalize (W₂.image IntExtNode.unsplit)
        (image_unsplit_subset_extendingCDMGsWith_V hW₁ hW₂)).L
      = ((G.marginalize W₂ hW₂).extendingCDMGsWith W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)).L := by
  apply Finset.ext
  intro e
  change
    e ∈ ((G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit)
          ×ˢ (G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit)).filter
        (fun e => e.1 ≠ e.2 ∧
          (G.extendingCDMGsWith W₁ hW₁).MarginalizationΦL
            (W₂.image IntExtNode.unsplit) e.1 e.2)
    ↔ e ∈ (((G.V \ W₂) ×ˢ (G.V \ W₂)).filter
              (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W₂ e.1 e.2)).image
            (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
  rw [image_unsplit_sdiff]
  rw [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, h2⟩, hNe, hPhi⟩
    obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp h1
    obtain ⟨v, hv, hv_eq⟩ := Finset.mem_image.mp h2
    refine Finset.mem_image.mpr ⟨(u, v), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, ?_, ?_⟩
      · -- u ≠ v from .unsplit u ≠ .unsplit v
        intro huv
        apply hNe
        exact hu_eq.symm.trans ((congrArg IntExtNode.unsplit huv).trans hv_eq)
      · rw [show e.1 = IntExtNode.unsplit u from hu_eq.symm,
            show e.2 = IntExtNode.unsplit v from hv_eq.symm] at hPhi
        exact (ext_marg_PhiL_iff_unsplit hW₁ hDisj).mp hPhi
    · exact Prod.ext hu_eq hv_eq
  · intro h_lifted
    obtain ⟨⟨u, v⟩, hUV_mem, hUV_eq⟩ := Finset.mem_image.mp h_lifted
    rw [Finset.mem_filter, Finset.mem_product] at hUV_mem
    obtain ⟨⟨hu_in, hv_in⟩, hNe, hPhi⟩ := hUV_mem
    have h1_eq : e.1 = IntExtNode.unsplit u :=
      congrArg Prod.fst hUV_eq.symm
    have h2_eq : e.2 = IntExtNode.unsplit v :=
      congrArg Prod.snd hUV_eq.symm
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [h1_eq]; exact Finset.mem_image.mpr ⟨u, hu_in, rfl⟩
    · rw [h2_eq]; exact Finset.mem_image.mpr ⟨v, hv_in, rfl⟩
    · rw [h1_eq, h2_eq]
      intro heq
      apply hNe
      injection heq
    · rw [h1_eq, h2_eq]
      exact (ext_marg_PhiL_iff_unsplit hW₁ hDisj).mpr hPhi

-- claim_3_18 -- start statement
theorem marginalize_extendingCDMGsWith_comm (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (G.extendingCDMGsWith W₁ hW₁).marginalize (W₂.image IntExtNode.unsplit)
        (image_unsplit_subset_extendingCDMGsWith_V hW₁ hW₂)
      = (G.marginalize W₂ hW₂).extendingCDMGsWith W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)
-- claim_3_18 -- end statement
:= by
  -- Field-by-field CDMG extensionality (matches Part i's pattern but over `IntExtNode Node`).
  have cdmgExt : ∀ {G₁ G₂ : CDMG (IntExtNode Node)},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨_, _, _, _, _, _, _, _, _⟩
           ⟨_, _, _, _, _, _, _, _, _⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL; rfl
  refine cdmgExt ?_ ?_ ?_ ?_
  · -- J: both sides reduce to G.J.image .unsplit ∪ (W₁ \ G.J).image .intCopy
    rfl
  · -- V: image-sdiff identity
    change G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit
      = (G.V \ W₂).image IntExtNode.unsplit
    exact image_unsplit_sdiff
  · -- E: lift / descend through walk-algebra; see `ext_marg_E_field_eq`.
    exact ext_marg_E_field_eq W₁ hW₁ W₂ hW₂ hDisj
  · -- L: bifurcation lift / descend; see `ext_marg_L_field_eq`.
    exact ext_marg_L_field_eq W₁ hW₁ W₂ hW₂ hDisj

-- ref: claim_3_18 (part iii / 3 — node-splitting)
-- For any CDMG `G : CDMG Node`, subsets `W₁, W₂ ⊆ G.V` with `Disjoint
-- W₁ W₂`, marginalization and node-splitting commute as a literal
-- `=` of CDMGs over the split carrier `SplitNode Node`:
--   `(G_{spl(W₁)})^{∖W₂} = (G^{∖W₂})_{spl(W₁)}`.
/-
LN tex (rewritten canonical statement for `claim_3_18`, part (iii)):

  For every `W₁ ⊆ V` and `W₂ ⊆ V` with `W₁ ∩ W₂ = ∅`:
    `(G_{spl(W₁)})^{∖W₂} = (G^{∖W₂})_{spl(W₁)}`.

LN block (verbatim, for backup): the LN's lemma block closes with
"A similar statement holds for ..., and also for marginalizations
and node-splitting interventions"; per the row's `addition_to_the_LN`
clause `[trailing_similar_statement_two_unstated_claims]`, that
trailer is authoritative and asserts this part (iii) with the typing
on `W₁` tightened to `W₁ ⊆ V` (matching `def_3_11`'s precondition).
-/
-- ## Design choice
--
-- *Typing on `W₁` is `W₁ ⊆ G.V`, NOT `W₁ ⊆ G.J ∪ G.V`.*  Departure
--   from Parts (i) and (ii): `nodeSplittingOn` (`def_3_11`) requires
--   `W₁ ⊆ G.V` strictly (the construction *removes* `W₁` from `V` and
--   creates tagged copies, which only makes sense on output nodes).
--   So Part (iii)'s `W₁`-binder is `hW₁ : W₁ ⊆ G.V`.  Confirmed by
--   the rewritten canonical statement tex.
--
-- *Literal `=` of CDMGs over `SplitNode Node`.*  Carrier analysis:
--   the LHS's outermost operator is `marginalize` applied to
--   `G.nodeSplittingOn W₁ hW₁ : CDMG (SplitNode Node)`, preserving
--   the carrier — so LHS : `CDMG (SplitNode Node)`.  The RHS's
--   outermost operator is `nodeSplittingOn` applied to `G.marginalize
--   W₂ hW₂ : CDMG Node`, carrying to `CDMG (SplitNode Node)` — so
--   RHS : `CDMG (SplitNode Node)` also.  Both sides have identical
--   Lean type; the equality is a literal `=`.  Same carrier-matching
--   pattern as Part (ii), now over `SplitNode Node`.
--
-- *Inner-`marginalize` lifted set `W₂.image SplitNode.unsplit`.*  The
--   inner CDMG `G.nodeSplittingOn W₁ hW₁` lives over `SplitNode
--   Node`, so the LHS marginalization's `W` argument must inhabit
--   `Finset (SplitNode Node)`.  The natural lift of `W₂ : Finset
--   Node` is `W₂.image SplitNode.unsplit`, which targets the
--   `(G.V \ W₁).image .unsplit` slice of `(G.nodeSplittingOn W₁
--   hW₁).V` (after `W₂ ⊆ G.V` + `Disjoint W₁ W₂` give `W₂ ⊆
--   G.V \ W₁`).  The subset proof is discharged by
--   `image_unsplit_subset_nodeSplittingOn_V_of_disjoint hW₁ hW₂
--   hDisj.symm` (note the `.symm`: the helper consumes
--   `Disjoint W₂ W₁`, the LN's symmetric phrasing here is `Disjoint
--   W₁ W₂`).
--
-- *Outer-`nodeSplittingOn` carrier transport via
--   `subset_sdiff_of_disjoint`.*  The RHS's outer `.nodeSplittingOn
--   W₁` requires `W₁ ⊆ (G.marginalize W₂ hW₂).V = G.V \ W₂`,
--   discharged by `subset_sdiff_of_disjoint hW₁ hDisj` (LN-direct
--   `Disjoint W₁ W₂` orientation, no `.symm` needed).
--
-- *No `W₂` -side marginalization on `W₁.image .copy0 / .copy1`.*  The
--   lifted set is `W₂.image SplitNode.unsplit`, not `W₂.image
--   SplitNode.copy0` or `.copy1`.  This is the LN-faithful reading:
--   the marginalization is over the *original* output nodes `W₂`,
--   none of which is a tagged copy — and by disjointness with `W₁`,
--   none of `W₂`'s elements has a `copy0` / `copy1` in the split
--   graph anyway.  `verify_equivalence_strict` is the natural place
--   to gate this carrier-matching choice during Phase A.
-- ## Image-sdiff identity for injective `SplitNode.unsplit`.
private lemma image_split_unsplit_sdiff {S T : Finset Node} :
    S.image SplitNode.unsplit \ T.image SplitNode.unsplit
      = (S \ T).image SplitNode.unsplit := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, hAS, rfl⟩, h_notT⟩
    refine ⟨a, ⟨hAS, ?_⟩, rfl⟩
    intro hAT
    exact h_notT ⟨a, hAT, rfl⟩
  · rintro ⟨a, ⟨hAS, hANotT⟩, rfl⟩
    refine ⟨⟨a, hAS, rfl⟩, ?_⟩
    rintro ⟨b, hBT, hEq⟩
    apply hANotT
    have : b = a := by injection hEq
    exact this ▸ hBT

-- ## SplitNode constructor-disjointness helpers (Part iii V field).
--
-- `.unsplit v`, `.copy0 w`, `.copy1 w` are constructors of distinct cases of
-- the `SplitNode` inductive, so the three images do not share elements.

private lemma unsplit_image_disjoint_copy0 {S T : Finset Node} :
    Disjoint (S.image SplitNode.unsplit) (T.image SplitNode.copy0) := by
  rw [Finset.disjoint_left]
  intro x hUns hC0
  obtain ⟨_, _, h1⟩ := Finset.mem_image.mp hUns
  obtain ⟨_, _, h2⟩ := Finset.mem_image.mp hC0
  rw [← h2] at h1
  cases h1

private lemma unsplit_image_disjoint_copy1 {S T : Finset Node} :
    Disjoint (S.image SplitNode.unsplit) (T.image SplitNode.copy1) := by
  rw [Finset.disjoint_left]
  intro x hUns hC1
  obtain ⟨_, _, h1⟩ := Finset.mem_image.mp hUns
  obtain ⟨_, _, h2⟩ := Finset.mem_image.mp hC1
  rw [← h2] at h1
  cases h1

-- ## `.unsplit v ∈ split` ⟹ `v ∈ G` (carrier descent through `.unsplit`).
private lemma mem_G_of_unsplit_mem_split {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.V) {v : Node}
    (hv : SplitNode.unsplit v ∈ G.nodeSplittingOn W hW) : v ∈ G := by
  change v ∈ G.J ∪ G.V
  change SplitNode.unsplit v ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
      ∪ W.image SplitNode.copy1) at hv
  rcases Finset.mem_union.mp hv with hJ | hRest
  · obtain ⟨j, hjJ, hjEq⟩ := Finset.mem_image.mp hJ
    have hju : j = v := by injection hjEq
    subst hju
    exact Finset.mem_union_left _ hjJ
  · rcases Finset.mem_union.mp hRest with hV12 | h1
    · rcases Finset.mem_union.mp hV12 with hVuns | h0
      · obtain ⟨z, hzVW, hzEq⟩ := Finset.mem_image.mp hVuns
        have hzv : z = v := by injection hzEq
        subst hzv
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hzVW).1
      · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h0
        cases hEq
    · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h1
      cases hEq

-- ## `toCopy0 W v = .unsplit v` when v ∉ W.
private lemma toCopy0_unsplit_of_notW {W : Finset Node} {v : Node} (h : v ∉ W) :
    toCopy0 W v = SplitNode.unsplit v := by
  unfold toCopy0; rw [if_neg h]

private lemma toCopy1_unsplit_of_notW {W : Finset Node} {v : Node} (h : v ∉ W) :
    toCopy1 W v = SplitNode.unsplit v := by
  unfold toCopy1; rw [if_neg h]

-- ## Lifted edge `(toCopy1 W₁ u, .unsplit v) ∈ split.E` from `(u, v) ∈ G.E`
-- when `v ∉ W₁` (target untagged in split).
private lemma lifted_edge_in_split_E {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) {u v : Node}
    (huv_inE : (u, v) ∈ G.E) (hv_notW : v ∉ W₁) :
    (toCopy1 W₁ u, SplitNode.unsplit v) ∈ (G.nodeSplittingOn W₁ hW₁).E := by
  change _ ∈ G.E.image _ ∪ _
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_image.mpr ⟨(u, v), huv_inE, ?_⟩
  simp [toCopy0_unsplit_of_notW hv_notW]

-- ## Φ_E iff for Part (iii), source/target lifted via toCopy1/toCopy0.
-- This handles BOTH cases simultaneously: the source/target may be `.unsplit u` or
-- `.copy1 w` (for source) and `.unsplit v` or `.copy0 w` (for target).  We express
-- it uniformly via the toCopy lifts.
--
-- The lifted equivalence: marg-Φ_E on split (with source toCopy1 W₁ u and target
-- toCopy0 W₁ v) iff marg-Φ_E on G for (u, v), provided the marg-W₂ side is
-- compatible (W₁ ∩ W₂ = ∅, W₂ interior on G is also W₂-image-unsplit interior on split).

-- ## `v ∈ G` ⟹ `.unsplit v ∈ split` (carrier ascent for non-`W₁` vertices).
-- For `v ∈ J ∪ (G.V \ W₁)`, `.unsplit v` lives in `split.J ∪ split.V`.
private lemma mem_split_of_mem_G_unsplit {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {v : Node} (hv : v ∈ G) (hv_notW₁ : v ∉ W₁) :
    SplitNode.unsplit v ∈ G.nodeSplittingOn W₁ hW₁ := by
  change _ ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1)
  change v ∈ G.J ∪ G.V at hv
  rcases Finset.mem_union.mp hv with hJ | hV
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hJ, rfl⟩)
  · refine Finset.mem_union_right _ ?_
    refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hV, hv_notW₁⟩, rfl⟩

-- ## `.copy0 w ∈ split` for `w ∈ W₁`.
private lemma mem_split_of_mem_W₁_copy0 {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {w : Node} (hw : w ∈ W₁) :
    SplitNode.copy0 w ∈ G.nodeSplittingOn W₁ hW₁ := by
  change _ ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1)
  refine Finset.mem_union_right _ ?_
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

-- ## `.copy1 w ∈ split` for `w ∈ W₁`.
private lemma mem_split_of_mem_W₁_copy1 {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {w : Node} (hw : w ∈ W₁) :
    SplitNode.copy1 w ∈ G.nodeSplittingOn W₁ hW₁ := by
  change _ ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1)
  refine Finset.mem_union_right _ ?_
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

-- ## Generic E-field lifted edge: `(toCopy1 W₁ u, toCopy0 W₁ v) ∈ split.E`
-- from `(u, v) ∈ G.E`.  No `W₁`-side condition needed (the toCopy{0,1} helpers
-- handle the case split internally).
private lemma lifted_E_in_split_E_generic {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {u v : Node}
    (huv_inE : (u, v) ∈ G.E) :
    (toCopy1 W₁ u, toCopy0 W₁ v) ∈ (G.nodeSplittingOn W₁ hW₁).E := by
  change _ ∈ G.E.image _ ∪ _
  refine Finset.mem_union_left _ ?_
  exact Finset.mem_image.mpr ⟨(u, v), huv_inE, rfl⟩

-- ## Generic L-field lifted edge: `(toCopy0 W₁ u, toCopy0 W₁ v) ∈ split.L`
-- from `(u, v) ∈ G.L`.
private lemma lifted_L_in_split_L_generic {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {u v : Node}
    (huv_inL : (u, v) ∈ G.L) :
    (toCopy0 W₁ u, toCopy0 W₁ v) ∈ (G.nodeSplittingOn W₁ hW₁).L := by
  change _ ∈ G.L.image _
  exact Finset.mem_image.mpr ⟨(u, v), huv_inL, rfl⟩

-- ## `.unsplit v ∈ split` ⟹ `v ∈ G` AND `v ∉ W₁` (only the `(V\W₁).image .unsplit`
-- piece of split.V contains `.unsplit`-tagged elements with V-typed underlying).
private lemma unsplit_notW₁_of_unsplit_mem_split {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {v : Node}
    (hv : SplitNode.unsplit v ∈ G.nodeSplittingOn W₁ hW₁) : v ∈ G ∧ v ∉ W₁ := by
  change v ∈ G.J ∪ G.V ∧ _
  change SplitNode.unsplit v ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1) at hv
  rcases Finset.mem_union.mp hv with hJ | hRest
  · obtain ⟨j, hjJ, hjEq⟩ := Finset.mem_image.mp hJ
    have hjv : j = v := by injection hjEq
    subst hjv
    refine ⟨Finset.mem_union_left _ hjJ, ?_⟩
    -- W₁ ⊆ G.V; G.J ∩ G.V = ∅ (hJV_disj)
    intro hjW₁
    have hjV : j ∈ G.V := hW₁ hjW₁
    exact Finset.disjoint_left.mp G.hJV_disj hjJ hjV
  · rcases Finset.mem_union.mp hRest with hV12 | h1
    · rcases Finset.mem_union.mp hV12 with hVuns | h0
      · obtain ⟨z, hzVW, hzEq⟩ := Finset.mem_image.mp hVuns
        have hzv : z = v := by injection hzEq
        subst hzv
        obtain ⟨hzV, hzNW⟩ := Finset.mem_sdiff.mp hzVW
        exact ⟨Finset.mem_union_right _ hzV, hzNW⟩
      · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h0
        cases hEq
    · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h1
      cases hEq

-- ## `.copy0 w ∈ split` ⟹ `w ∈ W₁`.
private lemma mem_W₁_of_copy0_mem_split {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {w : Node}
    (hw : SplitNode.copy0 w ∈ G.nodeSplittingOn W₁ hW₁) : w ∈ W₁ := by
  change SplitNode.copy0 w ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1) at hw
  rcases Finset.mem_union.mp hw with hJ | hRest
  · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hJ; cases hEq
  · rcases Finset.mem_union.mp hRest with hV12 | h1
    · rcases Finset.mem_union.mp hV12 with hVuns | h0
      · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hVuns; cases hEq
      · obtain ⟨w', hw'W₁, hw'Eq⟩ := Finset.mem_image.mp h0
        have : w' = w := by injection hw'Eq
        exact this ▸ hw'W₁
    · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h1; cases hEq

-- ## `.copy1 w ∈ split` ⟹ `w ∈ W₁`.
private lemma mem_W₁_of_copy1_mem_split {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {w : Node}
    (hw : SplitNode.copy1 w ∈ G.nodeSplittingOn W₁ hW₁) : w ∈ W₁ := by
  change SplitNode.copy1 w ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1) at hw
  rcases Finset.mem_union.mp hw with hJ | hRest
  · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hJ; cases hEq
  · rcases Finset.mem_union.mp hRest with hV12 | h1
    · rcases Finset.mem_union.mp hV12 with hVuns | h0
      · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hVuns; cases hEq
      · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h0; cases hEq
    · obtain ⟨w', hw'W₁, hw'Eq⟩ := Finset.mem_image.mp h1
      have : w' = w := by injection hw'Eq
      exact this ▸ hw'W₁

-- ## Walk-step lift: directed step in G lifts to directed step in split via
-- `(toCopy1 W₁ a.1, toCopy0 W₁ a.2)`.  For the *forward* (Or.inl with E)
-- case this is direct; for Or.inl with L we get an L-edge lifted via copy0/copy0;
-- for Or.inr (backward E) we get the reversed lift.  This lemma handles the
-- generic case (no W₁ restriction); cases where intermediate consistency matters
-- are handled by the walk-level lift below.
private lemma walkStep_toSplit {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {u v : Node} {a : Node × Node}
    (h : G.WalkStep u a v) (hu_notW : u ∉ W₁) (hv_notW : v ∉ W₁) :
    (G.nodeSplittingOn W₁ hW₁).WalkStep
      (SplitNode.unsplit u) (toCopy1 W₁ a.1, toCopy0 W₁ a.2)
      (SplitNode.unsplit v) := by
  rcases h with ⟨ha, hOr⟩ | ⟨ha, hE⟩
  · -- a = (u, v) ∧ (a ∈ G.E ∨ a ∈ G.L)
    have h1 : a.1 = u := congrArg Prod.fst ha
    have h2 : a.2 = v := congrArg Prod.snd ha
    refine Or.inl ⟨?_, ?_⟩
    · -- (toCopy1 a.1, toCopy0 a.2) = (.unsplit u, .unsplit v)
      rw [h1, h2, toCopy1_unsplit_of_notW hu_notW, toCopy0_unsplit_of_notW hv_notW]
    · rcases hOr with hE | hL
      · refine Or.inl ?_
        -- Goal: (toCopy1 W₁ a.1, toCopy0 W₁ a.2) ∈ split.E
        change _ ∈ G.E.image _ ∪ _
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨a, hE, ?_⟩
        rfl
      · refine Or.inr ?_
        change _ ∈ G.L.image _
        refine Finset.mem_image.mpr ⟨a, hL, ?_⟩
        -- (toCopy0 W₁ a.1, toCopy0 W₁ a.2) = (toCopy1 W₁ a.1, toCopy0 W₁ a.2)
        -- Use a.1 = u ∉ W₁: toCopy0 = .unsplit = toCopy1
        rw [h1, h2, toCopy0_unsplit_of_notW hu_notW,
            toCopy0_unsplit_of_notW hv_notW, toCopy1_unsplit_of_notW hu_notW]
  · -- a = (v, u) ∧ a ∈ G.E (backward E)
    have h1 : a.1 = v := congrArg Prod.fst ha
    have h2 : a.2 = u := congrArg Prod.snd ha
    refine Or.inr ⟨?_, ?_⟩
    · rw [h1, h2, toCopy1_unsplit_of_notW hv_notW, toCopy0_unsplit_of_notW hu_notW]
    · change _ ∈ G.E.image _ ∪ _
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_image.mpr ⟨a, hE, ?_⟩
      rfl

-- ## Walk lift: G-walk u → v with ALL vertices in (J ∪ V) \ W₁ lifts to a
-- split-walk from `.unsplit u` to `.unsplit v` with all vertices `.unsplit`-tagged
-- and edges via `(toCopy1, toCopy0)`.
private def walk_toSplit_unsplit {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) :
    ∀ {u v : Node} (p : Walk G u v),
      (∀ x ∈ p.vertices, x ∉ W₁) →
      Walk (G.nodeSplittingOn W₁ hW₁) (SplitNode.unsplit u) (SplitNode.unsplit v)
  | _, _, .nil v hv, h_all =>
      Walk.nil (SplitNode.unsplit v)
        (mem_split_of_mem_G_unsplit (hW₁ := hW₁) hv
          (h_all v (by simp [Walk.vertices])))
  | u, _, .cons v a hStep p, h_all =>
      have hu_notW : u ∉ W₁ := h_all u (by simp [Walk.vertices])
      have hv_notW : v ∉ W₁ :=
        h_all v (by simp [Walk.vertices, Walk.head_mem_vertices])
      have h_all_p : ∀ x ∈ p.vertices, x ∉ W₁ := fun x hx =>
        h_all x (by simp [Walk.vertices]; exact Or.inr hx)
      Walk.cons (SplitNode.unsplit v)
        (toCopy1 W₁ a.1, toCopy0 W₁ a.2)
        (walkStep_toSplit (hW₁ := hW₁) hStep hu_notW hv_notW)
        (walk_toSplit_unsplit hW₁ p h_all_p)

private lemma walk_toSplit_unsplit_length {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) :
    ∀ {u v : Node} (p : Walk G u v) (h_all : ∀ x ∈ p.vertices, x ∉ W₁),
      (walk_toSplit_unsplit hW₁ p h_all).length = p.length
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ _ _ p, h_all => by
      change (walk_toSplit_unsplit hW₁ p _).length + 1 = p.length + 1
      rw [walk_toSplit_unsplit_length hW₁ p]

private lemma walk_toSplit_unsplit_vertices {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) :
    ∀ {u v : Node} (p : Walk G u v) (h_all : ∀ x ∈ p.vertices, x ∉ W₁),
      (walk_toSplit_unsplit hW₁ p h_all).vertices
        = p.vertices.map SplitNode.unsplit
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ _ _ p, h_all => by
      change _ :: (walk_toSplit_unsplit hW₁ p _).vertices = _ :: _
      rw [walk_toSplit_unsplit_vertices hW₁ p]

private lemma walk_toSplit_unsplit_isDirectedWalk {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) :
    ∀ {u v : Node} (p : Walk G u v) (h_all : ∀ x ∈ p.vertices, x ∉ W₁),
      p.IsDirectedWalk → (walk_toSplit_unsplit hW₁ p h_all).IsDirectedWalk
  | _, _, .nil _ _, _, _ => trivial
  | u, _, .cons v a hStep p, h_all, hDir => by
      obtain ⟨ha_eq, ha_E, hp_dir⟩ := hDir
      have hu_notW : u ∉ W₁ := h_all u (by simp [Walk.vertices])
      have hv_notW : v ∉ W₁ :=
        h_all v (by simp [Walk.vertices, Walk.head_mem_vertices])
      have h_all_p : ∀ x ∈ p.vertices, x ∉ W₁ := fun x hx =>
        h_all x (by simp [Walk.vertices]; exact Or.inr hx)
      refine ⟨?_, ?_, walk_toSplit_unsplit_isDirectedWalk hW₁ p h_all_p hp_dir⟩
      · -- (toCopy1 a.1, toCopy0 a.2) = (.unsplit u, .unsplit v)
        have h1 : a.1 = u := congrArg Prod.fst ha_eq
        have h2 : a.2 = v := congrArg Prod.snd ha_eq
        rw [h1, h2, toCopy1_unsplit_of_notW hu_notW, toCopy0_unsplit_of_notW hv_notW]
      · exact lifted_E_in_split_E_generic ha_E

private lemma walk_toSplit_unsplit_isBifurcationWithSplit {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) :
    ∀ {u v : Node} (p : Walk G u v) (h_all : ∀ x ∈ p.vertices, x ∉ W₁) (i : ℕ),
      p.IsBifurcationWithSplit i →
        (walk_toSplit_unsplit hW₁ p h_all).IsBifurcationWithSplit i
  | _, _, .nil _ _, _, _, h => h.elim
  | u, _, .cons v a hStep (.nil _ hv), h_all, 0, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
      obtain ⟨ha_eq, ha_L⟩ := hSpl
      have hu_notW : u ∉ W₁ := h_all u (by simp [Walk.vertices])
      have hv_notW : v ∉ W₁ :=
        h_all v (by simp [Walk.vertices, Walk.head_mem_vertices])
      simp only [walk_toSplit_unsplit, Walk.IsBifurcationWithSplit]
      have h1 : a.1 = u := congrArg Prod.fst ha_eq
      have h2 : a.2 = v := congrArg Prod.snd ha_eq
      refine ⟨?_, ?_⟩
      · -- (toCopy1 a.1, toCopy0 a.2) = (.unsplit u, .unsplit v)
        rw [h1, h2, toCopy1_unsplit_of_notW hu_notW, toCopy0_unsplit_of_notW hv_notW]
      · -- (toCopy1 W₁ a.1, toCopy0 W₁ a.2) ∈ split.L
        change _ ∈ G.L.image _
        refine Finset.mem_image.mpr ⟨a, ha_L, ?_⟩
        rw [h1, h2, toCopy0_unsplit_of_notW hu_notW,
            toCopy0_unsplit_of_notW hv_notW, toCopy1_unsplit_of_notW hu_notW]
  | u, _, .cons v a hStep (.cons _ _ _ _), h_all, 0, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
      obtain ⟨hOr, hDir⟩ := hSpl
      have hu_notW : u ∉ W₁ := h_all u (by simp [Walk.vertices])
      have hv_notW : v ∉ W₁ :=
        h_all v (by simp [Walk.vertices, Walk.head_mem_vertices])
      have h_all_p : ∀ x ∈ (Walk.cons (G := G) _ _ _ _).vertices, x ∉ W₁ :=
        fun x hx => h_all x (List.mem_cons_of_mem _ hx)
      simp only [walk_toSplit_unsplit, Walk.IsBifurcationWithSplit]
      refine ⟨?_, walk_toSplit_unsplit_isDirectedWalk hW₁ _ h_all_p hDir⟩
      rcases hOr with ⟨ha_vu, ha_E⟩ | ⟨ha_uv, ha_L⟩
      · refine Or.inl ⟨?_, ?_⟩
        · have h1 : a.1 = v := congrArg Prod.fst ha_vu
          have h2 : a.2 = u := congrArg Prod.snd ha_vu
          rw [h1, h2, toCopy1_unsplit_of_notW hv_notW, toCopy0_unsplit_of_notW hu_notW]
        · change _ ∈ G.E.image _ ∪ _
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨a, ha_E, ?_⟩
          rfl
      · refine Or.inr ⟨?_, ?_⟩
        · have h1 : a.1 = u := congrArg Prod.fst ha_uv
          have h2 : a.2 = v := congrArg Prod.snd ha_uv
          rw [h1, h2, toCopy1_unsplit_of_notW hu_notW, toCopy0_unsplit_of_notW hv_notW]
        · have h1 : a.1 = u := congrArg Prod.fst ha_uv
          have h2 : a.2 = v := congrArg Prod.snd ha_uv
          change _ ∈ G.L.image _
          refine Finset.mem_image.mpr ⟨a, ha_L, ?_⟩
          rw [h1, h2, toCopy0_unsplit_of_notW hu_notW,
              toCopy0_unsplit_of_notW hv_notW, toCopy1_unsplit_of_notW hu_notW]
  | u, _, .cons v a hStep p, h_all, k+1, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
      obtain ⟨ha_vu, ha_E, hRec⟩ := hSpl
      have hu_notW : u ∉ W₁ := h_all u (by simp [Walk.vertices])
      have hv_notW : v ∉ W₁ :=
        h_all v (by simp [Walk.vertices, Walk.head_mem_vertices])
      have h_all_p : ∀ x ∈ p.vertices, x ∉ W₁ := fun x hx =>
        h_all x (by simp [Walk.vertices]; exact Or.inr hx)
      simp only [walk_toSplit_unsplit, Walk.IsBifurcationWithSplit]
      refine ⟨?_, ?_, walk_toSplit_unsplit_isBifurcationWithSplit hW₁ p h_all_p k hRec⟩
      · have h1 : a.1 = v := congrArg Prod.fst ha_vu
        have h2 : a.2 = u := congrArg Prod.snd ha_vu
        rw [h1, h2, toCopy1_unsplit_of_notW hv_notW, toCopy0_unsplit_of_notW hu_notW]
      · exact lifted_E_in_split_E_generic ha_E

private lemma walk_toSplit_unsplit_isBifurcation {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) {u v : Node} (p : Walk G u v)
    (h_all : ∀ x ∈ p.vertices, x ∉ W₁) (hp : p.IsBifurcation) :
    (walk_toSplit_unsplit hW₁ p h_all).IsBifurcation := by
  obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hp
  refine ⟨?_, ?_, ?_, i, walk_toSplit_unsplit_isBifurcationWithSplit hW₁ p h_all i hi⟩
  · intro heq
    apply hne
    have : SplitNode.unsplit u = SplitNode.unsplit v := heq
    injection this
  · rw [walk_toSplit_unsplit_vertices hW₁ p]
    intro h
    rw [show (p.vertices.map SplitNode.unsplit).tail
              = p.vertices.tail.map SplitNode.unsplit from
        by cases p.vertices with
        | nil => rfl
        | cons _ _ => rfl] at h
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h
    have : a = u := by injection ha_eq
    exact hu_tail (this ▸ ha_in)
  · rw [walk_toSplit_unsplit_vertices hW₁ p]
    intro h
    have hMap : ∀ (l : List Node),
        (l.map SplitNode.unsplit).dropLast = l.dropLast.map SplitNode.unsplit := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
          cases xs with
          | nil => rfl
          | cons y ys =>
              simp only [List.map_cons, List.dropLast_cons₂]
              change _ :: ((y :: ys).map _).dropLast
                = _ :: ((y :: ys).dropLast).map SplitNode.unsplit
              rw [ih]
    rw [hMap p.vertices] at h
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h
    have : a = v := by injection ha_eq
    exact hv_drop (this ▸ ha_in)

-- ## Helpers extracting underlying node from toCopy{0,1} equation with `.unsplit`.
private lemma node_of_toCopy1_unsplit {W₁ : Finset Node} {z : Node} {w : Node}
    (h : toCopy1 W₁ z = SplitNode.unsplit w) : z = w := by
  unfold toCopy1 at h
  by_cases hIn : z ∈ W₁
  · rw [if_pos hIn] at h
    cases h
  · rw [if_neg hIn] at h
    injection h

private lemma node_of_toCopy0_unsplit {W₁ : Finset Node} {z : Node} {w : Node}
    (h : toCopy0 W₁ z = SplitNode.unsplit w) : z = w := by
  unfold toCopy0 at h
  by_cases hIn : z ∈ W₁
  · rw [if_pos hIn] at h
    cases h
  · rw [if_neg hIn] at h
    injection h

-- ## Walk-step descent: split-step with `.unsplit` source AND target lifts
-- back to a G-walk-step.  The split-edge data `a : SplitNode × SplitNode` may
-- be either a lifted edge `(toCopy1 W₁ e.1, toCopy0 W₁ e.2)` (then `e.1, e.2`
-- must satisfy toCopy{0,1} = .unsplit, i.e., not in W₁) or a lifted L-edge
-- `(toCopy0 W₁ e.1, toCopy0 W₁ e.2)`.  Transfer edges `(.copy0 w, .copy1 w)`
-- are excluded because their endpoints are NOT `.unsplit`-tagged.
private lemma walkStep_ofSplit_unsplit {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {u v : Node} {a : SplitNode Node × SplitNode Node}
    (h : (G.nodeSplittingOn W₁ hW₁).WalkStep
      (SplitNode.unsplit u) a (SplitNode.unsplit v)) :
    ∃ a' : Node × Node, G.WalkStep u a' v ∧
      a = (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2) := by
  rcases h with ⟨ha, hOr⟩ | ⟨ha, hE⟩
  · -- a = (.unsplit u, .unsplit v) ∧ (a ∈ split.E ∨ a ∈ split.L)
    have ha_full : a = (SplitNode.unsplit u, SplitNode.unsplit v) := ha
    rcases hOr with hE_split | hL_split
    · -- a ∈ G.E.image (toCopy1, toCopy0) ∪ W₁.image (copy0, copy1)
      have hE_split' : a ∈ G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))
              ∪ W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w)) :=
        hE_split
      rcases Finset.mem_union.mp hE_split' with hImg | hTrans
      · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hImg
        -- ha'_eq : (toCopy1 a'.1, toCopy0 a'.2) = a
        rw [ha_full] at ha'_eq
        have h1 : toCopy1 W₁ a'.1 = SplitNode.unsplit u := congrArg Prod.fst ha'_eq
        have h2 : toCopy0 W₁ a'.2 = SplitNode.unsplit v := congrArg Prod.snd ha'_eq
        have ha'1 : a'.1 = u := node_of_toCopy1_unsplit h1
        have ha'2 : a'.2 = v := node_of_toCopy0_unsplit h2
        refine ⟨a', Or.inl ⟨?_, Or.inl ha'_in⟩, ?_⟩
        · ext <;> [exact ha'1; exact ha'2]
        · rw [ha_full]; ext
          · exact congrArg SplitNode.unsplit ha'1.symm
          · exact congrArg SplitNode.unsplit ha'2.symm
      · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
        rw [ha_full] at hw_eq
        have hcontra : SplitNode.copy0 w = SplitNode.unsplit u := congrArg Prod.fst hw_eq
        cases hcontra
    · -- a ∈ G.L.image (toCopy0, toCopy0)
      have hL_split' : a ∈ G.L.image (fun e => (toCopy0 W₁ e.1, toCopy0 W₁ e.2)) :=
        hL_split
      obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hL_split'
      rw [ha_full] at ha'_eq
      have h1 : toCopy0 W₁ a'.1 = SplitNode.unsplit u := congrArg Prod.fst ha'_eq
      have h2 : toCopy0 W₁ a'.2 = SplitNode.unsplit v := congrArg Prod.snd ha'_eq
      have ha'1 : a'.1 = u := node_of_toCopy0_unsplit h1
      have ha'2 : a'.2 = v := node_of_toCopy0_unsplit h2
      refine ⟨a', Or.inl ⟨?_, Or.inr ha'_in⟩, ?_⟩
      · ext <;> [exact ha'1; exact ha'2]
      · rw [ha_full]; ext
        · exact congrArg SplitNode.unsplit ha'1.symm
        · exact congrArg SplitNode.unsplit ha'2.symm
  · -- a = (.unsplit v, .unsplit u) ∧ a ∈ split.E (backward E)
    have ha_full : a = (SplitNode.unsplit v, SplitNode.unsplit u) := ha
    have hE' : a ∈ G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))
            ∪ W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w)) := hE
    rcases Finset.mem_union.mp hE' with hImg | hTrans
    · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hImg
      rw [ha_full] at ha'_eq
      have h1 : toCopy1 W₁ a'.1 = SplitNode.unsplit v := congrArg Prod.fst ha'_eq
      have h2 : toCopy0 W₁ a'.2 = SplitNode.unsplit u := congrArg Prod.snd ha'_eq
      have ha'1 : a'.1 = v := node_of_toCopy1_unsplit h1
      have ha'2 : a'.2 = u := node_of_toCopy0_unsplit h2
      refine ⟨a', Or.inr ⟨?_, ha'_in⟩, ?_⟩
      · ext <;> [exact ha'1; exact ha'2]
      · rw [ha_full]; ext
        · exact congrArg SplitNode.unsplit ha'1.symm
        · exact congrArg SplitNode.unsplit ha'2.symm
    · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
      rw [ha_full] at hw_eq
      have hcontra : SplitNode.copy0 w = SplitNode.unsplit v := congrArg Prod.fst hw_eq
      cases hcontra

-- ## List utility: `(l.map .unsplit).tail = l.tail.map .unsplit` for SplitNode.
private lemma list_split_unsplit_tail (l : List Node) :
    (l.map SplitNode.unsplit).tail = l.tail.map SplitNode.unsplit := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

private lemma list_split_unsplit_dropLast :
    ∀ (l : List Node),
      (l.map SplitNode.unsplit).dropLast = l.dropLast.map SplitNode.unsplit
  | [] => rfl
  | _ :: [] => rfl
  | x :: y :: rest => by
      change SplitNode.unsplit x :: (((y :: rest).map SplitNode.unsplit).dropLast)
          = SplitNode.unsplit x :: ((y :: rest).dropLast.map SplitNode.unsplit)
      rw [list_split_unsplit_dropLast (y :: rest)]

private lemma list_split_unsplit_tail_dropLast (l : List Node) :
    (l.map SplitNode.unsplit).tail.dropLast
      = l.tail.dropLast.map SplitNode.unsplit := by
  rw [list_split_unsplit_tail, list_split_unsplit_dropLast]

-- ## Helper: equality of pairs through `.unsplit` (SplitNode variant).
private lemma pair_eq_of_split_unsplit_eq {a : Node × Node} {u v : Node}
    (h : (SplitNode.unsplit a.1, SplitNode.unsplit a.2)
        = (SplitNode.unsplit u, SplitNode.unsplit v)) :
    a = (u, v) := by
  have h1 : SplitNode.unsplit a.1 = SplitNode.unsplit u := congrArg Prod.fst h
  have h2 : SplitNode.unsplit a.2 = SplitNode.unsplit v := congrArg Prod.snd h
  have ha1 : a.1 = u := by injection h1
  have ha2 : a.2 = v := by injection h2
  exact Prod.ext ha1 ha2

-- ## Two helpers analogous to Part (ii)'s: a `.unsplit`-pair-lifted edge in
-- split.E / split.L descends to a G.E / G.L edge.  Transfer edges cannot
-- contribute (their source is `.copy0`, not `.unsplit`).
private lemma a_in_G_E_of_lifted_in_split {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {a' : Node × Node}
    {a : SplitNode Node × SplitNode Node}
    (ha_eq : a = (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2))
    (ha_E : a ∈ (G.nodeSplittingOn W₁ hW₁).E) : a' ∈ G.E := by
  have ha_E' : a ∈ G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))
          ∪ W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w)) := ha_E
  rcases Finset.mem_union.mp ha_E' with hLift | hTrans
  · obtain ⟨e', he'E, he'_eq⟩ := Finset.mem_image.mp hLift
    rw [ha_eq] at he'_eq
    have h1 : toCopy1 W₁ e'.1 = SplitNode.unsplit a'.1 := congrArg Prod.fst he'_eq
    have h2 : toCopy0 W₁ e'.2 = SplitNode.unsplit a'.2 := congrArg Prod.snd he'_eq
    have he1 : e'.1 = a'.1 := node_of_toCopy1_unsplit h1
    have he2 : e'.2 = a'.2 := node_of_toCopy0_unsplit h2
    have heq : e' = a' := Prod.ext he1 he2
    rw [← heq]; exact he'E
  · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
    rw [ha_eq] at hw_eq
    have hcontra : SplitNode.copy0 w = SplitNode.unsplit a'.1 := congrArg Prod.fst hw_eq
    cases hcontra

private lemma a_in_G_L_of_lifted_in_split {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {a' : Node × Node}
    {a : SplitNode Node × SplitNode Node}
    (ha_eq : a = (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2))
    (ha_L : a ∈ (G.nodeSplittingOn W₁ hW₁).L) : a' ∈ G.L := by
  have ha_L' : a ∈ G.L.image (fun e => (toCopy0 W₁ e.1, toCopy0 W₁ e.2)) := ha_L
  obtain ⟨e', he'L, he'_eq⟩ := Finset.mem_image.mp ha_L'
  rw [ha_eq] at he'_eq
  have h1 : toCopy0 W₁ e'.1 = SplitNode.unsplit a'.1 := congrArg Prod.fst he'_eq
  have h2 : toCopy0 W₁ e'.2 = SplitNode.unsplit a'.2 := congrArg Prod.snd he'_eq
  have he1 : e'.1 = a'.1 := node_of_toCopy0_unsplit h1
  have he2 : e'.2 = a'.2 := node_of_toCopy0_unsplit h2
  have heq : e' = a' := Prod.ext he1 he2
  rw [← heq]; exact he'L

-- ## Walk descent: split → G, when source/target are `.unsplit` and all
-- vertices are `.unsplit`-tagged.  Returns descended walk + length + vertex
-- list + edge list + IsDirectedWalk + IsBifurcationWithSplit preservation.
private lemma walk_ofSplit_unsplit_full {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) :
    ∀ {x y : SplitNode Node} (p : Walk (G.nodeSplittingOn W₁ hW₁) x y),
      (∀ z ∈ p.vertices, ∃ z' : Node, z = SplitNode.unsplit z') →
      ∀ (u v : Node), x = SplitNode.unsplit u → y = SplitNode.unsplit v →
      ∃ q : Walk G u v, q.length = p.length ∧
        q.vertices.map SplitNode.unsplit = p.vertices ∧
        q.edges.map (fun e => (SplitNode.unsplit e.1, SplitNode.unsplit e.2))
          = p.edges ∧
        (p.IsDirectedWalk → q.IsDirectedWalk) ∧
        (∀ i, p.IsBifurcationWithSplit i → q.IsBifurcationWithSplit i) := by
  intro x y p
  induction p with
  | nil w hw =>
      intro _ u v hxu hyv
      have hu_eq_v : SplitNode.unsplit u = (SplitNode.unsplit v : SplitNode Node) := by
        rw [← hxu, hyv]
      have huv : u = v := by injection hu_eq_v
      subst huv
      subst hxu
      have hu_in_G : u ∈ G :=
        (unsplit_notW₁_of_unsplit_mem_split (hW₁ := hW₁) hw).1
      refine ⟨Walk.nil u hu_in_G, rfl, rfl, rfl, fun _ => trivial, ?_⟩
      intro i h
      exact h.elim
  | @cons x' y' mid a hStep p' ih =>
      intro h_all u v hxu hyv
      subst hxu
      have hmid_in : mid ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid a hStep p').vertices := by
        change mid ∈ (SplitNode.unsplit u :: p'.vertices)
        exact List.mem_cons_of_mem _ (Walk.head_mem_vertices p')
      obtain ⟨m', hmid_eq⟩ := h_all mid hmid_in
      subst hmid_eq
      have h_all_p' : ∀ z ∈ p'.vertices, ∃ z' : Node, z = SplitNode.unsplit z' := by
        intro z hz
        exact h_all z (List.mem_cons_of_mem _ hz)
      obtain ⟨a', hStepG, ha_eq⟩ := walkStep_ofSplit_unsplit (hW₁ := hW₁) hStep
      obtain ⟨q', hq'_len, hq'_vs, hq'_es, hq'_dir, hq'_bif⟩ :=
        ih h_all_p' m' v rfl hyv
      refine ⟨Walk.cons m' a' hStepG q', ?_, ?_, ?_, ?_, ?_⟩
      · -- length
        change q'.length + 1 = p'.length + 1
        rw [hq'_len]
      · -- vertices.map
        change SplitNode.unsplit u :: (q'.vertices.map SplitNode.unsplit)
              = SplitNode.unsplit u :: p'.vertices
        rw [hq'_vs]
      · -- edges.map
        change (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2)
              :: (q'.edges.map (fun e => (SplitNode.unsplit e.1, SplitNode.unsplit e.2)))
            = a :: p'.edges
        rw [hq'_es]; rw [← ha_eq]
      · -- IsDirectedWalk preservation
        intro hp_dir
        simp only [Walk.IsDirectedWalk] at hp_dir
        obtain ⟨ha_p, ha_E, hp'_dir⟩ := hp_dir
        refine ⟨?_, ?_, hq'_dir hp'_dir⟩
        · -- a' = (u, m')
          have hpair : (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2)
                  = (SplitNode.unsplit u, SplitNode.unsplit m') := by
            rw [← ha_eq]; exact ha_p
          exact pair_eq_of_split_unsplit_eq hpair
        · -- a' ∈ G.E: descend a ∈ split.E via ha_eq.
          exact a_in_G_E_of_lifted_in_split (hW₁ := hW₁) ha_eq ha_E
      · -- IsBifurcationWithSplit preservation
        intro i hPi
        match i, p', hPi, q', hq'_len, hq'_dir, hq'_bif with
        | 0, .nil _ _, hPi, .nil _ _, _, _, _ =>
            simp only [Walk.IsBifurcationWithSplit] at hPi
            obtain ⟨ha_uv, ha_L⟩ := hPi
            simp only [Walk.IsBifurcationWithSplit]
            refine ⟨?_, ?_⟩
            · have hpair : (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2)
                          = (SplitNode.unsplit u, SplitNode.unsplit m') := by
                rw [← ha_eq]; exact ha_uv
              exact pair_eq_of_split_unsplit_eq hpair
            · exact a_in_G_L_of_lifted_in_split (hW₁ := hW₁) ha_eq ha_L
        | 0, .nil _ _, _, .cons _ _ _ _, hlen, _, _ =>
            simp [Walk.length] at hlen
        | 0, .cons _ _ _ _, _, .nil _ _, hlen, _, _ =>
            simp [Walk.length] at hlen
        | 0, .cons _ _ _ _, hPi, .cons _ _ _ _, _, hq'_dir, _ =>
            simp only [Walk.IsBifurcationWithSplit] at hPi
            obtain ⟨ha_or, hp'_dir⟩ := hPi
            simp only [Walk.IsBifurcationWithSplit]
            refine ⟨?_, hq'_dir hp'_dir⟩
            rcases ha_or with ⟨ha_vu, ha_E⟩ | ⟨ha_uv, ha_L⟩
            · refine Or.inl ⟨?_, ?_⟩
              · have hpair : (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2)
                            = (SplitNode.unsplit m', SplitNode.unsplit u) := by
                  rw [← ha_eq]; exact ha_vu
                exact pair_eq_of_split_unsplit_eq hpair
              · exact a_in_G_E_of_lifted_in_split (hW₁ := hW₁) ha_eq ha_E
            · refine Or.inr ⟨?_, ?_⟩
              · have hpair : (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2)
                            = (SplitNode.unsplit u, SplitNode.unsplit m') := by
                  rw [← ha_eq]; exact ha_uv
                exact pair_eq_of_split_unsplit_eq hpair
              · exact a_in_G_L_of_lifted_in_split (hW₁ := hW₁) ha_eq ha_L
        | k + 1, _, hPi, _, _, _, hq'_bif =>
            simp only [Walk.IsBifurcationWithSplit] at hPi
            obtain ⟨ha_vu, ha_E, hPi_rest⟩ := hPi
            simp only [Walk.IsBifurcationWithSplit]
            refine ⟨?_, ?_, hq'_bif k hPi_rest⟩
            · have hpair : (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2)
                          = (SplitNode.unsplit m', SplitNode.unsplit u) := by
                rw [← ha_eq]; exact ha_vu
              exact pair_eq_of_split_unsplit_eq hpair
            · exact a_in_G_E_of_lifted_in_split (hW₁ := hW₁) ha_eq ha_E

-- ## Helper: walk in split from .unsplit u to .unsplit v with interior in
-- W₂.image .unsplit ⟹ all vertices are .unsplit-tagged.
private lemma all_unsplit_of_interior_W_image_split
    {G : CDMG Node} {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V}
    {x y : SplitNode Node}
    (p : Walk (G.nodeSplittingOn W₁ hW₁) x y)
    (hp_pos : p.length ≥ 1)
    {u v : Node} (hxu : x = SplitNode.unsplit u) (hyv : y = SplitNode.unsplit v)
    {W₂ : Finset Node}
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast, z ∈ W₂.image SplitNode.unsplit) :
    ∀ z ∈ p.vertices, ∃ z' : Node, z = SplitNode.unsplit z' := by
  intro z hz
  rw [Walk.vertices_eq_head_cons_tail p] at hz
  rcases List.mem_cons.mp hz with h_eq | h_in_tail
  · exact ⟨u, h_eq.trans hxu⟩
  · have h_tail_ne : p.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos p hp_pos
    have h_drop_or_last : z ∈ p.vertices.tail.dropLast ∨ z = y := by
      rw [← List.dropLast_append_getLast h_tail_ne] at h_in_tail
      rcases List.mem_append.mp h_in_tail with h_drop | h_last
      · exact Or.inl h_drop
      · refine Or.inr ?_
        rw [List.mem_singleton] at h_last
        rw [h_last, Walk.tail_getLast_of_pos p hp_pos]
    rcases h_drop_or_last with h_drop | h_last
    · have h_in_image := hp_inter z h_drop
      obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp h_in_image
      exact ⟨w, hw_eq.symm⟩
    · exact ⟨v, h_last.trans hyv⟩

-- =====================================================================
-- ## Walk-surgery helpers for Part (iii) — toCopy0 endpoints.
--
-- These extend the .unsplit-endpoint machinery above to handle endpoints
-- landing in W₁ (which then map under toCopy0 to .copy0).  Used by the
-- E-field and L-field equalities in `marginalize_nodeSplittingOn_comm`.
-- =====================================================================

-- ## `toCopy0 W₁ v ∈ split` for v ∈ G.
private lemma mem_split_of_mem_G_toCopy0 {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {v : Node} (hv : v ∈ G) :
    toCopy0 W₁ v ∈ G.nodeSplittingOn W₁ hW₁ := by
  by_cases hvW : v ∈ W₁
  · unfold toCopy0; rw [if_pos hvW]
    exact mem_split_of_mem_W₁_copy0 (hW₁ := hW₁) hvW
  · rw [toCopy0_unsplit_of_notW hvW]
    exact mem_split_of_mem_G_unsplit (hW₁ := hW₁) hv hvW

-- ## `toCopy0 W₁` is injective on `Node`.
private lemma toCopy0_inj_node {W₁ : Finset Node} {a b : Node}
    (h : toCopy0 W₁ a = toCopy0 W₁ b) : a = b := by
  unfold toCopy0 at h
  by_cases hWa : a ∈ W₁
  · by_cases hWb : b ∈ W₁
    · rw [if_pos hWa, if_pos hWb] at h; injection h
    · rw [if_pos hWa, if_neg hWb] at h; cases h
  · by_cases hWb : b ∈ W₁
    · rw [if_neg hWa, if_pos hWb] at h; cases h
    · rw [if_neg hWa, if_neg hWb] at h; injection h

-- ## `toCopy0 W₁ v ∈ split.V \ W₂.image .unsplit` for `v ∈ G.V \ W₂`.
private lemma mem_split_V_marg_of_mem_V_W₂_toCopy0 {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    {v : Node} (hv : v ∈ G.V \ W₂) :
    toCopy0 W₁ v ∈ (G.nodeSplittingOn W₁ hW₁).V \ W₂.image SplitNode.unsplit := by
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · -- toCopy0 W₁ v ∈ split.V
    obtain ⟨hvV, _⟩ := Finset.mem_sdiff.mp hv
    change toCopy0 W₁ v ∈
      (G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
        ∪ W₁.image SplitNode.copy1
    by_cases hvW : v ∈ W₁
    · unfold toCopy0; rw [if_pos hvW]
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨v, hvW, rfl⟩
    · rw [toCopy0_unsplit_of_notW hvW]
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvV, hvW⟩, rfl⟩
  · -- toCopy0 W₁ v ∉ W₂.image .unsplit
    intro h
    obtain ⟨w, hw, hw_eq⟩ := Finset.mem_image.mp h
    obtain ⟨_, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
    by_cases hvW : v ∈ W₁
    · unfold toCopy0 at hw_eq; rw [if_pos hvW] at hw_eq; cases hw_eq
    · rw [toCopy0_unsplit_of_notW hvW] at hw_eq
      have : w = v := by injection hw_eq
      exact hv_notW₂ (this ▸ hw)

-- ## A `toCopy0 W₁ x` element of split.V \ W₂.image .unsplit is NOT a .copy1.
private lemma toCopy0_ne_copy1 {W₁ : Finset Node} {v w : Node} :
    toCopy0 W₁ v ≠ SplitNode.copy1 w := by
  unfold toCopy0
  by_cases hvW : v ∈ W₁
  · rw [if_pos hvW]; intro h; cases h
  · rw [if_neg hvW]; intro h; cases h

-- ## Recover underlying `v' ∈ G.V \ W₂` from a non-.copy1 split.V \ W₂.image .unsplit element.
private lemma exists_underlying_of_mem_split_V_marg_not_copy1
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂)
    (x : SplitNode Node)
    (hx : x ∈ (G.nodeSplittingOn W₁ hW₁).V \ W₂.image SplitNode.unsplit)
    (h_no_copy1 : ∀ w, x ≠ SplitNode.copy1 w) :
    ∃ v : Node, v ∈ G.V \ W₂ ∧ x = toCopy0 W₁ v := by
  obtain ⟨h_in_split_V, h_notW₂⟩ := Finset.mem_sdiff.mp hx
  change x ∈ (G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
            ∪ W₁.image SplitNode.copy1 at h_in_split_V
  rcases Finset.mem_union.mp h_in_split_V with h12 | h_c1
  · rcases Finset.mem_union.mp h12 with h_uns | h_c0
    · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp h_uns
      refine ⟨v, ?_, ?_⟩
      · obtain ⟨hvV, _hvNW₁⟩ := Finset.mem_sdiff.mp hv
        refine Finset.mem_sdiff.mpr ⟨hvV, ?_⟩
        intro hvW₂
        apply h_notW₂
        rw [← hveq]
        exact Finset.mem_image.mpr ⟨v, hvW₂, rfl⟩
      · rw [← hveq, toCopy0_unsplit_of_notW (Finset.mem_sdiff.mp hv).2]
    · obtain ⟨w, hwW₁, hweq⟩ := Finset.mem_image.mp h_c0
      refine ⟨w, ?_, ?_⟩
      · refine Finset.mem_sdiff.mpr ⟨hW₁ hwW₁, ?_⟩
        exact Finset.disjoint_left.mp hDisj hwW₁
      · rw [← hweq]
        unfold toCopy0; rw [if_pos hwW₁]
  · obtain ⟨w, _, hweq⟩ := Finset.mem_image.mp h_c1
    exfalso; exact h_no_copy1 w hweq.symm

-- ## Helper 1: lift a G-directed walk u → v whose interior lies in W₂ to a
-- split-walk from `.unsplit u` to `toCopy0 W₁ v`.  Source u ∉ W₁ is required
-- (so .unsplit u sits in split.V).  Interior vertices ∈ W₂ are automatically
-- ∉ W₁ via disjointness, so each intermediate lifts via the
-- `.unsplit`-pair edge.  Only the LAST edge may land in W₁ (when v ∈ W₁); there
-- the target lifts to `.copy0 v`, handled by `lifted_E_in_split_E_generic`.
private lemma exists_lifted_dir_walk_to_split_endTarget
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk →
      u ∉ W₁ →
      (∀ x ∈ p.vertices.tail.dropLast, x ∈ W₂) →
      ∃ (s : Walk (G.nodeSplittingOn W₁ hW₁) (SplitNode.unsplit u) (toCopy0 W₁ v)),
        s.IsDirectedWalk ∧ s.length = p.length ∧
        s.vertices = p.vertices.map (toCopy0 W₁)
  | _, _, .nil w hw, _, hu_notW, _ => by
      -- A nil walk: u = v = w.  Need s : Walk split (.unsplit w) (toCopy0 W₁ w).
      -- Since w ∉ W₁, toCopy0 W₁ w = .unsplit w.
      have h_eq : toCopy0 W₁ w = SplitNode.unsplit w := toCopy0_unsplit_of_notW hu_notW
      rw [h_eq]
      refine ⟨Walk.nil (SplitNode.unsplit w)
        (mem_split_of_mem_G_unsplit (hW₁ := hW₁) hw hu_notW), trivial, rfl, ?_⟩
      -- Walk.nil's vertices = [.unsplit w]; p.vertices = [w]; map .unsplit = [.unsplit w]
      change [SplitNode.unsplit w] = [toCopy0 W₁ w]
      rw [h_eq]
  | u, _, .cons w a hStep (.nil _ hw), hp_dir, hu_notW, _ => by
      -- Single-edge walk u → w via forward E-edge a = (u, w).
      obtain ⟨ha_eq, ha_E, _⟩ := hp_dir
      have hpair : a = (u, w) := by
        have h1 : a.1 = u := congrArg Prod.fst ha_eq
        have h2 : a.2 = w := congrArg Prod.snd ha_eq
        exact Prod.ext h1 h2
      have h_in_E : (u, w) ∈ G.E := by rw [← hpair]; exact ha_E
      have h_edge_inE : (toCopy1 W₁ u, toCopy0 W₁ w) ∈
          (G.nodeSplittingOn W₁ hW₁).E := lifted_E_in_split_E_generic h_in_E
      have h_u_lift : toCopy1 W₁ u = SplitNode.unsplit u :=
        toCopy1_unsplit_of_notW hu_notW
      rw [h_u_lift] at h_edge_inE
      have h_u_lift0 : toCopy0 W₁ u = SplitNode.unsplit u :=
        toCopy0_unsplit_of_notW hu_notW
      have hw_in_split : toCopy0 W₁ w ∈ G.nodeSplittingOn W₁ hW₁ :=
        mem_split_of_mem_G_toCopy0 (hW₁ := hW₁) hw
      refine ⟨Walk.cons (toCopy0 W₁ w) (SplitNode.unsplit u, toCopy0 W₁ w)
        (Or.inl ⟨rfl, Or.inl h_edge_inE⟩)
        (Walk.nil (toCopy0 W₁ w) hw_in_split), ?_, rfl, ?_⟩
      · exact ⟨rfl, h_edge_inE, trivial⟩
      -- vertices: cons-shape gives [.unsplit u, toCopy0 W₁ w]; p = [u, w] mapped = [toCopy0 u, toCopy0 w].
      change SplitNode.unsplit u :: [toCopy0 W₁ w] = toCopy0 W₁ u :: [toCopy0 W₁ w]
      rw [h_u_lift0]
  | u, v, .cons vMid a hStep (.cons vMid' a' hStep' p''), hp_dir, hu_notW, h_inter => by
      -- Recursion case: p' is a cons, so vMid is in tail.dropLast hence vMid ∈ W₂.
      obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir
      -- (outer).vertices = u :: vMid :: p''.vertices
      -- (outer).vertices.tail = vMid :: p''.vertices
      -- (outer).vertices.tail.dropLast = vMid :: p''.vertices.dropLast (when p''.vertices nonempty)
      -- But (.cons vMid' a' hStep' p'').vertices = vMid' :: p''.vertices (inner cons source = vMid')
      -- Note: the inner cons has source = vMid (from outer's middle), so:
      -- (.cons vMid' a' hStep' p'').vertices starts with vMid (inner source).
      -- Actually, in Walk.cons {u w : Node} (v : Node) (a : Node × Node) ..., the FIRST
      -- arg is the middle vertex, the implicit `u` is the source.  So
      -- `Walk.cons vMid' a' hStep' p''` has source = (implicit, inferred to be vMid),
      -- middle = vMid', and `.vertices = vMid :: p''.vertices` where p''.vertices starts with vMid'.
      have hvMid_inW₂ : vMid ∈ W₂ := by
        apply h_inter
        -- Goal: vMid ∈ (Walk.cons vMid a hStep (Walk.cons vMid' a' hStep' p'')).vertices.tail.dropLast
        change vMid ∈ (vMid :: p''.vertices).dropLast
        have hne : (p''.vertices : List Node) ≠ [] := Walk.vertices_ne_nil _
        rw [List.dropLast_cons_of_ne_nil hne]
        exact List.mem_cons_self
      have hvMid_notW : vMid ∉ W₁ :=
        Finset.disjoint_left.mp hDisj.symm hvMid_inW₂
      have hpair : a = (u, vMid) := by
        have h1 : a.1 = u := congrArg Prod.fst ha_eq
        have h2 : a.2 = vMid := congrArg Prod.snd ha_eq
        exact Prod.ext h1 h2
      have h_in_E : (u, vMid) ∈ G.E := by rw [← hpair]; exact ha_E
      have h_edge_inE : (toCopy1 W₁ u, toCopy0 W₁ vMid) ∈
          (G.nodeSplittingOn W₁ hW₁).E := lifted_E_in_split_E_generic h_in_E
      have h_u_lift : toCopy1 W₁ u = SplitNode.unsplit u :=
        toCopy1_unsplit_of_notW hu_notW
      have h_vMid_lift : toCopy0 W₁ vMid = SplitNode.unsplit vMid :=
        toCopy0_unsplit_of_notW hvMid_notW
      rw [h_u_lift, h_vMid_lift] at h_edge_inE
      have h_inter_p' :
          ∀ x ∈ (Walk.cons (G := G) vMid' a' hStep' p'').vertices.tail.dropLast,
            x ∈ W₂ := by
        intro x hx
        apply h_inter
        -- Goal: x ∈ (outer).vertices.tail.dropLast = (vMid :: p''.vertices).dropLast
        -- We have: hx : x ∈ (inner).vertices.tail.dropLast = (vMid' :: p''.vertices.tail).dropLast
        -- Wait inner vertices = vMid :: p''.vertices (source vMid).
        -- So inner.tail = p''.vertices (starts with vMid').
        -- inner.tail.dropLast = p''.vertices.dropLast.
        change x ∈ (vMid :: p''.vertices).dropLast
        have hne : (p''.vertices : List Node) ≠ [] := Walk.vertices_ne_nil _
        rw [List.dropLast_cons_of_ne_nil hne]
        refine List.mem_cons_of_mem _ ?_
        -- hx is in (inner).vertices.tail.dropLast = p''.vertices.dropLast
        -- Need p''.vertices.dropLast ⊆ p''.vertices.dropLast: yes!
        change x ∈ p''.vertices.dropLast
        exact hx
      obtain ⟨s', hs'_dir, hs'_len, hs'_verts⟩ :=
        exists_lifted_dir_walk_to_split_endTarget hW₁ hDisj
          (Walk.cons vMid' a' hStep' p'') hp'_dir hvMid_notW h_inter_p'
      have h_u_lift0 : toCopy0 W₁ u = SplitNode.unsplit u :=
        toCopy0_unsplit_of_notW hu_notW
      refine ⟨Walk.cons (SplitNode.unsplit vMid)
        (SplitNode.unsplit u, SplitNode.unsplit vMid)
        (Or.inl ⟨rfl, Or.inl h_edge_inE⟩) s', ?_, ?_, ?_⟩
      · exact ⟨rfl, h_edge_inE, hs'_dir⟩
      · change s'.length + 1 = (Walk.cons vMid' a' hStep' p'').length + 1
        rw [hs'_len]
      -- vertices: cons gives .unsplit u :: s'.vertices
      -- = .unsplit u :: (cons vMid' ...).vertices.map toCopy0
      -- = .unsplit u :: (vMid :: p''.vertices).map toCopy0
      -- = toCopy0 W₁ u :: (toCopy0 W₁ vMid :: p''.vertices.map toCopy0)
      -- p.vertices = u :: vMid :: p''.vertices, mapped = toCopy0 W₁ u :: toCopy0 W₁ vMid :: ...
      · change SplitNode.unsplit u :: s'.vertices
            = toCopy0 W₁ u :: (Walk.cons (G := G) vMid' a' hStep' p'').vertices.map (toCopy0 W₁)
        rw [hs'_verts, h_u_lift0]

-- ## Helper 2: lift a G-bifurcationWithSplit walk u → v whose interior lies in W₂
-- to a split-walk from `toCopy0 W₁ u` to `toCopy0 W₁ v`.  Sources/targets may be
-- in W₁ (lifted to .copy0), interior is in W₂ (so ∉ W₁, lifts via .unsplit).
-- Three sub-cases inside the cons step (matching `IsBifurcationWithSplit` shape):
--   * `i = 0, p' = nil`: single bidirected edge (a ∈ G.L).
--   * `i = 0, p' = cons`: hinge + directed right-arm (uses Helper 1).
--   * `i = k+1, p' anything`: left-arm reverse-E step + recurse via ih.
private lemma exists_lifted_bifWithSplit_to_split
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {u v : Node} (p : Walk G u v) (i : ℕ),
      p.IsBifurcationWithSplit i →
      (∀ x ∈ p.vertices.tail.dropLast, x ∈ W₂) →
      ∃ (q : Walk (G.nodeSplittingOn W₁ hW₁) (toCopy0 W₁ u) (toCopy0 W₁ v)),
        q.IsBifurcationWithSplit i ∧ q.length = p.length ∧
        q.vertices = p.vertices.map (toCopy0 W₁)
  | _, _, .nil _ _, _, hi, _ => hi.elim
  | u, _, .cons w a hStep (.nil _ hw), 0, hi, _ => by
      -- Single bidirected edge: a = (u, w) ∧ a ∈ G.L.
      simp only [Walk.IsBifurcationWithSplit] at hi
      obtain ⟨ha_eq, ha_L⟩ := hi
      have ha_pair : a = (u, w) := by
        have h1 : a.1 = u := congrArg Prod.fst ha_eq
        have h2 : a.2 = w := congrArg Prod.snd ha_eq
        exact Prod.ext h1 h2
      have h_in_L : (u, w) ∈ G.L := by rw [← ha_pair]; exact ha_L
      have h_lifted_L : (toCopy0 W₁ u, toCopy0 W₁ w) ∈
          (G.nodeSplittingOn W₁ hW₁).L := lifted_L_in_split_L_generic h_in_L
      have hw_in_split : toCopy0 W₁ w ∈ G.nodeSplittingOn W₁ hW₁ :=
        mem_split_of_mem_G_toCopy0 (hW₁ := hW₁) hw
      refine ⟨Walk.cons (toCopy0 W₁ w) (toCopy0 W₁ u, toCopy0 W₁ w)
        (Or.inl ⟨rfl, Or.inr h_lifted_L⟩)
        (Walk.nil (toCopy0 W₁ w) hw_in_split), ?_, rfl, ?_⟩
      · exact ⟨rfl, h_lifted_L⟩
      -- vertices: q = [toCopy0 W₁ u, toCopy0 W₁ w] = (u :: [w]).map toCopy0
      rfl
  | u, _, .cons vMid a hStep (.cons vMid' a' hStep' p''), 0, hi, h_inter => by
      -- Hinge + directed right-arm.  vMid is interior (∈ W₂).
      simp only [Walk.IsBifurcationWithSplit] at hi
      obtain ⟨hOr, hp'_dir⟩ := hi
      have hvMid_inW₂ : vMid ∈ W₂ := by
        apply h_inter
        change vMid ∈ (vMid :: p''.vertices).dropLast
        have hne : (p''.vertices : List Node) ≠ [] := Walk.vertices_ne_nil _
        rw [List.dropLast_cons_of_ne_nil hne]
        exact List.mem_cons_self
      have hvMid_notW : vMid ∉ W₁ :=
        Finset.disjoint_left.mp hDisj.symm hvMid_inW₂
      have h_vMid_lift : toCopy0 W₁ vMid = SplitNode.unsplit vMid :=
        toCopy0_unsplit_of_notW hvMid_notW
      have h_vMid_lift1 : toCopy1 W₁ vMid = SplitNode.unsplit vMid :=
        toCopy1_unsplit_of_notW hvMid_notW
      -- Peel off the first edge of the right-arm directed walk (so we expose
      -- the cons structure to IsBifurcationWithSplit).
      obtain ⟨ha'_eq, ha'_E, hp''_dir⟩ := hp'_dir
      -- ha'_eq : a' = (vMid, vMid'), ha'_E : a' ∈ G.E, hp''_dir : p''.IsDirectedWalk
      have ha'_pair : a' = (vMid, vMid') := by
        have h1 : a'.1 = vMid := congrArg Prod.fst ha'_eq
        have h2 : a'.2 = vMid' := congrArg Prod.snd ha'_eq
        exact Prod.ext h1 h2
      have h_in_E_pair' : (vMid, vMid') ∈ G.E := by rw [← ha'_pair]; exact ha'_E
      -- Recurse on p'' with source vMid', target = original target v'.
      -- vMid' may or may not be in W₁ (interior or last vertex if p'' is nil).
      -- We need vMid' ∉ W₁ for Helper 1 source constraint.  vMid' ∈ W₂ iff
      -- vMid' ∈ p''.vertices.dropLast OR p''.vertices = [vMid']
      -- (i.e., p'' = nil and vMid' is the final target).
      -- Need a different approach: handle p'' = nil vs cons separately.
      match h_p'' : p'' with
      | .nil _ hw =>
          -- The right-arm is a single edge vMid → vMid'; lifted edge in split.E.
          have h_lifted_E' : (toCopy1 W₁ vMid, toCopy0 W₁ vMid') ∈
              (G.nodeSplittingOn W₁ hW₁).E := lifted_E_in_split_E_generic h_in_E_pair'
          rw [h_vMid_lift1] at h_lifted_E'
          have hw_in_split : toCopy0 W₁ vMid' ∈ G.nodeSplittingOn W₁ hW₁ :=
            mem_split_of_mem_G_toCopy0 (hW₁ := hW₁) hw
          rcases hOr with ⟨ha_vu, ha_E⟩ | ⟨ha_uv, ha_L⟩
          · have ha_pair : a = (vMid, u) := by
              have h1 : a.1 = vMid := congrArg Prod.fst ha_vu
              have h2 : a.2 = u := congrArg Prod.snd ha_vu
              exact Prod.ext h1 h2
            have h_in_E_pair : (vMid, u) ∈ G.E := by rw [← ha_pair]; exact ha_E
            have h_lifted_E : (toCopy1 W₁ vMid, toCopy0 W₁ u) ∈
                (G.nodeSplittingOn W₁ hW₁).E := lifted_E_in_split_E_generic h_in_E_pair
            rw [h_vMid_lift1] at h_lifted_E
            refine ⟨Walk.cons (SplitNode.unsplit vMid)
              (SplitNode.unsplit vMid, toCopy0 W₁ u)
              (Or.inr ⟨rfl, h_lifted_E⟩)
              (Walk.cons (toCopy0 W₁ vMid') (SplitNode.unsplit vMid, toCopy0 W₁ vMid')
                (Or.inl ⟨rfl, Or.inl h_lifted_E'⟩)
                (Walk.nil (toCopy0 W₁ vMid') hw_in_split)), ?_, rfl, ?_⟩
            · refine ⟨Or.inl ⟨?_, h_lifted_E⟩, ?_, h_lifted_E', trivial⟩
              · rfl
              · rfl
            -- vertices: q.vertices = [toCopy0 W₁ u, .unsplit vMid, toCopy0 W₁ vMid']
            -- p.vertices = [u, vMid, vMid']; map gives [toCopy0 u, toCopy0 vMid, toCopy0 vMid']
            change toCopy0 W₁ u :: SplitNode.unsplit vMid :: [toCopy0 W₁ vMid']
              = toCopy0 W₁ u :: toCopy0 W₁ vMid :: [toCopy0 W₁ vMid']
            rw [← h_vMid_lift]
          · have ha_pair : a = (u, vMid) := by
              have h1 : a.1 = u := congrArg Prod.fst ha_uv
              have h2 : a.2 = vMid := congrArg Prod.snd ha_uv
              exact Prod.ext h1 h2
            have h_in_L_pair : (u, vMid) ∈ G.L := by rw [← ha_pair]; exact ha_L
            have h_lifted_L : (toCopy0 W₁ u, toCopy0 W₁ vMid) ∈
                (G.nodeSplittingOn W₁ hW₁).L := lifted_L_in_split_L_generic h_in_L_pair
            rw [h_vMid_lift] at h_lifted_L
            refine ⟨Walk.cons (SplitNode.unsplit vMid)
              (toCopy0 W₁ u, SplitNode.unsplit vMid)
              (Or.inl ⟨rfl, Or.inr h_lifted_L⟩)
              (Walk.cons (toCopy0 W₁ vMid') (SplitNode.unsplit vMid, toCopy0 W₁ vMid')
                (Or.inl ⟨rfl, Or.inl h_lifted_E'⟩)
                (Walk.nil (toCopy0 W₁ vMid') hw_in_split)), ?_, rfl, ?_⟩
            · refine ⟨Or.inr ⟨?_, h_lifted_L⟩, ?_, h_lifted_E', trivial⟩
              · rfl
              · rfl
            change toCopy0 W₁ u :: SplitNode.unsplit vMid :: [toCopy0 W₁ vMid']
              = toCopy0 W₁ u :: toCopy0 W₁ vMid :: [toCopy0 W₁ vMid']
            rw [← h_vMid_lift]
      | .cons vMid'' a'' hStep'' p''' =>
          -- p'' is cons.  vMid' is in tail.dropLast of original walk (now an interior).
          -- Actually need to think — vMid' is the middle of the inner cons (vMid → vMid').
          -- In original walk vertices: u :: vMid :: vMid' :: p'''.vertices (after unfolding).
          -- tail.dropLast = vMid :: vMid' :: <p'''.vertices.dropLast> = interior.
          -- So vMid' ∈ W₂, hence ∉ W₁.
          have hvMid'_inW₂ : vMid' ∈ W₂ := by
            apply h_inter
            change vMid' ∈ (vMid :: vMid' :: p'''.vertices).dropLast
            have hne1 : ((vMid' :: p'''.vertices) : List Node) ≠ [] := by simp
            rw [List.dropLast_cons_of_ne_nil hne1]
            refine List.mem_cons_of_mem _ ?_
            have hne2 : (p'''.vertices : List Node) ≠ [] := Walk.vertices_ne_nil _
            rw [List.dropLast_cons_of_ne_nil hne2]
            exact List.mem_cons_self
          have hvMid'_notW : vMid' ∉ W₁ :=
            Finset.disjoint_left.mp hDisj.symm hvMid'_inW₂
          have h_vMid'_lift : toCopy0 W₁ vMid' = SplitNode.unsplit vMid' :=
            toCopy0_unsplit_of_notW hvMid'_notW
          have h_lifted_E' : (toCopy1 W₁ vMid, toCopy0 W₁ vMid') ∈
              (G.nodeSplittingOn W₁ hW₁).E := lifted_E_in_split_E_generic h_in_E_pair'
          rw [h_vMid_lift1, h_vMid'_lift] at h_lifted_E'
          -- Recurse Helper 1 on p''' = Walk.cons vMid'' a'' hStep'' p'''.  Actually
          -- here p'' itself is `Walk.cons vMid'' a'' hStep'' p'''`, with source vMid'.
          have h_inter_p''_for_helper :
              ∀ x ∈ (Walk.cons (G := G) vMid'' a'' hStep'' p''').vertices.tail.dropLast,
                x ∈ W₂ := by
            intro x hx
            apply h_inter
            change x ∈ (vMid :: vMid' :: p'''.vertices).dropLast
            have hne1 : ((vMid' :: p'''.vertices) : List Node) ≠ [] := by simp
            rw [List.dropLast_cons_of_ne_nil hne1]
            refine List.mem_cons_of_mem _ ?_
            have hne2 : (p'''.vertices : List Node) ≠ [] := Walk.vertices_ne_nil _
            rw [List.dropLast_cons_of_ne_nil hne2]
            refine List.mem_cons_of_mem _ ?_
            change x ∈ p'''.vertices.dropLast
            exact hx
          obtain ⟨t', ht'_dir, ht'_len, ht'_verts⟩ :=
            exists_lifted_dir_walk_to_split_endTarget hW₁ hDisj
              (Walk.cons vMid'' a'' hStep'' p''') hp''_dir hvMid'_notW
              h_inter_p''_for_helper
          -- Now construct the lifted walk: hinge edge + lifted right-arm first edge + t'
          rcases hOr with ⟨ha_vu, ha_E⟩ | ⟨ha_uv, ha_L⟩
          · have ha_pair : a = (vMid, u) := by
              have h1 : a.1 = vMid := congrArg Prod.fst ha_vu
              have h2 : a.2 = u := congrArg Prod.snd ha_vu
              exact Prod.ext h1 h2
            have h_in_E_pair : (vMid, u) ∈ G.E := by rw [← ha_pair]; exact ha_E
            have h_lifted_E : (toCopy1 W₁ vMid, toCopy0 W₁ u) ∈
                (G.nodeSplittingOn W₁ hW₁).E := lifted_E_in_split_E_generic h_in_E_pair
            rw [h_vMid_lift1] at h_lifted_E
            refine ⟨Walk.cons (SplitNode.unsplit vMid)
              (SplitNode.unsplit vMid, toCopy0 W₁ u)
              (Or.inr ⟨rfl, h_lifted_E⟩)
              (Walk.cons (SplitNode.unsplit vMid')
                (SplitNode.unsplit vMid, SplitNode.unsplit vMid')
                (Or.inl ⟨rfl, Or.inl h_lifted_E'⟩) t'), ?_, ?_, ?_⟩
            · refine ⟨Or.inl ⟨?_, h_lifted_E⟩, ?_, h_lifted_E', ht'_dir⟩
              · rfl
              · rfl
            · simp only [Walk.length] at ht'_len ⊢
              omega
            -- vertices: q.vertices = toCopy0 W₁ u :: .unsplit vMid :: .unsplit vMid' :: t'.tail
            -- but t' is a cons starting at .unsplit vMid', so t'.vertices = .unsplit vMid' :: t'.tail
            -- and ht'_verts : t'.vertices = (vMid' :: p'''.vertices).map toCopy0
            -- = toCopy0 vMid' :: p'''.vertices.map toCopy0 = .unsplit vMid' :: ...
            -- p.vertices = u :: vMid :: vMid' :: p'''.vertices
            · change toCopy0 W₁ u :: SplitNode.unsplit vMid :: t'.vertices
                = (u :: vMid :: vMid' :: p'''.vertices).map (toCopy0 W₁)
              rw [ht'_verts, ← h_vMid_lift]
              -- Now goal: toCopy0 u :: toCopy0 vMid :: (vMid' :: p'''.vertices).map toCopy0
              --        = (u :: vMid :: vMid' :: p'''.vertices).map toCopy0
              rfl
          · have ha_pair : a = (u, vMid) := by
              have h1 : a.1 = u := congrArg Prod.fst ha_uv
              have h2 : a.2 = vMid := congrArg Prod.snd ha_uv
              exact Prod.ext h1 h2
            have h_in_L_pair : (u, vMid) ∈ G.L := by rw [← ha_pair]; exact ha_L
            have h_lifted_L : (toCopy0 W₁ u, toCopy0 W₁ vMid) ∈
                (G.nodeSplittingOn W₁ hW₁).L := lifted_L_in_split_L_generic h_in_L_pair
            rw [h_vMid_lift] at h_lifted_L
            refine ⟨Walk.cons (SplitNode.unsplit vMid)
              (toCopy0 W₁ u, SplitNode.unsplit vMid)
              (Or.inl ⟨rfl, Or.inr h_lifted_L⟩)
              (Walk.cons (SplitNode.unsplit vMid')
                (SplitNode.unsplit vMid, SplitNode.unsplit vMid')
                (Or.inl ⟨rfl, Or.inl h_lifted_E'⟩) t'), ?_, ?_, ?_⟩
            · refine ⟨Or.inr ⟨?_, h_lifted_L⟩, ?_, h_lifted_E', ht'_dir⟩
              · rfl
              · rfl
            · simp only [Walk.length] at ht'_len ⊢
              omega
            · change toCopy0 W₁ u :: SplitNode.unsplit vMid :: t'.vertices
                = (u :: vMid :: vMid' :: p'''.vertices).map (toCopy0 W₁)
              rw [ht'_verts, ← h_vMid_lift]
              rfl
  | u, _, .cons vMid a hStep (.nil _ _), k + 1, hi, _ => by
      -- nil tail with positive split index is impossible.
      simp only [Walk.IsBifurcationWithSplit] at hi
      exact hi.2.2.elim
  | u, _, .cons vMid a hStep (.cons vMid' a' hStep' p''), k + 1, hi, h_inter => by
      -- Left-arm step: a = (vMid, u), a ∈ G.E, rest is bif with split k.
      simp only [Walk.IsBifurcationWithSplit] at hi
      obtain ⟨ha_vu, ha_E, hi_rec⟩ := hi
      have hvMid_inW₂ : vMid ∈ W₂ := by
        apply h_inter
        change vMid ∈ (vMid :: p''.vertices).dropLast
        have hne : (p''.vertices : List Node) ≠ [] := Walk.vertices_ne_nil _
        rw [List.dropLast_cons_of_ne_nil hne]
        exact List.mem_cons_self
      have hvMid_notW : vMid ∉ W₁ :=
        Finset.disjoint_left.mp hDisj.symm hvMid_inW₂
      have h_vMid_lift : toCopy0 W₁ vMid = SplitNode.unsplit vMid :=
        toCopy0_unsplit_of_notW hvMid_notW
      have h_vMid_lift1 : toCopy1 W₁ vMid = SplitNode.unsplit vMid :=
        toCopy1_unsplit_of_notW hvMid_notW
      have ha_pair : a = (vMid, u) := by
        have h1 : a.1 = vMid := congrArg Prod.fst ha_vu
        have h2 : a.2 = u := congrArg Prod.snd ha_vu
        exact Prod.ext h1 h2
      have h_in_E_pair : (vMid, u) ∈ G.E := by rw [← ha_pair]; exact ha_E
      -- Convert the lifted edge to use `toCopy0 W₁ vMid` as its first component
      -- (matches s''s source type, avoiding a `rw at s'` that would orphan
      -- `hs'_split` / `hs'_len` to inaccessible `s'✝`).
      have h_lifted_E_raw : (toCopy1 W₁ vMid, toCopy0 W₁ u) ∈
          (G.nodeSplittingOn W₁ hW₁).E := lifted_E_in_split_E_generic h_in_E_pair
      have h_lifted_E : (toCopy0 W₁ vMid, toCopy0 W₁ u) ∈
          (G.nodeSplittingOn W₁ hW₁).E := by
        rw [h_vMid_lift1, ← h_vMid_lift] at h_lifted_E_raw
        exact h_lifted_E_raw
      have h_inter_p' :
          ∀ x ∈ (Walk.cons (G := G) vMid' a' hStep' p'').vertices.tail.dropLast,
            x ∈ W₂ := by
        intro x hx
        apply h_inter
        change x ∈ (vMid :: p''.vertices).dropLast
        have hne : (p''.vertices : List Node) ≠ [] := Walk.vertices_ne_nil _
        rw [List.dropLast_cons_of_ne_nil hne]
        refine List.mem_cons_of_mem _ ?_
        change x ∈ p''.vertices.dropLast
        exact hx
      obtain ⟨s', hs'_split, hs'_len, hs'_verts⟩ :=
        exists_lifted_bifWithSplit_to_split hW₁ hDisj
          (Walk.cons vMid' a' hStep' p'') k hi_rec h_inter_p'
      -- Keep s' at its original type Walk split (toCopy0 W₁ vMid) (toCopy0 W₁ v).
      refine ⟨Walk.cons (toCopy0 W₁ vMid)
        (toCopy0 W₁ vMid, toCopy0 W₁ u)
        (Or.inr ⟨rfl, h_lifted_E⟩) s', ?_, ?_, ?_⟩
      · simp only [Walk.IsBifurcationWithSplit]
        exact ⟨trivial, h_lifted_E, hs'_split⟩
      · change s'.length + 1 = (Walk.cons vMid' a' hStep' p'').length + 1
        rw [hs'_len]
      -- vertices: q.vertices = toCopy0 W₁ u :: s'.vertices
      --   = toCopy0 W₁ u :: (vMid :: p''.vertices).map toCopy0
      -- p.vertices = u :: vMid :: p''.vertices, mapped accordingly.
      · change toCopy0 W₁ u :: s'.vertices
            = toCopy0 W₁ u :: (Walk.cons (G := G) vMid' a' hStep' p'').vertices.map (toCopy0 W₁)
        rw [hs'_verts]

-- ## Helper 3: bifurcation lift (combining helpers).  Wraps Helper 2 by
-- extracting the split index and rebuilding the IsBifurcation conjunction.
-- The vertex constraints follow because every interior vertex in the lifted
-- walk is `.unsplit`-tagged (by Helper 1's all-.unsplit-interior structure
-- and Helper 2's all-.unsplit-interior structure).  We restate the constraint
-- via a vertex-list-tracking argument on the lifted walk.
private lemma exists_lifted_bif_to_split
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsBifurcation →
      (∀ x ∈ p.vertices.tail.dropLast, x ∈ W₂) →
      ∃ (q : Walk (G.nodeSplittingOn W₁ hW₁) (toCopy0 W₁ u) (toCopy0 W₁ v)),
        q.IsBifurcation ∧ (∀ x ∈ q.vertices.tail.dropLast, x ∈ W₂.image SplitNode.unsplit) := by
  intro u v p hp_bif h_inter
  obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hp_bif
  obtain ⟨q, hq_split, _hq_len, hq_verts⟩ :=
    exists_lifted_bifWithSplit_to_split hW₁ hDisj p i hi h_inter
  -- Vertex-list list-utility analogues for `toCopy0 W₁` (not just `.unsplit`).
  have h_tail_map : ∀ (l : List Node),
      (l.map (toCopy0 W₁)).tail = l.tail.map (toCopy0 W₁) := by
    intro l; cases l with
    | nil => rfl
    | cons _ _ => rfl
  have h_dropLast_map : ∀ (l : List Node),
      (l.map (toCopy0 W₁)).dropLast = l.dropLast.map (toCopy0 W₁) := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
        cases xs with
        | nil => rfl
        | cons y ys =>
            simp only [List.map_cons, List.dropLast_cons₂]
            change _ :: (((y :: ys).map (toCopy0 W₁)).dropLast)
                = _ :: ((y :: ys).dropLast.map (toCopy0 W₁))
            rw [ih]
  refine ⟨q, ⟨?_, ?_, ?_, i, hq_split⟩, ?_⟩
  · -- toCopy0 W₁ u ≠ toCopy0 W₁ v
    intro h_eq
    exact hne (toCopy0_inj_node h_eq)
  · -- toCopy0 W₁ u ∉ q.vertices.tail
    intro h_mem
    rw [hq_verts, h_tail_map] at h_mem
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h_mem
    have : a = u := toCopy0_inj_node ha_eq
    exact hu_tail (this ▸ ha_in)
  · -- toCopy0 W₁ v ∉ q.vertices.dropLast
    intro h_mem
    rw [hq_verts, h_dropLast_map] at h_mem
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h_mem
    have : a = v := toCopy0_inj_node ha_eq
    exact hv_drop (this ▸ ha_in)
  · -- ∀ x ∈ q.vertices.tail.dropLast, x ∈ W₂.image .unsplit
    intro x hx
    -- Decode x: by vertex correspondence, x = toCopy0 W₁ y for some y ∈ p.vertices.tail.dropLast.
    have h_interior_map :
        q.vertices.tail.dropLast = p.vertices.tail.dropLast.map (toCopy0 W₁) := by
      rw [hq_verts, h_tail_map, h_dropLast_map]
    rw [h_interior_map] at hx
    obtain ⟨y, hy_in, hy_eq⟩ := List.mem_map.mp hx
    have hy_inW₂ : y ∈ W₂ := h_inter y hy_in
    have hy_notW₁ : y ∉ W₁ := Finset.disjoint_left.mp hDisj.symm hy_inW₂
    have h_y_lift : toCopy0 W₁ y = SplitNode.unsplit y := toCopy0_unsplit_of_notW hy_notW₁
    rw [← hy_eq, h_y_lift]
    exact Finset.mem_image.mpr ⟨y, hy_inW₂, rfl⟩

-- ## Helper: a directed walk in split from `.copy0 w` (for `w ∈ W₁`)
-- with interior in `W₂.image .unsplit` (and `Disjoint W₁ W₂`) forces target
-- to be `.copy1 w` (i.e., is the single transfer edge).
--
-- Analogue of Part (ii)'s `walk_intCopy_target_unsplit`: the only outgoing
-- edge from `.copy0 w` in `split.E` is either the transfer edge
-- `(.copy0 w, .copy1 w)` or a lifted G-edge `(toCopy1 W₁ a, toCopy0 W₁ b)`
-- with `toCopy1 W₁ a = .copy0 w` — but `toCopy1 W₁ a ∈ {.unsplit a, .copy1 a}`,
-- never `.copy0`, so the lifted-edge case is impossible.  Hence the first
-- (and, by the interior constraint, only) edge is the transfer edge.
private lemma walk_copy0_target_copy1 {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {W₂ : Finset Node} (hDisj : Disjoint W₁ W₂)
    {w : Node} (hwW₁ : w ∈ W₁) {y : SplitNode Node}
    (p : Walk (G.nodeSplittingOn W₁ hW₁) (SplitNode.copy0 w) y)
    (hp_dir : p.IsDirectedWalk)
    (hp_pos : p.length ≥ 1)
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast,
      z ∈ W₂.image SplitNode.unsplit) :
    y = SplitNode.copy1 w := by
  cases p with
  | nil _ _ => simp [Walk.length] at hp_pos
  | @cons _ _ mid a hStep p' =>
      simp only [Walk.IsDirectedWalk] at hp_dir
      obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir
      change a ∈ G.E.image _ ∪ W₁.image _ at ha_E
      rcases Finset.mem_union.mp ha_E with hLift | hTrans
      · -- a = (toCopy1 W₁ e'.1, toCopy0 W₁ e'.2) for some (e'.1, e'.2) ∈ G.E.
        -- But a.1 = .copy0 w, and toCopy1 W₁ e'.1 ∈ {.unsplit, .copy1}, never .copy0.
        obtain ⟨e', _, he'_eq⟩ := Finset.mem_image.mp hLift
        rw [ha_eq] at he'_eq
        have hcontra : toCopy1 W₁ e'.1 = SplitNode.copy0 w :=
          congrArg Prod.fst he'_eq
        unfold toCopy1 at hcontra
        by_cases hW : e'.1 ∈ W₁
        · rw [if_pos hW] at hcontra; cases hcontra
        · rw [if_neg hW] at hcontra; cases hcontra
      · -- a = (.copy0 w', .copy1 w') for some w' ∈ W₁. Match w' = w.
        obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp hTrans
        rw [ha_eq] at hw'_eq
        have h1 : SplitNode.copy0 w' = SplitNode.copy0 w :=
          congrArg Prod.fst hw'_eq
        have h2 : SplitNode.copy1 w' = mid :=
          congrArg Prod.snd hw'_eq
        have hww' : w' = w := by injection h1
        rw [hww'] at h2
        have hmid : mid = SplitNode.copy1 w := h2.symm
        subst hmid
        -- Now p' : Walk split (.copy1 w) y.  Show p' is nil (so y = .copy1 w).
        cases p' with
        | nil _ _ => rfl
        | @cons _ _ mid2 a2 hStep2 p2 =>
            -- p' = cons mid2 a2 hStep2 p2, so the walk has length ≥ 2.
            -- The vertex `.copy1 w` is in tail.dropLast, but it's not .unsplit,
            -- contradiction with hp_inter.
            have h_pv_ne : p2.vertices ≠ [] := Walk.vertices_ne_nil p2
            have h_w_inter : SplitNode.copy1 w ∈
                (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                  (SplitNode.copy1 w) a hStep
                  (Walk.cons mid2 a2 hStep2 p2)).vertices.tail.dropLast := by
              change SplitNode.copy1 w ∈ (SplitNode.copy0 w
                :: SplitNode.copy1 w :: p2.vertices).tail.dropLast
              rw [show (SplitNode.copy0 w :: SplitNode.copy1 w
                          :: p2.vertices : List _).tail
                      = SplitNode.copy1 w :: p2.vertices from rfl]
              rw [List.dropLast_cons_of_ne_nil h_pv_ne]
              exact List.mem_cons_self
            have h_in_image := hp_inter (SplitNode.copy1 w) h_w_inter
            obtain ⟨w'', _, hw''_eq⟩ := Finset.mem_image.mp h_in_image
            cases hw''_eq

-- ## Walk ascent: lift G-walk to split with `toCopy1/toCopy0` endpoints.
--
-- Given a G-walk `q : Walk G u v` of positive length (directed, interior in W₂),
-- produce a split-walk from `toCopy1 W₁ u` to `toCopy0 W₁ v` with interior in
-- `W₂.image .unsplit`.  Each step lifts the underlying G-edge to its lifted form
-- `(toCopy1 W₁ a, toCopy0 W₁ b)` ∈ split.E via `lifted_E_in_split_E_generic`.
-- The length-positivity is required: a 0-length lift would need a walk from
-- `toCopy1 W₁ u` to `toCopy0 W₁ u`, which doesn't exist when u ∈ W₁
-- (then `.copy1 u` ≠ `.copy0 u`).
private lemma walk_G_lift_to_split
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {u v : Node} (q : Walk G u v),
      q.IsDirectedWalk →
      q.length ≥ 1 →
      (∀ z ∈ q.vertices.tail.dropLast, z ∈ W₂) →
      ∃ p : Walk (G.nodeSplittingOn W₁ hW₁) (toCopy1 W₁ u) (toCopy0 W₁ v),
        p.IsDirectedWalk ∧ p.length = q.length ∧
        (∀ x ∈ p.vertices.tail.dropLast, x ∈ W₂.image SplitNode.unsplit)
  | _, _, .nil _ _, _, hpos, _ => by
      simp [Walk.length] at hpos
  | u, _, .cons w a hStep (.nil _ hw_in), hq_dir, _, _ => by
      -- Single-edge walk: q = cons w (u, w) (nil w hw_in), target = w.
      simp only [Walk.IsDirectedWalk] at hq_dir
      obtain ⟨ha_eq, ha_E, _⟩ := hq_dir
      have ha_pair : a = (u, w) := by
        have h1 : a.1 = u := congrArg Prod.fst ha_eq
        have h2 : a.2 = w := congrArg Prod.snd ha_eq
        exact Prod.ext h1 h2
      have h_uw_E : (u, w) ∈ G.E := by rw [← ha_pair]; exact ha_E
      have h_lifted_E : (toCopy1 W₁ u, toCopy0 W₁ w) ∈
          (G.nodeSplittingOn W₁ hW₁).E :=
        lifted_E_in_split_E_generic h_uw_E
      have h_w_in_split : toCopy0 W₁ w ∈ G.nodeSplittingOn W₁ hW₁ :=
        mem_split_of_mem_G_toCopy0 (hW₁ := hW₁) hw_in
      refine ⟨Walk.cons (toCopy0 W₁ w) (toCopy1 W₁ u, toCopy0 W₁ w)
        (Or.inl ⟨rfl, Or.inl h_lifted_E⟩)
        (Walk.nil (toCopy0 W₁ w) h_w_in_split),
        ⟨rfl, h_lifted_E, trivial⟩, by change 1 = 0 + 1; omega, ?_⟩
      intro x hx
      simp [Walk.vertices, List.tail, List.dropLast] at hx
  | u, _, .cons w a hStep (.cons w2 a2 hStep2 q2), hq_dir, _, hq_inter => by
      -- Multi-edge walk: q = cons w (u, w) (cons w2 a2 hStep2 q2).
      simp only [Walk.IsDirectedWalk] at hq_dir
      obtain ⟨ha_eq, ha_E, hq'_dir⟩ := hq_dir
      have ha_pair : a = (u, w) := by
        have h1 : a.1 = u := congrArg Prod.fst ha_eq
        have h2 : a.2 = w := congrArg Prod.snd ha_eq
        exact Prod.ext h1 h2
      have h_uw_E : (u, w) ∈ G.E := by rw [← ha_pair]; exact ha_E
      have h_lifted_E : (toCopy1 W₁ u, toCopy0 W₁ w) ∈
          (G.nodeSplittingOn W₁ hW₁).E :=
        lifted_E_in_split_E_generic h_uw_E
      have h_qv_ne : q2.vertices ≠ [] := Walk.vertices_ne_nil q2
      have hw_inW₂ : w ∈ W₂ := by
        apply hq_inter
        change w ∈ (w :: q2.vertices).dropLast
        rw [List.dropLast_cons_of_ne_nil h_qv_ne]
        exact List.mem_cons_self
      have hw_notW₁ : w ∉ W₁ :=
        Finset.disjoint_left.mp hDisj.symm hw_inW₂
      have h_w_lift0 : toCopy0 W₁ w = SplitNode.unsplit w :=
        toCopy0_unsplit_of_notW hw_notW₁
      have h_w_lift1 : toCopy1 W₁ w = SplitNode.unsplit w :=
        toCopy1_unsplit_of_notW hw_notW₁
      have hq'_inter_aux :
          ∀ z ∈ (Walk.cons (G := G) w2 a2 hStep2 q2).vertices.tail.dropLast,
            z ∈ W₂ := by
        intro z hz
        apply hq_inter
        change z ∈ (w :: q2.vertices).dropLast
        rw [List.dropLast_cons_of_ne_nil h_qv_ne]
        refine List.mem_cons_of_mem _ ?_
        change z ∈ q2.vertices.dropLast
        exact hz
      have h_q'_pos : (Walk.cons (G := G) w2 a2 hStep2 q2).length ≥ 1 := by
        change q2.length + 1 ≥ 1; omega
      obtain ⟨p', hp'_dir, hp'_len, hp'_inter⟩ :=
        walk_G_lift_to_split hW₁ hDisj (Walk.cons w2 a2 hStep2 q2) hq'_dir h_q'_pos hq'_inter_aux
      have h_lifted_E' : (toCopy1 W₁ u, toCopy1 W₁ w) ∈
          (G.nodeSplittingOn W₁ hW₁).E := by
        rw [h_w_lift1, ← h_w_lift0]; exact h_lifted_E
      refine ⟨Walk.cons (toCopy1 W₁ w) (toCopy1 W₁ u, toCopy1 W₁ w)
        (Or.inl ⟨rfl, Or.inl h_lifted_E'⟩) p',
        ⟨rfl, h_lifted_E', hp'_dir⟩, ?_, ?_⟩
      · change p'.length + 1 = (Walk.cons (G := G) w2 a2 hStep2 q2).length + 1
        rw [hp'_len]
      · intro x hx
        change x ∈ p'.vertices.dropLast at hx
        have h_p'_pos : p'.length ≥ 1 := by rw [hp'_len]; exact h_q'_pos
        have h_p'_tail_ne : p'.vertices.tail ≠ [] :=
          Walk.tail_vertices_ne_nil_of_pos p' h_p'_pos
        rw [Walk.vertices_eq_head_cons_tail p'] at hx
        rw [List.dropLast_cons_of_ne_nil h_p'_tail_ne] at hx
        rcases List.mem_cons.mp hx with hx_head | hx_tail
        · rw [hx_head]; rw [h_w_lift1]
          exact Finset.mem_image.mpr ⟨w, hw_inW₂, rfl⟩
        · exact hp'_inter x hx_tail

-- ## Walk descent: split → G with `toCopy1/toCopy0` endpoints.
--
-- Dual to `walk_G_lift_to_split`.  Given a split walk `p : Walk split x y` with
-- `x = toCopy1 W₁ u` and `y = toCopy0 W₁ v`, directed, interior in
-- `W₂.image .unsplit`, produce a G-walk `q : Walk G u v` of equal length with
-- interior in W₂.  The key observation: the source `toCopy1 W₁ u` is never a
-- `.copy0` constructor (it's `.unsplit` or `.copy1`), so no transfer edge can
-- start at `x`; every edge is a lifted G-edge.  Interior `.unsplit z` (z ∈ W₂,
-- so z ∉ W₁) acts as `toCopy1 W₁ z = toCopy0 W₁ z`, allowing the recursion to
-- continue with the same `toCopy1/toCopy0` discipline.
private lemma walk_split_descend_to_G
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {x y : SplitNode Node} (p : Walk (G.nodeSplittingOn W₁ hW₁) x y),
      p.IsDirectedWalk →
      (∀ z ∈ p.vertices.tail.dropLast, z ∈ W₂.image SplitNode.unsplit) →
      ∀ {u v : Node}, x = toCopy1 W₁ u → y = toCopy0 W₁ v →
      ∃ q : Walk G u v, q.IsDirectedWalk ∧ q.length = p.length ∧
        (∀ z ∈ q.vertices.tail.dropLast, z ∈ W₂)
  | _, _, .nil w hw, _, _, u, v, hxu, hyv => by
      have hCopy_eq : toCopy1 W₁ u = toCopy0 W₁ v := hxu.symm.trans hyv
      by_cases huW : u ∈ W₁
      · have h1 : toCopy1 W₁ u = SplitNode.copy1 u := by
          unfold toCopy1; rw [if_pos huW]
        rw [h1] at hCopy_eq
        unfold toCopy0 at hCopy_eq
        by_cases hvW : v ∈ W₁
        · rw [if_pos hvW] at hCopy_eq; cases hCopy_eq
        · rw [if_neg hvW] at hCopy_eq; cases hCopy_eq
      · have h1 : toCopy1 W₁ u = SplitNode.unsplit u :=
          toCopy1_unsplit_of_notW huW
        rw [h1] at hCopy_eq
        unfold toCopy0 at hCopy_eq
        by_cases hvW : v ∈ W₁
        · rw [if_pos hvW] at hCopy_eq; cases hCopy_eq
        · rw [if_neg hvW] at hCopy_eq
          have huv : u = v := by injection hCopy_eq
          subst huv
          have hu_G : u ∈ G := by
            have hu_in_split : SplitNode.unsplit u ∈ G.nodeSplittingOn W₁ hW₁ := by
              rw [← h1, ← hxu]; exact hw
            exact mem_G_of_unsplit_mem_split hW₁ hu_in_split
          refine ⟨Walk.nil u hu_G, trivial, rfl, ?_⟩
          intro x hx
          simp [Walk.vertices, List.tail, List.dropLast] at hx
  | x, _, .cons mid a hStep (.nil _ hmid_in), hp_dir, _, u, v, hxu, hyv => by
      -- Single-edge split walk: source x → mid, then nil at mid.  So target = mid.
      -- The cons's hStep tells us a ∈ split.E and a = (x, mid).
      simp only [Walk.IsDirectedWalk] at hp_dir
      obtain ⟨ha_eq, ha_E, _⟩ := hp_dir
      change a ∈ G.E.image _ ∪ W₁.image _ at ha_E
      rcases Finset.mem_union.mp ha_E with hLift | hTrans
      · obtain ⟨e', he'_E, he'_eq⟩ := Finset.mem_image.mp hLift
        rw [ha_eq] at he'_eq
        have h_e1 : toCopy1 W₁ e'.1 = x := congrArg Prod.fst he'_eq
        have h_e2 : toCopy0 W₁ e'.2 = mid := congrArg Prod.snd he'_eq
        rw [hxu] at h_e1
        have he'1 : e'.1 = u := by
          unfold toCopy1 at h_e1
          by_cases hW₁_e' : e'.1 ∈ W₁
          · by_cases hW₁_u : u ∈ W₁
            · rw [if_pos hW₁_e', if_pos hW₁_u] at h_e1; injection h_e1
            · rw [if_pos hW₁_e', if_neg hW₁_u] at h_e1; cases h_e1
          · by_cases hW₁_u : u ∈ W₁
            · rw [if_neg hW₁_e', if_pos hW₁_u] at h_e1; cases h_e1
            · rw [if_neg hW₁_e', if_neg hW₁_u] at h_e1; injection h_e1
        -- Nil's source = target = mid, so toCopy0 W₁ v = mid.
        -- Hence toCopy0 W₁ e'.2 = mid = toCopy0 W₁ v ⇒ e'.2 = v.
        have h_e2v : toCopy0 W₁ e'.2 = toCopy0 W₁ v := by
          rw [h_e2]; exact hyv
        have he'2 : e'.2 = v := toCopy0_inj_node h_e2v
        -- Build (u, v) ∈ G.E from e' = (u, v).
        have h_uv_E : (u, v) ∈ G.E := by
          have h_eq : (u, v) = e' := by
            ext
            · exact he'1.symm
            · exact he'2.symm
          rw [h_eq]; exact he'_E
        obtain ⟨_, hv_G⟩ := G.hE_subset h_uv_E
        refine ⟨Walk.cons v (u, v) (Or.inl ⟨rfl, Or.inl h_uv_E⟩)
          (Walk.nil v (Finset.mem_union_right _ hv_G)),
          ⟨rfl, h_uv_E, trivial⟩, by change 1 = 0 + 1; omega, ?_⟩
        intro x hx
        simp [Walk.vertices, List.tail, List.dropLast] at hx
      · obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hTrans
        rw [ha_eq] at hw'_eq
        have hcontra : SplitNode.copy0 w' = x :=
          congrArg Prod.fst hw'_eq
        rw [hxu] at hcontra
        unfold toCopy1 at hcontra
        by_cases hW1 : u ∈ W₁
        · rw [if_pos hW1] at hcontra; cases hcontra
        · rw [if_neg hW1] at hcontra; cases hcontra
  | x, _, .cons mid a hStep (.cons mid2 a2 hStep2 p2), hp_dir, hp_inter, u, v, hxu, hyv => by
      -- Multi-edge split walk: source x → mid → mid2 → ... → target.
      simp only [Walk.IsDirectedWalk] at hp_dir
      obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir
      change a ∈ G.E.image _ ∪ W₁.image _ at ha_E
      rcases Finset.mem_union.mp ha_E with hLift | hTrans
      · obtain ⟨e', he'_E, he'_eq⟩ := Finset.mem_image.mp hLift
        rw [ha_eq] at he'_eq
        have h_e1 : toCopy1 W₁ e'.1 = x := congrArg Prod.fst he'_eq
        have h_e2 : toCopy0 W₁ e'.2 = mid := congrArg Prod.snd he'_eq
        rw [hxu] at h_e1
        have he'1 : e'.1 = u := by
          unfold toCopy1 at h_e1
          by_cases hW₁_e' : e'.1 ∈ W₁
          · by_cases hW₁_u : u ∈ W₁
            · rw [if_pos hW₁_e', if_pos hW₁_u] at h_e1; injection h_e1
            · rw [if_pos hW₁_e', if_neg hW₁_u] at h_e1; cases h_e1
          · by_cases hW₁_u : u ∈ W₁
            · rw [if_neg hW₁_e', if_pos hW₁_u] at h_e1; cases h_e1
            · rw [if_neg hW₁_e', if_neg hW₁_u] at h_e1; injection h_e1
        have h_pv_ne : p2.vertices ≠ [] := Walk.vertices_ne_nil p2
        have hmid_inter : mid ∈ W₂.image SplitNode.unsplit := by
          apply hp_inter
          change mid ∈ (mid :: p2.vertices).dropLast
          rw [List.dropLast_cons_of_ne_nil h_pv_ne]
          exact List.mem_cons_self
        obtain ⟨z, hzW₂, hz_eq⟩ := Finset.mem_image.mp hmid_inter
        have hz_notW₁ : z ∉ W₁ :=
          Finset.disjoint_left.mp hDisj.symm hzW₂
        have h_z_lift : toCopy0 W₁ z = SplitNode.unsplit z :=
          toCopy0_unsplit_of_notW hz_notW₁
        have he'2_eq : toCopy0 W₁ e'.2 = toCopy0 W₁ z := by
          rw [h_e2, ← hz_eq, h_z_lift]
        have he'2 : e'.2 = z := toCopy0_inj_node he'2_eq
        have h_uz_E : (u, z) ∈ G.E := by
          have h_eq : (u, z) = e' := by
            ext
            · exact he'1.symm
            · exact he'2.symm
          rw [h_eq]; exact he'_E
        have h_z_lift1 : toCopy1 W₁ z = SplitNode.unsplit z :=
          toCopy1_unsplit_of_notW hz_notW₁
        have hp'_inter : ∀ x ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 a2 hStep2 p2).vertices.tail.dropLast,
            x ∈ W₂.image SplitNode.unsplit := by
          intro x hx
          apply hp_inter
          change x ∈ (mid :: p2.vertices).dropLast
          rw [List.dropLast_cons_of_ne_nil h_pv_ne]
          refine List.mem_cons_of_mem _ ?_
          change x ∈ p2.vertices.dropLast
          exact hx
        -- Source of (cons mid2 a2 hStep2 p2) = mid = .unsplit z = toCopy1 W₁ z.
        obtain ⟨q', hq'_dir, hq'_len, hq'_inter⟩ :=
          walk_split_descend_to_G hW₁ hDisj
            (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 a2 hStep2 p2)
            hp'_dir hp'_inter (hz_eq.symm.trans h_z_lift1.symm) hyv
        refine ⟨Walk.cons z (u, z) (Or.inl ⟨rfl, Or.inl h_uz_E⟩) q',
          ⟨rfl, h_uz_E, hq'_dir⟩, ?_, ?_⟩
        · change q'.length + 1 = (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 a2 hStep2 p2).length + 1
          rw [hq'_len]
        · intro x hx
          change x ∈ q'.vertices.dropLast at hx
          have h_q'_pos : q'.length ≥ 1 := by
            rw [hq'_len]; change p2.length + 1 ≥ 1; omega
          have h_q'_tail_ne : q'.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos q' h_q'_pos
          rw [Walk.vertices_eq_head_cons_tail q'] at hx
          rw [List.dropLast_cons_of_ne_nil h_q'_tail_ne] at hx
          rcases List.mem_cons.mp hx with hx_z | hx_tail
          · rw [hx_z]; exact hzW₂
          · exact hq'_inter x hx_tail
      · -- Transfer edge case: a is (.copy0 w', .copy1 w'), but a.1 = x = toCopy1 W₁ u, never .copy0.
        obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hTrans
        rw [ha_eq] at hw'_eq
        have hcontra : SplitNode.copy0 w' = x :=
          congrArg Prod.fst hw'_eq
        rw [hxu] at hcontra
        unfold toCopy1 at hcontra
        by_cases hW1 : u ∈ W₁
        · rw [if_pos hW1] at hcontra; cases hcontra
        · rw [if_neg hW1] at hcontra; cases hcontra

-- ## The Part (iii) Φ_E iff for `toCopy1`-source / `toCopy0`-target.
--
-- Direct bijection between a directed walk in `G.nodeSplittingOn W₁ hW₁` from
-- `toCopy1 W₁ u` to `toCopy0 W₁ v` (interior in `W₂.image .unsplit`) and a
-- directed walk in `G` from `u` to `v` (interior in `W₂`).  Uses the descent
-- and ascent helpers above.
private lemma split_marg_PhiE_iff
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) {u v : Node} :
    (G.nodeSplittingOn W₁ hW₁).MarginalizationΦE (W₂.image SplitNode.unsplit)
        (toCopy1 W₁ u) (toCopy0 W₁ v) ↔
      G.MarginalizationΦE W₂ u v := by
  constructor
  · rintro ⟨p, hp_dir, hp_pos, hp_inter⟩
    obtain ⟨q, hq_dir, hq_len, hq_inter⟩ :=
      walk_split_descend_to_G hW₁ hDisj p hp_dir hp_inter rfl rfl
    refine ⟨q, hq_dir, ?_, hq_inter⟩
    rw [hq_len]; exact hp_pos
  · rintro ⟨q, hq_dir, hq_pos, hq_inter⟩
    obtain ⟨p, hp_dir, hp_len, hp_inter⟩ :=
      walk_G_lift_to_split hW₁ hDisj q hq_dir hq_pos hq_inter
    refine ⟨p, hp_dir, ?_, hp_inter⟩
    rw [hp_len]; exact hq_pos

-- ## Helper: a directed walk in split ending at `.copy1 w` (for `w ∈ W₁`),
-- with positive length and interior in `W₂.image .unsplit`, has its source equal
-- to `.copy0 w` (and is the single transfer edge).
--
-- Symmetric / dual to `walk_copy0_target_copy1`: the only incoming edge to
-- `.copy1 w` in `split.E` is either the transfer edge `(.copy0 w, .copy1 w)`
-- or a lifted G-edge `(toCopy1 W₁ a, toCopy0 W₁ b)` with `toCopy0 W₁ b = .copy1 w` —
-- but `toCopy0 W₁ b ∈ {.copy0 b, .unsplit b}`, never `.copy1`, so the lifted-edge
-- case is impossible.  Hence the last edge into `.copy1 w` is the transfer edge,
-- and any preceding edges must have been impossible (since interior `.unsplit z`
-- can't be `.copy0 w`).
private lemma walk_target_copy1_source_copy0
    {G : CDMG Node} {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V} {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {x : SplitNode Node} {w : Node}, w ∈ W₁ →
      (p : Walk (G.nodeSplittingOn W₁ hW₁) x (SplitNode.copy1 w)) →
      p.IsDirectedWalk → p.length ≥ 1 →
      (∀ z ∈ p.vertices.tail.dropLast, z ∈ W₂.image SplitNode.unsplit) →
      x = SplitNode.copy0 w
  | _, _, _, .nil _ _, _, hp_pos, _ => by
      simp [Walk.length] at hp_pos
  | x, w, _, .cons _ a hStep (.nil _ _), hp_dir, _, _ => by
      -- Single edge x → mid where mid = .copy1 w (target of nil = source of nil = mid).
      simp only [Walk.IsDirectedWalk] at hp_dir
      obtain ⟨ha_eq, ha_E, _⟩ := hp_dir
      change a ∈ G.E.image _ ∪ W₁.image _ at ha_E
      rcases Finset.mem_union.mp ha_E with hLift | hTrans
      · obtain ⟨e', _, he'_eq⟩ := Finset.mem_image.mp hLift
        rw [ha_eq] at he'_eq
        have h_e2 : toCopy0 W₁ e'.2 = SplitNode.copy1 w :=
          congrArg Prod.snd he'_eq
        exact absurd h_e2 toCopy0_ne_copy1
      · obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hTrans
        rw [ha_eq] at hw'_eq
        have h_e2 : SplitNode.copy1 w' = SplitNode.copy1 w :=
          congrArg Prod.snd hw'_eq
        have h_e1 : SplitNode.copy0 w' = x :=
          congrArg Prod.fst hw'_eq
        have : w' = w := by injection h_e2
        rw [this] at h_e1
        exact h_e1.symm
  | x, w, hwW₁, .cons mid a hStep (.cons mid2 a2 hStep2 p2), hp_dir, _, hp_inter => by
      -- Multi-edge walk: first edge x → mid, then mid → mid2 → ... → .copy1 w.
      -- The first edge ends at mid, which is interior (= .unsplit z for z ∈ W₂).
      simp only [Walk.IsDirectedWalk] at hp_dir
      obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir
      have h_pv_ne : p2.vertices ≠ [] := Walk.vertices_ne_nil p2
      have hmid_inter : mid ∈ W₂.image SplitNode.unsplit := by
        apply hp_inter
        change mid ∈ (mid :: p2.vertices).dropLast
        rw [List.dropLast_cons_of_ne_nil h_pv_ne]
        exact List.mem_cons_self
      obtain ⟨z, hzW₂, hz_eq⟩ := Finset.mem_image.mp hmid_inter
      have hz_notW₁ : z ∉ W₁ :=
        Finset.disjoint_left.mp hDisj.symm hzW₂
      change a ∈ G.E.image _ ∪ W₁.image _ at ha_E
      rcases Finset.mem_union.mp ha_E with hLift | hTrans
      · -- First edge is lifted; mid = toCopy0 W₁ e'.2.  Need to recursively handle the rest.
        -- The rest p' = (cons mid2 a2 hStep2 p2) has source mid = .unsplit z.
        -- Apply IH: rest's source must be .copy0 w.  So .unsplit z = .copy0 w, impossible.
        have h_p'_pos : (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 a2 hStep2 p2).length ≥ 1 := by
          change p2.length + 1 ≥ 1; omega
        have hp'_inter : ∀ z' ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 a2 hStep2 p2).vertices.tail.dropLast,
            z' ∈ W₂.image SplitNode.unsplit := by
          intro z' hz'
          apply hp_inter
          change z' ∈ (mid :: p2.vertices).dropLast
          rw [List.dropLast_cons_of_ne_nil h_pv_ne]
          refine List.mem_cons_of_mem _ ?_
          change z' ∈ p2.vertices.dropLast
          exact hz'
        have h_rec :
            mid = SplitNode.copy0 w :=
          walk_target_copy1_source_copy0 hDisj hwW₁
            (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 a2 hStep2 p2)
            hp'_dir h_p'_pos hp'_inter
        -- mid = .unsplit z = .copy0 w; impossible.
        rw [h_rec] at hz_eq
        cases hz_eq
      · -- First edge is transfer; mid = .copy1 w' for some w' ∈ W₁.
        -- But mid is interior = .unsplit z; .copy1 w' = .unsplit z impossible.
        obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hTrans
        rw [ha_eq] at hw'_eq
        have h_e2 : SplitNode.copy1 w' = mid :=
          congrArg Prod.snd hw'_eq
        rw [← hz_eq] at h_e2
        cases h_e2

-- ## E-field equality for Part (iii).
--
-- Mirrors Part (ii)'s `ext_marg_E_field_eq`.  The carrier of the LHS includes
-- a `W₁.image .copy0` summand (transfer-edge source), handled separately via
-- `walk_copy0_target_copy1` (forces target = `.copy1 w` for the same w).  The
-- other sources (`.unsplit j ∈ G.J`, `.unsplit v' ∈ (G.V \ W₁) \ W₂`, `.copy1 w`)
-- all factor through `toCopy1 W₁`, and `split_marg_PhiE_iff` bridges them to the
-- G-side Φ_E predicate.
set_option maxHeartbeats 800000 in
-- The `change`/`rw` cascade unfolds nested `marginalize`/`nodeSplittingOn` field
-- definitions and case-splits on five carrier-shape combinations (J-source,
-- unsplit/copy0/copy1-source × unsplit/copy0/copy1-target); the default
-- heartbeats are insufficient for the elaborator's whnf reduction work.
private lemma split_marg_E_field_eq
    {G : CDMG Node} (W₁ : Finset Node) (hW₁ : W₁ ⊆ G.V)
    (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    ((G.nodeSplittingOn W₁ hW₁).marginalize (W₂.image SplitNode.unsplit)
        (image_unsplit_subset_nodeSplittingOn_V_of_disjoint hW₁ hW₂ hDisj.symm)).E
      = ((G.marginalize W₂ hW₂).nodeSplittingOn W₁
        (subset_sdiff_of_disjoint hW₁ hDisj)).E := by
  apply Finset.ext
  rintro ⟨e1, e2⟩
  -- LHS: filter (predicates : Φ_E on split) over (J ∪ V_marg) ×ˢ V_marg.
  --   where V_marg = ((G.V \ W₁).image .unsplit ∪ W₁.image .copy0 ∪ W₁.image .copy1) \ W₂.image .unsplit.
  -- RHS: ((G.marginalize W₂).E).image (toCopy1 W₁, toCopy0 W₁) ∪ W₁.image (.copy0, .copy1).
  change
    (e1, e2) ∈ ((G.J.image SplitNode.unsplit ∪
            ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
              ∪ W₁.image SplitNode.copy1) \ W₂.image SplitNode.unsplit)
          ×ˢ (((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
                ∪ W₁.image SplitNode.copy1) \ W₂.image SplitNode.unsplit)).filter
        (fun e => (G.nodeSplittingOn W₁ hW₁).MarginalizationΦE
                    (W₂.image SplitNode.unsplit) e.1 e.2)
    ↔ (e1, e2) ∈ (((G.J ∪ (G.V \ W₂)) ×ˢ (G.V \ W₂)).filter
              (fun e => G.MarginalizationΦE W₂ e.1 e.2)).image
            (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))
        ∪ W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
  rw [Finset.mem_filter, Finset.mem_product]
  constructor
  · -- Forward direction.
    rintro ⟨⟨h1, h2⟩, hPhi⟩
    -- Case-split on e2's piece.
    obtain ⟨h2_in_V, h2_notW₂⟩ := Finset.mem_sdiff.mp h2
    rcases Finset.mem_union.mp h2_in_V with h2_uns_or_c0 | h2_c1
    · -- e2 = .unsplit v' OR e2 = .copy0 w'.  Both factor as toCopy0 W₁ *.
      rcases Finset.mem_union.mp h2_uns_or_c0 with h2_uns | h2_c0
      · -- e2 = .unsplit v' for v' ∈ G.V \ W₁ \ W₂.
        obtain ⟨v', hv'_VW₁, hv'_eq⟩ := Finset.mem_image.mp h2_uns
        obtain ⟨hv'_V, hv'_notW₁⟩ := Finset.mem_sdiff.mp hv'_VW₁
        have hv'_notW₂ : v' ∉ W₂ := by
          intro hv'W₂
          apply h2_notW₂; rw [← hv'_eq]
          exact Finset.mem_image.mpr ⟨v', hv'W₂, rfl⟩
        have hv'_lift : toCopy0 W₁ v' = SplitNode.unsplit v' :=
          toCopy0_unsplit_of_notW hv'_notW₁
        have h_e2_toCopy0 : e2 = toCopy0 W₁ v' := hv'_eq.symm.trans hv'_lift.symm
        -- Case-split on e1's piece.
        rcases Finset.mem_union.mp h1 with h1_J | h1_V_marg
        · -- e1 = .unsplit j for j ∈ G.J.
          obtain ⟨j, hjJ, hj_eq⟩ := Finset.mem_image.mp h1_J
          have hj_notW₁ : j ∉ W₁ := by
            intro hjW₁
            exact Finset.disjoint_left.mp G.hJV_disj hjJ (hW₁ hjW₁)
          have hj_lift1 : toCopy1 W₁ j = SplitNode.unsplit j :=
            toCopy1_unsplit_of_notW hj_notW₁
          have h_e1_toCopy1 : e1 = toCopy1 W₁ j := hj_eq.symm.trans hj_lift1.symm
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨(j, v'), ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_union_left _ hjJ, Finset.mem_sdiff.mpr ⟨hv'_V, hv'_notW₂⟩⟩, ?_⟩
            rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
            exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
          · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
        · -- e1 ∈ ((G.V \ W₁).image .unsplit ∪ W₁.image .copy0 ∪ W₁.image .copy1) \ W₂.image .unsplit.
          obtain ⟨h1_in_V, _⟩ := Finset.mem_sdiff.mp h1_V_marg
          rcases Finset.mem_union.mp h1_in_V with h1_uns_or_c0 | h1_c1
          · rcases Finset.mem_union.mp h1_uns_or_c0 with h1_uns | h1_c0
            · -- e1 = .unsplit u' for u' ∈ G.V \ W₁.
              obtain ⟨u', hu'_VW₁, hu'_eq⟩ := Finset.mem_image.mp h1_uns
              obtain ⟨hu'_V, hu'_notW₁⟩ := Finset.mem_sdiff.mp hu'_VW₁
              -- u' ∉ W₂ since e1 ∉ W₂.image .unsplit.
              have hu'_notW₂ : u' ∉ W₂ := by
                intro hu'W₂
                obtain ⟨_, h_notW₂⟩ := Finset.mem_sdiff.mp h1_V_marg
                apply h_notW₂; rw [← hu'_eq]
                exact Finset.mem_image.mpr ⟨u', hu'W₂, rfl⟩
              have hu'_lift1 : toCopy1 W₁ u' = SplitNode.unsplit u' :=
                toCopy1_unsplit_of_notW hu'_notW₁
              have h_e1_toCopy1 : e1 = toCopy1 W₁ u' := hu'_eq.symm.trans hu'_lift1.symm
              refine Finset.mem_union_left _ ?_
              refine Finset.mem_image.mpr ⟨(u', v'), ?_, ?_⟩
              · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                  ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hu'_V, hu'_notW₂⟩),
                    Finset.mem_sdiff.mpr ⟨hv'_V, hv'_notW₂⟩⟩, ?_⟩
                rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
                exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
              · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
            · -- e1 = .copy0 w' for w' ∈ W₁.  Transfer edge case.
              obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h1_c0
              exfalso
              obtain ⟨p, hp_dir, hp_pos, hp_inter⟩ := hPhi
              have hsrc_eq : SplitNode.copy0 w' = e1 := hw'_eq
              -- Substitute e1 := .copy0 w' by Lean's `subst` after generalizing.
              -- First extract what we need from the walk shape.
              -- Construct a walk explicitly using Walk.cast or similar — easiest: use Eq.mpr.
              have h_tgt_eq : e2 = SplitNode.copy1 w' := by
                -- Apply walk_copy0_target_copy1 via the type-transported walk.
                have := walk_copy0_target_copy1 (hW₁ := hW₁) hDisj hw'W₁ (hsrc_eq ▸ p)
                  (by cases hsrc_eq; exact hp_dir)
                  (by cases hsrc_eq; exact hp_pos)
                  (by cases hsrc_eq; exact hp_inter)
                exact this
              -- But e2 = .unsplit v'.
              rw [h_tgt_eq] at hv'_eq
              cases hv'_eq
          · -- e1 = .copy1 w' for w' ∈ W₁.
            obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h1_c1
            have hw'_lift1 : toCopy1 W₁ w' = SplitNode.copy1 w' := by
              unfold toCopy1; rw [if_pos hw'W₁]
            have h_e1_toCopy1 : e1 = toCopy1 W₁ w' := hw'_eq.symm.trans hw'_lift1.symm
            have hw'_V : w' ∈ G.V := hW₁ hw'W₁
            have hw'_notW₂ : w' ∉ W₂ := Finset.disjoint_left.mp hDisj hw'W₁
            refine Finset.mem_union_left _ ?_
            refine Finset.mem_image.mpr ⟨(w', v'), ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hw'_V, hw'_notW₂⟩),
                  Finset.mem_sdiff.mpr ⟨hv'_V, hv'_notW₂⟩⟩, ?_⟩
              rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
              exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
            · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
      · -- e2 = .copy0 w' for w' ∈ W₁.
        obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h2_c0
        have hw'_lift0 : toCopy0 W₁ w' = SplitNode.copy0 w' := by
          unfold toCopy0; rw [if_pos hw'W₁]
        have h_e2_toCopy0 : e2 = toCopy0 W₁ w' := hw'_eq.symm.trans hw'_lift0.symm
        have hw'_V : w' ∈ G.V := hW₁ hw'W₁
        have hw'_notW₂ : w' ∉ W₂ := Finset.disjoint_left.mp hDisj hw'W₁
        -- Now case on e1.  Same case-analysis as above.
        rcases Finset.mem_union.mp h1 with h1_J | h1_V_marg
        · obtain ⟨j, hjJ, hj_eq⟩ := Finset.mem_image.mp h1_J
          have hj_notW₁ : j ∉ W₁ := by
            intro hjW₁
            exact Finset.disjoint_left.mp G.hJV_disj hjJ (hW₁ hjW₁)
          have hj_lift1 : toCopy1 W₁ j = SplitNode.unsplit j :=
            toCopy1_unsplit_of_notW hj_notW₁
          have h_e1_toCopy1 : e1 = toCopy1 W₁ j := hj_eq.symm.trans hj_lift1.symm
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨(j, w'), ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_union_left _ hjJ, Finset.mem_sdiff.mpr ⟨hw'_V, hw'_notW₂⟩⟩, ?_⟩
            rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
            exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
          · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
        · obtain ⟨h1_in_V, _⟩ := Finset.mem_sdiff.mp h1_V_marg
          rcases Finset.mem_union.mp h1_in_V with h1_uns_or_c0 | h1_c1
          · rcases Finset.mem_union.mp h1_uns_or_c0 with h1_uns | h1_c0
            · -- e1 = .unsplit u' for u' ∈ G.V \ W₁.
              obtain ⟨u', hu'_VW₁, hu'_eq⟩ := Finset.mem_image.mp h1_uns
              obtain ⟨hu'_V, hu'_notW₁⟩ := Finset.mem_sdiff.mp hu'_VW₁
              have hu'_notW₂ : u' ∉ W₂ := by
                intro hu'W₂
                obtain ⟨_, h_notW₂⟩ := Finset.mem_sdiff.mp h1_V_marg
                apply h_notW₂; rw [← hu'_eq]
                exact Finset.mem_image.mpr ⟨u', hu'W₂, rfl⟩
              have hu'_lift1 : toCopy1 W₁ u' = SplitNode.unsplit u' :=
                toCopy1_unsplit_of_notW hu'_notW₁
              have h_e1_toCopy1 : e1 = toCopy1 W₁ u' := hu'_eq.symm.trans hu'_lift1.symm
              refine Finset.mem_union_left _ ?_
              refine Finset.mem_image.mpr ⟨(u', w'), ?_, ?_⟩
              · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                  ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hu'_V, hu'_notW₂⟩),
                    Finset.mem_sdiff.mpr ⟨hw'_V, hw'_notW₂⟩⟩, ?_⟩
                rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
                exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
              · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
            · -- e1 = .copy0 w'' for w'' ∈ W₁.  Then walk_copy0_target_copy1 forces e2 = .copy1 w''.
              -- But e2 = .copy0 w'.  Impossible.
              obtain ⟨w'', hw''W₁, hw''_eq⟩ := Finset.mem_image.mp h1_c0
              exfalso
              obtain ⟨p, hp_dir, hp_pos, hp_inter⟩ := hPhi
              have hsrc_eq : SplitNode.copy0 w'' = e1 := hw''_eq
              have h_tgt_eq : e2 = SplitNode.copy1 w'' := by
                have := walk_copy0_target_copy1 (hW₁ := hW₁) hDisj hw''W₁ (hsrc_eq ▸ p)
                  (by cases hsrc_eq; exact hp_dir)
                  (by cases hsrc_eq; exact hp_pos)
                  (by cases hsrc_eq; exact hp_inter)
                exact this
              -- But e2 = .copy0 w'.
              rw [h_tgt_eq] at hw'_eq
              cases hw'_eq
          · -- e1 = .copy1 w'' for w'' ∈ W₁.
            obtain ⟨w'', hw''W₁, hw''_eq⟩ := Finset.mem_image.mp h1_c1
            have hw''_lift1 : toCopy1 W₁ w'' = SplitNode.copy1 w'' := by
              unfold toCopy1; rw [if_pos hw''W₁]
            have h_e1_toCopy1 : e1 = toCopy1 W₁ w'' := hw''_eq.symm.trans hw''_lift1.symm
            have hw''_V : w'' ∈ G.V := hW₁ hw''W₁
            have hw''_notW₂ : w'' ∉ W₂ := Finset.disjoint_left.mp hDisj hw''W₁
            refine Finset.mem_union_left _ ?_
            refine Finset.mem_image.mpr ⟨(w'', w'), ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hw''_V, hw''_notW₂⟩),
                  Finset.mem_sdiff.mpr ⟨hw'_V, hw'_notW₂⟩⟩, ?_⟩
              rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
              exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
            · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
    · -- e2 = .copy1 w' for w' ∈ W₁.  Force e1 = .copy0 w' via walk_target_copy1_source_copy0.
      obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h2_c1
      obtain ⟨p, hp_dir, hp_pos, hp_inter⟩ := hPhi
      have h_tgt_eq : e2 = SplitNode.copy1 w' := hw'_eq.symm
      have h_src_eq : e1 = SplitNode.copy0 w' := by
        have := walk_target_copy1_source_copy0 (hW₁ := hW₁) hDisj hw'W₁ (h_tgt_eq ▸ p)
          (by cases h_tgt_eq; exact hp_dir)
          (by cases h_tgt_eq; exact hp_pos)
          (by cases h_tgt_eq; exact hp_inter)
        exact this
      -- Now e = (.copy0 w', .copy1 w'), the transfer edge.
      refine Finset.mem_union_right _ ?_
      refine Finset.mem_image.mpr ⟨w', hw'W₁, ?_⟩
      exact Prod.ext h_src_eq.symm h_tgt_eq.symm
  · -- Backward direction.
    intro h_union
    rcases Finset.mem_union.mp h_union with h_lifted | h_transfer
    · -- e ∈ ((G.marginalize W₂).E).image (toCopy1 W₁, toCopy0 W₁).
      obtain ⟨⟨u, v⟩, h_uv_mem, h_uv_eq⟩ := Finset.mem_image.mp h_lifted
      rw [Finset.mem_filter, Finset.mem_product] at h_uv_mem
      obtain ⟨⟨hu_in, hv_in⟩, hPhi⟩ := h_uv_mem
      have h_e1 : e1 = toCopy1 W₁ u := congrArg Prod.fst h_uv_eq.symm
      have h_e2 : e2 = toCopy0 W₁ v := congrArg Prod.snd h_uv_eq.symm
      obtain ⟨hv_V, hv_notW₂⟩ := Finset.mem_sdiff.mp hv_in
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- e1 ∈ J ∪ V_marg.
        rw [h_e1]
        by_cases hu_W₁ : u ∈ W₁
        · -- toCopy1 W₁ u = .copy1 u.
          have hu_lift1 : toCopy1 W₁ u = SplitNode.copy1 u := by
            unfold toCopy1; rw [if_pos hu_W₁]
          rw [hu_lift1]
          have hu_notW₂ : u ∉ W₂ := Finset.disjoint_left.mp hDisj hu_W₁
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · -- .copy1 u ∈ V_marg without sdiff: in W₁.image .copy1.
            refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨u, hu_W₁, rfl⟩
          · -- .copy1 u ∉ W₂.image .unsplit.
            intro h_in
            obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp h_in
            cases hw_eq
        · -- u ∉ W₁: toCopy1 W₁ u = .unsplit u.
          have hu_lift1 : toCopy1 W₁ u = SplitNode.unsplit u :=
            toCopy1_unsplit_of_notW hu_W₁
          rw [hu_lift1]
          -- Need .unsplit u ∈ J ∪ V_marg.  u ∈ G.J ∪ G.V \ W₂ from hu_in.
          rcases Finset.mem_union.mp hu_in with hu_J | hu_VW₂
          · -- u ∈ G.J.
            exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu_J, rfl⟩)
          · -- u ∈ G.V \ W₂.
            obtain ⟨hu_V, hu_notW₂⟩ := Finset.mem_sdiff.mp hu_VW₂
            refine Finset.mem_union_right _ ?_
            refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · refine Finset.mem_union_left _ ?_
              refine Finset.mem_union_left _ ?_
              exact Finset.mem_image.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu_V, hu_W₁⟩, rfl⟩
            · intro h_in
              obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp h_in
              have : w = u := by injection hw_eq
              exact hu_notW₂ (this ▸ hwW₂)
      · -- e2 ∈ V_marg.
        rw [h_e2]
        by_cases hv_W₁ : v ∈ W₁
        · have hv_lift0 : toCopy0 W₁ v = SplitNode.copy0 v := by
            unfold toCopy0; rw [if_pos hv_W₁]
          rw [hv_lift0]
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_left _ ?_
            refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨v, hv_W₁, rfl⟩
          · intro h_in
            obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp h_in
            cases hw_eq
        · have hv_lift0 : toCopy0 W₁ v = SplitNode.unsplit v :=
            toCopy0_unsplit_of_notW hv_W₁
          rw [hv_lift0]
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_left _ ?_
            refine Finset.mem_union_left _ ?_
            exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_W₁⟩, rfl⟩
          · intro h_in
            obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp h_in
            have : w = v := by injection hw_eq
            exact hv_notW₂ (this ▸ hwW₂)
      · -- Φ_E predicate.
        rw [h_e1, h_e2]
        exact (split_marg_PhiE_iff hW₁ hDisj).mpr hPhi
    · -- e ∈ W₁.image (fun w => (.copy0 w, .copy1 w)).  Transfer edge.
      obtain ⟨w, hwW₁, hw_eq⟩ := Finset.mem_image.mp h_transfer
      have h_e1 : e1 = SplitNode.copy0 w := congrArg Prod.fst hw_eq.symm
      have h_e2 : e2 = SplitNode.copy1 w := congrArg Prod.snd hw_eq.symm
      have hw_V : w ∈ G.V := hW₁ hwW₁
      have hw_notW₂ : w ∉ W₂ := Finset.disjoint_left.mp hDisj hwW₁
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h_e1]
        refine Finset.mem_union_right _ ?_
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · refine Finset.mem_union_left _ ?_
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · intro h_in
          obtain ⟨_, _, hw_eq'⟩ := Finset.mem_image.mp h_in
          cases hw_eq'
      · rw [h_e2]
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · intro h_in
          obtain ⟨_, _, hw_eq'⟩ := Finset.mem_image.mp h_in
          cases hw_eq'
      · -- Φ_E from .copy0 w to .copy1 w via single transfer edge.
        rw [h_e1, h_e2]
        -- Build the single-edge walk.
        have h_transfer_E : (SplitNode.copy0 w, SplitNode.copy1 w) ∈
            (G.nodeSplittingOn W₁ hW₁).E := by
          change _ ∈ G.E.image _ ∪ W₁.image _
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        have h_src_in : SplitNode.copy0 w ∈ G.nodeSplittingOn W₁ hW₁ :=
          mem_split_of_mem_W₁_copy0 (hW₁ := hW₁) hwW₁
        have h_tgt_in : SplitNode.copy1 w ∈ G.nodeSplittingOn W₁ hW₁ :=
          mem_split_of_mem_W₁_copy1 (hW₁ := hW₁) hwW₁
        refine ⟨Walk.cons (SplitNode.copy1 w) (SplitNode.copy0 w, SplitNode.copy1 w)
          (Or.inl ⟨rfl, Or.inl h_transfer_E⟩)
          (Walk.nil (SplitNode.copy1 w) h_tgt_in),
          ⟨rfl, h_transfer_E, trivial⟩, by change 1 ≥ 1; omega, ?_⟩
        intro x hx
        simp [Walk.vertices, List.tail, List.dropLast] at hx

-- =====================================================================
-- ## Part (iii) L-field helpers
--
-- The L-field iff and equality.  Both endpoints are `toCopy0`-tagged (which
-- collapses to `.unsplit`/`.copy0` depending on `W₁`-membership), and we
-- exclude `.copy1`-tagged endpoints via a bifurcation-walk analysis.
-- =====================================================================

-- ## Pair equality through `toCopy0 W₁`.
private lemma pair_eq_of_toCopy0_eq {W₁ : Finset Node} {a : Node × Node} {u v : Node}
    (h : (toCopy0 W₁ a.1, toCopy0 W₁ a.2) = (toCopy0 W₁ u, toCopy0 W₁ v)) :
    a = (u, v) := by
  have h1 : toCopy0 W₁ a.1 = toCopy0 W₁ u := congrArg Prod.fst h
  have h2 : toCopy0 W₁ a.2 = toCopy0 W₁ v := congrArg Prod.snd h
  exact Prod.ext (toCopy0_inj_node h1) (toCopy0_inj_node h2)

-- ## `toCopy1 v = toCopy0 u` forces both `∉ W₁` and `u = v`.
private lemma toCopy1_eq_toCopy0_imp_notW {W₁ : Finset Node} {u v : Node}
    (h : toCopy1 W₁ v = toCopy0 W₁ u) : u ∉ W₁ ∧ v ∉ W₁ ∧ u = v := by
  unfold toCopy1 toCopy0 at h
  by_cases hW_v : v ∈ W₁ <;> by_cases hW_u : u ∈ W₁
  · rw [if_pos hW_v, if_pos hW_u] at h; cases h
  · rw [if_pos hW_v, if_neg hW_u] at h; cases h
  · rw [if_neg hW_v, if_pos hW_u] at h; cases h
  · rw [if_neg hW_v, if_neg hW_u] at h
    refine ⟨hW_u, hW_v, ?_⟩
    have heq : SplitNode.unsplit v = SplitNode.unsplit u := h
    have hvu : v = u := by injection heq
    exact hvu.symm

-- ## E-edge descent through `toCopy0`-tagged endpoints (transfer ruled out).
private lemma a_in_G_E_of_toCopy0_lifted_in_split {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {a' : Node × Node}
    {a : SplitNode Node × SplitNode Node}
    (ha_eq : a = (toCopy0 W₁ a'.1, toCopy0 W₁ a'.2))
    (ha_E : a ∈ (G.nodeSplittingOn W₁ hW₁).E) : a' ∈ G.E := by
  change a ∈ G.E.image _ ∪ W₁.image _ at ha_E
  rcases Finset.mem_union.mp ha_E with hLift | hTrans
  · obtain ⟨e', he'E, he'_eq⟩ := Finset.mem_image.mp hLift
    rw [ha_eq] at he'_eq
    have h1 : toCopy1 W₁ e'.1 = toCopy0 W₁ a'.1 := congrArg Prod.fst he'_eq
    have h2 : toCopy0 W₁ e'.2 = toCopy0 W₁ a'.2 := congrArg Prod.snd he'_eq
    obtain ⟨_, _, he1⟩ := toCopy1_eq_toCopy0_imp_notW h1
    have he2 : e'.2 = a'.2 := toCopy0_inj_node h2
    have heq : e' = a' := Prod.ext he1.symm he2
    rw [← heq]; exact he'E
  · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
    rw [ha_eq] at hw_eq
    have hcontra : SplitNode.copy1 w = toCopy0 W₁ a'.2 := congrArg Prod.snd hw_eq
    exact (toCopy0_ne_copy1 hcontra.symm).elim

-- ## L-edge descent through `toCopy0`-tagged endpoints.
private lemma a_in_G_L_of_toCopy0_lifted_in_split {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {a' : Node × Node}
    {a : SplitNode Node × SplitNode Node}
    (ha_eq : a = (toCopy0 W₁ a'.1, toCopy0 W₁ a'.2))
    (ha_L : a ∈ (G.nodeSplittingOn W₁ hW₁).L) : a' ∈ G.L := by
  change a ∈ G.L.image _ at ha_L
  obtain ⟨e', he'L, he'_eq⟩ := Finset.mem_image.mp ha_L
  rw [ha_eq] at he'_eq
  have h1 : toCopy0 W₁ e'.1 = toCopy0 W₁ a'.1 := congrArg Prod.fst he'_eq
  have h2 : toCopy0 W₁ e'.2 = toCopy0 W₁ a'.2 := congrArg Prod.snd he'_eq
  have he1 : e'.1 = a'.1 := toCopy0_inj_node h1
  have he2 : e'.2 = a'.2 := toCopy0_inj_node h2
  have heq : e' = a' := Prod.ext he1 he2
  rw [← heq]; exact he'L

-- ## WalkStep descent: both endpoints `toCopy0`-tagged.
private lemma walkStep_ofSplit_toCopy0 {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {u v : Node} {a : SplitNode Node × SplitNode Node}
    (h : (G.nodeSplittingOn W₁ hW₁).WalkStep
      (toCopy0 W₁ u) a (toCopy0 W₁ v)) :
    ∃ a' : Node × Node, G.WalkStep u a' v ∧
      a = (toCopy0 W₁ a'.1, toCopy0 W₁ a'.2) := by
  rcases h with ⟨ha, hOr⟩ | ⟨ha, hE⟩
  · have ha_full : a = (toCopy0 W₁ u, toCopy0 W₁ v) := ha
    rcases hOr with hE_split | hL_split
    · change a ∈ G.E.image _ ∪ W₁.image _ at hE_split
      rcases Finset.mem_union.mp hE_split with hImg | hTrans
      · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hImg
        rw [ha_full] at ha'_eq
        have h1 : toCopy1 W₁ a'.1 = toCopy0 W₁ u := congrArg Prod.fst ha'_eq
        have h2 : toCopy0 W₁ a'.2 = toCopy0 W₁ v := congrArg Prod.snd ha'_eq
        obtain ⟨hu_notW, ha'1_notW, ha'1_eq⟩ := toCopy1_eq_toCopy0_imp_notW h1
        have ha'2 : a'.2 = v := toCopy0_inj_node h2
        refine ⟨a', Or.inl ⟨?_, Or.inl ha'_in⟩, ?_⟩
        · exact Prod.ext ha'1_eq.symm ha'2
        · rw [ha_full]
          have hlift_eq : toCopy0 W₁ a'.1 = toCopy1 W₁ a'.1 := by
            rw [toCopy0_unsplit_of_notW ha'1_notW, toCopy1_unsplit_of_notW ha'1_notW]
          ext
          · rw [hlift_eq]; exact h1.symm
          · exact h2.symm
      · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
        rw [ha_full] at hw_eq
        have hcontra : SplitNode.copy1 w = toCopy0 W₁ v := congrArg Prod.snd hw_eq
        exact (toCopy0_ne_copy1 hcontra.symm).elim
    · change a ∈ G.L.image _ at hL_split
      obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hL_split
      rw [ha_full] at ha'_eq
      have h1 : toCopy0 W₁ a'.1 = toCopy0 W₁ u := congrArg Prod.fst ha'_eq
      have h2 : toCopy0 W₁ a'.2 = toCopy0 W₁ v := congrArg Prod.snd ha'_eq
      have ha'1 : a'.1 = u := toCopy0_inj_node h1
      have ha'2 : a'.2 = v := toCopy0_inj_node h2
      refine ⟨a', Or.inl ⟨?_, Or.inr ha'_in⟩, ?_⟩
      · exact Prod.ext ha'1 ha'2
      · rw [ha_full]; ext
        · exact h1.symm
        · exact h2.symm
  · have ha_full : a = (toCopy0 W₁ v, toCopy0 W₁ u) := ha
    change a ∈ G.E.image _ ∪ W₁.image _ at hE
    rcases Finset.mem_union.mp hE with hImg | hTrans
    · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hImg
      rw [ha_full] at ha'_eq
      have h1 : toCopy1 W₁ a'.1 = toCopy0 W₁ v := congrArg Prod.fst ha'_eq
      have h2 : toCopy0 W₁ a'.2 = toCopy0 W₁ u := congrArg Prod.snd ha'_eq
      obtain ⟨hv_notW, ha'1_notW, ha'1_eq⟩ := toCopy1_eq_toCopy0_imp_notW h1
      have ha'2 : a'.2 = u := toCopy0_inj_node h2
      refine ⟨a', Or.inr ⟨?_, ha'_in⟩, ?_⟩
      · exact Prod.ext ha'1_eq.symm ha'2
      · rw [ha_full]
        have hlift_eq : toCopy0 W₁ a'.1 = toCopy1 W₁ a'.1 := by
          rw [toCopy0_unsplit_of_notW ha'1_notW, toCopy1_unsplit_of_notW ha'1_notW]
        ext
        · rw [hlift_eq]; exact h1.symm
        · exact h2.symm
    · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
      rw [ha_full] at hw_eq
      have hcontra : SplitNode.copy1 w = toCopy0 W₁ u := congrArg Prod.snd hw_eq
      exact (toCopy0_ne_copy1 hcontra.symm).elim

-- ## Carrier descent: `toCopy0 W₁ v ∈ split` ⟹ `v ∈ G`.
private lemma mem_G_of_toCopy0_mem_split {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {v : Node}
    (h : toCopy0 W₁ v ∈ G.nodeSplittingOn W₁ hW₁) : v ∈ G := by
  by_cases hW : v ∈ W₁
  · exact Finset.mem_union_right _ (hW₁ hW)
  · rw [toCopy0_unsplit_of_notW hW] at h
    exact mem_G_of_unsplit_mem_split hW₁ h

-- ## List utilities for `toCopy0 W₁` map.
private lemma list_toCopy0_tail {W₁ : Finset Node} (l : List Node) :
    (l.map (toCopy0 W₁)).tail = l.tail.map (toCopy0 W₁) := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

private lemma list_toCopy0_dropLast {W₁ : Finset Node} :
    ∀ (l : List Node),
      (l.map (toCopy0 W₁)).dropLast = l.dropLast.map (toCopy0 W₁)
  | [] => rfl
  | _ :: [] => rfl
  | x :: y :: rest => by
      change toCopy0 W₁ x :: (((y :: rest).map (toCopy0 W₁)).dropLast)
          = toCopy0 W₁ x :: ((y :: rest).dropLast.map (toCopy0 W₁))
      rw [list_toCopy0_dropLast (y :: rest)]

-- ## Walk descent: split → G with all vertices `toCopy0`-tagged.
-- Generalises `walk_ofSplit_unsplit_full` to allow `.copy0` tags (W₁-underlying).
-- Transfer edges are ruled out automatically (their `.copy1` target conflicts).
private lemma walk_ofSplit_toCopy0_full {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) :
    ∀ {x y : SplitNode Node} (p : Walk (G.nodeSplittingOn W₁ hW₁) x y),
      (∀ z ∈ p.vertices, ∃ z' : Node, z = toCopy0 W₁ z') →
      ∀ (u v : Node), x = toCopy0 W₁ u → y = toCopy0 W₁ v →
      ∃ q : Walk G u v, q.length = p.length ∧
        q.vertices.map (toCopy0 W₁) = p.vertices ∧
        (p.IsDirectedWalk → q.IsDirectedWalk) ∧
        (∀ i, p.IsBifurcationWithSplit i → q.IsBifurcationWithSplit i) := by
  intro x y p
  induction p with
  | nil w hw =>
      intro _ u v hxu hyv
      have hu_eq_v : toCopy0 W₁ u = toCopy0 W₁ v := hxu.symm.trans hyv
      have huv : u = v := toCopy0_inj_node hu_eq_v
      subst huv; subst hxu
      have hu_in_G : u ∈ G := mem_G_of_toCopy0_mem_split (hW₁ := hW₁) hw
      refine ⟨Walk.nil u hu_in_G, rfl, rfl, fun _ => trivial, ?_⟩
      intro i h; exact h.elim
  | @cons x' y' mid a hStep p' ih =>
      intro h_all u v hxu hyv
      subst hxu
      have hmid_in : mid ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid a hStep p').vertices := by
        change mid ∈ (toCopy0 W₁ u :: p'.vertices)
        exact List.mem_cons_of_mem _ (Walk.head_mem_vertices p')
      obtain ⟨m', hmid_eq⟩ := h_all mid hmid_in
      subst hmid_eq
      have h_all_p' : ∀ z ∈ p'.vertices, ∃ z' : Node, z = toCopy0 W₁ z' := by
        intro z hz
        exact h_all z (List.mem_cons_of_mem _ hz)
      obtain ⟨a', hStepG, ha_eq⟩ := walkStep_ofSplit_toCopy0 (hW₁ := hW₁) hStep
      obtain ⟨q', hq'_len, hq'_vs, hq'_dir, hq'_bif⟩ :=
        ih h_all_p' m' v rfl hyv
      refine ⟨Walk.cons m' a' hStepG q', ?_, ?_, ?_, ?_⟩
      · change q'.length + 1 = p'.length + 1
        rw [hq'_len]
      · change toCopy0 W₁ u :: q'.vertices.map (toCopy0 W₁) = toCopy0 W₁ u :: p'.vertices
        rw [hq'_vs]
      · intro hp_dir
        simp only [Walk.IsDirectedWalk] at hp_dir
        obtain ⟨ha_p, ha_E, hp'_dir⟩ := hp_dir
        refine ⟨?_, ?_, hq'_dir hp'_dir⟩
        · have hpair : (toCopy0 W₁ a'.1, toCopy0 W₁ a'.2)
                      = (toCopy0 W₁ u, toCopy0 W₁ m') := by
            rw [← ha_eq]; exact ha_p
          exact pair_eq_of_toCopy0_eq hpair
        · exact a_in_G_E_of_toCopy0_lifted_in_split (hW₁ := hW₁) ha_eq ha_E
      · intro i hPi
        match i, p', hPi, q', hq'_len, hq'_dir, hq'_bif with
        | 0, .nil _ _, hPi, .nil _ _, _, _, _ =>
            simp only [Walk.IsBifurcationWithSplit] at hPi
            obtain ⟨ha_uv, ha_L⟩ := hPi
            simp only [Walk.IsBifurcationWithSplit]
            refine ⟨?_, ?_⟩
            · have hpair : (toCopy0 W₁ a'.1, toCopy0 W₁ a'.2)
                          = (toCopy0 W₁ u, toCopy0 W₁ m') := by
                rw [← ha_eq]; exact ha_uv
              exact pair_eq_of_toCopy0_eq hpair
            · exact a_in_G_L_of_toCopy0_lifted_in_split (hW₁ := hW₁) ha_eq ha_L
        | 0, .nil _ _, _, .cons _ _ _ _, hlen, _, _ =>
            simp [Walk.length] at hlen
        | 0, .cons _ _ _ _, _, .nil _ _, hlen, _, _ =>
            simp [Walk.length] at hlen
        | 0, .cons _ _ _ _, hPi, .cons _ _ _ _, _, hq'_dir, _ =>
            simp only [Walk.IsBifurcationWithSplit] at hPi
            obtain ⟨ha_or, hp'_dir⟩ := hPi
            simp only [Walk.IsBifurcationWithSplit]
            refine ⟨?_, hq'_dir hp'_dir⟩
            rcases ha_or with ⟨ha_vu, ha_E⟩ | ⟨ha_uv, ha_L⟩
            · refine Or.inl ⟨?_, ?_⟩
              · have hpair : (toCopy0 W₁ a'.1, toCopy0 W₁ a'.2)
                            = (toCopy0 W₁ m', toCopy0 W₁ u) := by
                  rw [← ha_eq]; exact ha_vu
                exact pair_eq_of_toCopy0_eq hpair
              · exact a_in_G_E_of_toCopy0_lifted_in_split (hW₁ := hW₁) ha_eq ha_E
            · refine Or.inr ⟨?_, ?_⟩
              · have hpair : (toCopy0 W₁ a'.1, toCopy0 W₁ a'.2)
                            = (toCopy0 W₁ u, toCopy0 W₁ m') := by
                  rw [← ha_eq]; exact ha_uv
                exact pair_eq_of_toCopy0_eq hpair
              · exact a_in_G_L_of_toCopy0_lifted_in_split (hW₁ := hW₁) ha_eq ha_L
        | k + 1, _, hPi, _, _, _, hq'_bif =>
            simp only [Walk.IsBifurcationWithSplit] at hPi
            obtain ⟨ha_vu, ha_E, hPi_rest⟩ := hPi
            simp only [Walk.IsBifurcationWithSplit]
            refine ⟨?_, ?_, hq'_bif k hPi_rest⟩
            · have hpair : (toCopy0 W₁ a'.1, toCopy0 W₁ a'.2)
                          = (toCopy0 W₁ m', toCopy0 W₁ u) := by
                rw [← ha_eq]; exact ha_vu
              exact pair_eq_of_toCopy0_eq hpair
            · exact a_in_G_E_of_toCopy0_lifted_in_split (hW₁ := hW₁) ha_eq ha_E

-- ## All vertices `toCopy0`-tagged from `toCopy0` endpoints + interior in `W₂.image .unsplit`.
private lemma all_toCopy0_of_interior_W_image_split
    {G : CDMG Node} {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V}
    {W₂ : Finset Node} (hDisj : Disjoint W₁ W₂)
    {x y : SplitNode Node}
    (p : Walk (G.nodeSplittingOn W₁ hW₁) x y)
    (hp_pos : p.length ≥ 1)
    {u v : Node} (hxu : x = toCopy0 W₁ u) (hyv : y = toCopy0 W₁ v)
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast, z ∈ W₂.image SplitNode.unsplit) :
    ∀ z ∈ p.vertices, ∃ z' : Node, z = toCopy0 W₁ z' := by
  intro z hz
  rw [Walk.vertices_eq_head_cons_tail p] at hz
  rcases List.mem_cons.mp hz with h_eq | h_in_tail
  · exact ⟨u, h_eq.trans hxu⟩
  · have h_tail_ne : p.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos p hp_pos
    have h_drop_or_last : z ∈ p.vertices.tail.dropLast ∨ z = y := by
      rw [← List.dropLast_append_getLast h_tail_ne] at h_in_tail
      rcases List.mem_append.mp h_in_tail with h_drop | h_last
      · exact Or.inl h_drop
      · refine Or.inr ?_
        rw [List.mem_singleton] at h_last
        rw [h_last, Walk.tail_getLast_of_pos p hp_pos]
    rcases h_drop_or_last with h_drop | h_last
    · obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp (hp_inter z h_drop)
      have hw_notW : w ∉ W₁ := Finset.disjoint_left.mp hDisj.symm hwW₂
      exact ⟨w, hw_eq.symm.trans (toCopy0_unsplit_of_notW hw_notW).symm⟩
    · exact ⟨v, h_last.trans hyv⟩

-- ## Part (iii) Φ_L iff: bifurcation in split iff bifurcation in G.
private lemma split_marg_PhiL_iff
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) {u v : Node} (huv : u ≠ v) :
    (G.nodeSplittingOn W₁ hW₁).MarginalizationΦL (W₂.image SplitNode.unsplit)
        (toCopy0 W₁ u) (toCopy0 W₁ v) ↔
      G.MarginalizationΦL W₂ u v := by
  constructor
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · have hp_pos : p.length ≥ 1 := Walk.length_pos_of_isBifurcation hp_bif
      have h_all := all_toCopy0_of_interior_W_image_split
        (hW₁ := hW₁) (hDisj := hDisj) p hp_pos rfl rfl hp_inter
      obtain ⟨_hne, hu_tail, hv_drop, i, hi⟩ := hp_bif
      obtain ⟨q, _hq_len, hq_vs, _, hq_bif⟩ :=
        walk_ofSplit_toCopy0_full hW₁ p h_all u v rfl rfl
      refine Or.inl ⟨q, ⟨huv, ?_, ?_, i, hq_bif i hi⟩, ?_⟩
      · intro h
        apply hu_tail
        have : p.vertices.tail = q.vertices.tail.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_tail]
        rw [this]
        exact List.mem_map.mpr ⟨u, h, rfl⟩
      · intro h
        apply hv_drop
        have : p.vertices.dropLast = q.vertices.dropLast.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_dropLast]
        rw [this]
        exact List.mem_map.mpr ⟨v, h, rfl⟩
      · intro x hx
        have : p.vertices.tail.dropLast = q.vertices.tail.dropLast.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_tail, list_toCopy0_dropLast]
        have hx_p : toCopy0 W₁ x ∈ p.vertices.tail.dropLast := by
          rw [this]
          exact List.mem_map.mpr ⟨x, hx, rfl⟩
        obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp (hp_inter _ hx_p)
        have hw_notW : w ∉ W₁ := Finset.disjoint_left.mp hDisj.symm hwW₂
        have hw_lift : toCopy0 W₁ w = SplitNode.unsplit w := toCopy0_unsplit_of_notW hw_notW
        have heq : toCopy0 W₁ x = toCopy0 W₁ w := hw_eq.symm.trans hw_lift.symm
        have hxw : x = w := toCopy0_inj_node heq
        exact hxw ▸ hwW₂
    · have hp_pos : p.length ≥ 1 := Walk.length_pos_of_isBifurcation hp_bif
      have h_all := all_toCopy0_of_interior_W_image_split
        (hW₁ := hW₁) (hDisj := hDisj) p hp_pos (u := v) (v := u) rfl rfl hp_inter
      obtain ⟨_hne, hv_tail, hu_drop, i, hi⟩ := hp_bif
      obtain ⟨q, _hq_len, hq_vs, _, hq_bif⟩ :=
        walk_ofSplit_toCopy0_full hW₁ p h_all v u rfl rfl
      refine Or.inr ⟨q, ⟨huv.symm, ?_, ?_, i, hq_bif i hi⟩, ?_⟩
      · intro h
        apply hv_tail
        have : p.vertices.tail = q.vertices.tail.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_tail]
        rw [this]
        exact List.mem_map.mpr ⟨v, h, rfl⟩
      · intro h
        apply hu_drop
        have : p.vertices.dropLast = q.vertices.dropLast.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_dropLast]
        rw [this]
        exact List.mem_map.mpr ⟨u, h, rfl⟩
      · intro x hx
        have : p.vertices.tail.dropLast = q.vertices.tail.dropLast.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_tail, list_toCopy0_dropLast]
        have hx_p : toCopy0 W₁ x ∈ p.vertices.tail.dropLast := by
          rw [this]
          exact List.mem_map.mpr ⟨x, hx, rfl⟩
        obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp (hp_inter _ hx_p)
        have hw_notW : w ∉ W₁ := Finset.disjoint_left.mp hDisj.symm hwW₂
        have hw_lift : toCopy0 W₁ w = SplitNode.unsplit w := toCopy0_unsplit_of_notW hw_notW
        have heq : toCopy0 W₁ x = toCopy0 W₁ w := hw_eq.symm.trans hw_lift.symm
        have hxw : x = w := toCopy0_inj_node heq
        exact hxw ▸ hwW₂
  · rintro (⟨q, hq_bif, hq_inter⟩ | ⟨q, hq_bif, hq_inter⟩)
    · obtain ⟨p, hp_bif, hp_inter⟩ :=
        exists_lifted_bif_to_split hW₁ hDisj q hq_bif hq_inter
      exact Or.inl ⟨p, hp_bif, hp_inter⟩
    · obtain ⟨p, hp_bif, hp_inter⟩ :=
        exists_lifted_bif_to_split hW₁ hDisj q hq_bif hq_inter
      exact Or.inr ⟨p, hp_bif, hp_inter⟩

-- ## W₁¹-exclusion (source side): no bifurcation walk in split with source
-- `.copy1 w` (w ∈ W₁) and interior in `W₂.image .unsplit`.
private lemma not_bif_source_copy1
    {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {W₂ : Finset Node} (hDisj : Disjoint W₁ W₂)
    {w : Node} {y : SplitNode Node}
    (p : Walk (G.nodeSplittingOn W₁ hW₁) (SplitNode.copy1 w) y)
    (hp_bif : p.IsBifurcation)
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast, z ∈ W₂.image SplitNode.unsplit) :
    False := by
  obtain ⟨_hne, hu_tail, _hv_drop, i, hi⟩ := hp_bif
  cases p with
  | nil _ _ => exact hi
  | @cons _ _ mid a hStep p' =>
      rcases hStep with ⟨ha, hOr⟩ | ⟨ha, hE⟩
      · have h_a1 : a.1 = SplitNode.copy1 w := congrArg Prod.fst ha
        rcases hOr with hE' | hL'
        · change a ∈ G.E.image _ ∪ W₁.image _ at hE'
          rcases Finset.mem_union.mp hE' with hLift | hTrans
          · match i, p', hi with
            | 0, .nil _ _, hi =>
                simp only [Walk.IsBifurcationWithSplit] at hi
                obtain ⟨_, ha_L⟩ := hi
                change a ∈ G.L.image _ at ha_L
                obtain ⟨_, _, he_eq⟩ := Finset.mem_image.mp ha_L
                have h := congrArg Prod.fst he_eq
                rw [h_a1] at h
                exact toCopy0_ne_copy1 h
            | 0, .cons _ _ _ _, hi =>
                simp only [Walk.IsBifurcationWithSplit] at hi
                obtain ⟨hOr_bif, _⟩ := hi
                rcases hOr_bif with ⟨ha_vu, _⟩ | ⟨_, ha_L⟩
                · have h_mid_eq : a.1 = mid := congrArg Prod.fst ha_vu
                  rw [h_a1] at h_mid_eq
                  subst h_mid_eq
                  apply hu_tail
                  simp only [Walk.vertices, List.tail]
                  exact List.mem_cons_self
                · change a ∈ G.L.image _ at ha_L
                  obtain ⟨_, _, he_eq⟩ := Finset.mem_image.mp ha_L
                  have h := congrArg Prod.fst he_eq
                  rw [h_a1] at h
                  exact toCopy0_ne_copy1 h
            | k + 1, p_rest, hi =>
                simp only [Walk.IsBifurcationWithSplit] at hi
                obtain ⟨ha_vu, _, _⟩ := hi
                have h_mid_eq : a.1 = mid := congrArg Prod.fst ha_vu
                rw [h_a1] at h_mid_eq
                subst h_mid_eq
                apply hu_tail
                simp only [Walk.vertices, List.tail]
                exact Walk.head_mem_vertices p_rest
          · obtain ⟨_, _, hw_eq⟩ := Finset.mem_image.mp hTrans
            have h := congrArg Prod.fst hw_eq
            rw [h_a1] at h
            cases h
        · change a ∈ G.L.image _ at hL'
          obtain ⟨_, _, he_eq⟩ := Finset.mem_image.mp hL'
          have h := congrArg Prod.fst he_eq
          rw [h_a1] at h
          exact toCopy0_ne_copy1 h
      · have h_a2 : a.2 = SplitNode.copy1 w := congrArg Prod.snd ha
        change a ∈ G.E.image _ ∪ W₁.image _ at hE
        rcases Finset.mem_union.mp hE with hLift | hTrans
        · obtain ⟨_, _, he_eq⟩ := Finset.mem_image.mp hLift
          have h := congrArg Prod.snd he_eq
          rw [h_a2] at h
          exact toCopy0_ne_copy1 h
        · obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hTrans
          have ha2_copy1 : SplitNode.copy1 w' = a.2 := congrArg Prod.snd hw'_eq
          rw [h_a2] at ha2_copy1
          have hw'w : w' = w := by injection ha2_copy1
          have ha1_copy0 : SplitNode.copy0 w' = a.1 := congrArg Prod.fst hw'_eq
          rw [hw'w] at ha1_copy0
          have h_a1_mid : a.1 = mid := congrArg Prod.fst ha
          rw [h_a1_mid] at ha1_copy0
          have h_mid : mid = SplitNode.copy0 w := ha1_copy0.symm
          cases p' with
          | nil _ _ =>
              match i, hi with
              | 0, hi =>
                  simp only [Walk.IsBifurcationWithSplit] at hi
                  obtain ⟨ha_uv, _⟩ := hi
                  have ha_uv_1 : a.1 = SplitNode.copy1 w := congrArg Prod.fst ha_uv
                  rw [h_a1_mid, h_mid] at ha_uv_1
                  cases ha_uv_1
              | k + 1, hi =>
                  simp only [Walk.IsBifurcationWithSplit] at hi
                  exact hi.2.2
          | @cons _ _ mid2 a2 hStep2 p2 =>
              have h_ne : (p2.vertices : List _) ≠ [] := Walk.vertices_ne_nil p2
              have hmid_inter : mid ∈ W₂.image SplitNode.unsplit := by
                apply hp_inter
                change mid ∈ (mid :: p2.vertices).dropLast
                rw [List.dropLast_cons_of_ne_nil h_ne]
                exact List.mem_cons_self
              rw [h_mid] at hmid_inter
              obtain ⟨_, _, hcontra⟩ := Finset.mem_image.mp hmid_inter
              cases hcontra

-- ## W₁¹-exclusion (target side, auxiliary on bifurcation index).
private lemma not_bif_target_copy1_aux
    {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {W₂ : Finset Node} (hDisj : Disjoint W₁ W₂)
    {w : Node} (hwW₁ : w ∈ W₁) :
    ∀ {x : SplitNode Node} (p : Walk (G.nodeSplittingOn W₁ hW₁) x (SplitNode.copy1 w))
      (i : ℕ),
      p.IsBifurcationWithSplit i →
      (∀ z ∈ p.vertices.tail.dropLast, z ∈ W₂.image SplitNode.unsplit) →
      False
  | _, .nil _ _, _, hi, _ => hi
  | _, .cons _ a _ (.nil _ _), 0, hi, _ => by
      simp only [Walk.IsBifurcationWithSplit] at hi
      obtain ⟨ha_uv, ha_L⟩ := hi
      change a ∈ G.L.image _ at ha_L
      obtain ⟨_, _, he_eq⟩ := Finset.mem_image.mp ha_L
      have h_a2 : a.2 = SplitNode.copy1 w := congrArg Prod.snd ha_uv
      have h := congrArg Prod.snd he_eq
      rw [h_a2] at h
      exact toCopy0_ne_copy1 h
  | _, .cons _ _ _ (.nil _ _), k + 1, hi, _ => by
      simp only [Walk.IsBifurcationWithSplit] at hi
      exact hi.2.2
  | _, .cons mid _ _ (.cons mid' a' hStep' p''), 0, hi, h_inter => by
      simp only [Walk.IsBifurcationWithSplit] at hi
      obtain ⟨_, hp'_dir⟩ := hi
      have hp'_pos :
          (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid' a' hStep' p'').length ≥ 1 := by
        change p''.length + 1 ≥ 1; omega
      have hp'_inter :
          ∀ z ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid' a' hStep' p'').vertices.tail.dropLast,
            z ∈ W₂.image SplitNode.unsplit := by
        intro z hz
        apply h_inter
        change z ∈ (mid :: p''.vertices).dropLast
        have h_ne : p''.vertices ≠ [] := Walk.vertices_ne_nil _
        rw [List.dropLast_cons_of_ne_nil h_ne]
        exact List.mem_cons_of_mem _ hz
      have h_src_eq : mid = SplitNode.copy0 w :=
        walk_target_copy1_source_copy0 (hW₁ := hW₁) hDisj hwW₁
          (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid' a' hStep' p'')
          hp'_dir hp'_pos hp'_inter
      have hmid_inter : mid ∈ W₂.image SplitNode.unsplit := by
        apply h_inter
        change mid ∈ (mid :: p''.vertices).dropLast
        have h_ne : p''.vertices ≠ [] := Walk.vertices_ne_nil _
        rw [List.dropLast_cons_of_ne_nil h_ne]
        exact List.mem_cons_self
      rw [h_src_eq] at hmid_inter
      obtain ⟨_, _, hcontra⟩ := Finset.mem_image.mp hmid_inter
      cases hcontra
  | _, .cons mid _ _ (.cons mid' a' hStep' p''), k + 1, hi, h_inter => by
      simp only [Walk.IsBifurcationWithSplit] at hi
      obtain ⟨_, _, hi_rest⟩ := hi
      have hp'_inter :
          ∀ z ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid' a' hStep' p'').vertices.tail.dropLast,
            z ∈ W₂.image SplitNode.unsplit := by
        intro z hz
        apply h_inter
        change z ∈ (mid :: p''.vertices).dropLast
        have h_ne : p''.vertices ≠ [] := Walk.vertices_ne_nil _
        rw [List.dropLast_cons_of_ne_nil h_ne]
        exact List.mem_cons_of_mem _ hz
      exact not_bif_target_copy1_aux hDisj hwW₁
        (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid' a' hStep' p'') k hi_rest hp'_inter

private lemma not_bif_target_copy1
    {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {W₂ : Finset Node} (hDisj : Disjoint W₁ W₂)
    {w : Node} (hwW₁ : w ∈ W₁) {x : SplitNode Node}
    (p : Walk (G.nodeSplittingOn W₁ hW₁) x (SplitNode.copy1 w))
    (hp_bif : p.IsBifurcation)
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast, z ∈ W₂.image SplitNode.unsplit) :
    False := by
  obtain ⟨_, _, _, i, hi⟩ := hp_bif
  exact not_bif_target_copy1_aux hDisj hwW₁ p i hi hp_inter

-- ## Part (iii) L-field equality.
private lemma split_marg_L_field_eq
    {G : CDMG Node} (W₁ : Finset Node) (hW₁ : W₁ ⊆ G.V)
    (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    ((G.nodeSplittingOn W₁ hW₁).marginalize (W₂.image SplitNode.unsplit)
        (image_unsplit_subset_nodeSplittingOn_V_of_disjoint hW₁ hW₂ hDisj.symm)).L
      = ((G.marginalize W₂ hW₂).nodeSplittingOn W₁
        (subset_sdiff_of_disjoint hW₁ hDisj)).L := by
  apply Finset.ext
  rintro ⟨e1, e2⟩
  change
    (e1, e2) ∈ ((((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
              ∪ W₁.image SplitNode.copy1) \ W₂.image SplitNode.unsplit) ×ˢ
          (((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
              ∪ W₁.image SplitNode.copy1) \ W₂.image SplitNode.unsplit)).filter
        (fun e => e.1 ≠ e.2 ∧
          (G.nodeSplittingOn W₁ hW₁).MarginalizationΦL
            (W₂.image SplitNode.unsplit) e.1 e.2)
    ↔ (e1, e2) ∈ (((G.V \ W₂) ×ˢ (G.V \ W₂)).filter
              (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W₂ e.1 e.2)).image
            (fun e => (toCopy0 W₁ e.1, toCopy0 W₁ e.2))
  rw [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, h2⟩, hNe, hPhi⟩
    -- Reduce (e1, e2).1 / (e1, e2).2 to e1 / e2 in all hypotheses.
    change e1 ∈ _ at h1
    change e2 ∈ _ at h2
    change e1 ≠ e2 at hNe
    change (G.nodeSplittingOn W₁ hW₁).MarginalizationΦL
      (W₂.image SplitNode.unsplit) e1 e2 at hPhi
    -- W₁¹-exclusion for both endpoints.
    have h_e1_not_copy1 : ∀ w, e1 ≠ SplitNode.copy1 w := by
      intro w h_eq
      have hwW₁ : w ∈ W₁ := by
        rw [h_eq] at h1
        obtain ⟨h_in_v, _⟩ := Finset.mem_sdiff.mp h1
        rcases Finset.mem_union.mp h_in_v with h12 | h_c1
        · rcases Finset.mem_union.mp h12 with h_uns | h_c0
          · obtain ⟨_, _, h_uns_eq⟩ := Finset.mem_image.mp h_uns
            cases h_uns_eq
          · obtain ⟨_, _, h_c0_eq⟩ := Finset.mem_image.mp h_c0
            cases h_c0_eq
        · obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h_c1
          have hw'w : w' = w := by injection hw'_eq
          exact hw'w ▸ hw'W₁
      rcases hPhi with ⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩
      · -- Walk e1 → e2; source = e1 = .copy1 w
        exact not_bif_source_copy1 (hW₁ := hW₁) hDisj (h_eq ▸ p)
          (by cases h_eq; exact hp_bif)
          (by cases h_eq; exact hp_inter)
      · -- Walk e2 → e1; target = e1 = .copy1 w
        exact not_bif_target_copy1 (hW₁ := hW₁) hDisj hwW₁ (h_eq ▸ p)
          (by cases h_eq; exact hp_bif)
          (by cases h_eq; exact hp_inter)
    have h_e2_not_copy1 : ∀ w, e2 ≠ SplitNode.copy1 w := by
      intro w h_eq
      have hwW₁ : w ∈ W₁ := by
        rw [h_eq] at h2
        obtain ⟨h_in_v, _⟩ := Finset.mem_sdiff.mp h2
        rcases Finset.mem_union.mp h_in_v with h12 | h_c1
        · rcases Finset.mem_union.mp h12 with h_uns | h_c0
          · obtain ⟨_, _, h_uns_eq⟩ := Finset.mem_image.mp h_uns
            cases h_uns_eq
          · obtain ⟨_, _, h_c0_eq⟩ := Finset.mem_image.mp h_c0
            cases h_c0_eq
        · obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h_c1
          have hw'w : w' = w := by injection hw'_eq
          exact hw'w ▸ hw'W₁
      rcases hPhi with ⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩
      · -- Walk e1 → e2; target = e2 = .copy1 w
        exact not_bif_target_copy1 (hW₁ := hW₁) hDisj hwW₁ (h_eq ▸ p)
          (by cases h_eq; exact hp_bif)
          (by cases h_eq; exact hp_inter)
      · -- Walk e2 → e1; source = e2 = .copy1 w
        exact not_bif_source_copy1 (hW₁ := hW₁) hDisj (h_eq ▸ p)
          (by cases h_eq; exact hp_bif)
          (by cases h_eq; exact hp_inter)
    obtain ⟨u, hu, hu_eq⟩ :=
      exists_underlying_of_mem_split_V_marg_not_copy1 hW₁ hDisj e1 h1 h_e1_not_copy1
    obtain ⟨v, hv, hv_eq⟩ :=
      exists_underlying_of_mem_split_V_marg_not_copy1 hW₁ hDisj e2 h2 h_e2_not_copy1
    refine Finset.mem_image.mpr ⟨(u, v), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, ?_, ?_⟩
      · -- (u, v).1 ≠ (u, v).2, i.e., u ≠ v.
        intro huv
        apply hNe
        change u = v at huv
        rw [hu_eq, hv_eq, huv]
      · have huv_ne : u ≠ v := by
          intro huv
          apply hNe
          rw [hu_eq, hv_eq, huv]
        rw [hu_eq, hv_eq] at hPhi
        exact (split_marg_PhiL_iff hW₁ hDisj huv_ne).mp hPhi
    · exact Prod.ext hu_eq.symm hv_eq.symm
  · intro h_lifted
    obtain ⟨⟨u, v⟩, hUV_mem, hUV_eq⟩ := Finset.mem_image.mp h_lifted
    rw [Finset.mem_filter, Finset.mem_product] at hUV_mem
    obtain ⟨⟨hu_in, hv_in⟩, hNe, hPhi⟩ := hUV_mem
    have h1_eq : e1 = toCopy0 W₁ u := congrArg Prod.fst hUV_eq.symm
    have h2_eq : e2 = toCopy0 W₁ v := congrArg Prod.snd hUV_eq.symm
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [h1_eq]
      exact mem_split_V_marg_of_mem_V_W₂_toCopy0 hW₁ hu_in
    · rw [h2_eq]
      exact mem_split_V_marg_of_mem_V_W₂_toCopy0 hW₁ hv_in
    · rw [h1_eq, h2_eq]
      intro h_eq
      exact hNe (toCopy0_inj_node h_eq)
    · rw [h1_eq, h2_eq]
      exact (split_marg_PhiL_iff hW₁ hDisj hNe).mpr hPhi

-- claim_3_18 -- start statement
theorem marginalize_nodeSplittingOn_comm (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (G.nodeSplittingOn W₁ hW₁).marginalize (W₂.image SplitNode.unsplit)
        (image_unsplit_subset_nodeSplittingOn_V_of_disjoint hW₁ hW₂ hDisj.symm)
      = (G.marginalize W₂ hW₂).nodeSplittingOn W₁
        (subset_sdiff_of_disjoint hW₁ hDisj)
-- claim_3_18 -- end statement
:= by
  -- CDMG.ext: prove four data fields agree.
  have cdmgExt : ∀ {G₁ G₂ : CDMG (SplitNode Node)},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨_, _, _, _, _, _, _, _, _⟩
           ⟨_, _, _, _, _, _, _, _, _⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL; rfl
  refine cdmgExt ?_ ?_ ?_ ?_
  · -- J: marginalize and nodeSplittingOn both preserve G.J's image under .unsplit.
    rfl
  · -- V: ((G.V \ W₁).image .unsplit ∪ W₁.image .copy0 ∪ W₁.image .copy1) \ W₂.image .unsplit
    --   = ((G.V \ W₂) \ W₁).image .unsplit ∪ W₁.image .copy0 ∪ W₁.image .copy1
    -- Strategy: the W₂.image .unsplit slice only intersects the .unsplit-piece;
    -- the .copy0 / .copy1 pieces survive intact.  Then apply image_split_unsplit_sdiff
    -- and sdiff_right_comm.
    change ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
              ∪ W₁.image SplitNode.copy1) \ (W₂.image SplitNode.unsplit)
        = ((G.V \ W₂) \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
              ∪ W₁.image SplitNode.copy1
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨h_main, h_notW₂⟩
      rcases h_main with (h_uns_or_c0 | h_c1)
      · rcases h_uns_or_c0 with h_uns | h_c0
        · -- x ∈ (G.V \ W₁).image .unsplit
          obtain ⟨v, ⟨hvV, hvNW₁⟩, rfl⟩ := h_uns
          refine Or.inl (Or.inl ⟨v, ⟨⟨hvV, ?_⟩, hvNW₁⟩, rfl⟩)
          intro hvW₂
          exact h_notW₂ ⟨v, hvW₂, rfl⟩
        · -- x ∈ W₁.image .copy0
          exact Or.inl (Or.inr h_c0)
      · exact Or.inr h_c1
    · rintro (h_uns_or_c0 | h_c1)
      · rcases h_uns_or_c0 with h_uns | h_c0
        · -- x ∈ ((G.V \ W₂) \ W₁).image .unsplit
          obtain ⟨v, ⟨⟨hvV, hvNW₂⟩, hvNW₁⟩, rfl⟩ := h_uns
          refine ⟨Or.inl (Or.inl ⟨v, ⟨hvV, hvNW₁⟩, rfl⟩), ?_⟩
          rintro ⟨w, hw, hEq⟩
          have : w = v := by injection hEq
          exact hvNW₂ (this ▸ hw)
        · -- x ∈ W₁.image .copy0 — distinct constructor from .unsplit
          obtain ⟨w, hw, rfl⟩ := h_c0
          refine ⟨Or.inl (Or.inr ⟨w, hw, rfl⟩), ?_⟩
          rintro ⟨v, _, hEq⟩
          cases hEq
      · -- x ∈ W₁.image .copy1
        obtain ⟨w, hw, rfl⟩ := h_c1
        refine ⟨Or.inr ⟨w, hw, rfl⟩, ?_⟩
        rintro ⟨v, _, hEq⟩
        cases hEq
  · -- E: complex case analysis on edge constructors (.unsplit_pair, transfer .copy0/.copy1).
    exact split_marg_E_field_eq W₁ hW₁ W₂ hW₂ hDisj
  · -- L: bifurcation surgery (no transfer edges interact with L since L uses copy0 only).
    exact split_marg_L_field_eq W₁ hW₁ W₂ hW₂ hDisj

end CDMG

end Causality
