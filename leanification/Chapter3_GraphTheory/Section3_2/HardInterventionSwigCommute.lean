import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard
import Chapter3_GraphTheory.Section3_2.HardInterventionNodeSplittingCommute

-- TeX statement: tex/claim_3_11_statement_DisjointHardInterventions.tex
-- TeX proof: tex/claim_3_11_proof_DisjointHardInterventions.tex (Manager B)

/-!
# Disjoint hard interventions and node-splitting hard interventions (SWIGs) commute (claim_3_11)

This file formalises the lecture notes' lemma "disjoint hard
interventions and node-splitting hard interventions commute" --
`lecture-notes/lecture_notes/graphs.tex` Lem at lines 666 -- 671.
The LN states the equality

  `(G_{do(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{do(W₁)}`

under the prose preconditions `W₁ ⊆ J ∪ V`, `W₂ ⊆ V`, and
`Disjoint W₁ W₂` (LN proof at lines 672 -- 700).

This is the **SWIG mirror** of claim_3_8
(`HardInterventionNodeSplittingCommute.lean`): the same shape with
`\swig` in place of `\spl` on the inner operation, and dependence on
`def_3_12` (`NodeSplittingHard.lean`) instead of `def_3_11`. The two
sides of the equation share the carrier `α ⊕ ↑W₂`, so the statement
is a literal `Eq` of CDMGs -- the same regime as claim_3_8 -- not a
`CDMGEquiv`.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

/-! ## Local CDMG-extensionality helper -/

/-- Local CDMG-extensionality helper for this row: two CDMGs over the
same carrier are equal as soon as their four data fields `J / V / E / L`
agree. The six prop fields close by proof irrelevance after the data
fields are pinned down.

Re-declared verbatim from `HardInterventionNodeSplittingCommute.lean`
lines 128 -- 140 (the claim_3_8 sibling) rather than imported, per the
workspace plan (lines 105 -- 112): the helper is carrier-generic, so
duplicating ten lines is the right trade-off against pulling in
claim_3_8's row-specific E/L case-splits as a build-graph dependency,
and `CDMG` is intentionally not `@[ext]`-tagged so we keep this
helper `private`. -/
private theorem mk_eq_of_data {G H : CDMG α}
    (hJ : G.J = H.J) (hV : G.V = H.V) (hE : G.E = H.E) (hL : G.L = H.L) :
    G = H := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := G
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := H
  subst hJ
  subst hV
  subst hE
  subst hL
  rfl

/-! ## The commute identity -/

-- claim_3_11
-- title: DisjointHardInterventions
--
-- Hard intervention on a set `W₁` and node-splitting hard intervention
-- (SWIG) on a set `W₂ ⊆ G.V` commute when `W₁` and `W₂` are disjoint:
-- `(G_{do(W₁)})_{swig(W₂)} = (G_{swig(W₂)})_{do(W₁)}`. On the RHS the
-- hard intervention's target set is the canonical `Sum.inl`-lift of
-- `W₁` (since the post-SWIG graph lives over the carrier `α ⊕ ↑W₂`);
-- under our convention `Sum.inl = 0-copy = canonical observation
-- copy` (see `NodeSplittingOn.lean` lines 244 -- 269), this matches
-- the LN's implicit identification `α ≅ inl '' α` exactly.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 666 -- 671)
-- the prose paragraph and displayed equation are reflowed for the
-- 100-character line limit (linewrap only; LaTeX whitespace collapses
-- between tokens, so this is verbatim under \LaTeX semantics):

\begin{claimmark}
\begin{Lem}[Disjoint hard interventions and node-splitting hard interventions commute]
   Let $G=(J,V,E,L)$ be a CADMG and $W_1 \ins J \cup V$ and $W_2 \ins V$
   two disjoint subsets of nodes from $G$.
   Then the CADMG obtained from first hard intervening on $W_1$ and then
   node-splitting on $W_2$ is the same CDMG that arises from first
   node-splitting on $W_2$ and then hard intervening on $W_1$.
      \[ \lp G_{\doit(W_1)} \rp_{\swig(W_2)} =  \lp G_{\swig(W_2)} \rp_{\doit(W_1)}.   \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_11 (`DisjointHardInterventions`): for a CDMG `G : CDMG α`
and disjoint subsets `W₁ W₂ : Set α` with `W₂ ⊆ G.V`, hard intervention
on `W₁` and the node-splitting hard intervention (SWIG) on `W₂`
commute. Mirrors the displayed equation in the `\Lem` at
`lecture-notes/lecture_notes/graphs.tex` line 669.

## Design choice

* **Literal `Eq`, not `CDMGEquiv`.** Both sides have carrier
  `α ⊕ ↑W₂`. On the LHS, `G.hardInterventionOn W₁` is
  carrier-preserving (`α → α`; see `HardInterventionOn.lean`
  lines 225 -- 232) and then `swig W₂` extends to `α ⊕ ↑W₂`. On
  the RHS, `G.swig W₂ hW₂` extends to `α ⊕ ↑W₂` and then
  `hardInterventionOn` is carrier-preserving
  (`α ⊕ ↑W₂ → α ⊕ ↑W₂`). The SWIG itself inherits the carrier
  shape verbatim from `nodeSplittingOn` -- the inner HI layer of
  `swig` does not touch the carrier, as recorded by the four
  `@[simp]` lemmas `nodeSplittingHardInterventionOn_J/V` and
  `mem_nodeSplittingHardInterventionOn_E/L` in
  `NodeSplittingHard.lean` lines 237 -- 319, all of which leave
  `α ⊕ ↑W` untouched. The two iterated carriers are therefore
  *definitionally* equal, so literal `Eq` is type-correct -- the
  same regime as claim_3_8
  (`HardInterventionNodeSplittingCommute.lean` lines 20 -- 44)
  and claim_3_4 (`HardInterventionsCommute.lean`).

  Contrast with the SWIG--SWIG sibling claim_3_10
  (`TwoDisjointSwigsCommute.lean`), which iterates *two* SWIGs
  on disjoint sets: there the carriers are
  `(α ⊕ ↑W₁) ⊕ ↑(Sum.inl '' W₂)` vs
  `(α ⊕ ↑W₂) ⊕ ↑(Sum.inl '' W₁)`, which differ def-equally even
  before checking field equality, and claim_3_10 has to use
  `CDMGEquiv` (the carrier-rewriting regime). In our row `swig`
  is applied *only once* and on the *same set `W₂`* on each
  side, and the partner operation is the carrier-preserving
  `hardInterventionOn`; that absorbs the iteration without
  forcing a re-labeling bijection.

* **No `W₁ ⊆ G.J ∪ G.V` precondition.** The LN writes
  `W₁ ⊆ J ∪ V`, but `G.hardInterventionOn W₁` is well-defined
  for every `W₁ : Set α` -- see the definition itself at
  `HardInterventionOn.lean` lines 225 -- 232 ("intentionally
  well-defined for every `W : Set α`, with no `W ⊆ G.J ∪ G.V`
  precondition") and the longer design notes at lines
  88 -- 215. The same drop is made in the `\spl` sibling
  claim_3_8 at `HardInterventionNodeSplittingCommute.lean`
  lines 236 -- 248, with the same justification we echo here:
  vertices in `W₁ \ (G.J ∪ G.V)` are inert under
  `hardInterventionOn` (no edge has an endpoint there, by
  `G.E_subset` and `G.L_subset`), so they ride along the
  LHS / RHS equality without contributing anything, and the
  commute identity holds for arbitrary `W₁`. The LN's
  `W₁ ⊆ J ∪ V` is informal scaffolding ("`W₁ ⊆ G`" so that
  `\doit(W₁)` is meaningful in prose), not a load-bearing
  hypothesis.

* **`hW₂ : W₂ ⊆ G.V` is structurally required on both sides;
  the LHS slot consumes the bridge
  `subset_hardInterventionOn_V_of_disjoint hW₂ hdisj`.** `swig`
  is defined in `NodeSplittingHard.lean` lines 205 -- 207 to
  demand `W ⊆ G.V`, so both occurrences in the conclusion need
  a containment proof. The RHS slot consumes `hW₂` directly.
  The LHS's inner `swig W₂` is applied to
  `G.hardInterventionOn W₁`, whose vertex set is `G.V \ W₁`
  (`hardInterventionOn_V` at `HardInterventionOn.lean`
  lines 275 -- 276), so we need `W₂ ⊆ G.V \ W₁`; disjointness
  of `W₁` from `W₂` plus `W₂ ⊆ G.V` is exactly enough. The
  helper that packages this discharge lives in
  `HardInterventionNodeSplittingCommute.lean`
  lines 175 -- 182, where it was introduced for claim_3_8 and
  explicitly kept *public* with the design note "The SWIG
  analogue (claim_3_11) will re-use this same helper unchanged"
  (sibling file lines 162 -- 167). This row is that anticipated
  second consumer; we use the helper verbatim and add no new
  design choice on it. Both `hW₂` and `hdisj` are therefore
  load-bearing: dropping either makes the LHS fail to
  elaborate.

* **Lift `W₁ ↦ Sum.inl '' W₁` on the RHS's HI argument.** The
  outer operation on the RHS is hard intervention on the
  *post-SWIG* graph `G.swig W₂ hW₂`, which lives over the
  carrier `α ⊕ ↑W₂`. Its target set must therefore be a
  `Set (α ⊕ ↑W₂)`, not a `Set α`. The natural lift is
  `Sum.inl '' W₁`: under the convention
  `Sum.inl = 0-copy = canonical observation copy` established in
  `NodeSplittingOn.lean` lines 244 -- 269 and inherited by
  `NodeSplittingHard.lean`, the LN's "the same `W₁`" *is* the
  `inl`-image of `W₁` in the SWIG carrier. The LN writes `W₁`
  on both sides because it identifies `α ≅ inl '' α` implicitly
  throughout def_3_11 / def_3_12 (LN hint at `graphs.tex`
  line 197 "we ... make the identification `W = W^o`"); Lean's
  stricter type discipline forces us to spell the lift out.
  Without it we would be intervening on a nonsensical set in
  `α ⊕ ↑W₂` and the `Eq` would not even be type-correct -- so
  the lift is forced by carrier-typing first, and only
  secondarily by faithfulness to LN intent.

  This is faithful to that LN intent. Vertices of `W₁ ∩ G.J`
  survive into the SWIG as
  `Sum.inl '' (G.J ∩ W₁) ⊆ Sum.inl '' G.J ⊆ (G.swig W₂ hW₂).J`,
  and vertices of `W₁ ∩ G.V` survive as
  `Sum.inl '' (G.V ∩ W₁) ⊆ Sum.inl '' G.V = (G.swig W₂ hW₂).V`
  -- note that for SWIG, `V` is *just* `Sum.inl '' G.V` (the
  `range Sum.inr` piece carried by bare `nodeSplittingOn` is
  killed by the SWIG's inner HI; `nodeSplittingHardInterventionOn_V`
  in `NodeSplittingHard.lean` lines 253 -- 267). So removing
  `Sum.inl '' W₁` from the SWIG mirrors the LN's "then
  `\doit(W₁)`" on the right-hand side exactly. Vertices of
  `W₁ \ (G.J ∪ G.V)`, which are inert anyway by the previous
  bullet, ride along under `Sum.inl` too. The same lift / same
  justification is used in the `\spl` sibling claim_3_8 at
  `HardInterventionNodeSplittingCommute.lean` lines 294 -- 332,
  which also rejects the narrower lift
  `Sum.inl '' (W₁ ∩ (G.J ∪ G.V))` for the same two reasons
  (inert vertices give the same RHS CDMG; the narrower lift
  would force every call site to thread the `W₁ ⊆ J ∪ V` fact).

* **Surface API `G.swig W hW`, not the long-form
  `nodeSplittingHardInterventionOn`.** The four `@[simp]`
  characterisation lemmas in `NodeSplittingHard.lean`
  (`nodeSplittingHardInterventionOn_J/V`,
  `mem_nodeSplittingHardInterventionOn_E/L`, lines 237 -- 319)
  are stated about the long-form name but fire on `G.swig W hW`
  by reducibility, because `swig` is declared as a
  `noncomputable abbrev` (`NodeSplittingHard.lean`
  lines 192 -- 207). Choosing `swig` in the statement therefore
  loses nothing simp-wise and gains the LN's notation verbatim
  (`G_{\swig(W)}` in prose ↔ `G.swig W` in Lean). Manager B's
  proof can rewrite against the four `@[simp]` lemmas without
  any extra `unfold swig` step.

* **Argument order `hW₂` before `hdisj`.** Mirrors the
  signature of the `\spl` sibling
  `hardInterventionOn_nodeSplittingOn_comm`
  (`HardInterventionNodeSplittingCommute.lean`
  lines 381 -- 386). The two commute lemmas
  (`_nodeSplittingOn_comm` and `_swig_comm`) form a parallel
  pair; identical hypothesis order lets a downstream consumer
  swap one for the other by pattern with zero call-site churn.
  Same convention as the helper
  `subset_hardInterventionOn_V_of_disjoint` itself (same file
  lines 175 -- 178), so the bridging discharge slots in
  left-to-right without any re-ordering.

* **`G : CDMG α` implicit; `W₁ W₂ : Set α` implicit; `hW₂` and
  `hdisj` explicit.** Both sets appear in the hypotheses and in
  the conclusion, so the elaborator can recover them from
  either side; making them implicit matches the `\spl` sibling
  `hardInterventionOn_nodeSplittingOn_comm`
  (`HardInterventionNodeSplittingCommute.lean`
  lines 381 -- 386) and the SWIG--SWIG sibling
  `swig_comm_equiv` (`TwoDisjointSwigsCommute.lean`
  lines 485 -- 492), maintaining the sets-pinned-by-hypotheses
  convention across the four commute lemmas of the subsection.

* **Naming `hardInterventionOn_swig_comm`.** Follows the
  Mathlib `_comm` convention for commutativity of two operators
  (`add_comm`, `mul_comm`, `Set.union_comm`), with operators in
  the name (left to right matching the LHS of the conclusion).
  The subsection's commute-lemma family now reads as a uniform
  menu: `_comm` for the literal-`Eq` rows
  (`hardInterventionOn_comm` for claim_3_4,
  `hardInterventionOn_nodeSplittingOn_comm` for claim_3_8,
  `hardInterventionOn_swig_comm` for this row) and `_comm_equiv`
  for the `CDMGEquiv` rows (`nodeSplittingOn_comm_equiv` for
  claim_3_7, `swig_comm_equiv` for claim_3_10). The mirror
  `swig_hardInterventionOn_comm` (operators reversed) is
  technically equivalent but not exposed -- consumers can use
  `.symm` if they want the swap; we follow the LN's
  LHS-then-RHS reading order.

* **Distinct from the downstream claim_3_15.** claim_3_15
  (`graphs.tex` "Adding intervention nodes commutes with
  disjoint node-splitting hard interventions",
  `tex/claim_3_15_statement_AddingInterventionNodes.tex`)
  states a *different* commute identity:
  `(G_{\swig(W_1)})_{\doit(I_{W_2})} = (G_{\doit(I_{W_2})})_{\swig(W_1)}`,
  where `\doit(I_{W_2})` is the intervention on the
  *intervention-node extension* `I_{W_2}` of `W₂`, not on `W₂`
  itself. claim_3_11 here is the direct SWIG-mirror of
  claim_3_8 with `swig` in place of `nodeSplittingOn` and is
  *foundational* -- not a special case or corollary of any
  later commute lemma, and not the same statement as claim_3_15
  even though the displayed equations look superficially
  similar. Flagging the distinction so a future reader does not
  collapse the two rows. -/
theorem hardInterventionOn_swig_comm
    {G : CDMG α} {W₁ W₂ : Set α}
    (hW₂ : W₂ ⊆ G.V) (hdisj : Disjoint W₁ W₂) :
    (G.hardInterventionOn W₁).swig W₂
        (subset_hardInterventionOn_V_of_disjoint hW₂ hdisj)
      = (G.swig W₂ hW₂).hardInterventionOn (Sum.inl '' W₁) := by
  -- Mirrors `tex/claim_3_11_proof_DisjointHardInterventions.tex`: four
  -- component-wise checks J / V / E / L, via `mk_eq_of_data`. The
  -- SWIG `@[simp]` lemmas (`nodeSplittingHardInterventionOn_J/V`,
  -- `mem_nodeSplittingHardInterventionOn_E/L` in `NodeSplittingHard.lean`)
  -- fire on `G.swig W hW` by `abbrev`-reducibility. The LN proof's
  -- `v_k^o ∈ W_1 ↔ v_k ∈ W_1` case-split collapses here to
  -- `Sum.inl` injectivity (uniform `inl`-embedding for all of `α`).
  refine mk_eq_of_data ?_ ?_ ?_ ?_
  · -- Node sets, `J` half (TeX "Node sets" section, left half).
    -- LHS = `Sum.inl '' (G.J ∪ W₁) ∪ Set.range Sum.inr`;
    -- RHS = `(Sum.inl '' G.J ∪ Set.range Sum.inr) ∪ Sum.inl '' W₁`.
    -- Both equal `Sum.inl '' G.J ∪ Sum.inl '' W₁ ∪ Set.range Sum.inr`
    -- after distributing `Sum.inl` over the union and using
    -- `union_right_comm` to swap the last two summands.
    simp only [nodeSplittingHardInterventionOn_J, hardInterventionOn_J,
      Set.image_union]
    exact Set.union_right_comm _ _ _
  · -- Node sets, `V` half (TeX "Node sets" section, right half).
    -- LHS = `Sum.inl '' (G.V \ W₁)`; RHS = `Sum.inl '' G.V \ Sum.inl '' W₁`.
    -- The SWIG kills the `Set.range Sum.inr` summand of the bare-NS V
    -- (`nodeSplittingHardInterventionOn_V` lines 253 -- 267 in
    -- `NodeSplittingHard.lean`), so there is *no* extra summand on
    -- either side to manage -- the V step reduces to `image_diff` for
    -- the injective `Sum.inl`.
    simp only [nodeSplittingHardInterventionOn_V, hardInterventionOn_V]
    exact Set.image_diff Sum.inl_injective G.V W₁
  · -- Directed edges (TeX "Directed edges" section).
    -- The SWIG kills the bare-NS split edges (target in `Set.range
    -- Sum.inr`), so both sides only have the "original edge" piece.
    -- Goal after simp: `∃ v₁ v₂, ((v₁, v₂) ∈ G.E ∧ v₂ ∉ W₁) ∧
    --     p = (split1 W₂ v₁, Sum.inl v₂)
    --   ↔ (∃ v₁ v₂, (v₁, v₂) ∈ G.E ∧ p = (split1 W₂ v₁, Sum.inl v₂))
    --     ∧ p.2 ∉ Sum.inl '' W₁`.
    -- Target `p.2 = Sum.inl v₂`; `Sum.inl v₂ ∈ Sum.inl '' W₁ ↔ v₂ ∈ W₁`
    -- by `Sum.inl_injective`.
    ext p
    simp only [mem_nodeSplittingHardInterventionOn_E, mem_hardInterventionOn_E]
    constructor
    · rintro ⟨v₁, v₂, ⟨hE, hv₂⟩, rfl⟩
      refine ⟨⟨v₁, v₂, hE, rfl⟩, ?_⟩
      rintro ⟨z, hzW, hzeq⟩
      exact hv₂ (Sum.inl_injective hzeq ▸ hzW)
    · rintro ⟨⟨v₁, v₂, hE, rfl⟩, hno⟩
      refine ⟨v₁, v₂, ⟨hE, ?_⟩, rfl⟩
      intro hv₂W
      exact hno ⟨v₂, hv₂W, rfl⟩
  · -- Bidirected edges (TeX "Bidirected edges" section).
    -- Identical shape to claim_3_8's L block. Both endpoints become
    -- `Sum.inl vₖ`, so `Sum.inl vₖ ∈ Sum.inl '' W₁ ↔ vₖ ∈ W₁` by
    -- `Sum.inl_injective`. Both sides exclude exactly the same pairs.
    ext p
    simp only [mem_nodeSplittingHardInterventionOn_L, mem_hardInterventionOn_L]
    constructor
    · rintro ⟨v₁, v₂, ⟨hL, hv₁, hv₂⟩, rfl⟩
      refine ⟨⟨v₁, v₂, hL, rfl⟩, ?_, ?_⟩
      · rintro ⟨z, hzW, hzeq⟩
        exact hv₁ (Sum.inl_injective hzeq ▸ hzW)
      · rintro ⟨z, hzW, hzeq⟩
        exact hv₂ (Sum.inl_injective hzeq ▸ hzW)
    · rintro ⟨⟨v₁, v₂, hL, rfl⟩, hno₁, hno₂⟩
      refine ⟨v₁, v₂, ⟨hL, ?_, ?_⟩, rfl⟩
      · intro h₁W
        exact hno₁ ⟨v₁, h₁W, rfl⟩
      · intro h₂W
        exact hno₂ ⟨v₂, h₂W, rfl⟩

end CDMG

end Causality
