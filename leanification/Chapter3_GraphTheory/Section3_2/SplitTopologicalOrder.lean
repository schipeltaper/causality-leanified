import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_1.AcyclicIffTopologicalOrder
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn

-- TeX proof: tex/claim_3_6_proof_SplitTopologicalOrder.tex
-- Refactor (claim_3_2_no_finite): tex/refactor_claim_3_6_proof_SplitTopologicalOrder.tex

/-!
# Acyclicity and topological orders survive node-splitting (claim_3_6)

This file formalises the lecture notes' remark immediately following
the definition of the node-splitting `G_{\spl(W)}` (def_3_11): if `G`
is a CADMG (i.e. acyclic) and `W ⊆ G.V`, then `G.nodeSplittingOn W hW`
is also acyclic; furthermore, given a topological order `<` of `G`,
an *explicit* topological order on `G.nodeSplittingOn W hW` can be
built by interleaving each `v_j ∈ W` with two new index slots
`j - 1/3` and `j + 1/3` for `v_j^0` and `v_j^1` respectively, then
re-sorting. See `lecture-notes/lecture_notes/graphs.tex` Rem at
lines 444 -- 455.

The LN bundles two distinct mathematical statements under one `\Rem`
block; we split them into two theorems, mirroring `claim_3_3`'s
two-theorem decomposition (`isAcyclic_hardInterventionOn` +
`isTopologicalOrder_hardInterventionOn`) for the analogous remark
attached to `hardInterventionOn`. The two halves carry different
proof shapes and the per-theorem design notes below justify the
split:

* `isTopologicalOrder_nodeSplittingOn` -- the **core constructive
  content** of the remark: from a topological order `r` of `G` and
  `hW : W ⊆ G.V`, produce a *named* topological order
  `splitOrder W r` of `G.nodeSplittingOn W hW`. The construction is
  the LN's "assign `v_j^0` the index `j - 1/3` and `v_j^1` the index
  `j + 1/3`", encoded as a four-case pattern match on the carrier
  `α ⊕ ↑W`. No `[Finite α]` is needed: the construction is purely
  relational (it does not enumerate vertices), and the four
  `IsTopologicalOrder` fields transport via the `@[simp]`
  membership lemmas of `NodeSplittingOn.lean`.

* `isAcyclic_nodeSplittingOn` -- acyclicity preservation. The
  statement-phase signature keeps `[Finite α]` *off* the
  hypothesis list. Two proof routes are available to the prover:
  (i) via `isTopologicalOrder_nodeSplittingOn` plus claim_3_2
  (`isAcyclic_iff_hasTopologicalOrder`), at the cost of pulling in
  `[Finite α]` for the `→` half of claim_3_2; (ii) a direct
  walk-lifting argument analogous to claim_3_3 part A, lifting a
  hypothetical cycle in `G.nodeSplittingOn W hW` back to a cycle in
  `G` via `Sum.inl ↦ id, Sum.inr ⟨w, _⟩ ↦ w` plus compression of
  the trivial `Sum.inl w → Sum.inr ⟨w, hw⟩` split edges. Route
  (ii) is preferred by precedent (claim_3_3 part A is direct and
  finiteness-free) and would let the iSCM chapters apply this
  result over not-yet-finitised vertex types; we leave the choice
  to the prover. If finiteness turns out to be unavoidable, the
  prover can request a `correct_tex_proof` to add `[Finite α]`.

## Where this gets used downstream

* **claim_3_9** (`graphs.tex` Rem, "SWIG acyclic topological
  order") -- the SWIG `G_{\swig(W)}` is a node-splitting composed
  with a hard intervention (def_3_12 `nodeSplittingHard`); its
  acyclicity / topological-order preservation reads as this
  claim_3_6 result composed with claim_3_3
  (`AcyclicUnderIntervention`).
* **claim_3_7 / claim_3_8 / claim_3_12** (commutation and
  composition of `nodeSplittingOn` with itself and with
  `hardInterventionOn`) -- iterated node-splitting reasoning often
  needs acyclicity of intermediate split graphs to talk about
  topological orders or directed walks.
* **Chapters 8 -- 10 (iSCMs, SWIGs and counterfactuals)** -- the
  Richardson--Robins SWIG machinery and the iSCM uniqueness
  theory both quote the split graph's topological order along
  which mechanisms are evaluated. The `splitOrder` defined here
  is *exactly* the order they use.
* **Chapters 11 -- 16 (causal discovery)** -- FCI and related
  algorithms reduce reasoning about latent confounding to
  reasoning on a derived split-and-projected graph; acyclicity of
  the split graph is the (often implicit) sanity check.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

/-! ### The split-order construction

The LN's "index `j` for `v_j`, `j - 1/3` for `v_j^0`, `j + 1/3` for
`v_j^1`" recipe is encoded below as a four-case pattern match on
the carrier `α ⊕ ↑W`. We do *not* commit to an actual `Real`-valued
index function: the index recipe is a *device* for visualising why
the induced order is a topological order. The induced order itself
is what we formalise, and it is fully determined by the original
order `r` and the case-split on which "copy" each endpoint sits in.

The four cases are read off the index recipe as follows. Let
`idx(v) := j` for `v = v_j` in the original enumeration of
`G.J ∪ G.V` (so `r v w ↔ idx(v) < idx(w)` for `v, w ∈ G`), with the
LN's `±1/3` shifts on the split copies:

* **`(Sum.inl v₁, Sum.inl v₂)`** -- both endpoints are 0-copies, so
  if `v_i ∈ W` they sit at `idx(v_i) − 1/3`, and if `v_i ∉ W` they
  sit at `idx(v_i)`. In either configuration the LHS--RHS shift is
  the same, so `idx(v₁) − ε₁ < idx(v₂) − ε₂` iff `idx(v₁) < idx(v₂)`
  iff `r v₁ v₂`. (Integer-spaced indices and a `1/3` shift cannot
  reorder pairs that already disagreed on the original integers.)
* **`(Sum.inr ⟨w₁,_⟩, Sum.inr ⟨w₂,_⟩)`** -- both 1-copies, both
  shifted by `+1/3`; offsets cancel and the case collapses to
  `r w₁ w₂`.
* **`(Sum.inl v, Sum.inr ⟨w,_⟩)`** -- LHS sits at `idx(v)` (or
  `idx(v) − 1/3` if `v ∈ W`); RHS sits at `idx(w) + 1/3`. The
  inequality `idx(LHS) < idx(RHS)` is equivalent to
  `idx(v) ≤ idx(w)` (integer-spaced indices + a `+1/3` gap rule out
  any non-integer middle ground), i.e. `r v w ∨ v = w`. When
  `v ∉ W`, the disjunct `v = w` would force `v ∈ W` (since `w ∈ W`),
  so it vacuously fails and the case collapses to `r v w`. When
  `v = w ∈ W`, the disjunct *does* fire (it's the "split edge"
  case: `v^0` precedes `v^1`), and this is exactly the
  configuration where the split graph adds a fresh directed edge
  `(Sum.inl w, Sum.inr w)` that `parent_lt` must respect.
* **`(Sum.inr ⟨w,_⟩, Sum.inl v)`** -- LHS sits at `idx(w) + 1/3`,
  RHS at `idx(v)` (or `idx(v) − 1/3` if `v ∈ W`). The inequality
  `idx(LHS) < idx(RHS)` reduces to `idx(w) < idx(v)`, i.e.
  `r w v`. No `w = v` disjunct: if `v ∈ W` and `w = v`, the LHS is
  `idx(v) + 1/3` and the RHS is `idx(v) − 1/3`, which is *strictly
  greater*, not less -- correctly excluded by `r`'s irreflexivity
  applied to `w = v`.
-/

-- ## Design choice (`splitOrder`)
--
-- * **Standalone helper rather than an inlined `match`.** The
--   `splitOrder W r` relation is used in *both* halves of this
--   row (Part A directly; Part B optionally via claim_3_2) and is
--   itself the LN's named construction. Factoring it out gives a
--   single referent for "the topological order on the split graph
--   from a topological order on `G`" -- downstream rows (claim_3_9
--   for SWIGs, the iSCM chapters quoting "the topological order
--   inherited from the split") can talk about this exact relation
--   by name rather than re-deriving the four-case match each time.
-- * **No `G : CDMG α` argument.** The relation is defined purely
--   on the carrier `α ⊕ ↑W` and is parameterised by `W : Set α`
--   and `r : α → α → Prop`; it does not need to inspect any
--   structure of `G`. Keeping `G` out of the signature means
--   `splitOrder` composes with arbitrary preorders / relations on
--   `α`, not just topological orders of some specific CDMG -- e.g.
--   the `IsTopologicalOrder` proof can pattern-match against
--   `splitOrder W r` without first instantiating `G`. The
--   `G.IsTopologicalOrder r` hypothesis enters only when we ask
--   `(G.nodeSplittingOn W hW).IsTopologicalOrder (splitOrder W r)`.
-- * **`Sum`-shaped pattern match, not `dite` on `v ∈ W`.** The
--   carrier `α ⊕ ↑W` already encodes the 0-copy / 1-copy
--   distinction at the type level (via the `Sum.inl` / `Sum.inr`
--   constructors), so a pattern match is the natural shape. A
--   `dite v ∈ W` approach would force every case to
--   `Classical.propDecidable` the membership and would lose the
--   structural recursion that `Sum.casesOn` provides "for free".
-- * **`r v w ∨ v = w` on the `(inl, inr)` case, not just `r v w`.**
--   The disjunct `v = w` is the LN's "split edge" condition: when
--   `v = w ∈ W`, the split graph adds a fresh directed edge
--   `(Sum.inl w, Sum.inr w)`, and `parent_lt` on
--   `(G.nodeSplittingOn W hW).IsTopologicalOrder (splitOrder W r)`
--   demands that this edge be respected. Encoding `v = w` as a
--   disjunct (rather than as a side condition or a separate edge
--   case) keeps the construction first-order and lets the proof
--   of `parent_lt` discharge the split-edge case via `Or.inr rfl`.
--   The asymmetry "the `(inl, inr)` case has the `v = w` disjunct
--   but the `(inr, inl)` case does not" is *not* a typo or
--   oversight: it reflects the directed nature of the LN's
--   split-edge convention `w^0 → w^1`, i.e. the `±1/3` shift
--   makes `(Sum.inl w, Sum.inr w)` an edge but `(Sum.inr w,
--   Sum.inl w)` not an edge.
-- * **`noncomputable`.** The relation `r` is `Prop`-valued and
--   need not be decidable. Marking `splitOrder` `noncomputable`
--   keeps the construction consistent with `NodeSplittingOn`'s
--   own `noncomputable` `nodeSplittingOn`; downstream uses are
--   all `Prop`-valued (membership in `IsTopologicalOrder`), so
--   the choice has no observable cost.

/-- The *split-order* `splitOrder W r` on the carrier `α ⊕ ↑W`,
induced by a relation `r : α → α → Prop` and a set `W : Set α`.
This is the LN's interleaving recipe from claim_3_6: assign each
`v_j ∈ W` two new index slots `j − 1/3` (for `v_j^0 = Sum.inl v_j`)
and `j + 1/3` (for `v_j^1 = Sum.inr ⟨v_j, hv_j⟩`), then order by
index value. The four cases of the pattern match correspond to the
four `(Sum.inl/inr, Sum.inl/inr)` corner pairs; see the design block
above and the file-level docstring for the index-recipe derivation.

`noncomputable` because we do not assume any decidability on `r` or
`v ∈ W`; downstream uses are all `Prop`-valued so the classical
choice has no observable cost. Used by
`isTopologicalOrder_nodeSplittingOn` (this file) and quoted by name
in claim_3_9 (SWIG topological order) and the iSCM uniqueness
theory of chapters 8 -- 10. -/
noncomputable def splitOrder (W : Set α) (r : α → α → Prop) :
    (α ⊕ ↑W) → (α ⊕ ↑W) → Prop
  | Sum.inl v₁, Sum.inl v₂ => r v₁ v₂
  | Sum.inr ⟨w₁, _⟩, Sum.inr ⟨w₂, _⟩ => r w₁ w₂
  | Sum.inl v, Sum.inr ⟨w, _⟩ => r v w ∨ v = w
  | Sum.inr ⟨w, _⟩, Sum.inl v => r w v

-- claim_3_6 (part A)
-- title: SplitTopologicalOrder -- topological order preserved
--
-- The LN's "for a CADMG `G = (J, V, E, L)`, also `G_{spl(W)}` is
-- acyclic; if `<` is any topological order of `G` ... then ... a
-- topological order for `G_{spl(W)}` can be achieved by assigning
-- `v_j^0` the index `j - 1/3` and `v_j^1` the index `j + 1/3` and
-- ordering by index value" splits into two formal statements (see
-- the file-level docstring for the rationale). This is the
-- *constructive* half: from a topological order `r` of `G` and the
-- precondition `hW : W ⊆ G.V` (required by `nodeSplittingOn`
-- def_3_11 itself), produce a topological order `splitOrder W r`
-- of `G.nodeSplittingOn W hW`. The construction follows the LN's
-- `± 1/3` interleaving recipe verbatim, encoded as the four-case
-- `splitOrder` pattern match.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(Rem 444 -- 455):

\begin{claimmark}
\begin{Rem}
    For a CADMG $G=(J,V,E,L)$, also $G_{\spl(W)}$ is acyclic.
    If $<$ is any topological order of $G$ given by enumerating
    all nodes $v \in J \cup V$ via:
    \[ v_1 < v_2 < \cdots < v_n,\]
    then, for instance,
    a topological order for $G_{\spl(W)}$ can be achieved by
    assigning for a node $v_j \in W$ with index $j$ the node
    $v_j^0$ the index $j-\frac{1}{3}$
    and $v_j^1$ the index $j+\frac{1}{3}$, and then ordering all
    nodes according to their index value.
\end{Rem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **Why a separate theorem from the acyclicity half.** The LN
--   bundles "$G_{\spl(W)}$ is acyclic" and "an explicit topological
--   order on $G_{\spl(W)}$" under one `\Rem`. We split because:
--     (1) The topological-order half is the *named-construction*
--         result -- downstream callers (claim_3_9 SWIG, iSCM
--         chapters) want `splitOrder W r` by name to plug into
--         their own constructions.
--     (2) The acyclicity half is the *side-condition* result --
--         downstream callers (claim_3_7, claim_3_12, the iSCM
--         well-foundedness theory) want `(G.nodeSplittingOn W
--         hW).IsAcyclic` as a hypothesis without committing to a
--         specific topological order.
--   Bundling them would force the second class of callers to
--   either project (`.1` / `.2` from a conjunction) or to drag in
--   the topological-order data they do not need. Mirrors
--   claim_3_3's two-theorem decomposition exactly.
-- * **`{G}, {W}, hW, {r}, hr` binder choice (and asymmetry vs.
--   claim_3_3 part B).** `G` and `W` are implicit because they
--   are unifiable from the conclusion
--   `(G.nodeSplittingOn W hW).IsTopologicalOrder (splitOrder W r)`
--   *and* from `hW : W ⊆ G.V`. `r` is implicit because it is
--   unifiable from `hr : G.IsTopologicalOrder r`. `hW` is
--   explicit because the LN's "for a CADMG `G = (J, V, E, L)` ..."
--   takes `W ⊆ V` for granted at def_3_11, but in Lean we must
--   pass the precondition every time we mention `nodeSplittingOn`.
--   This matches `NodeSplittingOn.lean`'s `nodeSplittingOn G W hW`
--   signature exactly (where `G` is explicit only because it is
--   the outer dot-projection target). Note that `W` here is
--   implicit (matching the brief), in mild contrast to claim_3_3
--   part A's explicit `W` -- the difference is that claim_3_3
--   part A had `W` *only* in the conclusion (no `hW` hypothesis to
--   recover it from), whereas here `hW : W ⊆ G.V` makes `W`
--   unifiable.
-- * **No `[Finite α]` instance hypothesis.** The construction is
--   purely relational (no enumeration of vertices) and the four
--   `IsTopologicalOrder` fields transport via the `@[simp]`
--   membership lemmas of `NodeSplittingOn.lean`, neither of which
--   needs finiteness. Downstream callers in iSCM chapters
--   working over not-yet-finitised vertex types can apply this
--   result directly.
-- * **Naming follows Mathlib's `<conclusion>_<construction>`
--   convention.** `isTopologicalOrder_nodeSplittingOn` reads as
--   "the result `IsTopologicalOrder` applied to the construction
--   `nodeSplittingOn`", consistent with
--   `isTopologicalOrder_hardInterventionOn` from claim_3_3 part B.
-- * **"For instance" -- non-uniqueness preserved as a hedge.**
--   The LN writes "*for instance*, a topological order for
--   `G_{spl(W)}` can be achieved by ..." -- the `±1/3` interleave
--   is *one* concrete construction, not the canonical one. Our
--   theorem proves that `splitOrder W r` is *a* topological order
--   of the split graph; it does not claim uniqueness, and any
--   other valid interleaving (e.g. swapping the `±1/3` shifts for
--   a global integer renumbering after the splits) would yield a
--   different relation, equally valid. This is the second reason
--   we factor `splitOrder` as a *standalone named def* (alongside
--   the reuse reason in the `splitOrder` block above): downstream
--   callers that quote "the topological order from claim_3_6"
--   (claim_3_9 SWIG; the iSCM chapters' "the topological order
--   inherited from the split") work with *this specific*
--   construction by name, while remaining free to instantiate
--   `IsTopologicalOrder` differently when their context favours
--   a different recipe.
-- * **Proof-phase road map (hint to the prover, not a proof).**
--   The four `IsTopologicalOrder` fields discharge via the
--   `@[simp]` rewrite machinery of `NodeSplittingOn.lean`:
--     - `irrefl`: destruct `v : α ⊕ ↑W` on `Sum.inl` / `Sum.inr`;
--       both cases collapse `splitOrder W r v v` to `r v' v'`
--       for some `v' ∈ G`, then `hr.irrefl` finishes. Node
--       membership in `G.nodeSplittingOn W hW` is unpacked via
--       `nodeSplittingOn_J` and `nodeSplittingOn_V`.
--     - `trans`: case-split on the carrier of the middle
--       element; each of the four sub-shapes reduces to a single
--       `hr.trans` application, with the `r v w ∨ v = w`
--       disjunct on the `(inl, inr)` case collapsing the
--       split-edge sub-case via substitution.
--     - `trichotomous`: destruct both endpoints on
--       `Sum.inl` / `Sum.inr`; each of the four pattern-match
--       cases reduces to `hr.trichotomous` applied to the
--       underlying `α`-elements, with the `r v w ∨ v = w`
--       disjunct on the `(inl, inr)` configuration absorbing
--       `hr.trichotomous`'s `v = w` branch.
--     - `parent_lt`: case-split on the two pieces of
--       `mem_nodeSplittingOn_E`. Piece 1 (relabeled `G.E`
--       edges): `split1_of_mem` / `split1_of_not_mem` rewrite
--       the source dispatch, and the resulting `splitOrder`
--       case reduces to `hr.parent_lt`. Piece 2 (fresh split
--       edges `(Sum.inl w, Sum.inr ⟨w, hw⟩)`): the `(inl, inr)`
--       case of `splitOrder` fires with the `v = w` disjunct
--       via `Or.inr rfl`, no `hr` needed -- this is exactly the
--       payoff of the `r v w ∨ v = w` shape chosen in
--       `splitOrder`.

/-- claim_3_6 part A: if `W ⊆ G.V` and `r` is a topological order
of `G`, then `splitOrder W r` is a topological order of
`G.nodeSplittingOn W hW`. Mirrors the constructive half of the
`\Rem` immediately after def_3_11 in
`lecture-notes/lecture_notes/graphs.tex` (lines 444 -- 455), with
the LN's `± 1/3` interleaving recipe encoded as the four-case
`splitOrder` pattern match.

The `W ⊆ G.V` precondition is structurally required by
`nodeSplittingOn` itself (def_3_11) -- the split edge
`Sum.inl w → Sum.inr ⟨w, hw⟩` needs its source `Sum.inl w` to live
in the split graph's output set, which is true only when
`w ∈ G.V`. This is not a topological-order condition; it is the
def_3_11 condition transported.

See `isAcyclic_nodeSplittingOn` below for the acyclicity half of
the LN remark and the file-level docstring for the rationale
behind splitting the LN's single `\Rem` into two theorems. -/
theorem isTopologicalOrder_nodeSplittingOn
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.V)
    {r : α → α → Prop} (hr : G.IsTopologicalOrder r) :
    (G.nodeSplittingOn W hW).IsTopologicalOrder (splitOrder W r) := by
  -- Mirrors `tex/claim_3_6_proof_SplitTopologicalOrder.tex` Part B.
  -- The TeX proof's Step 1 (`σ` injectivity) is not needed as a
  -- separate lemma in Lean: our `splitOrder` is relational and the
  -- four-case pattern match plus `(inl, inr) ↦ r v w ∨ v = w` makes
  -- the "middle" branch of trichotomy and `parent_lt`'s split-edge
  -- case discharge directly. Steps 2 -- 5 of the TeX map onto the
  -- four `IsTopologicalOrder` fields below.
  -- Helper: `Sum.inl v ∈ G.nodeSplittingOn W hW ↔ v ∈ G`.
  have mem_inl : ∀ {v : α},
      (Sum.inl v : α ⊕ ↑W) ∈ G.nodeSplittingOn W hW ↔ v ∈ G := by
    intro v
    simp only [CDMG.mem_iff, nodeSplittingOn_J, nodeSplittingOn_V,
      Set.mem_union, Set.mem_image, Set.mem_range]
    constructor
    · rintro (⟨j, hj, hjv⟩ | ⟨v', hv', hvv'⟩ | ⟨w, hw⟩)
      · cases Sum.inl_injective hjv; exact Or.inl hj
      · cases Sum.inl_injective hvv'; exact Or.inr hv'
      · exact nomatch hw
    · rintro (hJ | hV)
      · exact Or.inl ⟨v, hJ, rfl⟩
      · exact Or.inr (Or.inl ⟨v, hV, rfl⟩)
  -- Helper: every `w ∈ W` is in `G` via `hW : W ⊆ G.V`.
  have inr_mem_G : ∀ w' : ↑W, (w' : α) ∈ G :=
    fun w' => Or.inr (hW w'.property)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (TeX Step 2) irrefl: case-split on `α ⊕ ↑W`; either branch
    -- collapses `splitOrder W r v v` to `r v' v'` for `v' ∈ G`,
    -- closed by `hr.irrefl`.
    rintro (v | ⟨w, hw⟩) hv
    · exact hr.irrefl v (mem_inl.mp hv)
    · exact hr.irrefl (w : α) (inr_mem_G ⟨w, hw⟩)
  · -- (TeX Step 3) trans: case-split on all three carrier shapes
    -- (8 cases); each collapses to a single `hr.trans` application,
    -- with the `r v w ∨ v = w` disjunct on `(inl, inr)` branches
    -- absorbed by substitution.
    rintro (a | ⟨a, ha⟩) h_a (b | ⟨b, hb⟩) h_b (c | ⟨c, hc⟩) h_c
    · -- (inl a, inl b, inl c)
      intro h_ab h_bc
      exact hr.trans a (mem_inl.mp h_a) b (mem_inl.mp h_b) c (mem_inl.mp h_c)
        h_ab h_bc
    · -- (inl a, inl b, inr c) -- h_bc : r b c ∨ b = c
      rintro h_ab (h_bc | rfl)
      · exact Or.inl (hr.trans a (mem_inl.mp h_a) b (mem_inl.mp h_b)
          c (inr_mem_G ⟨c, hc⟩) h_ab h_bc)
      · exact Or.inl h_ab
    · -- (inl a, inr b, inl c) -- h_ab : r a b ∨ a = b
      rintro (h_ab | rfl) h_bc
      · exact hr.trans a (mem_inl.mp h_a) b (inr_mem_G ⟨b, hb⟩)
          c (mem_inl.mp h_c) h_ab h_bc
      · exact h_bc
    · -- (inl a, inr b, inr c) -- h_ab : r a b ∨ a = b
      rintro (h_ab | rfl) h_bc
      · exact Or.inl (hr.trans a (mem_inl.mp h_a) b (inr_mem_G ⟨b, hb⟩)
          c (inr_mem_G ⟨c, hc⟩) h_ab h_bc)
      · exact Or.inl h_bc
    · -- (inr a, inl b, inl c)
      intro h_ab h_bc
      exact hr.trans (a : α) (inr_mem_G ⟨a, ha⟩) b (mem_inl.mp h_b)
        c (mem_inl.mp h_c) h_ab h_bc
    · -- (inr a, inl b, inr c) -- h_bc : r b c ∨ b = c
      rintro h_ab (h_bc | rfl)
      · exact hr.trans (a : α) (inr_mem_G ⟨a, ha⟩) b (mem_inl.mp h_b)
          c (inr_mem_G ⟨c, hc⟩) h_ab h_bc
      · exact h_ab
    · -- (inr a, inr b, inl c)
      intro h_ab h_bc
      exact hr.trans (a : α) (inr_mem_G ⟨a, ha⟩) b (inr_mem_G ⟨b, hb⟩)
        c (mem_inl.mp h_c) h_ab h_bc
    · -- (inr a, inr b, inr c)
      intro h_ab h_bc
      exact hr.trans (a : α) (inr_mem_G ⟨a, ha⟩) b (inr_mem_G ⟨b, hb⟩)
        c (inr_mem_G ⟨c, hc⟩) h_ab h_bc
  · -- (TeX Step 4) trichotomous: case-split on both endpoints (4
    -- cases). Each collapses to `hr.trichotomous` on the underlying
    -- `α`-elements; the `=`-middle branch maps to `Or.inr (Or.inl _)`
    -- with `Sum.inl.injEq` / `Subtype.ext` (or `rfl` after `subst`).
    rintro (a | ⟨a, ha⟩) h_a (b | ⟨b, hb⟩) h_b
    · -- (inl a, inl b)
      rcases hr.trichotomous a (mem_inl.mp h_a) b (mem_inl.mp h_b) with
        h | rfl | h
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    · -- (inl a, inr b)
      -- Goal: (r a b ∨ a = b) ∨ Sum.inl a = Sum.inr ⟨b, hb⟩ ∨ r b a
      rcases hr.trichotomous a (mem_inl.mp h_a) b (inr_mem_G ⟨b, hb⟩) with
        h | rfl | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr (Or.inr h)
    · -- (inr a, inl b)
      -- Goal: r a b ∨ Sum.inr ⟨a, ha⟩ = Sum.inl b ∨ (r b a ∨ b = a)
      rcases hr.trichotomous (a : α) (inr_mem_G ⟨a, ha⟩) b
        (mem_inl.mp h_b) with h | rfl | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl h))
    · -- (inr a, inr b)
      rcases hr.trichotomous (a : α) (inr_mem_G ⟨a, ha⟩) (b : α)
        (inr_mem_G ⟨b, hb⟩) with h | h_eq | h
      · exact Or.inl h
      · -- h_eq : a = b (as α). Lift to subtype equality.
        refine Or.inr (Or.inl ?_)
        exact congrArg Sum.inr (Subtype.ext h_eq)
      · exact Or.inr (Or.inr h)
  · -- (TeX Step 5) parent_lt: case-split on the two pieces of
    -- `mem_nodeSplittingOn_E`.
    intro v w h_pa
    obtain ⟨_, h_vw_E⟩ := h_pa
    -- Unfold `tuh` notation to plain set-membership so `simp only`
    -- below can fire on `mem_nodeSplittingOn_E`.
    change (v, w) ∈ (G.nodeSplittingOn W hW).E at h_vw_E
    rw [mem_nodeSplittingOn_E] at h_vw_E
    rcases h_vw_E with ⟨v₁, v₂, hE, h_eq⟩ | ⟨w', h_eq⟩
    · -- (TeX Step 5, Case (i)) relabeled original edge.
      -- (v, w) = (split1 W v₁, Sum.inl v₂) with (v₁, v₂) ∈ G.E.
      obtain ⟨hv_eq, hw_eq⟩ : v = split1 W v₁ ∧ w = Sum.inl v₂ := by
        rw [Prod.mk.injEq] at h_eq; exact h_eq
      have hv₁_G : v₁ ∈ G :=
        CDMG.mem_iff.mpr (Set.mem_prod.mp (G.E_subset hE)).1
      have h_r : r v₁ v₂ := hr.parent_lt ⟨hv₁_G, hE⟩
      subst hv_eq
      subst hw_eq
      -- `splitOrder W r (split1 W v₁) (Sum.inl v₂)` -- dispatch on `v₁ ∈ W`.
      by_cases hv₁_W : v₁ ∈ W
      · rw [split1_of_mem hv₁_W]; exact h_r
      · rw [split1_of_not_mem hv₁_W]; exact h_r
    · -- (TeX Step 5, Case (ii)) fresh split edge.
      -- (v, w) = (Sum.inl w'.val, Sum.inr w'). The `(inl, inr)` case
      -- of `splitOrder` fires with `Or.inr rfl` -- the payoff of the
      -- `r v w ∨ v = w` shape chosen for `splitOrder`.
      obtain ⟨hv_eq, hw_eq⟩ : v = Sum.inl (w' : α) ∧ w = Sum.inr w' := by
        rw [Prod.mk.injEq] at h_eq; exact h_eq
      subst hv_eq
      subst hw_eq
      exact Or.inr rfl

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: isAcyclic_nodeSplittingOn
-- claim_3_6 (part B)
-- title: SplitTopologicalOrder -- acyclicity preserved
--
-- The acyclicity half of the LN remark: if `G` is acyclic and
-- `W ⊆ G.V`, then `G.nodeSplittingOn W hW` is acyclic. Two viable
-- proof routes are available (the prover chooses):
--
--   (i) Via Part A + claim_3_2: from `G.IsAcyclic` pull a
--       topological order via the `→` direction of
--       `isAcyclic_iff_hasTopologicalOrder` (needs `[Finite α]`),
--       apply Part A to lift it to `(G.nodeSplittingOn W
--       hW).IsTopologicalOrder (splitOrder W r)`, then use the `←`
--       direction of claim_3_2 to conclude
--       `(G.nodeSplittingOn W hW).IsAcyclic`. Cleanest, but pulls
--       in `[Finite α]` (which the LN's `\Rem` does not state).
--   (ii) Direct walk-lifting analogous to claim_3_3 part A:
--        project a hypothetical cycle in `G.nodeSplittingOn W hW`
--        down to a cycle in `G` via `Sum.inl v ↦ v, Sum.inr ⟨w,_⟩
--        ↦ w` and compression of the trivial `Sum.inl w → Sum.inr
--        ⟨w, hw⟩` split edges (which project to self-loops, hence
--        not real edges in `G`; they shrink the projected walk).
--        More work but no finiteness needed.
--
-- Statement-phase keeps both routes open by *not* adding
-- `[Finite α]`. If the prover finds route (ii) infeasible they
-- can request a `correct_tex_proof` to add `[Finite α]`; the
-- statement is then trivially compatible with route (i).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(Rem 444 -- 455; same block as part A):

\begin{claimmark}
\begin{Rem}
    For a CADMG $G=(J,V,E,L)$, also $G_{\spl(W)}$ is acyclic.
    ...
\end{Rem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **No `[Finite α]` instance hypothesis at statement phase.**
--   Discussed in the comment block immediately above. The
--   statement signature is intentionally *minimal* -- the prover
--   can add `[Finite α]` if route (i) wins out, but the manager
--   should not pre-commit at the statement phase.
-- * **`{G}, {W}, hW, h` binder choice.** Same rationale as Part A
--   -- `G` and `W` recovered from the conclusion / `hW`; `hW`
--   explicit because `nodeSplittingOn` demands it. `h :
--   G.IsAcyclic` is explicit because it is the hypothesis we are
--   transporting; no opportunity for Lean to unify it from
--   elsewhere.
-- * **Naming `isAcyclic_nodeSplittingOn`.** Mirrors `claim_3_3`
--   part A `isAcyclic_hardInterventionOn` (this section's
--   precedent) and follows Mathlib's
--   `<conclusion>_<construction>` convention. The
--   `IsAcyclic` part comes first because it is the result; the
--   `nodeSplittingOn` part second because it is the construction
--   we are showing preserves acyclicity.

/-- claim_3_6 part B: if `W ⊆ G.V` and `G` is acyclic, then
`G.nodeSplittingOn W hW` is acyclic. Mirrors the acyclicity half
of the `\Rem` immediately after def_3_11 in
`lecture-notes/lecture_notes/graphs.tex` (lines 444 -- 455); see
`isTopologicalOrder_nodeSplittingOn` above for the constructive
half and the file-level docstring for the rationale behind
splitting the LN's single `\Rem` into two theorems.

The `W ⊆ G.V` precondition is structurally required by
`nodeSplittingOn` itself (def_3_11), not by acyclicity per se;
see `isTopologicalOrder_nodeSplittingOn`. No `[Finite α]`
hypothesis is added at the statement phase to keep both proof
routes open (claim_3_2-based vs. direct walk-lifting); see the
per-theorem design block above for the discussion. -/
theorem isAcyclic_nodeSplittingOn
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.V)
    (h : G.IsAcyclic) :
    (G.nodeSplittingOn W hW).IsAcyclic := by
  -- Route (ii) of the per-theorem design block: direct walk-lifting,
  -- finiteness-free. The projection `α ⊕ ↑W → α` sends
  -- `Sum.inl v ↦ v` and `Sum.inr ⟨w, _⟩ ↦ w`. Under this
  -- projection, every "piece-1" edge of `(G.nodeSplittingOn W hW).E`
  -- (a relabeled `G.E`-edge) projects to a real `G.E`-edge, and every
  -- "piece-2" edge (a fresh split edge `Sum.inl w → Sum.inr ⟨w, _⟩`)
  -- projects to a self-loop `(w, w)` which compresses out.
  --
  -- The key existence lemma `proj_exists`: any directed walk in the
  -- split graph projects to a directed walk in `G`. The auxiliary
  -- "positive-length" clause: for cycles `v → ⋯ → v` (where either
  -- `v` is `Sum.inl _` or `Sum.inr _`), the projection has positive
  -- length, because at least one step is a piece-1 relabeled edge
  -- (the last step is piece-1 if the cycle endpoint is `Sum.inl _`;
  -- the first step is piece-1 if it is `Sum.inr _`).
  rintro v hv ⟨π, h_dir, h_pos⟩
  let proj : α ⊕ ↑W → α := Sum.elim id Subtype.val
  -- General projection lemma.
  have proj_exists : ∀ {a b : α ⊕ ↑W} (π : Walk (G.nodeSplittingOn W hW) a b),
      π.IsDirected →
      ∃ ρ : Walk G (proj a) (proj b),
        ρ.IsDirected ∧
        (1 ≤ π.length →
          (∃ v₀, b = Sum.inl v₀) ∨ (∃ w', a = Sum.inr w') →
          1 ≤ ρ.length) := by
    intro a b π
    induction π with
    | nil _ =>
      intro _
      refine ⟨Walk.nil _, by simp, ?_⟩
      intro h_pos _
      simp at h_pos
    | @cons _ y b' s p ih =>
      intro h_dir
      cases s with
      | forward h =>
        have h_p : p.IsDirected := h_dir
        obtain ⟨ρ_p, h_ρ_p_dir, h_ρ_p_len⟩ := ih h_p
        -- Dispatch on the edge form via `mem_nodeSplittingOn_E`.
        change (_, _) ∈ (G.nodeSplittingOn W hW).E at h
        rw [mem_nodeSplittingOn_E] at h
        rcases h with ⟨v₁, v₂, hE, h_eq⟩ | ⟨w', h_eq⟩
        · -- Piece 1 (relabeled edge): a = split1 W v₁, y = Sum.inl v₂.
          rw [Prod.mk.injEq] at h_eq
          obtain ⟨ha_eq, hy_eq⟩ := h_eq
          subst hy_eq
          -- Dispatch on `v₁ ∈ W` to make `split1 W v₁` concrete in
          -- `ha_eq`, then `subst` to replace `a` throughout.
          by_cases hv₁ : v₁ ∈ W
          · rw [split1_of_mem hv₁] at ha_eq
            subst ha_eq
            -- `proj (Sum.inr ⟨v₁, hv₁⟩)` reduces to `v₁` by `Sum.elim` def.
            refine ⟨Walk.cons (.forward hE) ρ_p, ?_, ?_⟩
            · simp only [Walk.isDirected_cons_forward]; exact h_ρ_p_dir
            · intro _ _; simp
          · rw [split1_of_not_mem hv₁] at ha_eq
            subst ha_eq
            refine ⟨Walk.cons (.forward hE) ρ_p, ?_, ?_⟩
            · simp only [Walk.isDirected_cons_forward]; exact h_ρ_p_dir
            · intro _ _; simp
        · -- Piece 2 (split edge): a = Sum.inl w'.val, y = Sum.inr w'.
          rw [Prod.mk.injEq] at h_eq
          obtain ⟨ha_eq, hy_eq⟩ := h_eq
          subst ha_eq
          subst hy_eq
          -- proj (Sum.inl w'.val) = w'.val = proj (Sum.inr w'), so
          -- `ρ_p : Walk G w'.val (proj b')` already has the goal type.
          refine ⟨ρ_p, h_ρ_p_dir, ?_⟩
          intro _ h_endpts
          -- "source is Sum.inr" disjunct of `h_endpts` is false; hence
          -- "target is Sum.inl" disjunct holds.
          have hb_inl : ∃ v₀, b' = Sum.inl v₀ := by
            rcases h_endpts with hb | ⟨w'', hw''⟩
            · exact hb
            · cases hw''
          -- If `p.length = 0` then `p = .nil _` so `b' = Sum.inr w'`,
          -- contradicting `hb_inl`.
          have hp_pos : 1 ≤ p.length := by
            cases p with
            | nil _ =>
              exfalso
              obtain ⟨v₀, hv⟩ := hb_inl
              cases hv
            | cons _ _ => simp
          exact h_ρ_p_len hp_pos (Or.inr ⟨w', rfl⟩)
      | backward _ => exact absurd h_dir (by simp)
      | bidir _ => exact absurd h_dir (by simp)
  -- Apply the lemma to `π`.
  obtain ⟨ρ, h_ρ_dir, h_ρ_len⟩ := proj_exists π h_dir
  -- For the cycle (source = target = v), one of the endpoint
  -- conditions of `proj_exists` holds.
  have h_endpts : (∃ v₀, v = Sum.inl v₀) ∨ (∃ w', v = Sum.inr w') := by
    rcases v with v₀ | w'
    · exact Or.inl ⟨v₀, rfl⟩
    · exact Or.inr ⟨w', rfl⟩
  have h_proj_pos : 1 ≤ ρ.length := h_ρ_len h_pos h_endpts
  -- `proj v ∈ G`.
  have hv_proj : proj v ∈ G := by
    simp only [CDMG.mem_iff, nodeSplittingOn_J, nodeSplittingOn_V,
      Set.mem_union, Set.mem_image, Set.mem_range] at hv
    rcases v with v₀ | ⟨w, hwW⟩
    · change v₀ ∈ G
      rcases hv with ⟨j, hj, hjv⟩ | ⟨v', hv', hvv'⟩ | ⟨w, hw⟩
      · cases Sum.inl_injective hjv; exact Or.inl hj
      · cases Sum.inl_injective hvv'; exact Or.inr hv'
      · exact nomatch hw
    · change w ∈ G
      exact Or.inr (hW hwW)
  -- Derive contradiction with `G.IsAcyclic`.
  exact h _ hv_proj ⟨ρ, h_ρ_dir, h_proj_pos⟩
-- REFACTOR-BLOCK-ORIGINAL-END: isAcyclic_nodeSplittingOn

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: isAcyclic_nodeSplittingOn (was: refactor_isAcyclic_nodeSplittingOn)
-- claim_3_6 (part B, refactored: rides claim_3_2_no_finite)
-- title: SplitTopologicalOrder -- acyclicity preserved
--
-- The acyclicity half of the LN remark. With the
-- `claim_3_2_no_finite` refactor delivering a finiteness-free
-- `isAcyclic_iff_hasTopologicalOrder` (claim_3_2), this becomes the
-- three-step citation that the LN's own one-line "also `G_{spl(W)}`
-- is acyclic" prose offers:
--   1. `(refactor_isAcyclic_iff_hasTopologicalOrder G).mp h` pulls a
--      topological order `r` of `G` from `G.IsAcyclic`. Pre-refactor,
--      this step would have required `[Finite α]` (LN line 238 of
--      `graphs.tex` invokes "since `G_i` is acyclic and finite, it
--      has a parent-free node"); the Szpilrajn-route proof of the
--      refactored claim_3_2 lifts that restriction.
--   2. `isTopologicalOrder_nodeSplittingOn hW hr` lifts `r` through
--      Part A to a topological order `splitOrder W r` of
--      `G.nodeSplittingOn W hW`. Part A is itself finiteness-free, so
--      no extra hypothesis is introduced here.
--   3. `(refactor_isAcyclic_iff_hasTopologicalOrder _).mpr ⟨_, _⟩`
--      concludes acyclicity. The `⇐` direction of claim_3_2 has
--      always been finiteness-free (irreflexivity + transitivity of
--      the topological order suffices), so no surprise.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Rem 444 -- 455; same block as Part A):

\begin{claimmark}
\begin{Rem}
    For a CADMG $G=(J,V,E,L)$, also $G_{\spl(W)}$ is acyclic.
    ...
\end{Rem}
\end{claimmark}
-/
--
-- ## Design choice (refactor)
--
-- * **No `[Finite α]` hypothesis** (same as the original). The
--   refactor only changes the proof; the statement signature is
--   identical to the walk-lifting version above.
-- * **Why the three-step citation route now wins.** Pre-refactor, the
--   walk-lifting route (route (ii) in the original's design block)
--   was preferred precisely because route (i) needed `[Finite α]` via
--   the `⇒` direction of claim_3_2. With the `claim_3_2_no_finite`
--   refactor lifting that restriction, route (i) is both shorter and
--   matches the LN's own one-liner "also `G_{spl(W)}` is acyclic".
--   The walk-lifting proof remains preserved verbatim in the
--   `REFACTOR-BLOCK-ORIGINAL` block above (which Phase 7 cleanup
--   will strip), so the alternative reasoning is documented even
--   though it is no longer the load-bearing proof.
-- * **Calls `refactor_isAcyclic_iff_hasTopologicalOrder` (not the
--   original `isAcyclic_iff_hasTopologicalOrder`).** During the
--   refactor window, both versions of claim_3_2 coexist. Phase 7's
--   global whole-word rename `refactor_<Name>` -> `<Name>` will turn
--   this call into the canonical `isAcyclic_iff_hasTopologicalOrder`
--   at cleanup time.
-- * **Naming `refactor_isAcyclic_nodeSplittingOn`.** Phase 7 cleanup
--   strips the `refactor_` prefix to produce the final
--   `isAcyclic_nodeSplittingOn`.

/-- claim_3_6 part B (refactored, rides `claim_3_2_no_finite`): if
`W ⊆ G.V` and `G` is acyclic, then `G.nodeSplittingOn W hW` is
acyclic. Mirrors the acyclicity half of the `\Rem` immediately after
def_3_11 in `lecture-notes/lecture_notes/graphs.tex` (lines 444 --
455); see the refactor twin proof at
`tex/refactor_claim_3_6_proof_SplitTopologicalOrder.tex` for the
verified mathematical roadmap. The proof is the three-step citation
of the refactored finiteness-free `claim_3_2`
(`refactor_isAcyclic_iff_hasTopologicalOrder`) composed with Part A
(`isTopologicalOrder_nodeSplittingOn`), matching the LN's own
one-line statement of the result. -/
theorem refactor_isAcyclic_nodeSplittingOn
    {G : CDMG α} {W : Set α} (hW : W ⊆ G.V)
    (h : G.IsAcyclic) :
    (G.nodeSplittingOn W hW).IsAcyclic := by
  -- Mirrors `tex/refactor_claim_3_6_proof_SplitTopologicalOrder.tex`
  -- Part (B): three citations of the refactored claim_3_2.
  -- Step 1 (TeX Part B step 1): G acyclic ⇒ G has a topological order
  -- via the `⇒` direction of refactored claim_3_2.
  obtain ⟨r, hr⟩ := (refactor_isAcyclic_iff_hasTopologicalOrder G).mp h
  -- Step 2 (TeX Part B step 2): lift `r` to a topological order on
  -- `G.nodeSplittingOn W hW` via Part A.
  have h_split : (G.nodeSplittingOn W hW).HasTopologicalOrder :=
    ⟨splitOrder W r, isTopologicalOrder_nodeSplittingOn hW hr⟩
  -- Step 3 (TeX Part B step 3): the `⇐` direction of refactored
  -- claim_3_2 concludes acyclicity.
  exact (refactor_isAcyclic_iff_hasTopologicalOrder
    (G.nodeSplittingOn W hW)).mpr h_split
-- REFACTOR-BLOCK-REPLACEMENT-END: isAcyclic_nodeSplittingOn

end CDMG

end Causality
