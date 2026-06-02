import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.Marginalization
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard

-- TeX statement: tex/claim_3_19_statement_MarginalizingOutThe.tex
-- TeX proof:    tex/claim_3_19_proof_MarginalizingOutThe.tex (later phase)

/-!
# Marginalizing out the output part of splitted nodes equals hard intervention (claim_3_19)

This file formalises the lecture notes' lemma "Marginalizing out the
output part of splitted nodes equals hard intervention" --
`lecture-notes/lecture_notes/graphs.tex` Lem at lines 1167 -- 1175
(with proof at lines 1176 -- 1211, scope of a *later* worker phase).

The LN states:

  `G_{do(W)} ≅ (G_{swig(W)})^{∖ W^o},  w ↦ w^i.`

That is: for a CDMG `G = (J, V, E, L)` and an output-node subset
`W ⊆ V`, the hard-intervened CDMG `G_{do(W)}` is (graph-)isomorphic
to the marginalization of the SWIG `G_{swig(W)}` over the `W^o`
copies. The identification sends each `w ∈ W` (which is an *input*
of the LHS, by the hard intervention) to its `w^i` copy in the
SWIG, and is the identity on `J ∪ (V ∖ W)`.

In the Lean encoding (inherited from `NodeSplittingOn.lean` /
`NodeSplittingHard.lean`): `w^o = Sum.inl w` (canonical observation
copy) and `w^i = Sum.inr ⟨w, hw⟩` (fresh intervention-input
label). Hence `W^o` is the `Set (α ⊕ ↑W)` `Sum.inl '' W`, and the
"identification" map `α → α ⊕ ↑W` is precisely the `split1 W`
helper from `NodeSplittingOn.lean` (sending `v ∉ W` to
`Sum.inl v` and `v ∈ W` to `Sum.inr ⟨v, hv⟩`).

## Design choices (file-level overview; per-declaration details below)

* **`W^o` inside the SWIG's carrier.** No new helper: the LN's
  `W^o` is the existing `Sum.inl '' W : Set (α ⊕ ↑W)`, matching the
  encoding pinned down in `NodeSplittingOn.lean`'s design block
  (`Sum.inl = 0-copy = w^o`).

* **Cross-carrier isomorphism: a local `CDMGNodeIso` helper, not
  `CDMGEquiv`.** Unlike claim_3_7 / claim_3_10 (`CDMGEquiv` between
  iterated and fused node-splittings, both over carriers of *the
  same* cardinality `|α| + |W₁| + |W₂|`), the two CDMGs of
  claim_3_19 live over carriers of *different* cardinality: LHS
  over `α` and RHS over `α ⊕ ↑W`. The existing `CDMGEquiv`
  requires an `α ≃ β` bijection -- in general impossible here
  (e.g. for any finite `α` with a non-empty `W`). We introduce a
  small helper structure `CDMGNodeIso G H` in this file: a
  function `α → β` that is injective on `G`'s nodes and that
  preserves the four data fields `J / V / E / L`. This captures
  the LN's `\cong` faithfully when the carrier types differ.

* **File name.** `MarginalizingOutSplitOutput.lean` -- a
  short paraphrase of the LN title; matches the chapter pattern
  of one Lean file per claim row.

* **Declaration name.** `hardInterventionOn_nodeIso_swig_marginalize_outputs`
  -- long but searchable; the `_nodeIso_` infix signals the
  cross-carrier isomorphism, distinguishing this row's iso from
  the same-cardinality `CDMGEquiv`-style iso used in claim_3_7
  / claim_3_10.
-/

namespace Causality

namespace CDMG

universe u

/-! ## Cross-carrier graph isomorphism (local helper for claim_3_19) -/

/-- A graph isomorphism between two CDMGs over potentially distinct
carrier types, encoded as a carrier *function* (not a carrier
bijection) together with the injectivity-on-nodes condition that
makes it a bijection on the actual node sets.

Concretely, a `CDMGNodeIso G H` packages:

* a function `toFun : α → β`,
* a proof `injOn_nodes` that `toFun` is injective on
  `G.J ∪ G.V` (so, together with the four image-equality fields
  below, it bijects `G`'s nodes onto `H.J ∪ H.V`),
* four image equalities recording that `toFun` sends `G`'s four
  data fields `J / V / E / L` exactly to those of `H`.

## Design choice

* **Why a *function* `α → β` + `Set.InjOn`, not a carrier
  bijection `α ≃ β`.** A `CDMGEquiv`-style bundle would demand
  a full `α ≃ β`, but for claim_3_19 the source carrier is `α`
  and the target is `α ⊕ ↑W`. Whenever `α` is finite and `W` is
  non-empty, `|α| ≠ |α ⊕ ↑W| = |α| + |W|`, so no `Equiv` exists
  -- the literal `Equiv`-shaped statement is *unprovable* in
  those cases. (Both `review_design` and `verify_equivalence`
  flagged this as the central obstacle.) The
  `Set.InjOn` + four-image-equality combo *is* a bijection on
  the nodes themselves -- it bijects `G.J ∪ G.V` onto
  `H.J ∪ H.V` -- which is all that the LN's `\cong` ever
  asserts. The unused part of the carrier (the elements of `α`
  outside `G.J ∪ G.V`, and the elements of `β` outside
  `H.J ∪ H.V`) is irrelevant to the LN's notion of "graph
  isomorphism", and demanding a bijection there is strictly
  stronger than the LN.

* **Why exactly four image equalities (`J_eq`, `V_eq`, `E_eq`,
  `L_eq`).** `CDMG` (def_3_1, `Section3_1/CDMG.lean`) has
  exactly four data fields `J`, `V`, `E`, `L`; the six prop
  fields are proof-irrelevant once those four are pinned down.
  This mirrors `CDMGEquiv`'s four-field shape one-for-one --
  the only difference is the underlying carrier datum
  (function-plus-`InjOn` here vs. full `Equiv` there). If def_3_1
  ever grew a fifth data field both shapes would need a
  matching fifth equation; until then, four is exactly right.

* **Why `Prod.map toFun toFun` on `E` / `L`.** Edges and
  bidirected edges live in `α × α`; the canonical functorial
  action of a carrier map `toFun : α → β` on a pair of
  endpoints is `Prod.map toFun toFun` (i.e. `toFun` applied
  componentwise). This is identical to the shape used by
  `CDMGEquiv.E_eq` / `L_eq` in
  `TwoDisjointNodeSplittingsCommute.lean`, so a future
  unification of the two iso-styles would not need to
  reconcile two different edge-relabel conventions.

* **No `refl` / `symm` / `trans` operations at this row.**
  `CDMGEquiv` ships its three groupoid laws because the
  `nodeSplittingOn_comm_equiv` corollary chains two
  `fusionEquiv`-style equivalences via `.symm.trans`.
  `CDMGNodeIso` has a single intended consumer at this row
  (claim_3_19's statement itself); no chaining is on the
  table, so no laws are written. Mirrors the
  "wait-for-second-consumer" policy that
  `TwoDisjointNodeSplittingsCommute.lean`'s own design block
  documents for `CDMGEquiv`. If a downstream consumer needs
  composition (e.g. transitively chaining a claim_3_19 iso
  with another cross-carrier iso) the laws can be added here
  in a small follow-up; until then they are unjustified
  surface area.

* **Local to this file, not promoted to a shared module.**
  Same single-consumer rationale: lifting now would force a
  placement decision -- `Section3_1/` alongside `CDMG.lean`
  (where def_3_1 lives), or `Section3_2/` alongside
  `CDMGEquiv` in `TwoDisjointNodeSplittingsCommute.lean` --
  which should wait until a *second* cross-carrier-iso row
  surfaces and reveals the natural API shape. The cost of
  lifting later (re-import, rename, possibly
  unify-with-`CDMGEquiv`) is small; the cost of locking in
  the wrong shape now would be repaid by every downstream
  consumer. -/
structure CDMGNodeIso {α β : Type u} (G : CDMG α) (H : CDMG β) where
  /-- The underlying function on carrier types. -/
  toFun : α → β
  /-- The function is injective on `G`'s nodes. -/
  injOn_nodes : Set.InjOn toFun (G.J ∪ G.V)
  /-- The function sends `G.J` to `H.J`. -/
  J_eq : H.J = toFun '' G.J
  /-- The function sends `G.V` to `H.V`. -/
  V_eq : H.V = toFun '' G.V
  /-- The function sends `G.E` to `H.E` (applied componentwise to
  endpoints). -/
  E_eq : H.E = (Prod.map toFun toFun) '' G.E
  /-- The function sends `G.L` to `H.L` (applied componentwise to
  endpoints). -/
  L_eq : H.L = (Prod.map toFun toFun) '' G.L

/-! ### Private helpers for the proof of claim_3_19

These three helpers underpin the proof body below:

* `split1_injective` — `split1 W` is injective on all of `α`.
  Used for `injOn_nodes` (the carrier map need only be injective on
  the LHS's nodes, but `split1` is in fact globally injective, so
  we prove the stronger statement and restrict at the call site).
* `no_swig_edge_source_in_inlW` — every directed edge of
  `G.swig W hW` has its source outside `Sum.inl '' W = W^o`. This
  is the LN proof's key observation ("nodes in `W^o` have no
  outgoing directed edges in the SWIG"): the SWIG inherits its
  edges from `nodeSplittingOn`, whose source dispatch
  (`split1 W v₁`) lands in `Sum.inl '' (G.V ∖ W) ∪ Set.range Sum.inr`
  — disjoint from `Sum.inl '' W`.
* `swig_directed_walk_interior_in_inlW_imp_edge` — a non-trivial
  directed walk in the SWIG whose every intermediate vertex lies
  in `W^o` is forced to be a single forward step. Proof: the
  second vertex of any longer walk would be both intermediate
  (hence in `W^o` by hypothesis) and a source of a SWIG edge
  (witnessed by the walk's second step) — forbidden by the
  previous helper. This collapses the walk-existential in
  `marginalize.E` membership to a single SWIG edge. -/

private theorem split1_injective {α : Type u} (W : Set α) :
    Function.Injective (split1 W) := by
  intro x y hxy
  by_cases hxW : x ∈ W
  · by_cases hyW : y ∈ W
    · rw [split1_of_mem hxW, split1_of_mem hyW] at hxy
      have h_eq : (⟨x, hxW⟩ : ↑W) = ⟨y, hyW⟩ := Sum.inr_injective hxy
      exact congrArg Subtype.val h_eq
    · rw [split1_of_mem hxW, split1_of_not_mem hyW] at hxy
      exact nomatch hxy
  · by_cases hyW : y ∈ W
    · rw [split1_of_not_mem hxW, split1_of_mem hyW] at hxy
      exact nomatch hxy
    · rw [split1_of_not_mem hxW, split1_of_not_mem hyW] at hxy
      exact Sum.inl_injective hxy

private theorem no_swig_edge_source_in_inlW
    {α : Type u} {G : CDMG α} {W : Set α} {hW : W ⊆ G.V}
    {s t : α ⊕ ↑W} (h : (s, t) ∈ (G.swig W hW).E) :
    s ∉ Sum.inl '' W := by
  rw [mem_nodeSplittingHardInterventionOn_E] at h
  obtain ⟨v₁, _, _, h_eq⟩ := h
  obtain ⟨hs_eq, _⟩ := (Prod.mk.injEq _ _ _ _).mp h_eq
  rintro ⟨w, hw, hsw⟩
  -- hs_eq : s = split1 W v₁ and hsw : Sum.inl w = s.
  rw [hs_eq] at hsw
  by_cases hv₁ : v₁ ∈ W
  · rw [split1_of_mem hv₁] at hsw
    exact nomatch hsw
  · rw [split1_of_not_mem hv₁] at hsw
    -- hsw : Sum.inl w = Sum.inl v₁
    have : w = v₁ := Sum.inl_injective hsw
    exact hv₁ (this ▸ hw)

/-- For a walk that begins `cons step rest` where `rest` has at
least one more step, the target of `step` (the second vertex of
the walk) lies in `support.tail.dropLast` — i.e. it is an
intermediate vertex of the walk. -/
private theorem second_vertex_mem_interior
    {α : Type*} {G : CDMG α}
    {s w t : α} (step : WalkStep G s w) (rest : Walk G w t)
    (h_pos : 1 ≤ rest.length) :
    w ∈ (Walk.cons step rest).support.tail.dropLast := by
  change w ∈ (s :: rest.support).tail.dropLast
  rw [List.tail_cons]
  cases rest with
  | nil _ => simp [Walk.length] at h_pos
  | cons _ rest' =>
    change w ∈ (w :: rest'.support).dropLast
    have hps_ne : rest'.support ≠ [] := by
      intro h
      have := rest'.support_length
      rw [h] at this; simp at this
    rw [List.dropLast_cons_of_ne_nil hps_ne]
    exact List.mem_cons_self

/-- A non-trivial directed walk in `G.swig W hW` whose interior
lies in `Sum.inl '' W = W^o` is forced to be a single forward
step. Equivalently, the endpoints already form a SWIG edge. -/
private theorem swig_directed_walk_interior_in_inlW_imp_edge
    {α : Type u} {G : CDMG α} {W : Set α} {hW : W ⊆ G.V} :
    ∀ {s t : α ⊕ ↑W} (π : Walk (G.swig W hW) s t),
      π.IsDirected → π.InteriorIn (Sum.inl '' W) → 1 ≤ π.length →
        (s, t) ∈ (G.swig W hW).E := by
  intro s t π
  cases π with
  | nil _ => intro _ _ hπl; simp at hπl
  | cons s' p =>
    cases s' with
    | forward h =>
      cases p with
      | nil _ => intro _ _ _; exact h
      | cons s'' p' =>
        intro _ hi _
        exfalso
        -- The second vertex `w` (target of `forward h`) is an
        -- intermediate vertex. Since `s''` starts at `w` and the
        -- walk is directed, `s''` must be `forward h''`, forcing
        -- `w` to be the source of a SWIG edge — forbidden by
        -- `no_swig_edge_source_in_inlW` once we know `w ∈ W^o`.
        rename_i w _ _ _
        have hsup_ne : p'.support ≠ [] := by
          intro he
          have hl := p'.support_length
          rw [he] at hl
          simp at hl
        have hw_int :
            w ∈ (Walk.cons (WalkStep.forward h)
                  (Walk.cons s'' p')).support.tail.dropLast := by
          simp only [Walk.support_cons, List.tail_cons]
          rw [List.dropLast_cons_of_ne_nil hsup_ne]
          exact List.mem_cons_self
        have hw_inlW : w ∈ Sum.inl '' W := hi _ hw_int
        cases s'' with
        | forward h'' =>
          exact no_swig_edge_source_in_inlW (hW := hW) h'' hw_inlW
        | backward _ => simp [Walk.IsDirected] at *
        | bidir _ => simp [Walk.IsDirected] at *
    | backward _ => intro hd _ _; simp [Walk.IsDirected] at hd
    | bidir _ => intro hd _ _; simp [Walk.IsDirected] at hd

/-- A bifurcation walk in `G.swig W hW` whose interior lies in
`Sum.inl '' W = W^o` is forced to consist of a single hinge step.
Combined with the bifurcation's `hingeIntoSource` constraint, the
hinge is either `backward` (giving `(t, s) ∈ E_swig`) or `bidir`
(giving `(s, t) ∈ L_swig`).

This is the bifurcation analogue of
`swig_directed_walk_interior_in_inlW_imp_edge`. The proof shows
that if `leftArm.length ≥ 1` or `rightArm.length ≥ 1`, an
intermediate vertex of `π` would be both in `W^o` (by hypothesis)
and the source of a SWIG E edge (by the arm's first step) —
contradicting `no_swig_edge_source_in_inlW`. -/
private theorem swig_bifurcation_interior_in_inlW_imp_L_or_revE
    {α : Type u} {G : CDMG α} {W : Set α} {hW : W ⊆ G.V}
    {s t : α ⊕ ↑W} (π : Walk (G.swig W hW) s t)
    (hπb : π.IsBifurcation) (hπi : π.InteriorIn (Sum.inl '' W)) :
    (s, t) ∈ (G.swig W hW).L ∨ (t, s) ∈ (G.swig W hW).E := by
  -- Destructure the bifurcation witness into independent locals.
  obtain ⟨_, _, _, ⟨bw⟩⟩ := hπb
  obtain ⟨bm, bm', leftArm, hinge, rightArm, h_decomp, h_lb, h_hIS, h_rd⟩ := bw
  cases leftArm with
  | cons step1 rest1 =>
    -- leftArm.length ≥ 1 → step1 is backward → its target is intermediate
    -- of π and is a source of an E_swig edge. Contradiction.
    exfalso
    cases step1 with
    | forward _ => simp [Walk.IsAllBackward] at h_lb
    | bidir _ => simp [Walk.IsAllBackward] at h_lb
    | backward h₁ =>
      rename_i w
      apply no_swig_edge_source_in_inlW (hW := hW) h₁
      apply hπi
      have hπ_eq :
          π = Walk.cons (.backward h₁)
                (rest1.append (Walk.cons hinge rightArm)) := by
        rw [h_decomp]; rfl
      rw [hπ_eq]
      apply second_vertex_mem_interior
      rw [Walk.length_append, Walk.length_cons]; omega
  | nil _ =>
    -- leftArm = nil ⇒ bm = s. Now case on rightArm.
    cases rightArm with
    | cons stepR restR =>
      -- rightArm.length ≥ 1 → stepR is forward → bm' is its source.
      -- bm' is intermediate of π.
      exfalso
      cases stepR with
      | backward _ => simp [Walk.IsDirected] at h_rd
      | bidir _ => simp [Walk.IsDirected] at h_rd
      | forward h_R =>
        apply no_swig_edge_source_in_inlW (hW := hW) h_R
        apply hπi
        have hπ_eq :
            π = Walk.cons hinge (Walk.cons (.forward h_R) restR) := by
          rw [h_decomp]; rfl
        rw [hπ_eq]
        apply second_vertex_mem_interior
        simp [Walk.length]
    | nil _ =>
      -- rightArm = nil ⇒ bm' = t. π = cons hinge (nil _).
      -- Hinge is at s → t with HasArrowheadAtSource.
      cases hinge with
      | forward _ => exfalso; simp [WalkStep.HasArrowheadAtSource] at h_hIS
      | backward h_h => exact Or.inr h_h
      | bidir h_h => exact Or.inl h_h

/-! ## The claim_3_19 statement -/

-- claim_3_19
-- title: MarginalizingOutThe
--
-- For a CDMG `G = (J, V, E, L)` and an output-node subset `W ⊆ V`:
-- the hard intervention `G_{do(W)}` (def_3_10, LHS, over carrier
-- `α`) is graph-isomorphic to the marginalization of the SWIG
-- `G_{swig(W)}` (def_3_12) over the `W^o` copies (RHS, over
-- carrier `α ⊕ ↑W`). The identification sends each `w ∈ W` --
-- which on the LHS is an input (promoted by the hard intervention)
-- and on the RHS is the fresh `w^i` copy -- to that `w^i` copy;
-- on `J ∪ (V ∖ W)` the identification is the identity (under the
-- canonical `inl`-embedding into `α ⊕ ↑W`).
--
-- In Lean: the identification is exactly `split1 W : α → α ⊕ ↑W`
-- (from `NodeSplittingOn.lean`), which sends `v ∉ W` to
-- `Sum.inl v` (the canonical `inl`-image, identifying with the
-- original vertex; this is the identity on `J ∪ (V ∖ W)` under
-- the `Sum.inl = w^o` convention) and `v ∈ W` to
-- `Sum.inr ⟨v, hv⟩` (the LN's `w ↦ w^i`).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(Lem at lines 1167 -- 1175):

\begin{claimmark}
\begin{Lem}[Marginalizing out the output part of splitted nodes equals hard intervention]
     Let $G=(J,V,E,L)$ be a CDMG and $W \ins V$ be a subset of output nodes from $G$.
     Then the CDMG that arises by first splitting the nodes on $W$
      and then marginalizing out the nodes from $W^o$
     can be identified with the CDMG that arises by hard intervention on $W$:
     \[ G_{\doit(W)} \cong \lp G_{\swig(W)}\rp^{\sm W^o}, \qquad w \mapsto w^i. \]
\end{Lem}
\end{claimmark}
-/
/-- claim_3_19 -- `MarginalizingOutThe`. The hard intervention
`G.hardInterventionOn W` (LHS, over carrier `α`) is
graph-isomorphic to the marginalization of the SWIG over the
`W^o = Sum.inl '' W` copies (RHS, over carrier `α ⊕ ↑W`). The
identification is `split1 W`, which sends `w ∈ W` to
`Sum.inr ⟨w, hw⟩` (the LN's `w ↦ w^i`) and is the identity on
`J ∪ (V ∖ W)` (under the canonical `inl`-embedding, which is the
LN's `v ↦ v^o := v` for `v ∉ W`).

## Design choice

* **Why the carrier-map witness is `split1 W`, not a bespoke
  function.** `split1 W : α → α ⊕ ↑W`
  (`NodeSplittingOn.lean`) is *exactly* the LN's identification:
  `v ∉ W` goes to `Sum.inl v` (the canonical observation copy,
  which under the `Sum.inl = w^o` convention is the LN's
  identity `v ↦ v^o = v` on `J ∪ (V ∖ W)`), and `v ∈ W` goes to
  `Sum.inr ⟨v, hv⟩` (the LN's `w ↦ w^i`). The LN block names
  only `w ↦ w^i` because the identity on the rest is "implicit
  by absence of any other rule"; in our encoding the implicit
  rule is `Sum.inl`, which is precisely `split1`'s
  `else`-branch. Re-using `split1` removes a degree of freedom
  (any other equivalent encoding would be definitionally
  different and force `simp`-rewrites to convert between them)
  and aligns with the chapter-3 split-graph identifications
  used by claim_3_6 / claim_3_7 / claim_3_8 / claim_3_12 /
  def_3_12.

* **Why `Sum.inl '' W` is the precise Lean rendering of `W^o`.**
  `NodeSplittingOn.lean`'s design block pins down the convention
  `Sum.inl = w^o` (0-copy, canonical observation copy) and
  `Sum.inr = w^i` (1-copy, fresh intervention-input label).
  Therefore the LN's `W^o` -- "the `o`-copies of `W` inside the
  SWIG's carrier `α ⊕ ↑W`" -- is literally `Sum.inl '' W :
  Set (α ⊕ ↑W)`. This is the same `inl`-image that
  `nodeSplittingHardInterventionOn_V` returns for the SWIG's
  output set, so the marginalize target shares carriers and
  notation with the surrounding API; no coercion or
  re-encoding is needed.

* **Why marginalize on `Sum.inl '' W` (the `^o` copies) and
  not on `W` itself or `Sum.inr '' W`.** The LN says
  "marginalize out the nodes from `W^o`"; under the
  `^o = Sum.inl` encoding, this is `Sum.inl '' W`.
  Marginalizing `Sum.inr '' W` (the `^i` copies) instead would
  be a *different* and *false* statement: deleting the fresh
  intervention-input copies would collapse the SWIG back
  toward the observational graph `G`, not toward
  `G_{do(W)}`. Marginalizing the raw `W : Set α` is a type
  error -- `marginalize` expects a `Set (α ⊕ ↑W)`, not a
  `Set α`. So `Sum.inl '' W` is the unique correct choice.

* **`hW : W ⊆ G.V` is required at the signature level, and
  only for the SWIG side.** `G.swig W hW` and
  `G.nodeSplittingOn W hW` carry `hW` as a precondition --
  load-bearing on the SWIG/NS side because without it the
  fresh split edge `(Sum.inl w, Sum.inr ⟨w, _⟩)` would violate
  `V_subset` for `w ∈ W ∖ G.V` (see `NodeSplittingOn.lean`'s
  design block, "Precondition `W ⊆ G.V` is structurally
  required"). By contrast, `hardInterventionOn`
  (`HardInterventionOn.lean`) and `marginalize`
  (`Marginalization.lean`) both *dropped* their LN
  preconditions because their constructions are well-defined
  for any `W` -- see those files' own design blocks. So the
  LHS `G.hardInterventionOn W` does not need `hW`; only the
  RHS does, which is why `hW` appears in the signature.

* **Why this is the LN's `\cong` and not literal `=`.** The
  LN writes `G_{do(W)} \cong (G_{swig(W)})^{∖ W^o}` precisely
  because the two CDMGs live over *different* carrier types:
  LHS is `CDMG α` and RHS is `CDMG (α ⊕ ↑W)`. Lean's `=`
  requires both sides to share a type, so an equality
  statement here is a category error. The LN's `\cong` is
  exactly the graph isomorphism captured by `CDMGNodeIso` --
  a node-level bijection that preserves the four data fields.
  Contrast claim_3_4, claim_3_8, claim_3_13 etc., where both
  sides of the chained equation live over the *same* carrier
  and the LN writes literal `=` (matched in Lean by an
  ordinary `theorem` of the form `... = ...`).

* **`noncomputable def` rather than `theorem`.** The
  conclusion `CDMGNodeIso ..` is a `structure` (data, not a
  proposition), so `def` is the correct keyword. The
  `noncomputable` modifier propagates from the
  `split1` / `nodeSplittingOn` chain (both `noncomputable`
  because of the classical case-split on set membership; see
  `NodeSplittingOn.lean`'s `split1` design block). This matches
  the declaration style of `nodeSplittingOn_nodeSplittingOn_equiv`
  and `nodeSplittingOn_comm_equiv` in
  `TwoDisjointNodeSplittingsCommute.lean`, where the same shape
  (`CDMGEquiv`-valued conclusion) is similarly a `noncomputable
  def`.

Body uses three private helpers above the declaration:
`split1_injective`, `no_swig_edge_source_in_inlW`, and
`swig_directed_walk_interior_in_inlW_imp_edge` (the LN proof's
observation that nodes in `W^o` have no outgoing directed edges
collapses the walk-existential in `marginalize.E` to a single SWIG
edge). -/
noncomputable def hardInterventionOn_nodeIso_swig_marginalize_outputs
    {α : Type u} {G : CDMG α} {W : Set α} (hW : W ⊆ G.V) :
    CDMGNodeIso (G.hardInterventionOn W)
                ((G.swig W hW).marginalize (Sum.inl '' W)) where
  toFun := split1 W
  injOn_nodes := fun _ _ _ _ hxy => split1_injective W hxy
  J_eq := by
    -- ((G.swig W hW).marginalize (Sum.inl '' W)).J = (G.swig W hW).J
    --   = Sum.inl '' G.J ∪ Set.range Sum.inr.
    -- split1 W '' (G.J ∪ W) = split1 W '' G.J ∪ split1 W '' W
    --   = Sum.inl '' G.J ∪ Set.range Sum.inr.
    rw [marginalize_J, nodeSplittingHardInterventionOn_J,
        hardInterventionOn_J, Set.image_union]
    have hJ_eq : split1 W '' G.J = Sum.inl '' G.J := by
      apply Set.image_congr
      intro j hj
      have hjW : j ∉ W := fun hjW =>
        Set.disjoint_left.mp G.disjoint_JV hj (hW hjW)
      exact split1_of_not_mem hjW
    have hW_eq : split1 W '' W = Set.range (Sum.inr : ↑W → α ⊕ ↑W) := by
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [split1_of_mem hw]
        exact ⟨⟨w, hw⟩, rfl⟩
      · rintro ⟨⟨w, hw⟩, rfl⟩
        exact ⟨w, hw, split1_of_mem hw⟩
    rw [hJ_eq, hW_eq]
  V_eq := by
    -- ((G.swig W hW).marginalize (Sum.inl '' W)).V = Sum.inl '' G.V \ Sum.inl '' W
    --   = Sum.inl '' (G.V \ W).
    -- split1 W '' (G.V \ W) = Sum.inl '' (G.V \ W).
    rw [marginalize_V, nodeSplittingHardInterventionOn_V,
        hardInterventionOn_V,
        ← Set.image_diff Sum.inl_injective]
    apply Set.image_congr
    intro v hv
    exact (split1_of_not_mem hv.2).symm
  E_eq := by
    -- Forward (⊇): split1 maps each (v₁, v₂) ∈ G.E with v₂ ∉ W to a
    -- SWIG edge (split1 W v₁, Sum.inl v₂); this is a length-1
    -- directed walk in the SWIG with empty interior.
    -- Backward (⊆): a directed walk with interior in W^o reduces by
    -- `swig_directed_walk_interior_in_inlW_imp_edge` to a single SWIG
    -- edge; unpacking via `mem_nodeSplittingHardInterventionOn_E`
    -- gives the LHS shape.
    ext ⟨p1, p2⟩
    rw [mem_marginalize_E]
    change _ ∧ p2 ∈ _ ∧ _ ↔ _
    constructor
    · rintro ⟨_, hp2, π, hπd, hπi, hπl⟩
      -- hp2 : p2 ∈ (G.swig W hW).V \ (Sum.inl '' W)
      rw [nodeSplittingHardInterventionOn_V] at hp2
      simp only [Set.mem_diff, Set.mem_image] at hp2
      obtain ⟨⟨v₂, hv₂V, hp2_eq⟩, hp2_nW⟩ := hp2
      have hv₂nW : v₂ ∉ W := fun hv₂W => hp2_nW ⟨v₂, hv₂W, hp2_eq⟩
      have hedge : (p1, p2) ∈ (G.swig W hW).E :=
        swig_directed_walk_interior_in_inlW_imp_edge π hπd hπi hπl
      rw [mem_nodeSplittingHardInterventionOn_E] at hedge
      obtain ⟨v₁, w₂, hE, heq⟩ := hedge
      obtain ⟨hp1_eq, hp2_eq'⟩ := (Prod.mk.injEq _ _ _ _).mp heq
      -- hp2_eq' : p2 = Sum.inl w₂  and  hp2_eq : Sum.inl v₂ = p2
      have hw_eq : v₂ = w₂ :=
        Sum.inl_injective (hp2_eq.trans hp2_eq')
      subst hw_eq
      refine ⟨(v₁, v₂), ?_, ?_⟩
      · -- (v₁, v₂) ∈ (G.hardInterventionOn W).E
        rw [mem_hardInterventionOn_E]
        exact ⟨hE, hv₂nW⟩
      · -- (split1 W v₁, split1 W v₂) = (p1, p2)
        have hp2_split : split1 W v₂ = p2 := by
          rw [split1_of_not_mem hv₂nW]; exact hp2_eq
        change (split1 W v₁, split1 W v₂) = (p1, p2)
        rw [hp1_eq.symm, hp2_split]
    · rintro ⟨⟨v₁, v₂⟩, hE_and_nW, h_eq⟩
      rw [mem_hardInterventionOn_E] at hE_and_nW
      obtain ⟨hE, hv₂nW⟩ := hE_and_nW
      change v₂ ∉ W at hv₂nW
      obtain ⟨hp1_eq, hp2_eq⟩ := (Prod.mk.injEq _ _ _ _).mp h_eq
      -- hp1_eq : split1 W v₁ = p1, hp2_eq : split1 W v₂ = p2
      have hp2_inl : p2 = Sum.inl v₂ := by
        rw [← hp2_eq, split1_of_not_mem hv₂nW]
      have hv₁V : v₁ ∈ G.J ∪ G.V := (G.E_subset hE).1
      have hv₂V : v₂ ∈ G.V := (G.E_subset hE).2
      refine ⟨?_, ?_, ?_⟩
      · -- p1 ∈ (G.swig).J ∪ ((G.swig).V \ Sum.inl '' W)
        rw [nodeSplittingHardInterventionOn_J, nodeSplittingHardInterventionOn_V,
            ← hp1_eq]
        by_cases hv₁W : v₁ ∈ W
        · rw [split1_of_mem hv₁W]
          exact Or.inl (Or.inr ⟨⟨v₁, hv₁W⟩, rfl⟩)
        · rw [split1_of_not_mem hv₁W]
          rcases hv₁V with hJ | hV
          · exact Or.inl (Or.inl ⟨v₁, hJ, rfl⟩)
          · refine Or.inr ⟨⟨v₁, hV, rfl⟩, ?_⟩
            rintro ⟨w, hw, hwv⟩
            have : v₁ = w := Sum.inl_injective hwv.symm
            exact hv₁W (this ▸ hw)
      · -- p2 ∈ (G.swig).V \ Sum.inl '' W
        rw [nodeSplittingHardInterventionOn_V, hp2_inl]
        refine ⟨⟨v₂, hv₂V, rfl⟩, ?_⟩
        rintro ⟨w, hw, hwv⟩
        have : v₂ = w := Sum.inl_injective hwv.symm
        exact hv₂nW (this ▸ hw)
      · -- Witness walk: single forward SWIG edge.
        have hswig_E : (p1, p2) ∈ (G.swig W hW).E := by
          rw [mem_nodeSplittingHardInterventionOn_E]
          refine ⟨v₁, v₂, hE, ?_⟩
          rw [← hp1_eq, hp2_inl]
        refine ⟨Walk.cons (WalkStep.forward hswig_E) (Walk.nil p2), ?_, ?_, ?_⟩
        · simp [Walk.IsDirected]
        · intro x hx
          simp [Walk.support] at hx
        · simp [Walk.length]
  L_eq := by
    -- Forward (⊇): given (u, v) ∈ G.L with u, v ∉ W, we build a
    -- length-1 bidir bifurcation walk witness in the SWIG using the
    -- L_swig edge (Sum.inl u, Sum.inl v) (decoded from
    -- `mem_nodeSplittingHardInterventionOn_L`).
    -- Backward (⊆): a bifurcation walk in the SWIG with interior in
    -- W^o is forced (by `swig_bifurcation_interior_in_inlW_imp_L_or_revE`)
    -- to be either an L_swig edge or a reverse-direction E_swig edge.
    -- The latter contradicts the L-marginalize requirement of no
    -- directed walk in either direction, leaving the L_swig case;
    -- decoding gives (u, v) ∈ G.L.
    ext ⟨p1, p2⟩
    rw [mem_marginalize_L]
    change p1 ∈ _ ∧ p2 ∈ _ ∧ _ ↔ _
    constructor
    · rintro ⟨hp1, hp2, hp_ne, hnE12, hnE21, hbif⟩
      rw [nodeSplittingHardInterventionOn_V] at hp1 hp2
      simp only [Set.mem_diff, Set.mem_image] at hp1 hp2
      obtain ⟨⟨u, huV, hp1_eq⟩, hp1_nW⟩ := hp1
      obtain ⟨⟨v, hvV, hp2_eq⟩, hp2_nW⟩ := hp2
      have huW : u ∉ W := fun huW => hp1_nW ⟨u, huW, hp1_eq⟩
      have hvW : v ∉ W := fun hvW => hp2_nW ⟨v, hvW, hp2_eq⟩
      -- WLOG, the bifurcation walk goes from p1 to p2 (use L_symm if needed)
      have h_L_swig_uv_or_vu :
          (p1, p2) ∈ (G.swig W hW).L ∨ (p2, p1) ∈ (G.swig W hW).L := by
        rcases hbif with ⟨π, hπb, hπi⟩ | ⟨π, hπb, hπi⟩
        · rcases swig_bifurcation_interior_in_inlW_imp_L_or_revE π hπb hπi with hL | hRevE
          · exact Or.inl hL
          · -- (p2, p1) ∈ E_swig — but this gives a directed walk p2 → p1,
            -- contradicting hnE21.
            exfalso
            apply hnE21
            refine ⟨Walk.cons (WalkStep.forward hRevE) (Walk.nil p1), ?_, ?_⟩
            · simp [Walk.IsDirected]
            · intro x hx; simp [Walk.support] at hx
        · rcases swig_bifurcation_interior_in_inlW_imp_L_or_revE π hπb hπi with hL | hRevE
          · exact Or.inr hL
          · -- (p1, p2) ∈ E_swig — directed walk p1 → p2, contradicts hnE12.
            exfalso
            apply hnE12
            refine ⟨Walk.cons (WalkStep.forward hRevE) (Walk.nil p2), ?_, ?_⟩
            · simp [Walk.IsDirected]
            · intro x hx; simp [Walk.support] at hx
      -- Decode the L_swig membership.
      rcases h_L_swig_uv_or_vu with hL | hL
      · rw [mem_nodeSplittingHardInterventionOn_L] at hL
        obtain ⟨u', v', huvL, hp_eq⟩ := hL
        obtain ⟨hp1_eq', hp2_eq'⟩ := (Prod.mk.injEq _ _ _ _).mp hp_eq
        have hu_eq : u = u' := Sum.inl_injective (hp1_eq.trans hp1_eq')
        have hv_eq : v = v' := Sum.inl_injective (hp2_eq.trans hp2_eq')
        subst hu_eq
        subst hv_eq
        refine ⟨(u, v), ?_, ?_⟩
        · rw [mem_hardInterventionOn_L]
          exact ⟨huvL, huW, hvW⟩
        · change (split1 W u, split1 W v) = (p1, p2)
          rw [split1_of_not_mem huW, split1_of_not_mem hvW, hp1_eq, hp2_eq]
      · rw [mem_nodeSplittingHardInterventionOn_L] at hL
        obtain ⟨v', u', hvuL, hp_eq⟩ := hL
        obtain ⟨hp2_eq', hp1_eq'⟩ := (Prod.mk.injEq _ _ _ _).mp hp_eq
        have hu_eq : u = u' := Sum.inl_injective (hp1_eq.trans hp1_eq')
        have hv_eq : v = v' := Sum.inl_injective (hp2_eq.trans hp2_eq')
        subst hu_eq
        subst hv_eq
        refine ⟨(u, v), ?_, ?_⟩
        · rw [mem_hardInterventionOn_L]
          exact ⟨G.L_symm hvuL, huW, hvW⟩
        · change (split1 W u, split1 W v) = (p1, p2)
          rw [split1_of_not_mem huW, split1_of_not_mem hvW, hp1_eq, hp2_eq]
    · rintro ⟨⟨u, v⟩, hLuv_and_nW, h_eq⟩
      rw [mem_hardInterventionOn_L] at hLuv_and_nW
      obtain ⟨huvL, huW, hvW⟩ := hLuv_and_nW
      obtain ⟨hp1_eq, hp2_eq⟩ := (Prod.mk.injEq _ _ _ _).mp h_eq
      have hp1_inl : p1 = Sum.inl u := by rw [← hp1_eq, split1_of_not_mem huW]
      have hp2_inl : p2 = Sum.inl v := by rw [← hp2_eq, split1_of_not_mem hvW]
      have huV : u ∈ G.V := (G.L_subset huvL).1
      have hvV : v ∈ G.V := (G.L_subset huvL).2
      have hu_ne_v : u ≠ v := G.L_irrefl huvL
      -- The SWIG L edge (Sum.inl u, Sum.inl v) decoded from huvL.
      have hL_swig : (Sum.inl u, Sum.inl v) ∈ (G.swig W hW).L := by
        rw [mem_nodeSplittingHardInterventionOn_L]
        exact ⟨u, v, huvL, rfl⟩
      -- Helper: no directed walk in either direction with interior in W^o.
      have h_no_dir :
          ∀ {a b : α}, (a, b) ∈ G.L → a ∉ W → b ∉ W →
            ¬ ∃ π : Walk (G.swig W hW) (Sum.inl a) (Sum.inl b),
              π.IsDirected ∧ π.InteriorIn (Sum.inl '' W) := by
        intro a b habL haW hbW ⟨π, hπd, hπi⟩
        by_cases hπl : 1 ≤ π.length
        · have hedge :=
            swig_directed_walk_interior_in_inlW_imp_edge π hπd hπi hπl
          rw [mem_nodeSplittingHardInterventionOn_E] at hedge
          obtain ⟨v₁, v₂, hE, h_eq'⟩ := hedge
          obtain ⟨ha_eq, hb_eq⟩ := (Prod.mk.injEq _ _ _ _).mp h_eq'
          have hv₂_eq : v₂ = b := Sum.inl_injective hb_eq.symm
          subst hv₂_eq
          by_cases hv₁W : v₁ ∈ W
          · rw [split1_of_mem hv₁W] at ha_eq; exact nomatch ha_eq
          · rw [split1_of_not_mem hv₁W] at ha_eq
            have : v₁ = a := Sum.inl_injective ha_eq.symm
            subst this
            exact Set.disjoint_left.mp G.disjoint_EL hE habL
        · -- ¬ (1 ≤ π.length): π must be nil.
          cases π with
          | nil _ => exact G.L_irrefl habL rfl
          | cons _ p =>
            apply hπl
            change 1 ≤ p.length + 1
            omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- p1 ∈ (G.swig).V \ Sum.inl '' W
        rw [nodeSplittingHardInterventionOn_V, hp1_inl]
        refine ⟨⟨u, huV, rfl⟩, ?_⟩
        rintro ⟨w, hw, hwu⟩
        have : u = w := Sum.inl_injective hwu.symm
        exact huW (this ▸ hw)
      · -- p2 ∈ (G.swig).V \ Sum.inl '' W
        rw [nodeSplittingHardInterventionOn_V, hp2_inl]
        refine ⟨⟨v, hvV, rfl⟩, ?_⟩
        rintro ⟨w, hw, hwv⟩
        have : v = w := Sum.inl_injective hwv.symm
        exact hvW (this ▸ hw)
      · -- p1 ≠ p2
        rw [hp1_inl, hp2_inl]
        intro h; exact hu_ne_v (Sum.inl_injective h)
      · -- ¬ ∃ directed walk p1 → p2 with interior in W^o
        rw [hp1_inl, hp2_inl]
        exact h_no_dir huvL huW hvW
      · -- ¬ ∃ directed walk p2 → p1 with interior in W^o
        rw [hp1_inl, hp2_inl]
        exact h_no_dir (G.L_symm huvL) hvW huW
      · -- ∃ bifurcation walk
        left
        -- Construct the length-1 bidir bifurcation walk.
        rw [hp1_inl, hp2_inl]
        refine ⟨Walk.cons (.bidir hL_swig) (Walk.nil _), ?_, ?_⟩
        · -- IsBifurcation
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro h; exact hu_ne_v (Sum.inl_injective h)
          · simp [Walk.support]
            intro h; exact hu_ne_v h
          · simp [Walk.support]
            intro h; exact hu_ne_v h.symm
          · refine ⟨⟨Sum.inl u, Sum.inl v,
              Walk.nil (Sum.inl u), .bidir hL_swig, Walk.nil (Sum.inl v),
              ?_, ?_, ?_, ?_⟩⟩
            · rfl
            · simp [Walk.IsAllBackward]
            · simp [WalkStep.HasArrowheadAtSource]
            · simp [Walk.IsDirected]
        · -- InteriorIn
          intro x hx; simp [Walk.support] at hx

end CDMG

end Causality
