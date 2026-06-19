import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn

/-!
# Node-splitting hard intervention (SWIG) on a CDMG (def 3.12)

This file formalises *definition 3.12* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`,
`def:G_node-splitting_intervention`): given a CDMG `G = (J, V, E, L)`
and a subset `W ⊆ V` of output nodes, the *single-world intervention
graph* (SWIG) `G_{swig(W)}` is obtained by first node-splitting on
`W` and then hard-intervening on the freshly introduced 1-copies
(the `W^i` set). Concretely:

```
G.nodeSplittingHardInterventionOn W hW
  := (G.nodeSplittingOn W hW).hardInterventionOn (Set.range Sum.inr)
```

— with the convention (established in `NodeSplittingOn.lean`) that
`Sum.inl = 0-copy = w^o = canonical observation copy` and
`Sum.inr ⟨w, _⟩ = 1-copy = w^i = fresh intervention-input`. The four
components of the SWIG then drop out of the `@[simp]` lemmas attached
to `hardInterventionOn` and `nodeSplittingOn`; see the four
characterisation lemmas at the bottom of this file.

This is the foundational definition of the **single-world
intervention graph** — the building block for counterfactuals and the
iSCM machinery in later chapters.

## Where this gets used downstream

* **claim_3_11** (`graphs.tex` Lem at lines 666 -- 671) -- the SWIG
  mirror of claim_3_8 "disjoint hard interventions and
  node-splittings commute". This is the most direct downstream
  consumer; its proof rewrites against the four `@[simp]` lemmas
  below in lockstep with `HardInterventionNodeSplittingCommute.lean`.
* **Chapters 4 -- 16** -- CBNs, do-calculus, iSCMs (especially the
  counterfactual layer in `counterfactuals.tex`), and identification
  all instantiate SWIGs as their graph-side substrate. The
  Richardson--Robins SWIG construction underpins the
  counterfactual / nested-potential-outcome machinery throughout.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

-- def_3_12
-- title: NodeSplittingHard
--
-- The *single-world intervention graph* (SWIG) of a CDMG
-- `G = (J, V, E, L)` w.r.t. a subset `W ⊆ V` of output nodes:
-- first node-split on `W` (yielding `G_{spl(W)}` over the carrier
-- `α ⊕ ↑W`, with `w^o = Sum.inl w` and `w^i = Sum.inr ⟨w, _⟩`),
-- then hard-intervene on the fresh `W^i = Set.range Sum.inr`
-- copies, promoting them to inputs and stripping every edge whose
-- target lies in `W^i`. The LN's `\swig(W)` subscript is the same
-- operator written infix.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.12):

\begin{defmark}
\begin{Def}[Node-splitting hard intervention on CADMGs]
  \label{def:G_node-splitting_intervention}
    Let $G=(J,V,E,L)$ be a CADMG and $W \ins V$ a subset of the output nodes.
    The \emph{single-world intervention graph (SWIG)} w.r.t.\ $W$ of $G$ is the CADMG:
    \[ G_{\swig(W)} :=\lp J_{\swig(W)}, V_{\swig(W)}, E_{\swig(W)},L_{\swig(W)} \rp,\]
    %\[ G_{\swig(W)} := G':=(J',V',E',L'),\]
    %\[G((V\sm W) \dcup W^o|\doit(W^i \dcup J)):=G':=(J',V',E',L'),\]
    constructed as follows.
    We first make two disjont copies of the nodes in $W$:
    \[ W^o:=\lC w^o\st w \in W \rC, \qquad W^i:=\lC w^i \st w \in W \rC.  \]
    Note that we consider $w^o \neq w^i$ for $w \in W$.
  However, for brevity, for $v \in J \cup V \sm W$ we put:
  \[ v^o:=v^i:=v.  \]
  We then define:
  \begin{enumerate}[label=\roman*.)]
      \item $J_{\swig(W)} := J \dcup W^i$,
      \item $V_{\swig(W)} := (V \sm W) \dcup W^o$,
      %which could be identified with $V$ again if we want to make the identification $W=W^o$.
      \item $E_{\swig(W)} := \lC v^i_1 \tuh v_2^o \st v_1 \tuh v_2 \in E  \rC$,
      \item $L_{\swig(W)} :=\lC v_1^o \huh v_2^o \st v_1 \huh v_2 \in L \rC$.
  \end{enumerate}
  where we turn all nodes of $W^i$ into input nodes, removing all edges into $W^i$,
  and we turn all nodes of $W^o$ into output nodes, removing all edges out of $W^o$.
\end{Def}
\end{defmark}
-/
--
-- ## Design choice
--
-- * **Composition `(G.nodeSplittingOn W hW).hardInterventionOn
--   (Set.range Sum.inr)` rather than a fresh `CDMG` built field
--   by field.** Aligning the LN's four bullets against the two
--   sister operators shows this composition *is* the LN's
--   construction — not a rephrasing of it, but the literal
--   item-by-item spelling:
--
--     * item i.) `J_{swig(W)} = J ⊔ W^i` is `J_{spl(W)} ∪ range
--       Sum.inr`: `nodeSplittingOn` carries `G.J` under `Sum.inl`,
--       and `hardInterventionOn (Set.range Sum.inr)` adjoins
--       exactly `range Sum.inr = W^i`.
--     * item ii.) `V_{swig(W)} = (V ∖ W) ⊔ W^o` is
--       `V_{spl(W)} ∖ range Sum.inr`: the split graph's outputs
--       are `Sum.inl '' G.V ∪ range Sum.inr`, and removing the
--       fresh copies collapses them to `Sum.inl '' G.V` — which
--       carries all of `(V ∖ W) ⊔ W^o` under our identification
--       `w^o = Sum.inl w`.
--     * item iii.) `E_{swig(W)} = {v_1^i → v_2^o | v_1 → v_2 ∈
--       E}` is piece 1 of `E_{spl(W)}` post-HI: the split graph's
--       piece 1 (`(split1 W v_1, Sum.inl v_2)`) has target
--       `Sum.inl _ ∉ W^i` and survives, while piece 2's fresh
--       split edges `(Sum.inl w, Sum.inr ⟨w, _⟩)` have target in
--       `W^i` and are deleted by the HI. What survives is the
--       LN's "relabel source via $v^i$, leave target as $v^o$"
--       rule verbatim.
--     * item iv.) `L_{swig(W)} = {v_1^o ↔ v_2^o | v_1 ↔ v_2 ∈
--       L}` is `L_{spl(W)}` unchanged: every bidirected edge in
--       the split graph has both endpoints of the form
--       `Sum.inl _`, so none touch `W^i = range Sum.inr` and the
--       HI is a no-op on `L`.
--
--   Defining the SWIG as this composition reuses every structural
--   obligation already discharged by the two building blocks
--   (`disjoint_JV`, `E_subset`, `L_subset`, `L_irrefl`, `L_symm`,
--   `disjoint_EL`); an independent field-by-field rebuild would
--   re-prove roughly fifty lines of structural lemmas and, worse,
--   would create a parallel API that every downstream composition
--   with another `nodeSplittingOn` / `hardInterventionOn` would
--   have to bridge. The composition shape is also what makes
--   claim_3_11 — the SWIG mirror of claim_3_8 "disjoint hard
--   interventions and node-splittings commute" — a near-direct
--   rewrite through the same `@[simp]` lemmas already used by
--   `HardInterventionNodeSplittingCommute.lean`.
--
-- * **Intervention target `Set.range (Sum.inr : ↑W → α ⊕ ↑W)` is
--   the post-split image of `W^i`.** In the `α ⊕ ↑W` carrier
--   produced by `nodeSplittingOn`, the fresh intervention-input
--   copies `W^i` are precisely `Sum.inr`'s image of `↑W`.
--   Hard-intervening on `Set.range Sum.inr` is therefore the
--   literal LN sentence at the bottom of def 3.12: "turn all
--   nodes of $W^i$ into input nodes, removing all edges into
--   $W^i$". This is the *role-flipped* analogue of the
--   `Sum.inl '' W₁` intervention target used in
--   `HardInterventionNodeSplittingCommute.lean` (claim_3_8):
--   claim_3_8 intervenes on the *canonical* copies of `W₁`
--   (lifted through `Sum.inl`), while def_3_12 intervenes on the
--   *fresh* copies of `W` (lifted through `Sum.inr`). The
--   asymmetry is what gives SWIG its "single-world" character —
--   the original outputs (`Sum.inl '' G.V`) are preserved as
--   observables while the fresh `W^i` carries the intervention.
--
-- * **Carrier `α ⊕ ↑W` and the `Sum.inl` / `Sum.inr` convention
--   are inherited from `nodeSplittingOn`.** No fresh design
--   choice is made at this row: `Sum.inl w = w^o` (canonical
--   observation copy, identified with the original `w`) and
--   `Sum.inr ⟨w, _⟩ = w^i` (fresh intervention-input label) are
--   fixed by `NodeSplittingOn.lean`, where the longer
--   justification lives — the LN's own hints `W = W^o` (def 3.11
--   and def 3.12) plus the Richardson--Robins SWIG convention
--   `X = X^o`. The reason to flag the convention at this row at
--   all is that the four `@[simp]` lemmas below speak in those
--   terms (`Sum.inl '' G.J` in `_J`, `Sum.inl '' G.V` in `_V`,
--   `split1 W v_1` and `Sum.inl v_2` in `_E`, double-`Sum.inl`
--   in `_L`); a reader who skips the `NodeSplittingOn.lean`
--   design block would otherwise be surprised by constructor
--   names appearing inside LN-faithful set-builder forms.

/-- The *single-world intervention graph (SWIG)* of the CDMG `G`
w.r.t. a set `W ⊆ G.V` of output nodes: the new CDMG over the
carrier `α ⊕ ↑W` obtained by first node-splitting on `W` (yielding
`w^o = Sum.inl w` and `w^i = Sum.inr ⟨w, _⟩`) and then
hard-intervening on the freshly introduced `W^i = Set.range Sum.inr`
copies. See `lecture-notes/lecture_notes/graphs.tex` definition
`def:G_node-splitting_intervention` (def 3.12 of the LN).

By construction this is exactly
`(G.nodeSplittingOn W hW).hardInterventionOn (Set.range Sum.inr)`;
the four `@[simp]` lemmas `nodeSplittingHardInterventionOn_J`,
`nodeSplittingHardInterventionOn_V`,
`mem_nodeSplittingHardInterventionOn_E`,
`mem_nodeSplittingHardInterventionOn_L` below characterise the four
components and are the gateway for every downstream SWIG rewrite. -/
noncomputable def nodeSplittingHardInterventionOn
    (G : CDMG α) (W : Set α) (hW : W ⊆ G.V) : CDMG (α ⊕ ↑W) :=
  (G.nodeSplittingOn W hW).hardInterventionOn
    (Set.range (Sum.inr : ↑W → α ⊕ ↑W))

/-- Short-form alias for `nodeSplittingHardInterventionOn`, exposing
the LN's `\swig` macro / Richardson--Robins SWIG terminology as
the dot-notation `G.swig W hW`. The alias is purely cosmetic:
its job is to let downstream Lean prose (claim_3_11 here, and the
counterfactual / identification / iSCM machinery of chapters
4 -- 16) read like the lecture notes' `G_{\swig(W)}` rather than
the eight-syllable long-form name.

Declared as a `noncomputable abbrev` (not `def`) so that the four
`@[simp]` lemmas attached to `nodeSplittingHardInterventionOn` fire
on `G.swig W hW` terms by reducibility; a plain `def` would have
forced every downstream caller either to `unfold swig` first or to
maintain a parallel `swig_*` simp-lemma family. -/
noncomputable abbrev swig (G : CDMG α) (W : Set α) (hW : W ⊆ G.V) :
    CDMG (α ⊕ ↑W) :=
  G.nodeSplittingHardInterventionOn W hW

/-! ## `@[simp]` projection / membership lemmas

These four lemmas are the SWIG's downstream API — one per LN field,
matching def 3.12 items i.) -- iv.) exactly. Their reason to exist
is the two-layer composition shape of
`nodeSplittingHardInterventionOn`: without them, every downstream
`simp` mentioning `G.swig W hW` (or its long-form twin) would have
to peel off `hardInterventionOn` *and* `nodeSplittingOn` by hand
before re-encoding the result into the LN's set-builder form. With
them, that whole unfold collapses to a single rewrite, and the
inner NS / HI constructions never need to surface in client proofs.

Each lemma is a 1 -- 4 line consequence of the corresponding
`@[simp]` lemmas on `hardInterventionOn` and `nodeSplittingOn` plus
the disjointness of `Sum.inl` and `Sum.inr` (no element of
`Sum.inl '' ·` lies in `Set.range Sum.inr`). Downstream consumers
(claim_3_11 and the chapter 4 -- 16 counterfactual machinery)
rewrite against these lemmas without ever having to unfold either
the composition or the underlying NS / HI constructions. -/

/-- The *input* nodes of `G.nodeSplittingHardInterventionOn W hW`
are `Sum.inl '' G.J ∪ Set.range Sum.inr`: the original inputs
(carried under the canonical `inl` embedding) plus the fresh
intervention-input labels `W^i = Set.range Sum.inr`. This matches
the LN's `J_{swig(W)} = J ⊔ W^i` (def 3.12 item i.) under the
identification `α ≅ inl '' α` of `NodeSplittingOn.lean`. By
definition of the composition together with the `@[simp]` lemmas
`hardInterventionOn_J` and `nodeSplittingOn_J`. -/
@[simp] theorem nodeSplittingHardInterventionOn_J
    (G : CDMG α) (W : Set α) (hW : W ⊆ G.V) :
    (G.nodeSplittingHardInterventionOn W hW).J =
      Sum.inl '' G.J ∪ Set.range (Sum.inr : ↑W → α ⊕ ↑W) := by
  change ((G.nodeSplittingOn W hW).hardInterventionOn
      (Set.range Sum.inr)).J = _
  rw [hardInterventionOn_J, nodeSplittingOn_J]

/-- The *output* nodes of `G.nodeSplittingHardInterventionOn W hW`
are `Sum.inl '' G.V`: the LN's `(V ∖ W) ⊔ W^o` collapses to all of
`Sum.inl '' G.V` under our identification `w^o = Sum.inl w` (so
`W^o ⊆ Sum.inl '' G.V` since `W ⊆ G.V`, and `(V ∖ W) ∪ W = V` when
`W ⊆ V`). Matches def 3.12 item ii. Proven by reducing to
`(Sum.inl '' G.V ∪ Set.range Sum.inr) \ Set.range Sum.inr` via the
NS / HI projection simp lemmas, then noting `Sum.inl '' G.V` is
disjoint from `Set.range Sum.inr` by constructor mismatch. -/
@[simp] theorem nodeSplittingHardInterventionOn_V
    (G : CDMG α) (W : Set α) (hW : W ⊆ G.V) :
    (G.nodeSplittingHardInterventionOn W hW).V = Sum.inl '' G.V := by
  change ((G.nodeSplittingOn W hW).hardInterventionOn
      (Set.range Sum.inr)).V = _
  rw [hardInterventionOn_V, nodeSplittingOn_V, Set.union_diff_right]
  ext x
  constructor
  · rintro ⟨h, _⟩
    exact h
  · intro h
    refine ⟨h, ?_⟩
    obtain ⟨v, _, rfl⟩ := h
    rintro ⟨w, hw⟩
    cases hw

/-- *Directed-edge* membership in `G.nodeSplittingHardInterventionOn
W hW`: a pair `p` is a directed edge of the SWIG iff it is the
relabeling `(split1 W v₁, Sum.inl v₂)` of some original edge
`(v₁, v₂) ∈ G.E`. Matches def 3.12 item iii.'s set-builder
`{v_1^i → v_2^o | v_1 → v_2 ∈ E}` (source dispatches on `v_1 ∈ W`
via `split1`; target is always the canonical `inl`). The post-NS
piece 2 (split edges `w^o → w^i`) of `nodeSplittingOn_E` is killed
by the HI because its target `Sum.inr w` lies in `W^i = Set.range
Sum.inr`; the post-NS piece 1's target `Sum.inl v₂` never does. -/
@[simp] theorem mem_nodeSplittingHardInterventionOn_E
    (G : CDMG α) (W : Set α) (hW : W ⊆ G.V)
    {p : (α ⊕ ↑W) × (α ⊕ ↑W)} :
    p ∈ (G.nodeSplittingHardInterventionOn W hW).E ↔
      ∃ v₁ v₂, (v₁, v₂) ∈ G.E ∧ p = (split1 W v₁, Sum.inl v₂) := by
  change p ∈ ((G.nodeSplittingOn W hW).hardInterventionOn
      (Set.range Sum.inr)).E ↔ _
  rw [mem_hardInterventionOn_E, mem_nodeSplittingOn_E]
  constructor
  · rintro ⟨h, hn⟩
    rcases h with ⟨v₁, v₂, hE, rfl⟩ | ⟨w, rfl⟩
    · exact ⟨v₁, v₂, hE, rfl⟩
    · exact absurd ⟨w, rfl⟩ hn
  · rintro ⟨v₁, v₂, hE, rfl⟩
    refine ⟨Or.inl ⟨v₁, v₂, hE, rfl⟩, ?_⟩
    rintro ⟨w, hw⟩
    cases hw

/-- *Bidirected-edge* membership in
`G.nodeSplittingHardInterventionOn W hW`: a pair `p` is a bidirected
edge of the SWIG iff it is the double-`inl` relabeling
`(Sum.inl v₁, Sum.inl v₂)` of some original `(v₁, v₂) ∈ G.L`.
Matches def 3.12 item iv.'s `L_{swig(W)} = {v_1^o ↔ v_2^o | v_1 ↔
v_2 ∈ L}`. The HI on `W^i = Set.range Sum.inr` is a no-op on
`nodeSplittingOn_L` because both endpoints of every edge in the
post-NS `L` are of the form `Sum.inl _` (constructor mismatch with
`Sum.inr`). -/
@[simp] theorem mem_nodeSplittingHardInterventionOn_L
    (G : CDMG α) (W : Set α) (hW : W ⊆ G.V)
    {p : (α ⊕ ↑W) × (α ⊕ ↑W)} :
    p ∈ (G.nodeSplittingHardInterventionOn W hW).L ↔
      ∃ v₁ v₂, (v₁, v₂) ∈ G.L ∧ p = (Sum.inl v₁, Sum.inl v₂) := by
  change p ∈ ((G.nodeSplittingOn W hW).hardInterventionOn
      (Set.range Sum.inr)).L ↔ _
  rw [mem_hardInterventionOn_L, mem_nodeSplittingOn_L]
  constructor
  · rintro ⟨h, _, _⟩
    exact h
  · rintro ⟨v₁, v₂, hL, rfl⟩
    refine ⟨⟨v₁, v₂, hL, rfl⟩, ?_, ?_⟩
    · rintro ⟨w, hw⟩; cases hw
    · rintro ⟨w, hw⟩; cases hw

end CDMG

end Causality
