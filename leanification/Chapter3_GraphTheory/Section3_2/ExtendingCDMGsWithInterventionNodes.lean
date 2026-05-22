import Chapter3_GraphTheory.Section3_1.CDMGNotation

/-!
# Extending a CDMG with intervention nodes (def 3.13)

This file formalises *definition 3.13* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`,
`def:cdmg_intervention_nodes`): given a CDMG `G = (J, V, E, L)` and
a subset `W ⊆ J ∪ V` of nodes, the *extended CDMG* `G_{do(I_W)}`
mints a fresh intervention-input node `I_w` for every `w ∈ W \ J`
and adds a directed edge `I_w → w`. The original `V` and `L` are
unchanged, and the LN's convention `I_j := j` for `j ∈ J ∩ W`
means no fresh node / edge is added when `w` is already an input.

Concretely, with carrier `α ⊕ ↑(W \ G.J)`:

```
J_{do(I_W)} := Sum.inl '' G.J ∪ Set.range Sum.inr   -- J ⊔ I_{W\J}
V_{do(I_W)} := Sum.inl '' G.V                       -- V (unchanged)
E_{do(I_W)} := (Sum.inl × Sum.inl) '' G.E
             ∪ { (Sum.inr ⟨w, hw⟩, Sum.inl w) | (w, hw) ∈ W \ G.J }
L_{do(I_W)} := (Sum.inl × Sum.inl) '' G.L           -- L (unchanged)
```

with the convention `Sum.inl v = the original vertex v` and
`Sum.inr ⟨w, _⟩ = the fresh intervention input I_w`.

## Where this gets used downstream

* **claim_3_13** -- `G_{do(I_W)}` inherits acyclicity from `G`; a
  topological order on the extended CDMG is obtained from one on
  `G` by placing each fresh `I_w` immediately before `w`.
* **claim_3_14 / claim_3_15** -- commutation of the extension
  operator with hard intervention and SWIG-style node-splitting
  hard intervention on disjoint sets.
* **Chapters 4 -- 16** -- CBN- and iSCM-level intervention
  machinery whose graph substrate is the extended CDMG.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

-- def_3_13
-- title: ExtendingCDMGsWith
--
-- The *extended CDMG* of `G = (J, V, E, L)` w.r.t. a set of nodes
-- `W ⊆ G.J ∪ G.V`. For every `w ∈ W \ G.J` we mint a fresh
-- intervention-input node `I_w` and add a directed edge
-- `I_w → w`; for `j ∈ G.J ∩ W` the LN's convention `I_j := j`
-- collapses to "no new node, no new edge". `V` and `L` are
-- unchanged. The LN's `\doit(I_W)` subscript is the same operator
-- written infix.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.13) --
the prose paragraph is reflowed for the 100-character line limit
(linewrap only; LaTeX whitespace collapses between tokens, so this is
verbatim under \LaTeX semantics):

\begin{defmark}
\begin{Def}[Extending CDMGs with intervention nodes]\label{def:cdmg_intervention_nodes}
  Let $G=(J,V,E,L)$ be a CDMG and $W \ins J \cup V$ a subset of nodes.
  The \emph{extended CDMG} of $G$ w.r.t.\ nodes $W \ins J \cup V$  and
  corresponding \emph{intervention nodes}
  $I_W = \{I_w \,|\, w \in W\}$ with $I_j:=j$ for $j \in J \cap W$,
  is the CDMG:
  \[ G_{\doit(I_W)}:=(J_{\doit(I_W)},V_{\doit(I_W)},E_{\doit(I_W)},L_{\doit(I_W)}),\]
  where:
  \begin{enumerate}[label=\roman*.)]
      \item $J_{\doit(I_W)}:= J\, \dot{\cup} \, \lC I_w\,|\, w \in W \sm J \rC$,
      \item $V_{\doit(I_W)}:= V$,
      \item $E_{\doit(I_W)}:= E\, \dot{\cup} \, \lC I_w \tuh w \,|\, w \in W\sm J \rC$,
      \item $L_{\doit(I_W)}:= L$,
  \end{enumerate}
  where we just add nodes $I_w$ for $w \in W \sm J$ and edges $I_w \tuh w$ for $ w \in W \sm J$.
\end{Def}
\end{defmark}
-/
--
-- ## Design choice
--
-- * **Carrier `α ⊕ ↑(W \ G.J)` -- not `α ⊕ ↑W`.** LN item i.
--   names the fresh-node *index set* as `W \ J`, not `W`.
--   Subtyping the `Sum.inr` summand by `↑(W \ G.J)` makes the
--   Lean carrier *exactly* the LN's set of fresh nodes: no
--   `Sum.inr ⟨j, _⟩` exists in the carrier for `j ∈ G.J ∩ W`.
--   This encodes the LN's `I_j := j` for `j ∈ G.J ∩ W`
--   convention *at the type level* -- not as a runtime equation
--   on a larger carrier. The alternative `α ⊕ ↑W` would mint a
--   ghost `Sum.inr ⟨j, _⟩` for every `j ∈ G.J ∩ W`, never used
--   in any CDMG field; every downstream rewrite would then have
--   to case-split on `w ∈ G.J` to identify those ghosts with
--   `Sum.inl j` (or carry them as junk through every membership
--   lemma). The sibling `nodeSplittingOn` (def_3_11) uses the
--   unsubtyped `α ⊕ ↑W` template but is restricted to `W ⊆ G.V`,
--   so it has no `J`-overlap to worry about; the stricter
--   subtype here is exactly the cost of the LN's `I_j := j`
--   shorthand. (A more elaborate alternative -- a quotient of
--   `α ⊕ ↑W` collapsing `Sum.inr ⟨j, _⟩ = Sum.inl j` on
--   `G.J ∩ W` -- would lose `DecidableEq` and complicate every
--   downstream lemma; rejected.)
--
-- * **`Sum.inl` / `Sum.inr` encoding.** Constructor-disjoint, so
--   the "no collision" obligations (`disjoint_JV`,
--   `disjoint_EL`, and the source-vs.-target case-split inside
--   `E_subset`) close by `nomatch` on `Sum.inl = Sum.inr`
--   mismatches rather than by hand-rolled case splits. The
--   original carrier `α` is losslessly embedded as
--   `Sum.inl '' α` -- the gateway for stating the `@[simp]`
--   projection lemmas below in LN-style notation
--   (`Sum.inl '' G.J`, `Sum.inl '' G.V`, ...).
--
-- * **Precondition `hW : W ⊆ G.J ∪ G.V`.** Mirrors the LN
--   hypothesis exactly, and is *structurally* needed: the fresh
--   edge `(Sum.inr ⟨w, hw⟩, Sum.inl w)` has target `Sum.inl w`,
--   which must lie in `V_ext = Sum.inl '' G.V`. For
--   `w ∈ W \ G.J`, `hW` gives `w ∈ G.J ∪ G.V`; ruling out
--   `w ∈ G.J` (by `w ∈ W \ G.J`) leaves `w ∈ G.V`. Unlike
--   `hardInterventionOn` (def_3_10), which drops the LN's
--   analogous precondition because the construction stays
--   well-defined for any `W`, here the fresh edge's
--   `E_subset` obligation pins the precondition in place.
--
-- * **`noncomputable`.** The underlying CDMG sets `G.J`, `G.V`,
--   `G.E`, `G.L` are `Set α`, so the `where`-block's images,
--   unions, and ranges are noncomputable. Same reason as
--   `nodeSplittingOn` and `nodeSplittingHardInterventionOn`
--   elsewhere in Section 3.2; no caller ever *evaluates* the
--   construction at runtime (every downstream use is
--   `Prop`-valued), so classical choice in the construction has
--   no observable cost.
--
-- * **`V` and `L` carried verbatim under `Sum.inl × Sum.inl`.**
--   LN items ii. and iv. say `V_{do(I_W)} = V` and
--   `L_{do(I_W)} = L`. The canonical `Sum.inl` lift is the
--   smallest faithful transport: `_V` closes by `rfl`, and `_L`
--   reduces to a clean `Set.mem_image` iff. No special-casing
--   for `w ∈ W` overlap is needed because the extension touches
--   only `J` (new inputs) and `E` (new edges), never `V` or
--   `L`.
--
-- * **Four `@[simp]` projection / membership lemmas.** One per
--   CDMG component, mirroring the `@[simp]` suites on
--   `hardInterventionOn` (def_3_10) and `nodeSplittingOn`
--   (def_3_11) so that downstream proofs in this section have a
--   uniform rewrite vocabulary. The shape choice per lemma:
--     * `_J`, `_V` close by `rfl` -- the `where`-block expresses
--       these components directly. Still `@[simp]` so that
--       callers never have to unfold the `where`-block by hand.
--     * `_E`, `_L` are *membership* iffs (not projection
--       `rfl`s) because the underlying `Set` is a union of an
--       `image` and a `range` (for `E`) or a single `image`
--       (for `L`). The client-friendly form is the LN's
--       disjunctive shape "(original edge) ∨ (fresh edge)" for
--       `E`, and "original bidirected edge under double-`inl`"
--       for `L`, which `simp` reaches after unfolding
--       `Set.mem_union` / `Set.mem_image` / `Set.mem_range`.
--   The load-bearing one downstream is `_E`: claim_3_13 builds
--   a topological order on `G_{do(I_W)}` by pattern-matching on
--   this disjunction -- the original-edge case inherits the
--   inequality from the topological order on `G`, and the
--   fresh-edge case is discharged by inserting each `I_w`
--   immediately before `w`.
--
-- * **Anticipated downstream usage.** claim_3_13 leans on `_E`
--   for topological-order inheritance and acyclicity; claim_3_14
--   / claim_3_15 (commutation with hard intervention / SWIG-style
--   node-splitting hard intervention) rewrite all four
--   membership lemmas against their `hardInterventionOn` /
--   `nodeSplittingHardInterventionOn` counterparts to verify
--   componentwise equality of the composite CDMGs. Chapters
--   4 -- 16 (CBN intervention semantics, do-calculus, iSCMs,
--   identification) compose these same membership lemmas with
--   their measure-theoretic counterparts.
--
-- * **Naming `extendingCDMGWithInterventionNodes`.** Long but
--   unambiguous; matches the row title and the LN's "extending
--   CDMGs with intervention nodes" prose. The LN macro
--   `\doit(I_W)` is convenient infix, but introducing notation
--   now would precede any downstream call site that could
--   motivate the precedence choice; callers write
--   `G.extendingCDMGWithInterventionNodes W hW` explicitly. A
--   later row may add `notation` if the volume of use sites
--   makes the prose form clunky.
--
-- * **Constraints / known limitations.** The precondition
--   `W ⊆ G.J ∪ G.V` must be supplied as a proof term at every
--   downstream call site, whereas the LN treats it as
--   ambient-of-Def context. This matches the in-house pattern
--   for `nodeSplittingOn` (which threads `hW : W ⊆ G.V`) and
--   costs no expressivity. The Lean shape also commits to a
--   concrete identity for the intervention nodes
--   (`Sum.inr ⟨w, _⟩`) rather than treating `I_w` as an opaque
--   symbol; no downstream proof relies on `I_w`'s identity
--   being abstract (they all pattern-match on `Sum.inr`), so
--   this concreteness is a feature, not a leak.

/-- The *extended CDMG* of `G` with respect to a subset of nodes
`W ⊆ G.J ∪ G.V`: a new CDMG over the carrier `α ⊕ ↑(W \ G.J)`
obtained by minting a fresh intervention-input node
`I_w := Sum.inr ⟨w, _⟩` for every `w ∈ W \ G.J` and a fresh
directed edge `I_w → w := (Sum.inr ⟨w, _⟩, Sum.inl w)`. The
original input, output, and bidirected-edge sets are carried
verbatim under the canonical `Sum.inl` embedding -- matching the
LN's convention `I_j := j` for `j ∈ G.J ∩ W` (no fresh node, no
fresh edge for existing inputs). See
`lecture-notes/lecture_notes/graphs.tex` definition
`def:cdmg_intervention_nodes` (def 3.13 of the LN).

The four `@[simp]` projection / membership lemmas
`extendingCDMGWithInterventionNodes_J`,
`extendingCDMGWithInterventionNodes_V`,
`mem_extendingCDMGWithInterventionNodes_E`,
`mem_extendingCDMGWithInterventionNodes_L` below characterise the
four components of the result and are the gateway for every
downstream rewrite. -/
noncomputable def extendingCDMGWithInterventionNodes
    (G : CDMG α) (W : Set α) (hW : W ⊆ G.J ∪ G.V) :
    CDMG (α ⊕ ↑(W \ G.J)) where
  J := Sum.inl '' G.J ∪
    Set.range (Sum.inr : ↑(W \ G.J) → α ⊕ ↑(W \ G.J))
  V := Sum.inl '' G.V
  disjoint_JV := by
    rw [Set.disjoint_left]
    rintro x hxJ ⟨v, hv, rfl⟩
    rcases hxJ with ⟨j, hj, hjv⟩ | ⟨w, hwv⟩
    · cases Sum.inl_injective hjv
      exact Set.disjoint_left.mp G.disjoint_JV hj hv
    · exact nomatch hwv
  E := (fun p : α × α => ((Sum.inl p.1 : α ⊕ ↑(W \ G.J)), Sum.inl p.2)) '' G.E
     ∪ Set.range (fun w : ↑(W \ G.J) =>
         ((Sum.inr w : α ⊕ ↑(W \ G.J)), Sum.inl (w : α)))
  E_subset := by
    rintro ⟨a, b⟩ h
    rcases h with ⟨⟨v₁, v₂⟩, hE, hab⟩ | ⟨w, hab⟩
    · -- piece 1: original directed edge (v₁, v₂) ∈ G.E, double-inl-lifted.
      simp only [Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      obtain ⟨hv₁, hv₂⟩ := G.E_subset hE
      refine ⟨?_, ?_⟩
      · -- source Sum.inl v₁ ∈ J_ext ∪ V_ext
        rcases hv₁ with hJ | hV
        · exact Or.inl (Or.inl ⟨v₁, hJ, rfl⟩)
        · exact Or.inr ⟨v₁, hV, rfl⟩
      · -- target Sum.inl v₂ ∈ V_ext
        exact ⟨v₂, hv₂, rfl⟩
    · -- piece 2: fresh edge (Sum.inr w, Sum.inl w.val) for w ∈ ↑(W \ G.J).
      simp only [Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      refine ⟨?_, ?_⟩
      · -- source Sum.inr w ∈ J_ext (the range-of-inr summand)
        exact Or.inl (Or.inr ⟨w, rfl⟩)
      · -- target Sum.inl w.val ∈ V_ext = Sum.inl '' G.V.
        -- w.property : (w : α) ∈ W \ G.J, so (w : α) ∈ W, (w : α) ∉ G.J;
        -- by hW, (w : α) ∈ G.J ∪ G.V; ruling out G.J leaves G.V.
        have hwW : (w : α) ∈ W := w.property.1
        have hwJ : (w : α) ∉ G.J := w.property.2
        rcases hW hwW with hJ | hV
        · exact absurd hJ hwJ
        · exact ⟨(w : α), hV, rfl⟩
  L := (fun p : α × α => ((Sum.inl p.1 : α ⊕ ↑(W \ G.J)), Sum.inl p.2)) '' G.L
  L_subset := by
    rintro ⟨a, b⟩ ⟨⟨v₁, v₂⟩, hL, hab⟩
    simp only [Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    obtain ⟨hv₁V, hv₂V⟩ := G.L_subset hL
    exact ⟨⟨v₁, hv₁V, rfl⟩, ⟨v₂, hv₂V, rfl⟩⟩
  L_irrefl := by
    rintro a₁ a₂ ⟨⟨v₁, v₂⟩, hL, hab⟩
    simp only [Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    intro heq
    exact G.L_irrefl hL (Sum.inl_injective heq)
  L_symm := by
    rintro a₁ a₂ ⟨⟨v₁, v₂⟩, hL, hab⟩
    refine ⟨(v₂, v₁), G.L_symm hL, ?_⟩
    simp only [Prod.mk.injEq] at hab ⊢
    exact ⟨hab.2, hab.1⟩
  disjoint_EL := by
    rw [Set.disjoint_left]
    rintro p hE ⟨⟨u₁, u₂⟩, huL, rfl⟩
    rcases hE with ⟨⟨v₁, v₂⟩, hvE, hvb⟩ | ⟨w, hvb⟩
    · -- piece 1 of E meets L: both p sides are (Sum.inl _, Sum.inl _),
      -- so Sum.inl-injectivity descends to (v₁, v₂) = (u₁, u₂) ∈ G.E ∩ G.L.
      simp only [Prod.mk.injEq] at hvb
      obtain ⟨h1, h2⟩ := hvb
      cases Sum.inl_injective h1
      cases Sum.inl_injective h2
      exact Set.disjoint_left.mp G.disjoint_EL hvE huL
    · -- piece 2 of E vs L: source Sum.inr w cannot equal Sum.inl u₁
      -- (constructor mismatch).
      simp only [Prod.mk.injEq] at hvb
      exact nomatch hvb.1

/-! ## `@[simp]` projection / membership lemmas

These four lemmas characterise the four CDMG components of
`extendingCDMGWithInterventionNodes` in terms of `G.J`, `G.V`,
`G.E`, `G.L` and `W`. Marked `@[simp]` so that a single `simp` call
inside a downstream proof reduces `(G.extendingCDMGWithInterventionNodes
W hW).{J, V, E, L}` to the LN's set-builder form without needing the
internal `where`-block to surface. Mirror the `@[simp]` lemma suite
attached to `nodeSplittingOn` and `hardInterventionOn`. -/

/-- The *input* nodes of `G.extendingCDMGWithInterventionNodes W hW`
are `Sum.inl '' G.J ∪ Set.range Sum.inr` -- the original inputs
embedded via `Sum.inl` together with one fresh `Sum.inr`-labeled
intervention input per element of `W \ G.J`. Matches the LN's
`J_{do(I_W)} = J ⊔ {I_w | w ∈ W \ J}` (def 3.13 item i.) under the
identification `α ≅ Sum.inl '' α`. Note the disjoint-union shape
follows from the `Sum.inl` / `Sum.inr` constructor disjointness --
no `Sum.inr ⟨j, _⟩` exists for `j ∈ G.J ∩ W` in the first place
(carrier-level encoding of `I_j := j`; see the design block). Used
by claim_3_13 (the topological order on `G_{do(I_W)}` must range
over `J_{do(I_W)}`) and claim_3_14 / claim_3_15 (input set of the
composite with hard intervention / SWIG). By definition. -/
@[simp] theorem extendingCDMGWithInterventionNodes_J
    (G : CDMG α) (W : Set α) (hW : W ⊆ G.J ∪ G.V) :
    (G.extendingCDMGWithInterventionNodes W hW).J =
      Sum.inl '' G.J ∪
        Set.range (Sum.inr : ↑(W \ G.J) → α ⊕ ↑(W \ G.J)) := rfl

/-- The *output* nodes of `G.extendingCDMGWithInterventionNodes W hW`
are `Sum.inl '' G.V` -- the original outputs carried verbatim
under the canonical `Sum.inl` embedding. Matches the LN's
`V_{do(I_W)} = V` (def 3.13 item ii.): the extension only adds
input nodes (`I_w`), never output nodes, so `V_ext = V` modulo
the carrier shift. Used by claim_3_13 (output set of the
extended CDMG) and claim_3_14 / claim_3_15 (output-set equality
of the composite operators reduces to a `Sum.inl ''`-image
equality). By definition. -/
@[simp] theorem extendingCDMGWithInterventionNodes_V
    (G : CDMG α) (W : Set α) (hW : W ⊆ G.J ∪ G.V) :
    (G.extendingCDMGWithInterventionNodes W hW).V = Sum.inl '' G.V := rfl

/-- *Directed-edge* membership in
`G.extendingCDMGWithInterventionNodes W hW`: a pair `p` is a
directed edge of the extended CDMG iff *either* it is the
double-`inl` lift `(Sum.inl v₁, Sum.inl v₂)` of some original edge
`(v₁, v₂) ∈ G.E`, *or* it is a fresh intervention edge
`(Sum.inr w, Sum.inl (w : α))` for some `w : ↑(W \ G.J)`. Matches
def 3.13 item iii.: `E_{do(I_W)} = E ⊔ {I_w → w | w ∈ W \ J}`.
The two disjuncts are disjoint at the type level -- their source
is `Sum.inl _` vs. `Sum.inr _` -- so case-splitting on them is
free. Load-bearing for downstream: claim_3_13 builds the
topological order on `G_{do(I_W)}` by pattern-matching on this
disjunction (inherit `<` from `G` on the original-edge case;
place each `I_w` immediately before `w` on the fresh-edge case).
claim_3_14 / claim_3_15 use the same disjunction to compute the
edge-set of the composite with hard intervention / SWIG. -/
@[simp] theorem mem_extendingCDMGWithInterventionNodes_E
    (G : CDMG α) (W : Set α) (hW : W ⊆ G.J ∪ G.V)
    {p : (α ⊕ ↑(W \ G.J)) × (α ⊕ ↑(W \ G.J))} :
    p ∈ (G.extendingCDMGWithInterventionNodes W hW).E ↔
      (∃ v₁ v₂, (v₁, v₂) ∈ G.E ∧ p = (Sum.inl v₁, Sum.inl v₂)) ∨
      (∃ w : ↑(W \ G.J), p = (Sum.inr w, Sum.inl (w : α))) := by
  change p ∈ (fun q : α × α =>
           ((Sum.inl q.1 : α ⊕ ↑(W \ G.J)), Sum.inl q.2)) '' G.E
       ∪ Set.range (fun w : ↑(W \ G.J) =>
           ((Sum.inr w : α ⊕ ↑(W \ G.J)), Sum.inl (w : α))) ↔ _
  simp only [Set.mem_union, Set.mem_image, Set.mem_range, Prod.exists]
  refine or_congr ?_ ?_
  · constructor
    · rintro ⟨v₁, v₂, hE, h⟩
      exact ⟨v₁, v₂, hE, h.symm⟩
    · rintro ⟨v₁, v₂, hE, rfl⟩
      exact ⟨v₁, v₂, hE, rfl⟩
  · constructor
    · rintro ⟨w, h⟩
      exact ⟨w, h.symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, rfl⟩

/-- *Bidirected-edge* membership in
`G.extendingCDMGWithInterventionNodes W hW`: a pair `p` is a
bidirected edge of the extended CDMG iff it is the double-`inl`
lift `(Sum.inl v₁, Sum.inl v₂)` of some original bidirected edge
`(v₁, v₂) ∈ G.L`. Matches def 3.13 item iv.: `L_{do(I_W)} = L` --
the extension never adds bidirected edges (the fresh `I_w → w`
edges are *directed*), so `L_ext = L` modulo the carrier shift.
Used by claim_3_14 / claim_3_15 to verify that the
bidirected-edge sets of the composite operators agree (both
sides reduce to a `Sum.inl × Sum.inl` image of `G.L`). -/
@[simp] theorem mem_extendingCDMGWithInterventionNodes_L
    (G : CDMG α) (W : Set α) (hW : W ⊆ G.J ∪ G.V)
    {p : (α ⊕ ↑(W \ G.J)) × (α ⊕ ↑(W \ G.J))} :
    p ∈ (G.extendingCDMGWithInterventionNodes W hW).L ↔
      ∃ v₁ v₂, (v₁, v₂) ∈ G.L ∧ p = (Sum.inl v₁, Sum.inl v₂) := by
  change p ∈ (fun q : α × α =>
           ((Sum.inl q.1 : α ⊕ ↑(W \ G.J)), Sum.inl q.2)) '' G.L ↔ _
  simp only [Set.mem_image, Prod.exists]
  constructor
  · rintro ⟨v₁, v₂, hL, h⟩
    exact ⟨v₁, v₂, hL, h.symm⟩
  · rintro ⟨v₁, v₂, hL, rfl⟩
    exact ⟨v₁, v₂, hL, rfl⟩

end CDMG

end Causality
