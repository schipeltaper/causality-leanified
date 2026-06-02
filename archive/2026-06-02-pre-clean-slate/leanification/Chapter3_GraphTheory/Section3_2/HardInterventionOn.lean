import Chapter3_GraphTheory.Section3_1.CDMGNotation

/-!
# Hard intervention on a CDMG (def 3.10)

This file formalises *definition 3.10* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`): given a
CDMG `G = (J, V, E, L)` and a subset of nodes `W`, the *hard
intervention* of `G` w.r.t. `W` is a new CDMG `G_{do(W)} =
(J_{do(W)}, V_{do(W)}, E_{do(W)}, L_{do(W)})` obtained by

  * promoting every vertex of `W` from an output to an input,
  * removing every directed edge into a vertex of `W`,
  * removing every bidirected edge incident to a vertex of `W`.

Concretely:

```
J_{do(W)} := J ∪ W
V_{do(W)} := V \ W
E_{do(W)} := E \ { (v, w) | w ∈ W }
L_{do(W)} := L \ { (v₁, v₂) | v₁ ∈ W ∨ v₂ ∈ W }
```

This is the foundational operation of Section 3.2; nearly every
later intervention statement and identification result in
chapters 4 -- 16 quotes it.

## Where this gets used downstream

* **claim_3_3** (`graphs.tex` Rem 311) -- "if `G` is acyclic then
  also `G_{do(W)}` is acyclic, and a topological order for `G` is
  also one for `G_{do(W)}`". Builds directly on the `@[simp]`
  membership lemmas `mem_hardInterventionOn_E` / `_L` below to
  track edge preservation under the deletion.
* **claim_3_4** (`graphs.tex` Lem 317, "hard interventions
  commute") -- `(G_{do(W₁)})_{do(W₂)} = (G_{do(W₂)})_{do(W₁)} =
  G_{do(W₁ ∪ W₂)}`. Iteration -- applying `hardInterventionOn` to
  the *result* of a previous `hardInterventionOn` call -- is the
  load-bearing compositional test; see the design note about the
  absence of a `W ⊆ G.J ∪ G.V` precondition.
* **claim_3_5** (`graphs.tex` Prp 360) -- bifurcations
  characterised via `Anc^{G_{do(w)}}(v)` for a single-vertex
  intervention.
* **claim_3_8 / claim_3_11** -- disjoint hard interventions.
* **claim_3_12** -- composition with `NodeSplittingOn`.
* **def_3_13** -- extending CDMGs with intervention nodes.
* **Chapters 4 -- 16** -- CBNs, do-calculus, iSCMs, identification,
  and discovery all compose `G_{do(W)}` with the rest of their
  machinery; the membership simp lemmas below are the gateway.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

-- def_3_10
-- title: HardInterventionOn
--
-- The *hard intervention* of `G` with respect to a set `W` of
-- nodes replaces `G = (J, V, E, L)` by `(J ∪ W, V \ W, E \ ...,
-- L \ ...)`, turning every vertex of `W` into an input node and
-- stripping out every edge with an endpoint in `W` (every
-- directed edge *into* `W` and every bidirected edge *incident
-- to* `W`). The LN's `\doit(W)` subscript is the same operator
-- written infix.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.10):

\begin{defmark}
\begin{Def}[Hard intervention on CDMGs]\label{def:G_hard_intervention}
    Let $G=(J,V,E,L)$ be a CDMG and $W \ins J \cup V$ a subset of nodes.
  The \emph{intervened CDMG} w.r.t.\ $W$ of $G$ is the CDMG:
  \[ G_{\doit(W)}:=(J_{\doit(W)},V_{\doit(W)},E_{\doit(W)},L_{\doit(W)}),\]
  where:
  \begin{enumerate}[label=\roman*.)]
      \item $J_{\doit(W)}:= J \cup W$,
      \item $V_{\doit(W)}:= V \sm W$,
      \item $E_{\doit(W)}:= E \sm \lC v \tuh w \,|\, v \in G, w  \in W  \rC$,
      \item $L_{\doit(W)}:= L \sm \lC v \huh w\,|\, v \in G, w \in W \rC$,
  \end{enumerate}
  where we turn all nodes from $W$ into input nodes and remove all edges into nodes from $W$.
\end{Def}
\end{defmark}
-/
--
-- ## Design choice
--
-- * **No `W ⊆ G.J ∪ G.V` precondition.** The LN literally writes
--   "let `W ⊆ J ∪ V`", but the formulas for the four components
--   `J_{do(W)}`, `V_{do(W)}`, `E_{do(W)}`, `L_{do(W)}` are
--   well-defined for *any* `W : Set α`: a vertex in
--   `W \ (G.J ∪ G.V)` simply gets added to the input set
--   `G.J ∪ W` without affecting any edges (none of `G.E` / `G.L`
--   touch such a vertex by `G.E_subset` / `G.L_subset`), and
--   `G.V \ W` collapses to `G.V \ (W ∩ G.V)` -- the same set we
--   would get from the LN's restricted `W`. Choosing *no*
--   precondition has two concrete payoffs:
--
--     1. **Iteration works unconditionally** (claim_3_4). The
--        outer call in `(G_{do(W₁)})_{do(W₂)}` would otherwise
--        need a hypothesis `W₂ ⊆ (G_{do(W₁)}).J ∪
--        (G_{do(W₁)}).V`. The LN's prose for claim_3_4 -- "let
--        `W₁, W₂ ⊆ J ∪ V`" -- states the precondition only for
--        the *base* graph `G`, never re-proves it for the inner
--        intervention, and quietly relies on `(W₁ ∪ W₂) ⊆ J ∪ V`
--        on the RHS. Dropping the precondition matches that
--        informal usage exactly.
--     2. **Every caller is one hypothesis shorter.** Downstream
--        uses (claim_3_5 with a single vertex `w`, claim_3_8 /
--        3_11 with disjoint `W₁, W₂`, the chapter 4 -- 16
--        do-calculus and identification machinery) never need to
--        thread the `W ⊆ G` hypothesis through their statements.
--
--   The trade-off: a user who passes a `W` *not* contained in
--   `G.J ∪ G.V` gets a CDMG that disagrees with the LN's prose
--   on the spurious vertices in `W \ (G.J ∪ G.V)` (they show up
--   as input nodes). The membership simp lemmas below make this
--   precise. In practice every claim that *reasons* about
--   `G_{do(W)}` adds `W ⊆ G.J ∪ G.V` (or a stronger form) at the
--   *claim* level, not at the *definition* level -- exactly as
--   the LN does.
--
-- * **`L_{do(W)}` removes pairs with *either* endpoint in `W`,
--   not just the second endpoint.** The LN writes
--   `L \ {v ↔ w | v ∈ G, w ∈ W}`, where `↔` is the *unordered*
--   bidirected-edge relation. In Lean we encode bidirected edges
--   as a `Set (α × α)` of ordered pairs together with a
--   symmetry field (`CDMG.L_symm`, def_3_1). A literal port
--   `L \ { (v, w) | w ∈ W }` would remove only one of each
--   symmetric pair: if `(a, b) ∈ G.L` with `a ∉ W` and `b ∈ W`,
--   the pair `(a, b)` would be deleted but its symmetric
--   partner `(b, a)` would survive -- and then `L_{do(W)}` would
--   no longer satisfy `L_symm`, breaking the very next field's
--   obligation when reassembling the intervened CDMG. The LN's
--   prose immediately after the four bullets -- "we ... remove
--   all edges into nodes from `W`" -- combined with the
--   unordered reading of `↔` makes the intended semantics
--   unambiguous: remove every bidirected edge with *any*
--   endpoint in `W`. We encode this as
--   `L \ { (v₁, v₂) | v₁ ∈ W ∨ v₂ ∈ W }`, which is
--   `L_symm`-preserving and equivalent to the LN's set
--   difference modulo the unordered convention.
--
-- * **Drop the `v ∈ G` clause from `E_{do(W)}`.** The LN writes
--   `E \ { v → w | v ∈ G, w ∈ W }`, but every directed edge
--   `(v, w) ∈ G.E` already satisfies `v ∈ G.J ∪ G.V = G` by
--   `G.E_subset`, so the `v ∈ G` clause is redundant on the set
--   being removed: the two formulations
--   `E \ { (v, w) | v ∈ G ∧ w ∈ W }` and `E \ { (v, w) | w ∈ W }`
--   are equal as subsets of `G.E`. We encode the cleaner second
--   form `G.E \ { p | p.2 ∈ W }`. The LN's claim_3_4 proof
--   itself drops the `v ∈ G` clause when computing
--   `E_{(G_{do(W₁)})_{do(W₂)}}`, so our simplification matches
--   the LN's working-out style. The bidirected case keeps the
--   `v₁ ∈ W ∨ v₂ ∈ W` disjunction (rather than `p.2 ∈ W`) for
--   the symmetry reason above.
--
-- * **Name `hardInterventionOn`, dot-projection
--   `G.hardInterventionOn W`.** The row title is
--   `HardInterventionOn` and the LN macro is `\doit(W)`; the
--   Lean identifier we choose has to be searchable and
--   pronounceable. `hardInterventionOn` reads as the prose name;
--   the dot-notation `G.hardInterventionOn W` lines up with the
--   LN's `G_{do(W)}` / "the hard intervention of `G` on `W`"
--   phrasing. CamelCase matches Mathlib's convention for
--   definitions taking arguments (`Set.image`, `Finset.filter`,
--   ...).
--
-- * **No new notation at this row.** The LN macro `\doit(W)` /
--   subscript `G_{do(W)}` is convenient mathematically but
--   introducing it now would create a notational dependency
--   before any downstream proof exists to motivate the precise
--   token / precedence choice. Callers in claim_3_3 / claim_3_4
--   will write `G.hardInterventionOn W` explicitly; a later row
--   (e.g. one introduced specifically for `\doit` notation) can
--   add `notation` syntax if the volume of use cases makes the
--   prose form clunky. Keeping notation out of this row keeps
--   the definition trivially usable from any file without
--   needing `open scoped`.
--
-- * **Structural fields discharged in-place.** The seven CDMG
--   obligations (`disjoint_JV`, `E_subset`, `L_subset`,
--   `L_irrefl`, `L_symm`, `disjoint_EL`) are each a one- to
--   three-line consequence of the corresponding `G.*` field
--   plus a set-membership manipulation:
--
--     * `disjoint_JV` -- a vertex in `(G.J ∪ W) ∩ (G.V \ W)` is
--       either in `G.J ∩ (G.V \ W) ⊆ G.J ∩ G.V` (vacuous by
--       `G.disjoint_JV`) or in `W ∩ (G.V \ W)` (vacuous by `\`).
--     * `E_subset` -- a directed edge `(v, w)` of `E_{do(W)}`
--       has `(v, w) ∈ G.E`, so `w ∈ G.V` and `w ∉ W` give
--       `w ∈ G.V \ W`; the source `v` is in `G.J ∪ G.V`, which
--       is contained in `(G.J ∪ W) ∪ (G.V \ W)` by a three-case
--       split on `v` (`v ∈ G.J`, or `v ∈ G.V ∩ W`, or
--       `v ∈ G.V \ W`).
--     * `L_subset` -- both endpoints of a surviving bidirected
--       edge are in `G.V` (by `G.L_subset`) and `∉ W` (by the
--       set-difference deletion), so in `G.V \ W`.
--     * `L_irrefl`, `disjoint_EL` -- monotone in `G.L` /
--       `G.E` / `G.L`; the deletions only shrink each set, so
--       the original irreflexivity / disjointness lift
--       directly.
--     * `L_symm` -- our both-endpoints removal makes the
--       deleted set itself symmetric in `(v₁, v₂)`, so
--       symmetry of `G.L` lifts to `L_{do(W)}` exactly. This
--       is the field that the design choice on `L_{do(W)}`
--       above is engineered to satisfy.
--
--   Discharging the seven fields here (rather than via a helper
--   lemma) keeps the proof obligations colocated with the
--   construction, matching the Mathlib house style for
--   one-shot structure builders.

/-- The *hard intervention* of the CDMG `G` with respect to a set
of nodes `W ⊆ α`: the new CDMG `G_{do(W)}` obtained by promoting
every vertex of `W` to an input node, removing every directed
edge whose *target* lies in `W`, and removing every bidirected
edge incident to *any* vertex of `W`. See
`lecture-notes/lecture_notes/graphs.tex` definition
`def:G_hard_intervention` (def 3.10 of the LN).

This is intentionally well-defined for *every* `W : Set α`, with
no `W ⊆ G.J ∪ G.V` precondition -- see the design note above for
why (the iterated form `(G.hardInterventionOn W₁).hardInterventionOn
W₂` of claim_3_4 needs this generality). The four `@[simp]` lemmas
`hardInterventionOn_J`, `hardInterventionOn_V`,
`mem_hardInterventionOn_E`, `mem_hardInterventionOn_L` below
characterise the four components of the result. -/
def hardInterventionOn (G : CDMG α) (W : Set α) : CDMG α where
  J := G.J ∪ W
  V := G.V \ W
  disjoint_JV := by
    rw [Set.disjoint_left]
    rintro x (hJ | hW) ⟨hV, hnW⟩
    · exact Set.disjoint_left.mp G.disjoint_JV hJ hV
    · exact hnW hW
  E := G.E \ { p : α × α | p.2 ∈ W }
  E_subset := by
    rintro ⟨v, w⟩ ⟨hE, hnW⟩
    obtain ⟨hv, hw⟩ := G.E_subset hE
    refine ⟨?_, hw, hnW⟩
    rcases hv with hJ | hV
    · exact Or.inl (Or.inl hJ)
    · by_cases hW : v ∈ W
      · exact Or.inl (Or.inr hW)
      · exact Or.inr ⟨hV, hW⟩
  L := G.L \ { p : α × α | p.1 ∈ W ∨ p.2 ∈ W }
  L_subset := by
    rintro ⟨v₁, v₂⟩ ⟨hL, hnW⟩
    obtain ⟨h1, h2⟩ := G.L_subset hL
    exact ⟨⟨h1, fun hW => hnW (Or.inl hW)⟩, ⟨h2, fun hW => hnW (Or.inr hW)⟩⟩
  L_irrefl := by
    intro v₁ v₂ h
    exact G.L_irrefl h.1
  L_symm := by
    intro v₁ v₂ h
    exact ⟨G.L_symm h.1, fun hh => h.2 hh.symm⟩
  disjoint_EL := by
    rw [Set.disjoint_left]
    rintro p ⟨hE, _⟩ ⟨hL, _⟩
    exact Set.disjoint_left.mp G.disjoint_EL hE hL

/-- The *input* nodes of the hard intervention `G.hardInterventionOn
W` are exactly `G.J ∪ W` -- promotion of every vertex of `W` to an
input. By definition. -/
@[simp] theorem hardInterventionOn_J (G : CDMG α) (W : Set α) :
    (G.hardInterventionOn W).J = G.J ∪ W := rfl

/-- The *output* nodes of the hard intervention
`G.hardInterventionOn W` are exactly `G.V \ W` -- removal of every
vertex of `W` from the output set. By definition. -/
@[simp] theorem hardInterventionOn_V (G : CDMG α) (W : Set α) :
    (G.hardInterventionOn W).V = G.V \ W := rfl

/-- *Directed-edge* membership in the hard intervention: a pair
`p = (v, w)` is a directed edge of `G.hardInterventionOn W` iff
it is a directed edge of `G` and its target `w = p.2` is not in
`W`. The `v ∈ G` clause of the LN's literal set-builder is
dropped -- it is redundant given `G.E_subset` (see the file's
design notes). Holds by `Iff.rfl`. -/
@[simp] theorem mem_hardInterventionOn_E
    (G : CDMG α) (W : Set α) {p : α × α} :
    p ∈ (G.hardInterventionOn W).E ↔ p ∈ G.E ∧ p.2 ∉ W := Iff.rfl

/-- *Bidirected-edge* membership in the hard intervention: a
pair `p = (v₁, v₂)` is a bidirected edge of
`G.hardInterventionOn W` iff it is a bidirected edge of `G` and
*neither* endpoint is in `W`. The both-endpoints exclusion is
the LN's "remove all edges into nodes from `W`" prose, encoded
so that the symmetry field `L_symm` survives the intervention
(see the file's design notes for why a single-endpoint exclusion
would break symmetry). -/
@[simp] theorem mem_hardInterventionOn_L
    (G : CDMG α) (W : Set α) {p : α × α} :
    p ∈ (G.hardInterventionOn W).L ↔ p ∈ G.L ∧ p.1 ∉ W ∧ p.2 ∉ W := by
  change p ∈ G.L \ _ ↔ _
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_or]

end CDMG

end Causality
