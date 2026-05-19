import Chapter3_GraphTheory.Section3_1.CDMGNotation

-- The verbatim TeX source of the LN definition is reproduced inside the
-- comments below. Disable the style linter for this file so the TeX is
-- kept byte-for-byte identical to `Section3_1/main.tex`.
set_option linter.style.longLine false

/-!
# def_3_3 — Adjacency, "into", and "out of"

The third LN definition of subsection 3.1 bundles three concepts under one
`\begin{Def}` block: adjacency between two nodes, and two ways of
classifying an edge by which endpoint its arrowhead points to ("into")
versus where its tail sits ("out of"). We produce one Lean declaration per
LN bullet point, sharing the `Causality.Chapter3` namespace with
`def_3_1` and `def_3_2`.
-/

namespace Causality
namespace Chapter3

variable {J V : Type*}

/-
Source (verbatim from `Section3_1/main.tex`, under `% def_3_3`):

\begin{defmark}
\begin{Def}
  Let $G=(J,V,E,L)$ be a CDMG.
  \begin{enumerate}
    \item If $v_1 \sus v_2 \in G$ then we call $v_1$ and $v_2$ \emph{adjacent in $G$}.
    \item Edges of the form $v_1 \hut v_2$ or $v_1 \huh v_2$ are called \emph{into $v_1$}.  \\
          Edges of the form $v_1 \tuh v_2$ or $v_1 \huh v_2$ are called \emph{into $v_2$}.
    \item Edges of the form $v_1 \tuh v_2$ or $v_2 \hut v_1$ are called \emph{out of $v_1$}.
  \end{enumerate}
\end{Def}
\end{defmark}
-/

-- def_3_3 (part 1/3) — Adjacency.
--
-- Two nodes `v₁` and `v₂` of `G` are *adjacent in `G`* iff there is some
-- edge between them, in any of the three primitive forms (`\tuh`, `\hut`,
-- `\huh`). That is exactly `G.sus` from `def_3_2`.
--
-- LN fragment:
-- /- If `v₁ \sus v₂ ∈ G` then we call `v₁` and `v₂` *adjacent in `G`*. -/
--
-- Design choice: this is a direct rename of `CDMG.sus`. We keep both names
-- because the LN uses "adjacent" as the noun-level concept (and downstream
-- statements like claim_3_1's "no two nodes in `J` are adjacent" name it
-- as such), while `\sus` is the lower-level edge notation. Using `def` (not
-- `abbrev`) keeps the abstraction one step removed, so unfolding only
-- happens when we ask for it. Symmetry of `Adjacent` is *not* claimed by
-- the LN here (it follows from properties of `sus`), so we do not prove it
-- — that's the job of whoever needs it.
def CDMG.Adjacent (G : CDMG J V) (v₁ v₂ : J ⊕ V) : Prop :=
  G.sus v₁ v₂

-- def_3_3 (part 2/3a) — "Into the first endpoint".
--
-- An edge `v₁ \hut v₂` or `v₁ \huh v₂` is *into `v₁`* because, in both
-- cases, the arrowhead sits on `v₁`. We package this as a predicate on
-- the pair `(v₁, v₂)` saying "the edge between these endpoints, in either
-- of those two forms, is into `v₁`".
--
-- LN fragment:
-- /- Edges of the form `v₁ \hut v₂` or `v₁ \huh v₂` are called *into `v₁`*. -/
--
-- Design choice — typing.
-- `\hut v₁ v₂` requires `v₁ : V` and `v₂ : J ⊕ V` (the arrowhead-end is in
-- `V` because `E ⊆ (J ∪ V) × V`); `\huh v₁ v₂` requires both endpoints in
-- `V`. The *focal* endpoint `v₁` is the arrowhead-end in both disjuncts, so
-- it lives in `V`. The *other* endpoint `v₂` is more permissive: it can
-- be in `J` (for the `\hut` case), so we take `v₂ : J ⊕ V` and lift the
-- `\huh` disjunct via a `Sum.inr` existential — exactly the pattern used
-- for `hus` / `suh` in `CDMGNotation.lean`. This typing makes
-- `IntoFst v₁ v₂` directly composable with `def_3_4`'s walks, which
-- carry endpoints in `J ⊕ V`.
def CDMG.IntoFst (G : CDMG J V) (v₁ : V) (v₂ : J ⊕ V) : Prop :=
  G.hut v₁ v₂ ∨ ∃ w₂ : V, v₂ = Sum.inr w₂ ∧ G.huh v₁ w₂

-- def_3_3 (part 2/3b) — "Into the second endpoint".
--
-- An edge `v₁ \tuh v₂` or `v₁ \huh v₂` is *into `v₂`* because the
-- arrowhead sits on `v₂` in both cases. Symmetric to `IntoFst`.
--
-- LN fragment:
-- /- Edges of the form `v₁ \tuh v₂` or `v₁ \huh v₂` are called *into `v₂`*. -/
--
-- Design choice — typing.
-- Mirror of `IntoFst`: the focal endpoint `v₂` is in `V` (both `\tuh` and
-- `\huh` have their arrowhead-end in `V`), while the other endpoint `v₁`
-- is in `J ⊕ V` with a `Sum.inr` existential lifting the `\huh` disjunct.
def CDMG.IntoSnd (G : CDMG J V) (v₁ : J ⊕ V) (v₂ : V) : Prop :=
  G.tuh v₁ v₂ ∨ ∃ w₁ : V, v₁ = Sum.inr w₁ ∧ G.huh w₁ v₂

-- def_3_3 (part 3/3) — "Out of `v₁`".
--
-- An edge `v₁ \tuh v₂` or `v₂ \hut v₁` is *out of `v₁`* because its tail
-- sits on `v₁` (equivalently: the arrowhead sits on `v₂`).
--
-- LN fragment:
-- /- Edges of the form `v₁ \tuh v₂` or `v₂ \hut v₁` are called *out of `v₁`*. -/
--
-- Design choice — typing.
-- The LN allows the *tail-end* `v₁` to be any node of `G`, i.e. in
-- `J ∪ V = J ⊕ V`: this is precisely the freedom that `\tuh` and `\hut`
-- provide on their non-`V` side (since `E ⊆ (J ∪ V) × V`). We therefore
-- type `v₁ : J ⊕ V` and `v₂ : V`. The arrowhead-end `v₂` lives in `V`
-- because the codomain of `E` is `V`, in both disjuncts.
--
-- Note on apparent redundancy. By unfolding `def_3_2`, the two disjuncts
-- are *definitionally equal*: `G.tuh v₁ v₂ = (v₁, v₂) ∈ G.E` and
-- `G.hut v₂ v₁ = (v₁, v₂) ∈ G.E`. We still write the disjunction (rather
-- than collapsing to a single membership) to mirror the LN's exact
-- phrasing — a downstream `Or.inl` / `Or.inr` introduction matches the LN
-- prose directly, and is the form `def_3_4` uses when classifying walk
-- ends.
def CDMG.OutOf (G : CDMG J V) (v₁ : J ⊕ V) (v₂ : V) : Prop :=
  G.tuh v₁ v₂ ∨ G.hut v₂ v₁

end Chapter3
end Causality
