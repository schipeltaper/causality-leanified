import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Basic

-- The verbatim TeX source of the LN definition is reproduced inside the
-- comments below; some of its lines exceed 100 characters. Disable the
-- style linter for this file so the TeX is kept byte-for-byte identical
-- to `Section3_1/main.tex`.
set_option linter.style.longLine false

/-!
# def_3_8 — Topological order

The eighth LN definition of subsection 3.1 introduces *topological orders*
of a CDMG: a total order on the union of input and output nodes such that
every parent precedes every one of its children. The notion is the bridge
between `def_3_6` (acyclicity) and `claim_3_2` ("a CDMG is acyclic iff it
admits a topological order").

We share the `Causality.Chapter3` namespace with `def_3_1`–`def_3_7`.
-/

namespace Causality
namespace Chapter3

variable {J V : Type*}

/-
Source (verbatim from `Section3_1/main.tex`, under `% def_3_8`):

\begin{defmark}
\begin{Def}[Topological order]
    Let $G=(J,V,E,L)$ be a CDMG.
    A \emph{topological order} of $G$ is a total order $<$ of $J \cup V$ such that for all $v,w \in G$:
    \[ v \in \Pa^G(w) \; \implies \; v < w.\]
    Equivalently, it can be described as an indexing of the nodes $J \cup V = \{v_1,\dots,v_K\}$ where parents always precede their children.
\end{Def}
\end{defmark}
-/

-- def_3_8 — topological order of a CDMG.
--
-- LN fragment:
-- /- A *topological order* of `G = (J, V, E, L)` is a total order `<`
--    of `J ∪ V` such that for all `v, w ∈ G`,
--    `v ∈ Pa^G(w) ⟹ v < w`. -/
--
-- A `G.TopologicalOrder` packages a `LinearOrder` on `J ⊕ V` together with
-- the parent-precedes-child axiom. Existence of such a structure
-- (`∃ _ : G.TopologicalOrder, True`, or just `Nonempty G.TopologicalOrder`)
-- is the statement "`G` admits a topological order" used by `claim_3_2`.
--
-- Design choice — bundled `structure`, not a `Prop` parameterized by an
-- ambient `LinearOrder`. We want the next row (`claim_3_2`) to say
-- "a CDMG is acyclic iff it has a topological order" — i.e. an existence
-- statement over orders. Bundling the `LinearOrder` as data inside
-- `TopologicalOrder G` lets that read as `Nonempty G.TopologicalOrder`,
-- with no need to thread a `LinearOrder (J ⊕ V)` instance through the
-- statement. A `Prop`-shaped alternative
-- `def TopologicalOrder (G) (lo : LinearOrder _) : Prop := …` would force
-- `claim_3_2` to existentially quantify over `lo : LinearOrder (J ⊕ V)`
-- separately, which adds clutter to every downstream use.
--
-- Design choice — `J ∪ V = J ⊕ V`. Per `def_3_1` the input and output
-- vertex sets are two type parameters `J V : Type*`, and the LN's
-- "`J ∪ V`" is realised as the disjoint sum type `J ⊕ V` (matching every
-- other definition in this section: `Walk`, `Pa`, `IsAcyclic`, etc.).
--
-- Design choice — `LinearOrder (J ⊕ V)`, not the bare strict
-- `IsStrictTotalOrder` / a hand-rolled "`StrictTotalOrder`" structure.
-- The LN says "a total order `<`" and writes the parent-precedes-child
-- axiom with the strict symbol `<`. In Mathlib, the canonical packaging
-- of a strict total order on a type is `LinearOrder`: it bundles the
-- non-strict `≤`, the strict `<`, their equivalence
-- (`lt_iff_le_not_le`), reflexivity / transitivity / antisymmetry of `≤`,
-- trichotomy (`le_total`), and decidability. Taking `LinearOrder` instead
-- of just `IsStrictTotalOrder _ (· < ·)` buys us free access to every
-- `LinearOrder`-only Mathlib lemma (intervals, `Finset.min`, …) when
-- proving `claim_3_2` and downstream rows, without forcing us to derive
-- `LinearOrder` from a strict total order at every call site.
--
-- Design choice — the LN's `parent_lt` axiom uses `<` from the order
-- being defined. We therefore phrase the field as
-- `toLinearOrder.lt v w` (i.e. the `lt` field of the bundled
-- `LinearOrder`), not `v < w`: at the structure-definition site, the
-- ambient `<` instance is not yet available (the `LinearOrder` is itself
-- a field), so the explicit field access is the unambiguous form. After
-- destructuring or via `haveI`, callers can switch to plain `<`
-- notation.
--
-- Design choice — the LN's "equivalent indexing" reformulation
-- (`J ∪ V = {v_1, …, v_K}` with parents before children) is *informally*
-- the well-known fact that a finite linearly ordered set is order-isomorphic
-- to an initial segment of `ℕ` (`Fin K`); for the infinite case the LN
-- definition is the only sensible one. We do not formalise the indexing
-- form as a separate definition — it would either duplicate
-- `LinearOrder` or require finiteness, neither of which the LN's main
-- form needs. We will revisit this if `claim_3_2` or a later row needs
-- the indexing view explicitly.
structure CDMG.TopologicalOrder (G : CDMG J V) where
  /-- A linear order on `J ⊕ V` (LN: "a total order `<` of `J ∪ V`").
  `LinearOrder` bundles `≤`, `<`, decidability, and trichotomy in one
  Mathlib-blessed package; see the file-level design-choice block above. -/
  toLinearOrder : LinearOrder (J ⊕ V)
  /-- Parents precede their children in the order (LN:
  "`v ∈ Pa^G(w) ⟹ v < w`"). Phrased via `toLinearOrder.lt` rather than
  bare `<` because at this declaration site the `LinearOrder` instance is
  itself a field of the structure being defined and is not yet available
  for instance resolution. -/
  parent_lt : ∀ ⦃v w : J ⊕ V⦄, v ∈ G.Pa w → toLinearOrder.lt v w

end Chapter3
end Causality
