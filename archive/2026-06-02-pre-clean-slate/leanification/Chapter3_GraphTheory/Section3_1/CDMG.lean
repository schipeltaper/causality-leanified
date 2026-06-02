import Mathlib.Data.Set.Prod
import Mathlib.Order.Disjoint

/-!
# Conditional Directed Mixed Graphs (CDMGs)

This file introduces the foundational geometric object of the Causality
lecture notes (Forré & Mooij, chapter 3): the *Conditional Directed Mixed
Graph* (CDMG). Subsequent chapters define CBNs (ch. 4), do-calculus
(ch. 5), iSCMs (ch. 8-10), and the causal-discovery algorithms
(ch. 11-16) on top of this single structure, so its shape needs to scale
without renegotiation.
-/

namespace Causality

-- def_3_1
-- title: CDMG
--
-- A *conditional directed mixed graph* over an ambient vertex type `α`
-- is a quadruple `(J, V, E, L)` where:
--
--   * `J ⊆ α` is the set of *input* nodes (the LN also calls these
--     *context* vertices) -- interventions and exogenous parameters
--     live here.
--   * `V ⊆ α` is the set of *output* nodes -- the endogenous vertices
--     the model talks about.
--   * `E ⊆ (J ∪ V) × V` is the set of *directed* edges. A directed edge
--     `j → v` may originate at an input, but no input may ever be a
--     target (no arrowheads point at `J`); the inclusion encodes this
--     in a single line.
--   * `L ⊆ V × V` is the set of *bidirected* edges, representing latent
--     confounding between two output nodes. We require `L` to be
--     symmetric and irreflexive on `V`, which is the unfolded version
--     of the LN's phrasing "`L` is a subset of `V × V` quotiented by
--     `(v₁,v₂) ∼ (v₂,v₁)`".
--   * `J` and `V` are disjoint, and so are `E` and `L`.
--
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`:

\begin{defmark}
\begin{Def}[Conditional directed mixed graphs (CDMG)]
    \label{def-cdmg}
    A \emph{conditional directed mixed graph (CDMG)} $G$---per definition---consists
    of two (disjoint) sets of vertices (also called nodes):
    \begin{enumerate}[label=\roman*.)]
        \item $J$, whose elements are called input nodes,
        \item $V$, whose elements are called output nodes,
    \end{enumerate}
%    such that $J \cup V \neq \emptyset$;
    and two (disjoint) sets of edges:
    \begin{enumerate}[resume,label=\roman*.)]
        \item $E \ins (J \cup V) \times V$ the set of directed edges,
        \item $L \ins V \times V/((v_1,v_2) \sim (v_2,v_1)) $, the set of bidirected edges,
        \item[]    with: $(v_1,v_2) \in L \, \implies\, v_1\neq v_2 \land (v_2,v_1) \in L$.
    \end{enumerate}
\end{Def}
\end{defmark}

The commented-out clause `J \cup V \neq \emptyset` in the LN source is
intentionally *not* part of the definition -- empty CDMGs are allowed.
-/
--
-- ## Design choice
--
-- * **Polymorphic vertex type `α : Type*`.** The LN does not commit to
--   finiteness or even countability of the vertex sets at this layer;
--   such assumptions come in later (e.g. some CBN factorisation
--   arguments need finite `V`). Keeping `α` fully polymorphic lets every
--   later chapter pick its ambient vertex type without forcing us back
--   here.
--
-- * **`Set α` for `J` and `V`, not `Finset α` or a separate `Fintype`.**
--   The LN literally says "two (disjoint) *sets* of vertices", and every
--   downstream definition reads `j ∈ J` / `v ∈ V` rather than indexing
--   into a list. `Set` is therefore both the most faithful and the
--   least restrictive shape.
--
-- * **Bidirected edges as a symmetric irreflexive subset of `V × V`,
--   not the literal quotient `V × V / ∼`.** The LN's quotient form is
--   propositionally equivalent to "symmetric subset of ordered pairs",
--   but a `Quotient` carrier forces explicit `Quotient.mk` /
--   `Quotient.lift` plumbing at every use site and obscures the
--   `(v₁, v₂) ∈ L` membership idiom that the rest of the notes rely on
--   (see e.g. def 3.2 `v₁ ↔ v₂ ∈ G` meaning `(v₁, v₂) ∈ L`). Encoding
--   the symmetry and irreflexivity as fields of the structure is much
--   cleaner and exactly equivalent.
--
-- * **`structure`, not `class` and not `abbrev`.** A specific CDMG over
--   `α` is *data*, not a canonical instance attached to `α`, so `class`
--   would be wrong: there is no globally unique CDMG to typeclass-
--   resolve into. `abbrev` would flatten the bundled fields and force
--   every downstream user to re-state the four constraints in every
--   signature. A `structure` gives us projection notation -- `G.J`,
--   `G.V`, `G.E`, `G.L` -- which lines up exactly with the LN's
--   recurring "Let `G = (J, V, E, L)` be a CDMG" prose pattern used in
--   def 3.3, def 3.4, def 3.5, def 3.6, def 3.7, def 3.8, def 3.9, the
--   subsequent intervention chapters, and beyond.
--
-- * **`Disjoint E L` is included as a field** because the LN explicitly
--   says "two (disjoint) sets of edges". With `E, L : Set (α × α)`
--   sharing the same ambient pair type, this is meaningful: it forbids
--   a pair `(v₁, v₂)` from being simultaneously a directed and a
--   bidirected edge between the same two nodes.
--
-- * **No `SimpleGraph` base.** `SimpleGraph` is single-sorted,
--   symmetric, and irreflexive on a single vertex type. It has neither
--   the input/output bipartition `(J, V)` nor the asymmetric directed
--   edges of a CDMG. Layering the directed/bidirected distinction on
--   top of `SimpleGraph` would cost more than it saves and obscure the
--   correspondence with the LN.

/-- A *Conditional Directed Mixed Graph (CDMG)* over the ambient vertex
type `α`, consisting of disjoint input/output node sets `J`, `V` and
edge sets `E` (directed) and `L` (bidirected, irreflexive and symmetric
on `V`). See `lecture-notes/lecture_notes/graphs.tex` definition
`def-cdmg` (def 3.1 of the LN). -/
structure CDMG (α : Type*) where
  /-- The set of *input* nodes. -/
  J : Set α
  /-- The set of *output* nodes. -/
  V : Set α
  /-- Inputs and outputs are disjoint sets of vertices. -/
  disjoint_JV : Disjoint J V
  /-- The set of *directed* edges. -/
  E : Set (α × α)
  /-- Directed edges originate at any node and terminate at an output. -/
  E_subset : E ⊆ (J ∪ V) ×ˢ V
  /-- The set of *bidirected* edges, encoded as a subset of `V × V`
  required to be symmetric and irreflexive -- equivalent to the LN's
  "subset of `V × V / ∼`" quotient form. -/
  L : Set (α × α)
  /-- Bidirected edges live between output nodes. -/
  L_subset : L ⊆ V ×ˢ V
  /-- Bidirected edges have no self-loops. -/
  L_irrefl : ∀ ⦃v₁ v₂ : α⦄, (v₁, v₂) ∈ L → v₁ ≠ v₂
  /-- Bidirected edges are unordered: `(v₁, v₂) ∈ L → (v₂, v₁) ∈ L`. -/
  L_symm : ∀ ⦃v₁ v₂ : α⦄, (v₁, v₂) ∈ L → (v₂, v₁) ∈ L
  /-- Directed and bidirected edges are disjoint as subsets of `α × α`. -/
  disjoint_EL : Disjoint E L

end Causality
