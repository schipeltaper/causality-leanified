import Mathlib.Data.Set.Basic

-- The verbatim TeX source of the LN definition is reproduced inside a
-- comment below; one of its lines exceeds 100 characters. Disable the
-- style linter for this file so the TeX is kept byte-for-byte identical
-- to `lecture-notes/lecture_notes/graphs.tex`.
set_option linter.style.longLine false

/-!
# def_3_1 — Conditional Directed Mixed Graphs (CDMG)

The cornerstone definition for chapter 3. A CDMG packages together two
disjoint vertex sets (input nodes `J` and output nodes `V`), a set of
directed edges `E ⊆ (J ∪ V) × V`, and a set of bidirected edges `L` on `V`
which is required to be symmetric and irreflexive.
-/

namespace Causality
namespace Chapter3

/-
Source (from the lecture notes, `lecture-notes/lecture_notes/graphs.tex`,
also mirrored in `Section3_1/main.tex`):

\begin{Def}[Conditional directed mixed graphs (CDMG)]
    \label{def-cdmg}
    A \emph{conditional directed mixed graph (CDMG)} $G$---per definition---consists of two (disjoint) sets of
    vertices (also called nodes):
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
-/

/-- A **Conditional Directed Mixed Graph (CDMG)** on input-node type `J` and
output-node type `V`.

The lecture notes tuple `G = (J, V, E, L)` is realised in Lean as:

* the two vertex sets `J` and `V` — the **type parameters** of `CDMG`;
* `E : Set ((J ⊕ V) × V)` — the directed edges, with sources in `J ∪ V`
  (encoded as `J ⊕ V`) and targets in `V`;
* `L : Set (V × V)` — the bidirected edges, together with two laws
  (`L_symm`, `L_irrefl`) that bake in the LN's `(v₁,v₂) ∼ (v₂,v₁)`
  quotient together with the requirement `v₁ ≠ v₂`.

Design choice (matters for every later row in this chapter):

* **Two type parameters `J V` instead of two subsets of one ambient type.**
  Modelling the disjoint vertex sets as separate Lean types makes the LN's
  "(disjoint) sets of vertices" hold *by construction*: there is nothing
  to prove, and `J ∪ V` is then exactly `J ⊕ V` (Lean's `Sum`). The
  alternative — one ambient type `W` with `J V : Set W` and a disjointness
  hypothesis — would force every downstream statement to carry that
  hypothesis around and would turn membership tests (`v ∈ J ∪ V`,
  `v ∈ V`) into propositional side-conditions. Since downstream notation
  (`v ∈ G`, parents, walks, …) is heavily indexed by which "side" a node
  lives on, the `Sum` encoding is by far the lighter weight.

* **`L` as a `Set (V × V)` with `L_symm` and `L_irrefl` laws, instead of a
  literal quotient.** The LN writes `L ⊆ V × V / ((v₁,v₂) ∼ (v₂,v₁))` and
  then immediately constrains the representatives. A set on the symmetric
  quotient with no fixed points is mathematically the same data as a
  symmetric, irreflexive subset of `V × V`, and the latter is far easier
  to use in proofs (no `Quot.lift` boilerplate, ordered pairs let us pattern
  match on `(v₁, v₂)` directly). Whenever we need to think of `L` as a set
  of unordered pairs, we recover that view by symmetry.

* **The commented-out `J ∪ V ≠ ∅` in the source is intentionally omitted.**
  It is `%`-commented in `graphs.tex`, so it is not part of the rendered
  definition; `CDMG` therefore allows both vertex types to be empty. The
  empty CDMG is a legitimate edge case.
-/
structure CDMG (J V : Type*) where
  /-- Directed edges of the CDMG, `E ⊆ (J ∪ V) × V` in the lecture notes. -/
  E : Set ((J ⊕ V) × V)
  /-- Bidirected edges of the CDMG, `L ⊆ V × V` quotiented by the swap
  identification in the lecture notes. We store representatives in `V × V`
  and enforce the quotient + irreflexivity laws via `L_symm` and
  `L_irrefl`. -/
  L : Set (V × V)
  /-- `L` is symmetric: this is the `(v₁,v₂) ∼ (v₂,v₁)` identification of
  the lecture notes, internalised as a law on the ordered-pair
  representation. -/
  L_symm : ∀ {v₁ v₂ : V}, (v₁, v₂) ∈ L → (v₂, v₁) ∈ L
  /-- `L` is irreflexive: the LN's explicit constraint
  `(v₁,v₂) ∈ L ⟹ v₁ ≠ v₂`. -/
  L_irrefl : ∀ {v₁ v₂ : V}, (v₁, v₂) ∈ L → v₁ ≠ v₂

end Chapter3
end Causality
