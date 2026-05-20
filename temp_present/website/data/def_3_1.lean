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
