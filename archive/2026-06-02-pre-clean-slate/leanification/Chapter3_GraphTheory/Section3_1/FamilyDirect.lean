import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Mathlib.Data.Set.Lattice

/-!
# Family relationships in a CDMG: direct-edge operators
(def 3.5, items 1 -- 3)

This file formalises the three *direct-edge* family-relationship
operators of definition 3.5 of the lecture notes (Forré &
Mooij, `lecture-notes/lecture_notes/graphs.tex`):

  * **Parents** `Pa^G(v)` / `Pa^G(A)` (LN def 3.5 item 1)
  * **Children** `Ch^G(v)` / `Ch^G(A)` (LN def 3.5 item 2)
  * **Siblings** `Sib^G(v)` (LN def 3.5 item 3 -- the LN gives
    only a vertex variant, **no set variant**)

These are the family operators that depend only on the
*single-edge* relations of def 3.2 (`⟶[G]`, `⟷[G]`). The
reachability operators (Anc / Desc / NonDesc / Sc) sit on top of
def 3.4's `Walk.IsDirected` and live in
`FamilyReachability.lean`; the district (Dist) sits on top of
def 3.4's `Walk.IsBidirected` and lives in
`FamilyDistrict.lean`. The three files are siblings (no
import between them), each lifting a different layer of the
graph-theory stack into the def_3_5 family-relationship API.

Almost every later chapter of the LN pattern-matches against
these operators -- chapter 4 (causal Bayesian networks)
factorises distributions over `Pa^G(v)`, chapter 5 (do-calculus)
moves edges incident to `Pa^G(\cdot)` / `Ch^G(\cdot)`, etc.

## Conventions adopted across the three `Family*.lean` files

* **`Set α` return type, parameterised by `G : CDMG α`.** The LN
  literally writes set-builders (`\{w \in G \mid \ldots\}`), so
  `Set α` is the natural codomain. The graph `G` is an explicit
  function argument so callers can vary it -- chapter 5's
  intervention `G^{do(v)}` is a different CDMG and asks for
  `Pa^{G^{do(v)}}(v)`.

* **`v ∈ G` guard baked into every set comprehension.** Each
  set-builder reads `\{w | w ∈ G ∧ \ldots\}`, matching the LN's
  literal text `\{w \in G \mid \ldots\}`. For the operators in
  this file (Pa / Ch / Sib) the `w ∈ G` conjunct is
  *propositionally redundant*: a directed edge `w ⟶[G] v` forces
  `w ∈ G.J ∪ G.V = G` via `G.E_subset`, and a bidirected edge
  `v ⟷[G] w` forces `w ∈ G.V ⊆ G` via `G.L_subset`. For the
  walk-based operators in `FamilyReachability.lean` and
  `FamilyDistrict.lean` the guard is **not** redundant (the
  trivial walk `Walk.nil w` exists for every `w : α`), so we
  bake it in uniformly here too so that callers see the same
  membership shape across all eight operators. The "reflexivity"
  theorems in the walk files (LN's "Note: `v ∈ Anc^G(v)`") then
  carry their natural precondition `v ∈ G` explicitly.

* **Two `def`s per operator** -- a vertex-input variant
  `Pa : CDMG α → α → Set α` and a set-input variant
  `PaSet : CDMG α → Set α → Set α` -- except for `Sib` (no set
  variant in the LN) and `NonDesc` (no vertex variant in the
  LN), where we mirror the LN's choice exactly. The LN
  overloads the same symbol `\Pa^G(\cdot)` for both inputs;
  Lean cannot, so we use the suffix `Set` to disambiguate. The
  set variant is *always* built directly on the vertex variant
  via `⋃ v ∈ A, f G v`, exactly mirroring the LN's
  `\Pa^G(A) := \bigcup_{v \in A} \Pa^G(v)` second-line
  definitions.

* **Each `def` is paired with one `@[simp]` membership
  characterisation lemma** named `mem_Pa`, `mem_PaSet`, etc.,
  reducing to `Iff.rfl` for vertex variants and to one
  `Set.mem_iUnion` + `exists_prop` rewrite for set variants.
  This mirrors the per-def simp lemmas in `EdgeRelations.lean`
  (`adjacent_iff`, `edgeInto_iff`, `edgeOutOf_iff`).

* **Naming on the LN names.** Each Lean def name is the LN's
  exact identifier modulo formatting (`\Pa` → `Pa`, `\Ch` →
  `Ch`, `\Sib` → `Sib`). The set variants append `Set`.
  Theorems use Mathlib snake_case with the def name as a token.
-/

namespace Causality

open scoped Causality.CDMG

namespace CDMG

variable {α : Type*}

/-! ## Parents (def 3.5, item 1) -/

-- def_3_5 (item 1: parents of a vertex)
-- title: FamilyRelationships -- parents of a vertex v
--
-- The set of *parents* of `v` in `G` is the set of vertices
-- `w ∈ G` such that there is a *directed* edge `w ⟶[G] v`
-- (equivalently `(w, v) ∈ G.E`). This is the LN's `\Pa^G(v)`.
-- Bidirected edges are deliberately excluded here: a
-- bidirected edge `w ⟷ v` makes `v` a *sibling* of `w` (see
-- the `Sib` operator below), never a parent.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 1, vertex variant):

  The set of \emph{parents} of $v$ in $G$:
  \[\Pa^G(v):=\{w \in G\,|\, w \tuh v \in G\}.\]
-/
--
-- ## Design choice
--
-- * **Directed-only.** The LN's `\tuh` is the directed-edge atom
--   (def_3_2), excluding `\huh` (bidirected). This matches the
--   def_3_3 split between "into" (arrowhead, includes `\huh`)
--   and "out of" (directed only, excludes `\huh`): parents are
--   read off "out of" edges from the parent's perspective.
--
-- * **`w ∈ G` guard kept** -- see the module docstring. For
--   parents the guard is propositionally redundant via
--   `G.E_subset`, but kept for textual fidelity and uniformity
--   with the walk-based operators in the sibling files.
--
-- * **Parents can lie in `G.J`.** The LN allows directed edges
--   `j ⟶ v` with `j ∈ J`, so input nodes can be parents of
--   output nodes. We do *not* restrict the parent set to `G.V`.
--   This is critical for chapters 4 -- 5 (CBN factorisation,
--   do-calculus): a CBN factorises `P(V | J)` as a product over
--   `Pa^G(v)`, and the parent set of an output `v` can include
--   input nodes (which is exactly how inputs enter the
--   factorisation).

/-- `Pa G v` -- the set of *parents* of the vertex `v` in `G`:
those `w ∈ G` with a directed edge `w ⟶[G] v`. Matches the LN's
`\Pa^G(v)` (`lecture-notes/lecture_notes/graphs.tex`, def 3.5
item 1). Parents can lie in either `G.J` or `G.V`. -/
def Pa (G : CDMG α) (v : α) : Set α :=
  {w | w ∈ G ∧ w ⟶[G] v}

/-- Membership characterisation of `Pa G v`. By definition,
`w ∈ Pa G v` iff `w ∈ G` and there is a directed edge from `w`
to `v` in `G`. -/
@[simp] theorem mem_Pa {G : CDMG α} {w v : α} :
    w ∈ Pa G v ↔ w ∈ G ∧ w ⟶[G] v := Iff.rfl

-- def_3_5 (item 1: parents of a set)
-- title: FamilyRelationships -- parents of a set A
--
-- The set of parents of a *set* `A` of vertices in `G` is the
-- union of the individual parent sets. The LN writes this as a
-- big-union over `v ∈ A`; we use the standard `⋃ v ∈ A, _`
-- (Mathlib `Set.iUnion₂`) idiom.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 1, set variant):

  The set of \emph{parents} of $A$ in $G$:
  \[\Pa^G(A):= \bigcup_{v \in A} \Pa^G(v).\]
-/
--
-- ## Design choice
--
-- * **`⋃ v ∈ A, Pa G v` (Mathlib's `Set.iUnion₂` shape), not
--   `Set.image (Pa G) A` or `{w | ∃ v ∈ A, w ∈ Pa G v}`.**
--   `⋃ v ∈ A, _` is the standard Mathlib idiom for "union
--   indexed over a set"; its membership lemma `Set.mem_iUnion`
--   (composed twice) unfolds to exactly the existential we want
--   in downstream proofs. `Set.image (Pa G)` would not
--   type-check (`Pa G : α → Set α`, not `α → α`); the bare
--   set-builder would force every caller to do the
--   `simp [Set.mem_iUnion]` themselves.
--
-- * **The LN's commented-out `\PF{…}` alternative** (parents
--   of `A` minus `A` itself) is explicitly NOT what we
--   formalise -- the rendered text uses the plain bigunion. The
--   commented-out alternative motivates the LN's worry about
--   self-loops `v ⟶ v`; in our setup `v` is allowed to be its
--   own parent if `(v, v) ∈ G.E`, and the parents of `{v}`
--   contain `v` in that case. Downstream rows that need to
--   exclude self-loops do so explicitly at the use site.

/-- `PaSet G A` -- the set of *parents* of the set of vertices
`A` in `G`: the union of the parent sets of each `v ∈ A`.
Matches the LN's set-input `\Pa^G(A)`. -/
def PaSet (G : CDMG α) (A : Set α) : Set α :=
  ⋃ v ∈ A, Pa G v

/-- Membership characterisation of `PaSet G A`: `w ∈ PaSet G A`
iff there exists `v ∈ A` with `w ∈ Pa G v`. Reduces via
`Set.mem_iUnion` + `exists_prop` (`Mathlib.Data.Set.Lattice`).
We use `simp only` here so the inner `Pa G v` is NOT also
unfolded (preserving readability of downstream goals). -/
@[simp] theorem mem_PaSet {G : CDMG α} {A : Set α} {w : α} :
    w ∈ PaSet G A ↔ ∃ v ∈ A, w ∈ Pa G v := by
  simp only [PaSet, Set.mem_iUnion, exists_prop]

/-! ## Children (def 3.5, item 2) -/

-- def_3_5 (item 2: children of a vertex)
-- title: FamilyRelationships -- children of a vertex v
--
-- Symmetric mirror of `Pa`: the children of `v` are the vertices
-- `w ∈ G` reached by a directed edge from `v`, i.e.
-- `v ⟶[G] w`. Bidirected edges are again excluded; the
-- bidirected partners of `v` are its *siblings*, not children.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 2, vertex variant):

  The set of \emph{children} of $v$ in $G$:
  \[\Ch^G(v):=\{w \in G\,|\, v \tuh w \in G\}.\]
-/
--
-- ## Design choice
--
-- * **Same shape as `Pa`, mirrored.** The argument order in the
--   edge swaps: `Pa G v` looks for `w ⟶ v` (edges INTO `v`),
--   `Ch G v` looks for `v ⟶ w` (edges OUT OF `v`). The LN's
--   "parents" and "children" are dual via the reversal of the
--   directed edge, and the def_3_3 vocabulary captures the same
--   duality (`EdgeOutOf G v w` ↔ `tuh G v w` ↔ `v ⟶[G] w`).
--
-- * **Children are always in `G.V`.** Unlike parents, children
--   *cannot* be input nodes: `v ⟶[G] w` means `(v, w) ∈ G.E`,
--   and `G.E_subset : G.E ⊆ (J ∪ V) ×ˢ V` forces the *target*
--   `w` to lie in `G.V`. So `Ch G v ⊆ G.V`. This asymmetry --
--   "parents range over `J ∪ V`, children over `V`" -- is
--   exactly the LN's encoding that "interventions point at
--   outputs, never the other way around".

/-- `Ch G v` -- the set of *children* of the vertex `v` in `G`:
those `w ∈ G` with a directed edge `v ⟶[G] w`. Matches the LN's
`\Ch^G(v)`. Children are always output nodes (`w ∈ G.V` follows
from `G.E_subset`); inputs cannot be children. -/
def Ch (G : CDMG α) (v : α) : Set α :=
  {w | w ∈ G ∧ v ⟶[G] w}

/-- Membership characterisation of `Ch G v`. -/
@[simp] theorem mem_Ch {G : CDMG α} {w v : α} :
    w ∈ Ch G v ↔ w ∈ G ∧ v ⟶[G] w := Iff.rfl

-- def_3_5 (item 2: children of a set)
-- title: FamilyRelationships -- children of a set A
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 2, set variant):

  The set of \emph{children} of $A$ in $G$:
  \[\Ch^G(A):= \bigcup_{v \in A} \Ch^G(v).\]
-/
--
-- ## Design choice
--
-- Identical to `PaSet`: `⋃ v ∈ A, Ch G v`. No further nuance.

/-- `ChSet G A` -- the set of *children* of the set of vertices
`A` in `G`. Matches the LN's set-input `\Ch^G(A)`. -/
def ChSet (G : CDMG α) (A : Set α) : Set α :=
  ⋃ v ∈ A, Ch G v

/-- Membership characterisation of `ChSet G A`. -/
@[simp] theorem mem_ChSet {G : CDMG α} {A : Set α} {w : α} :
    w ∈ ChSet G A ↔ ∃ v ∈ A, w ∈ Ch G v := by
  simp only [ChSet, Set.mem_iUnion, exists_prop]

/-! ## Siblings (def 3.5, item 3)

The LN defines only a vertex variant of `Sib^G`; **no set
variant is given**. We mirror that choice strictly: no `SibSet`
declaration is introduced here, even though one could be defined
analogously. Inventing it would diverge from the LN, and any
downstream row that needs it can declare it locally. -/

-- def_3_5 (item 3: siblings of a vertex)
-- title: FamilyRelationships -- siblings of a vertex v
--
-- The set of *siblings* of `v` in `G` is the set of vertices
-- `w ∈ G` with a *bidirected* edge `v ⟷[G] w` to `v`. This is
-- the LN's `\Sib^G(v)`. Symmetric in `v`/`w` thanks to
-- `G.L_symm` (def_3_1).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 3):

  The set of \emph{siblings} of $v$ in $G$:
  \[\Sib^G(v):=\{w \in G\,|\, v \huh w \in G\}.\]
-/
--
-- ## Design choice
--
-- * **No set variant.** Mirrors the LN strictly. The
--   commented-out `\item[] The set of children of A in G:` line
--   in the LN source (placed after `\Sib^G`) is *not* a
--   commented-out `\Sib^G(A)` -- it is a leftover comment
--   referencing children. The LN's intentional omission of
--   `\Sib^G(A)` stands.
--
-- * **Siblings are always in `G.V`.** Bidirected edges live in
--   `G.V × G.V` by `G.L_subset`, so `Sib G v ⊆ G.V`. Like
--   children, inputs never participate as siblings.
--
-- * **Symmetric in `v` / `w`.** By `G.L_symm`, `v ⟷[G] w`
--   iff `w ⟷[G] v`, so `w ∈ Sib G v ↔ v ∈ Sib G w` (with the
--   `w ∈ G` and `v ∈ G` guards adjusted). We do not state this
--   symmetry as a separate lemma here; it follows by `G.L_symm`
--   at the use site.

/-- `Sib G v` -- the set of *siblings* of the vertex `v` in `G`:
those `w ∈ G` with a bidirected edge `v ⟷[G] w`. Matches the LN's
`\Sib^G(v)`. The LN intentionally provides no set-input
counterpart, and neither do we. -/
def Sib (G : CDMG α) (v : α) : Set α :=
  {w | w ∈ G ∧ v ⟷[G] w}

/-- Membership characterisation of `Sib G v`. -/
@[simp] theorem mem_Sib {G : CDMG α} {w v : α} :
    w ∈ Sib G v ↔ w ∈ G ∧ v ⟷[G] w := Iff.rfl

end CDMG

end Causality
