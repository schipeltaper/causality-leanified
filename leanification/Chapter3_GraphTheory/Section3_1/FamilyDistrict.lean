import Chapter3_GraphTheory.Section3_1.WalkPredicates
import Mathlib.Data.Set.Lattice

/-!
# Family relationships in a CDMG: district (bidirected-reachability)
(def 3.5, item 8)

This file formalises the *bidirected-walk* family-relationship
operator of definition 3.5 of the lecture notes (Forré & Mooij,
`lecture-notes/lecture_notes/graphs.tex`):

  * **District** `Dist^G(v)` / `Dist^G(A)` (LN def 3.5 item 8)

It sits on top of def 3.4's `Walk` data type and the
`Walk.IsBidirected` predicate from `WalkPredicates.lean`. The
sibling files `FamilyDirect.lean` (Pa / Ch / Sib) and
`FamilyReachability.lean` (Anc / Desc / NonDesc / Sc) formalise
the other family operators of def 3.5; the three files are
siblings and none imports the others.

For the cross-file conventions (set return type, `w ∈ G` guard,
two-defs-per-operator pattern, simp lemma naming) see the
module docstring of `FamilyDirect.lean`. For the reflexivity-
note pattern shared with the directed-reachability operators
see the module docstring of `FamilyReachability.lean`.

## Why districts deserve their own file

Districts model the equivalence classes of `V` under the
reflexive-transitive closure of the bidirected-edge relation
`↔` (`\huh`). They are pervasively used as primitives in the
later chapters' graphical-separation criteria (ID algorithm
chapter 8 reasons about whether a node and its district are
"separated" by an intervention; FCI completeness in chapter 16
hinges on districts being preserved by acyclification). Putting
them in their own file keeps the directed-reachability
operators (`FamilyReachability.lean`) self-contained: a row
that only needs `Anc` / `Desc` / `Sc` doesn't accidentally also
pull in `Dist` and its design rationale.
-/

namespace Causality

open scoped Causality.CDMG

namespace CDMG

variable {α : Type*}

/-! ## District (def 3.5, item 8)

`Dist^G(v)` collects all `w ∈ G` reachable from `v` by a
*bidirected* walk. The trivial walk `Walk.nil v` is vacuously
`IsBidirected`, giving the LN's "Note: `v ∈ Dist^G(v)`". -/

-- def_3_5 (item 8: district of a vertex)
-- title: FamilyRelationships -- district of a vertex v
--
-- A vertex `w ∈ G` is in the district of `v` if there is a
-- bidirected walk from `v` to `w`, i.e. a walk all of whose
-- edges are bidirected (`\huh`). Re-uses `Walk.IsBidirected`
-- from `WalkPredicates.lean`. As with `Anc`/`Desc`, the
-- existential phrasing matches the LN's "$\exists$ bidirected
-- walk" prose.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 8, vertex variant):

  The \emph{district} of $v$ in $G$:
  \[\Dist^G(v) := \{w \in G\,|\, \exists \text{ bidirected walk: }
    v \huh v_1 \huh \cdots \huh v_{n-1} \huh w \in G \}.\]
  Note: $v\in \Dist^G(v)$.
-/
--
-- ## Design choice
--
-- * **Walk direction `v → w`.** The LN writes the bidirected
--   walk as `v ↔ v_1 ↔ ⋯ ↔ w`, starting at `v`. We mirror this:
--   `Walk G v w` is a walk *from* `v` to `w`. Because
--   bidirected edges are symmetric (`G.L_symm`), this choice is
--   propositionally symmetric -- but the *literal* walk
--   direction matches the LN.
--
-- * **All edges bidirected = `Walk.IsBidirected`.** The LN's
--   walk pattern `v ↔ v_1 ↔ ⋯ ↔ w` is exactly the predicate
--   `Walk.IsBidirected` from `WalkPredicates.lean`: every step
--   is `bidir` (`\huh`). No directed-edge mixing allowed.
--
-- * **`w ∈ G` guard load-bearing.** Same story as `Anc`/`Desc`
--   in `FamilyReachability.lean`: the trivial walk `Walk.nil v`
--   is vacuously bidirected, so without the guard every
--   `w : α` (even `w ∉ G`) would land in `Dist G w`. The LN's
--   "Note: `v ∈ Dist^G(v)`" relies on `v ∈ G` from the
--   preamble; we encode that as an explicit hypothesis on
--   `self_mem_Dist`.
--
-- * **Bidirected walks model latent common causes.** The LN's
--   district is exactly the equivalence class of `v` under the
--   reflexive-transitive closure of the bidirected-edge
--   relation; downstream chapters use districts to identify
--   subsets of `V` that share latent confounders, which
--   matters for the ID algorithm (chapter 8) and for the FCI
--   algorithm's PAG completeness arguments (chapter 16).

/-- `Dist G v` -- the *district* of `v` in `G`: those `w ∈ G` for
which there exists a *bidirected walk* (every step is `bidir`)
from `v` to `w`. Matches the LN's `\Dist^G(v)`. -/
def Dist (G : CDMG α) (v : α) : Set α :=
  {w | w ∈ G ∧ ∃ π : Walk G v w, π.IsBidirected}

/-- Membership characterisation of `Dist G v`. -/
@[simp] theorem mem_Dist {G : CDMG α} {w v : α} :
    w ∈ Dist G v ↔ w ∈ G ∧ ∃ π : Walk G v w, π.IsBidirected :=
  Iff.rfl

-- def_3_5 (item 8: "Note: v ∈ Dist^G(v)" reflexivity)
-- title: FamilyRelationships -- v is in its own district

/-- LN "Note: `v ∈ Dist^G(v)`" (def 3.5, item 8). Witness:
trivial walk, which is vacuously `IsBidirected`. -/
theorem self_mem_Dist {G : CDMG α} {v : α} (hv : v ∈ G) :
    v ∈ Dist G v :=
  ⟨hv, Walk.nil v, by simp⟩

-- def_3_5 (item 8: district of a set)
-- title: FamilyRelationships -- district of a set A
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 8, set variant):

  The \emph{district} of $A$ in $G$:
  \[\Dist^G(A) := \bigcup_{v \in A} \Dist^G(v).\]
  Note: $A \ins \Dist^G(A)$.
-/

/-- `DistSet G A` -- the *district* of the set `A` in `G`.
Matches the LN's set-input `\Dist^G(A)`. -/
def DistSet (G : CDMG α) (A : Set α) : Set α :=
  ⋃ v ∈ A, Dist G v

/-- Membership characterisation of `DistSet G A`. -/
@[simp] theorem mem_DistSet {G : CDMG α} {A : Set α} {w : α} :
    w ∈ DistSet G A ↔ ∃ v ∈ A, w ∈ Dist G v := by
  simp only [DistSet, Set.mem_iUnion, exists_prop]

-- def_3_5 (item 8: "Note: A ⊆ Dist^G(A)" reflexivity)
-- title: FamilyRelationships -- A is contained in its own district

/-- LN "Note: `A ⊆ Dist^G(A)`" (def 3.5, item 8). -/
theorem subset_Dist_set {G : CDMG α} {A : Set α}
    (hA : A ⊆ G.J ∪ G.V) : A ⊆ DistSet G A := by
  intro v hvA
  rw [mem_DistSet]
  exact ⟨v, hvA, self_mem_Dist (hA hvA)⟩

end CDMG

end Causality
