import Chapter3_GraphTheory.Section3_1.WalkPredicates
import Mathlib.Data.Set.Lattice

/-!
# Family relationships in a CDMG: directed-reachability operators
(def 3.5, items 4 -- 7)

This file formalises the four *directed-reachability*
family-relationship operators of definition 3.5 of the lecture
notes (Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`):

  * **Ancestors** `Anc^G(v)` / `Anc^G(A)` (LN def 3.5 item 4)
  * **Descendants** `Desc^G(v)` / `Desc^G(A)` (LN def 3.5 item 5)
  * **Non-descendants** `NonDesc^G(A)` (LN def 3.5 item 6 -- set
    input only, no vertex variant in the LN)
  * **Strongly connected component** `Sc^G(v)` / `Sc^G(A)`
    (LN def 3.5 item 7)

All four sit on top of def 3.4's `Walk` data type and the
`Walk.IsDirected` predicate from `WalkPredicates.lean`. The
sibling file `FamilyDirect.lean` formalises the direct-edge
operators Pa / Ch / Sib, and `FamilyDistrict.lean` formalises
the bidirected-walk operator Dist. The three files are
siblings: none imports the others.

For the cross-file conventions (set return type, `w ∈ G` guard,
two-defs-per-operator pattern, simp lemma naming) see the
module docstring of `FamilyDirect.lean`.

## Reflexivity "Note: …" lines

The LN flags four reflexivity facts on these operators as
"Note:" lines, two per family:

  * `v ∈ Anc^G(v)` / `A ⊆ Anc^G(A)`
  * `v ∈ Desc^G(v)` / `A ⊆ Desc^G(A)`
  * `v ∈ Sc^G(v)` / `A ⊆ Sc^G(A)`

(`NonDesc^G(A)` has no reflexivity note.) Each becomes a proper
`theorem` next to the corresponding `def`: the vertex
reflexivity uses `Walk.nil v` as a witness for the existential
walk; the set reflexivity follows by pointing each `v ∈ A` at
itself in the bigunion and invoking the vertex reflexivity.
Each reflexivity theorem carries the LN's silent precondition
"`v ∈ V` / `A ⊆ J ∪ V`" as an explicit hypothesis (`v ∈ G` /
`A ⊆ G.J ∪ G.V`).
-/

namespace Causality

open scoped Causality.CDMG

namespace CDMG

variable {α : Type*}

/-! ## Ancestors (def 3.5, item 4)

`Anc^G(v)` collects all `w ∈ G` from which a *directed walk*
reaches `v`. The trivial walk `Walk.nil v` -- which is vacuously
`IsDirected` -- certifies `v ∈ Anc^G(v)` whenever `v ∈ G`,
giving the LN's "Note: `v ∈ Anc^G(v)`" reflexivity. -/

-- def_3_5 (item 4: ancestors of a vertex)
-- title: FamilyRelationships -- ancestors of a vertex v
--
-- A vertex `w ∈ G` is an *ancestor* of `v` if there is a
-- directed walk from `w` to `v` in `G`. We re-use the
-- def_3_4 `Walk G w v` data type and the def_3_4
-- `Walk.IsDirected` predicate (from `WalkPredicates.lean`);
-- the existential "$\exists$ directed walk" matches the LN's
-- prose.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 4, vertex variant):

  The set of \emph{ancestors} of $v$ in $G$:
  \[\Anc^G(v):=\{w \in G\,|\,\exists \text{ directed walk: }
    w \tuh \cdots \tuh v \in G\}.\]
  Note: $v \in \Anc^G(v)$.
-/
--
-- ## Design choice
--
-- * **`∃ π : Walk G w v, π.IsDirected`, not a separate inductive
--   "ancestor" relation.** The plan-§-equivalent reasoning from
--   `WalkPredicates.lean`'s `IsDirected` design block applies:
--   composing on top of the existing `Walk` data layer reuses
--   the full walk API (`length`, `support`, `append`,
--   `reverse`) for free, whereas a separate inductive would
--   require re-proving all of that. Plus, downstream rows
--   reason existentially on walks anyway (claim 3.2, def 3.6
--   acyclicity, ...).
--
-- * **Walk direction `w → v`.** The LN writes "directed walk:
--   `w \tuh ⋯ \tuh v`", i.e. the walk starts at `w` (the
--   candidate ancestor) and ends at `v` (the descendant). We
--   match exactly: `Walk G w v` is "a walk *from* `w` *to*
--   `v`", and the existential is over such walks. The opposite
--   direction is captured by `Desc^G` (next operator).
--
-- * **`w ∈ G` guard is load-bearing here.** Without it, the
--   trivial walk `Walk.nil w : Walk G w w` -- which is
--   vacuously `IsDirected` (`Walk.isDirected_nil`) -- would
--   land every `w : α` in `Anc G w`, including vertices outside
--   `G.J ∪ G.V`. With the guard, `Anc G v` is empty for `v ∉ G`
--   in any sensible reading: for the trivial walk we'd need
--   `w = v` and `w ∈ G`, both of which are constrained; for
--   longer walks the final step `… ⟶[G] v` already forces
--   `v ∈ G.V ⊆ G` via `G.E_subset`. The LN's "Note: `v ∈
--   Anc^G(v)`" implicitly assumes the preamble's `v ∈ V`, i.e.
--   `v ∈ G`. We capture this as an explicit hypothesis on the
--   `self_mem_Anc` theorem below.

/-- `Anc G v` -- the set of *ancestors* of the vertex `v` in `G`:
those `w ∈ G` for which there exists a *directed walk* (in the
def_3_4 sense, i.e. `Walk G w v` plus `Walk.IsDirected`) from
`w` to `v`. Matches the LN's `\Anc^G(v)`. -/
def Anc (G : CDMG α) (v : α) : Set α :=
  {w | w ∈ G ∧ ∃ π : Walk G w v, π.IsDirected}

/-- Membership characterisation of `Anc G v`. -/
@[simp] theorem mem_Anc {G : CDMG α} {w v : α} :
    w ∈ Anc G v ↔ w ∈ G ∧ ∃ π : Walk G w v, π.IsDirected :=
  Iff.rfl

-- def_3_5 (item 4: "Note: v ∈ Anc^G(v)" reflexivity)
-- title: FamilyRelationships -- v is an ancestor of itself
--
-- The LN explicitly flags the reflexivity `v ∈ Anc^G(v)` as a
-- "Note:" line; we record it as a theorem so downstream rows can
-- cite it by name. The witness is the trivial walk `Walk.nil v`,
-- which is `IsDirected` vacuously (`Walk.isDirected_nil`). The
-- precondition `v ∈ G` -- silent in the LN, implicit in the
-- "Let $v, w \in V$" preamble -- is explicit here for the
-- reasons discussed above.

/-- LN "Note: `v ∈ Anc^G(v)`" (def 3.5, item 4). The witness is
the trivial walk `Walk.nil v`. The `v ∈ G` hypothesis is the
LN's implicit precondition (its preamble fixes `v ∈ V ⊆ G`). -/
theorem self_mem_Anc {G : CDMG α} {v : α} (hv : v ∈ G) :
    v ∈ Anc G v :=
  ⟨hv, Walk.nil v, by simp⟩

-- def_3_5 (item 4: ancestors of a set)
-- title: FamilyRelationships -- ancestors of a set A
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 4, set variant):

  The set of \emph{ancestors} of $A$ in $G$:
  \[\Anc^G(A):= \bigcup_{v \in A} \Anc^G(v).\]
  Note: $A \ins \Anc^G(A)$.
-/
--
-- ## Design choice
--
-- Same `⋃ v ∈ A, Anc G v` idiom as `PaSet` / `ChSet` (see
-- `FamilyDirect.lean`). The "Note: `A ⊆ Anc^G(A)`" reflexivity
-- becomes the theorem `subset_Anc_set` below.

/-- `AncSet G A` -- the set of *ancestors* of the set `A` in `G`.
Matches the LN's set-input `\Anc^G(A)`. -/
def AncSet (G : CDMG α) (A : Set α) : Set α :=
  ⋃ v ∈ A, Anc G v

/-- Membership characterisation of `AncSet G A`. -/
@[simp] theorem mem_AncSet {G : CDMG α} {A : Set α} {w : α} :
    w ∈ AncSet G A ↔ ∃ v ∈ A, w ∈ Anc G v := by
  simp only [AncSet, Set.mem_iUnion, exists_prop]

-- def_3_5 (item 4: "Note: A ⊆ Anc^G(A)" reflexivity)
-- title: FamilyRelationships -- A is contained in its own ancestor set
--
-- The LN's second reflexivity note for ancestors. Follows by
-- pointing each `v ∈ A` at itself in the bigunion and invoking
-- `self_mem_Anc`. Precondition: `A ⊆ G.J ∪ G.V` (the LN's
-- preamble "$A \ins J \cup V$" rendered into Lean).

/-- LN "Note: `A ⊆ Anc^G(A)`" (def 3.5, item 4). Each
`v ∈ A ⊆ G.J ∪ G.V` is its own ancestor via the trivial walk. -/
theorem subset_Anc_set {G : CDMG α} {A : Set α}
    (hA : A ⊆ G.J ∪ G.V) : A ⊆ AncSet G A := by
  intro v hvA
  rw [mem_AncSet]
  exact ⟨v, hvA, self_mem_Anc (hA hvA)⟩

/-! ## Descendants (def 3.5, item 5)

Mirror image of `Anc^G`: a vertex `w ∈ G` is a *descendant* of
`v` if there is a directed walk from `v` to `w`. The reflexivity
`v ∈ Desc^G(v)` again follows from the trivial walk. -/

-- def_3_5 (item 5: descendants of a vertex)
-- title: FamilyRelationships -- descendants of a vertex v
--
-- Mirror of `Anc`: walk direction is flipped to `v → w`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 5, vertex variant):

  The set of \emph{descendants} of $v$ in $G$:
  \[\Desc^G(v):=\{w \in G\,|\,\exists \text{ directed walk: }
    v \tuh \cdots \tuh w \in G\}.\]
  Note: $v \in \Desc^G(v)$.
-/
--
-- ## Design choice
--
-- Identical to `Anc` modulo direction reversal: the existential
-- walk is `Walk G v w` (from `v` to `w`) rather than
-- `Walk G w v`. All other shape considerations carry over
-- (`w ∈ G` guard, `IsDirected` predicate from `WalkPredicates`,
-- existential phrasing).
--
-- We do *not* define `Desc G v` as `Anc (reverse G) v`
-- (reverse-graph trick) because we have not introduced a graph
-- reversal operation on `CDMG` -- and the LN does not use such a
-- trick at this stage; it works with the natural-direction walk
-- formulation throughout.

/-- `Desc G v` -- the set of *descendants* of the vertex `v` in
`G`: those `w ∈ G` for which there exists a directed walk from
`v` to `w`. Matches the LN's `\Desc^G(v)`. -/
def Desc (G : CDMG α) (v : α) : Set α :=
  {w | w ∈ G ∧ ∃ π : Walk G v w, π.IsDirected}

/-- Membership characterisation of `Desc G v`. -/
@[simp] theorem mem_Desc {G : CDMG α} {w v : α} :
    w ∈ Desc G v ↔ w ∈ G ∧ ∃ π : Walk G v w, π.IsDirected :=
  Iff.rfl

-- def_3_5 (item 5: "Note: v ∈ Desc^G(v)" reflexivity)
-- title: FamilyRelationships -- v is a descendant of itself

/-- LN "Note: `v ∈ Desc^G(v)`" (def 3.5, item 5). Witness:
trivial walk. -/
theorem self_mem_Desc {G : CDMG α} {v : α} (hv : v ∈ G) :
    v ∈ Desc G v :=
  ⟨hv, Walk.nil v, by simp⟩

-- def_3_5 (item 5: descendants of a set)
-- title: FamilyRelationships -- descendants of a set A
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 5, set variant):

  The set of \emph{descendants} of $A$ in $G$:
  \[\Desc^G(A):= \bigcup_{v \in A} \Desc^G(v).\]
  Note: $A \ins \Desc^G(A)$.
-/

/-- `DescSet G A` -- the set of *descendants* of the set `A` in
`G`. Matches the LN's set-input `\Desc^G(A)`. -/
def DescSet (G : CDMG α) (A : Set α) : Set α :=
  ⋃ v ∈ A, Desc G v

/-- Membership characterisation of `DescSet G A`. -/
@[simp] theorem mem_DescSet {G : CDMG α} {A : Set α} {w : α} :
    w ∈ DescSet G A ↔ ∃ v ∈ A, w ∈ Desc G v := by
  simp only [DescSet, Set.mem_iUnion, exists_prop]

-- def_3_5 (item 5: "Note: A ⊆ Desc^G(A)" reflexivity)
-- title: FamilyRelationships -- A is contained in its own descendant set

/-- LN "Note: `A ⊆ Desc^G(A)`" (def 3.5, item 5). -/
theorem subset_Desc_set {G : CDMG α} {A : Set α}
    (hA : A ⊆ G.J ∪ G.V) : A ⊆ DescSet G A := by
  intro v hvA
  rw [mem_DescSet]
  exact ⟨v, hvA, self_mem_Desc (hA hvA)⟩

/-! ## Non-descendants (def 3.5, item 6)

`NonDesc^G(A)` is the set-theoretic complement of `Desc^G(A)`
inside the ambient vertex set `J ∪ V`. The LN gives only the
set-input variant; **no vertex-input `NonDesc^G(v)` is
defined**, and we do not invent one. -/

-- def_3_5 (item 6: non-descendants of a set)
-- title: FamilyRelationships -- non-descendants of a set A
--
-- `NonDesc^G(A) := (J ∪ V) \ Desc^G(A)` — every vertex of
-- `G` that is *not* a descendant of any vertex in `A`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 6):

  The set of \emph{non-descendants} of $A$ in $G$:
  \[ \NonDesc^G(A) := (J \cup V) \sm \Desc^G(A).\]
-/
--
-- ## Design choice
--
-- * **`(G.J ∪ G.V) \ DescSet G A`, not `(Set.univ) \ DescSet G A`.**
--   The LN's ambient set is the graph's vertex set `J ∪ V`, not
--   the ambient type `α`. A vertex `w : α` outside `G.J ∪ G.V` is
--   *not* a non-descendant; it simply isn't a vertex of `G` at
--   all. This is the same "ambient set is `J ∪ V`" reading we
--   used for the `w ∈ G` guard in the other operators -- a
--   non-descendant must in particular be in `G`.
--
-- * **Set-only operator (no vertex variant).** The LN provides
--   only `\NonDesc^G(A)`; introducing `NonDesc^G(v) := (J ∪ V)
--   \setminus \Desc^G(v)` would be inventing a definition not
--   in the LN. The set version is the natural primitive --
--   downstream rows (do-calculus rules 2 -- 3, the ID
--   algorithm's exclusion criterion) always reason about
--   "non-descendants of *some set* `X`", never a single vertex.
--
-- * **Difference order: `(J ∪ V) \ Desc, not Desc \ (J ∪ V)`.**
--   Set difference is not symmetric -- the LN writes `(J \cup V)
--   \setminus \Desc^G(A)`, "ambient minus descendants", which
--   is what we encode.

/-- `NonDesc G A` -- the set of *non-descendants* of the set `A`
in `G`: vertices of `G` (i.e. members of `G.J ∪ G.V`) that are
not descendants of any vertex in `A`. Matches the LN's
`\NonDesc^G(A)`. The LN provides no vertex-input variant. -/
def NonDesc (G : CDMG α) (A : Set α) : Set α :=
  (G.J ∪ G.V) \ DescSet G A

/-- Membership characterisation of `NonDesc G A`: `w ∈
NonDesc G A` iff `w ∈ G` (`= G.J ∪ G.V`) and `w` is not a
descendant of any vertex in `A`. -/
@[simp] theorem mem_NonDesc {G : CDMG α} {A : Set α} {w : α} :
    w ∈ NonDesc G A ↔ w ∈ G ∧ w ∉ DescSet G A := by
  simp [NonDesc, Set.mem_diff, CDMG.mem_iff]

/-! ## Strongly connected component (def 3.5, item 7)

`Sc^G(v) := Anc^G(v) ∩ Desc^G(v)` -- the LN's "strongly
connected component of `v`" is the set of vertices that are
both ancestors and descendants of `v`, i.e. that lie on a
directed walk *to* `v` and on a directed walk *from* `v`. -/

-- def_3_5 (item 7: strongly connected component of a vertex)
-- title: FamilyRelationships -- strongly connected component of v
--
-- Defined by intersection of `Anc^G(v)` and `Desc^G(v)` --
-- i.e. the set of `w ∈ G` with a directed walk `w → ⋯ → v`
-- AND a directed walk `v → ⋯ → w`. By symmetry this carves
-- out the cyclic equivalence class of `v` under directed
-- reachability.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 7, vertex variant):

  The \emph{strongly connected component} of $v$ in $G$:
  \[ \Sc^G(v) := \Anc^G(v) \cap \Desc^G(v).\]
  Note: $v \in \Sc^G(v)$.
-/
--
-- ## Design choice
--
-- * **`Anc G v ∩ Desc G v`, not a fresh walk-based primitive.**
--   The LN literally writes the intersection; we follow that
--   exactly. The `w ∈ G` guard is inherited from `Anc` and
--   `Desc` (both have it baked in), so a vertex is in
--   `Sc G v` iff (i) it's in `G`, (ii) it has a directed walk
--   to `v`, and (iii) it has a directed walk from `v`.
--
-- * **Reflexivity `v ∈ Sc^G(v)` composes from
--   `self_mem_Anc` and `self_mem_Desc`** -- this is the LN's
--   "Note:" line, encoded as the theorem `self_mem_Sc` below.

/-- `Sc G v` -- the *strongly connected component* of `v` in `G`:
the intersection of the ancestor and descendant sets of `v`.
Matches the LN's `\Sc^G(v)`. Equivalently, the set of `w ∈ G`
that lie on a directed walk to `v` and on a directed walk from
`v`. -/
def Sc (G : CDMG α) (v : α) : Set α :=
  Anc G v ∩ Desc G v

/-- Membership characterisation of `Sc G v`. -/
@[simp] theorem mem_Sc {G : CDMG α} {w v : α} :
    w ∈ Sc G v ↔ w ∈ Anc G v ∧ w ∈ Desc G v := Iff.rfl

-- def_3_5 (item 7: "Note: v ∈ Sc^G(v)" reflexivity)
-- title: FamilyRelationships -- v is in its own strongly connected component

/-- LN "Note: `v ∈ Sc^G(v)`" (def 3.5, item 7). Composes
`self_mem_Anc` and `self_mem_Desc`. -/
theorem self_mem_Sc {G : CDMG α} {v : α} (hv : v ∈ G) :
    v ∈ Sc G v :=
  ⟨self_mem_Anc hv, self_mem_Desc hv⟩

-- def_3_5 (item 7: strongly connected components of a set)
-- title: FamilyRelationships -- union of strongly connected components of a set A
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.5,
item 7, set variant):

  The (union of) \emph{strongly connected components} of $A$
  in $G$:
  \[ \Sc^G(A) := \bigcup_{v \in A} \Sc^G(v).\]
  Note: $A \ins \Sc^G(A)$.
-/
--
-- ## Design choice
--
-- Same `⋃ v ∈ A, _` idiom as the other set variants. The LN's
-- wording "(union of) strongly connected components" makes the
-- bigunion semantics explicit: `Sc^G(A)` is the union of each
-- `v ∈ A`'s component, *not* the smallest strongly connected
-- component containing `A` (which would be a different
-- definition, and would not coincide with the union when `A`
-- spans more than one component).

/-- `ScSet G A` -- the union of *strongly connected components*
of vertices in `A`. Matches the LN's set-input `\Sc^G(A)`. -/
def ScSet (G : CDMG α) (A : Set α) : Set α :=
  ⋃ v ∈ A, Sc G v

/-- Membership characterisation of `ScSet G A`. -/
@[simp] theorem mem_ScSet {G : CDMG α} {A : Set α} {w : α} :
    w ∈ ScSet G A ↔ ∃ v ∈ A, w ∈ Sc G v := by
  simp only [ScSet, Set.mem_iUnion, exists_prop]

-- def_3_5 (item 7: "Note: A ⊆ Sc^G(A)" reflexivity)
-- title: FamilyRelationships -- A is contained in its own SC-component union

/-- LN "Note: `A ⊆ Sc^G(A)`" (def 3.5, item 7). -/
theorem subset_Sc_set {G : CDMG α} {A : Set α}
    (hA : A ⊆ G.J ∪ G.V) : A ⊆ ScSet G A := by
  intro v hvA
  rw [mem_ScSet]
  exact ⟨v, hvA, self_mem_Sc (hA hvA)⟩

end CDMG

end Causality
