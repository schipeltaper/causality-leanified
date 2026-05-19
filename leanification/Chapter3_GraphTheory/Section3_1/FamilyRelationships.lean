import Chapter3_GraphTheory.Section3_1.Walks
import Mathlib.Data.Set.Lattice

-- The verbatim TeX source of the LN definition is reproduced inside the
-- comments below; some of its lines exceed 100 characters. Disable the
-- style linter for this file so the TeX is kept byte-for-byte identical
-- to `Section3_1/main.tex`.
set_option linter.style.longLine false

/-!
# def_3_5 — Family relationships

The fifth LN definition of subsection 3.1 bundles fourteen sub-definitions
under one `\begin{Def}[Family relationships]` block. Each LN bullet
becomes its own Lean declaration; the eight "node-form" bullets (`Pa`,
`Ch`, `Sib`, `Anc`, `Desc`, `Sc`, `Dist`, and the standalone `NonDesc`)
plus the six "set-form" bullets (`PaSet`, `ChSet`, `AncSet`, `DescSet`,
`ScSet`, `DistSet`) total 14 declarations. The `Sib` and `NonDesc`
operators are single because the LN only gives one form for each.

We share the `Causality.Chapter3` namespace with `def_3_1`–`def_3_4`.

The commented-out d-Markov / σ-Markov blanket items at the end of the LN
source are `%`-commented (not rendered) and are intentionally omitted.
-/

namespace Causality
namespace Chapter3

variable {J V : Type*}

/-
Source (verbatim from `Section3_1/main.tex`, under `% def_3_5`):

\begin{defmark}
\begin{Def}[Family relationships]
     Let $G=(J,V,E,L)$ be a CDMG, $v,w \in V$ and $A \ins J \cup V$ a subset of nodes.
     We then define:
     \begin{enumerate}
         \item The set of \emph{parents} of $v$ in $G$: \[\Pa^G(v):=\lC w \in G\,|\, w \tuh v \in G \rC.\]
         \item[] The set of \emph{parents} of $A$ in $G$: \[\Pa^G(A):= \bigcup_{v \in A} \Pa^G(v).\]
         \item The set of \emph{children} of $v$ in $G$: \[\Ch^G(v):=\lC w \in G\,|\, v \tuh w \in G \rC.\]
         \item[] The set of \emph{children} of $A$ in $G$: \[\Ch^G(A):= \bigcup_{v \in A} \Ch^G(v).\]
         \item The set of \emph{siblings} of $v$ in $G$: \[\Sib^G(v):=\lC w \in G\,|\, v \huh w \in G \rC.\]
         \item The set of \emph{ancestors} of $v$ in $G$:
             \[\Anc^G(v):=\lC w \in G\,|\,\exists \text{ directed walk: } w \tuh \cdots \tuh v \in G \rC.\]
             Note: $v \in \Anc^G(v)$.
         \item[] The set of \emph{ancestors} of $A$ in $G$: \[\Anc^G(A):= \bigcup_{v \in A} \Anc^G(v).\]
             Note: $A \ins \Anc^G(A)$.
         \item The set of \emph{descendants} of $v$ in $G$:
             \[\Desc^G(v):=\lC w \in G\,|\,\exists \text{ directed walk: } v \tuh \cdots \tuh w \in G \rC.\]
             Note: $v \in \Desc^G(v)$.
         \item[] The set of \emph{descendants} of $A$ in $G$: \[\Desc^G(A):= \bigcup_{v \in A} \Desc^G(v).\]
             Note: $A \ins \Desc^G(A)$.
         \item The set of \emph{non-descendants} of $A$ in $G$:
             \[ \NonDesc^G(A) := (J \cup V) \sm \Desc^G(A).\]
         \item The \emph{strongly connected component} of $v$ in $G$:
             \[ \Sc^G(v) := \Anc^G(v) \cap \Desc^G(v).\]
             Note: $v \in \Sc^G(v)$.
         \item[] The (union of) \emph{strongly connected components} of $A$ in $G$:
             \[ \Sc^G(A) := \bigcup_{v \in A} \Sc^G(v).\]
             Note: $A \ins \Sc^G(A)$.
         \item The \emph{district} of $v$ in $G$:
             \[\Dist^G(v) := \lC w \in G\,|\, \exists \text{ bidirected walk: }
             v \huh v_1 \huh \cdots \huh v_{n-1} \huh w \in G \rC.\]
             Note: $v\in \Dist^G(v)$.
         \item[] The \emph{district} of $A$ in $G$:
             \[\Dist^G(A) := \bigcup_{v \in A} \Dist^G(v).\]
             Note: $A \ins \Dist^G(A)$.
     \end{enumerate}
\end{Def}
\end{defmark}
-/

/-!
## Design choice — typing of the single-node operators

The LN preamble says `v, w ∈ V` and `A ⊆ J ∪ V`, but the operators are
well-defined for `v ∈ J ⊕ V` too — some are just empty when `v ∈ J`
(e.g. `Sib`, `Dist`) and some are non-trivially populated (e.g. `Ch^G(v)`
for `v ∈ J`, because `E ⊆ (J ∪ V) × V` does allow `J`-source edges).
Crucially, the set forms take `A : Set (J ⊕ V)`, so the union form
implicitly extends the single-node operators to `J ⊕ V`.

We therefore take **`v : J ⊕ V` for every single-node operator** and
return `Set (J ⊕ V)`. This is the most usable typing:

* It matches the endpoint typing of `def_3_4`'s `Walk` (needed for `Anc`,
  `Desc`, `Dist`).
* It matches the set version's natural domain `A : Set (J ⊕ V)`, so
  `PaSet`, `ChSet`, `AncSet`, etc. compose cleanly with their node-form
  siblings.
* The LN's notes "`v ∈ Anc^G(v)`", "`v ∈ Desc^G(v)`", "`v ∈ Sc^G(v)`",
  "`v ∈ Dist^G(v)`" only type-check uniformly when `v` ranges over
  `J ⊕ V`, since the result sets live in `J ⊕ V`.

The LN's `v, w ∈ V` preamble is read as a *typical-use* convention, not a
strict typing constraint — the equational content of every bullet remains
the same in either reading, with the `Sum.inr` existentials below
collapsing to `False` exactly when the LN definition would silently fail
to apply (e.g. `Sib^G(j) = ∅` for `j ∈ J` because `\huh` is `V × V`-only).

Membership in the single-node sets uses `tuh` / `huh` / `Walk` /
`DirectedWalk` / `BidirectedWalk` from `def_3_2` and `def_3_4` directly,
with `Sum.inr` existentials wherever a primitive arrow forces an endpoint
into `V`. Set forms use `Set.iUnion` (`⋃ v ∈ A, …`), matching the LN's
`\bigcup_{v \in A}` notation.

### A note for downstream rows depending on `def_3_5`

* `Anc`, `Desc`, `Dist`: the trivial walk `Walk.nil v` is in every shape
  predicate vacuously (the `∀ k ∈ p.stepKinds, _` of
  `DirectedWalk` / `BidirectedWalk` quantifies over the empty
  `stepKinds`). So the LN's reflexivity notes
  (`v ∈ Anc^G(v)`, `v ∈ Desc^G(v)`, `v ∈ Dist^G(v)`) hold by
  construction, with witness `Walk.nil v`. This is not proven here as a
  named lemma — the manager prompt says we should *verify* it falls out,
  not formalise it — but `claim_3_2` (topological order) and other
  downstream rows can use it directly.
* `Sc` reflexivity (`v ∈ Sc^G(v)`) follows from `Anc` and `Desc`
  reflexivity together with `Set.mem_inter_iff`.
* `NonDesc` uses `Set.univ \ G.DescSet A` for the LN's
  `(J ∪ V) \ Desc^G(A)`: in our encoding `J ∪ V = J ⊕ V` (as a
  *type*), so the ambient "all of `J ∪ V`" is `(Set.univ : Set (J ⊕ V))`.
-/

-- def_3_5 (part 1a/14) — parents of a single node `v`.
--
-- LN fragment:
-- /- The set of *parents* of `v` in `G`:
--    `Pa^G(v) := { w ∈ G | w \tuh v ∈ G }`. -/
--
-- Design choice: `G.tuh : (J ⊕ V) → V → Prop` forces the head into `V`,
-- so for an arbitrary `v : J ⊕ V` we read `w \tuh v` as "there exists
-- `v' : V` with `v = Sum.inr v'` and `G.tuh w v'`". When `v ∈ J`, the
-- existential is unsatisfiable and `Pa^G(v) = ∅`, which is the correct
-- behaviour since no edge can have its head in `J`.
def CDMG.Pa (G : CDMG J V) (v : J ⊕ V) : Set (J ⊕ V) :=
  { w | ∃ v' : V, v = Sum.inr v' ∧ G.tuh w v' }

-- def_3_5 (part 1b/14) — parents of a set `A`.
--
-- LN fragment:
-- /- The set of *parents* of `A` in `G`:
--    `Pa^G(A) := \bigcup_{v \in A} Pa^G(v)`. -/
--
-- Direct `Set.iUnion` over `A`; `A` itself lives in `Set (J ⊕ V)`, so
-- the union is taken over the LN's "`A ⊆ J ∪ V`" without modification.
def CDMG.PaSet (G : CDMG J V) (A : Set (J ⊕ V)) : Set (J ⊕ V) :=
  ⋃ v ∈ A, G.Pa v

-- def_3_5 (part 2a/14) — children of a single node `v`.
--
-- LN fragment:
-- /- The set of *children* of `v` in `G`:
--    `Ch^G(v) := { w ∈ G | v \tuh w ∈ G }`. -/
--
-- Mirror of `Pa`: here the *child* `w` is forced into `V` (it sits at
-- the head of `\tuh`), so we take a `Sum.inr` existential on `w`. The
-- *parent* `v` is in `J ⊕ V` — exactly the LN's "for `v ∈ V`" relaxed
-- to "for `v ∈ G`", per the design-choice block above, and matching
-- `def_3_8`'s topological order which uses `Pa`/`Ch` with both endpoints
-- in `J ∪ V`.
def CDMG.Ch (G : CDMG J V) (v : J ⊕ V) : Set (J ⊕ V) :=
  { w | ∃ w' : V, w = Sum.inr w' ∧ G.tuh v w' }

-- def_3_5 (part 2b/14) — children of a set `A`.
--
-- LN fragment:
-- /- The set of *children* of `A` in `G`:
--    `Ch^G(A) := \bigcup_{v \in A} Ch^G(v)`. -/
def CDMG.ChSet (G : CDMG J V) (A : Set (J ⊕ V)) : Set (J ⊕ V) :=
  ⋃ v ∈ A, G.Ch v

-- def_3_5 (part 3/14) — siblings of a single node `v`.
--
-- LN fragment:
-- /- The set of *siblings* of `v` in `G`:
--    `Sib^G(v) := { w ∈ G | v \huh w ∈ G }`. -/
--
-- `huh : V → V → Prop` forces both endpoints into `V`, so `Sib^G(v)`
-- needs `Sum.inr` existentials on *both* `v` and `w`. The LN gives no
-- set-version of `Sib`, so we produce only the single-node form.
--
-- Design choice: we could special-case `v : V` here, but uniform typing
-- across the file is more valuable for downstream rows that iterate
-- over `J ⊕ V`-indexed operators (e.g. a hypothetical `SibSet` derived
-- on demand by `⋃ v ∈ A, G.Sib v`).
def CDMG.Sib (G : CDMG J V) (v : J ⊕ V) : Set (J ⊕ V) :=
  { w | ∃ v' w' : V, v = Sum.inr v' ∧ w = Sum.inr w' ∧ G.huh v' w' }

-- def_3_5 (part 4a/14) — ancestors of a single node `v`.
--
-- LN fragment:
-- /- The set of *ancestors* of `v` in `G`:
--    `Anc^G(v) := { w ∈ G | ∃ directed walk: w \tuh ⋯ \tuh v ∈ G }`.
--    Note: `v ∈ Anc^G(v)`. -/
--
-- We use `def_3_4`'s `Walk` and `DirectedWalk` directly. The
-- existential ranges over `Walk G w v` (walks *from* `w` *to* `v` —
-- matching the arrow direction of the LN). The LN's `v ∈ Anc^G(v)`
-- note is delivered by the trivial walk `Walk.nil v`, which is a
-- `DirectedWalk` vacuously (its `stepKinds` is `[]`).
def CDMG.Anc (G : CDMG J V) (v : J ⊕ V) : Set (J ⊕ V) :=
  { w | ∃ p : Walk G w v, G.DirectedWalk p }

-- def_3_5 (part 4b/14) — ancestors of a set `A`.
--
-- LN fragment:
-- /- The set of *ancestors* of `A` in `G`:
--    `Anc^G(A) := \bigcup_{v \in A} Anc^G(v)`. Note: `A ⊆ Anc^G(A)`. -/
def CDMG.AncSet (G : CDMG J V) (A : Set (J ⊕ V)) : Set (J ⊕ V) :=
  ⋃ v ∈ A, G.Anc v

-- def_3_5 (part 5a/14) — descendants of a single node `v`.
--
-- LN fragment:
-- /- The set of *descendants* of `v` in `G`:
--    `Desc^G(v) := { w ∈ G | ∃ directed walk: v \tuh ⋯ \tuh w ∈ G }`.
--    Note: `v ∈ Desc^G(v)`. -/
--
-- Mirror of `Anc`, with the walk going from `v` to `w` instead. The
-- LN's reflexivity note holds again by `Walk.nil v`.
def CDMG.Desc (G : CDMG J V) (v : J ⊕ V) : Set (J ⊕ V) :=
  { w | ∃ p : Walk G v w, G.DirectedWalk p }

-- def_3_5 (part 5b/14) — descendants of a set `A`.
--
-- LN fragment:
-- /- The set of *descendants* of `A` in `G`:
--    `Desc^G(A) := \bigcup_{v \in A} Desc^G(v)`. Note: `A ⊆ Desc^G(A)`. -/
def CDMG.DescSet (G : CDMG J V) (A : Set (J ⊕ V)) : Set (J ⊕ V) :=
  ⋃ v ∈ A, G.Desc v

-- def_3_5 (part 6/14) — non-descendants of a set `A`.
--
-- LN fragment:
-- /- The set of *non-descendants* of `A` in `G`:
--    `NonDesc^G(A) := (J ∪ V) \ Desc^G(A)`. -/
--
-- In our encoding `J ∪ V = J ⊕ V` *as a type*, so the LN's ambient
-- "`J ∪ V`" is `(Set.univ : Set (J ⊕ V))`. The LN only gives a
-- set-version (no single-node version) — we follow suit.
def CDMG.NonDesc (G : CDMG J V) (A : Set (J ⊕ V)) : Set (J ⊕ V) :=
  (Set.univ : Set (J ⊕ V)) \ G.DescSet A

-- def_3_5 (part 7a/14) — strongly connected component of a single node `v`.
--
-- LN fragment:
-- /- The *strongly connected component* of `v` in `G`:
--    `Sc^G(v) := Anc^G(v) ∩ Desc^G(v)`. Note: `v ∈ Sc^G(v)`. -/
--
-- Direct intersection. Reflexivity (`v ∈ Sc^G(v)`) is immediate from
-- the reflexivity of `Anc` and `Desc` (witnesses: two copies of
-- `Walk.nil v`).
def CDMG.Sc (G : CDMG J V) (v : J ⊕ V) : Set (J ⊕ V) :=
  G.Anc v ∩ G.Desc v

-- def_3_5 (part 7b/14) — strongly connected components of a set `A`.
--
-- LN fragment:
-- /- The (union of) *strongly connected components* of `A` in `G`:
--    `Sc^G(A) := \bigcup_{v \in A} Sc^G(v)`. Note: `A ⊆ Sc^G(A)`. -/
def CDMG.ScSet (G : CDMG J V) (A : Set (J ⊕ V)) : Set (J ⊕ V) :=
  ⋃ v ∈ A, G.Sc v

-- def_3_5 (part 8a/14) — district of a single node `v`.
--
-- LN fragment:
-- /- The *district* of `v` in `G`:
--    `Dist^G(v) := { w ∈ G | ∃ bidirected walk:
--        v \huh v_1 \huh ⋯ \huh v_{n-1} \huh w ∈ G }`.
--    Note: `v ∈ Dist^G(v)`. -/
--
-- We use `def_3_4`'s `Walk` and `BidirectedWalk`. The LN's `n ≥ 0`
-- "walk of length zero" case, which gives `v ∈ Dist^G(v)`, is the
-- trivial walk `Walk.nil v` — vacuously a `BidirectedWalk`. Note that
-- this means `Dist^G(j) = {j}` for any `j ∈ J`: only the trivial walk
-- can witness, because every non-trivial bidirected step forces both
-- endpoints into `V` (the `bid` constructor of `WalkStep`). This is
-- consistent with the LN's intent: `\huh` edges are between `V`-nodes.
def CDMG.Dist (G : CDMG J V) (v : J ⊕ V) : Set (J ⊕ V) :=
  { w | ∃ p : Walk G v w, G.BidirectedWalk p }

-- def_3_5 (part 8b/14) — district of a set `A`.
--
-- LN fragment:
-- /- The *district* of `A` in `G`:
--    `Dist^G(A) := \bigcup_{v \in A} Dist^G(v)`. Note: `A ⊆ Dist^G(A)`. -/
def CDMG.DistSet (G : CDMG J V) (A : Set (J ⊕ V)) : Set (J ⊕ V) :=
  ⋃ v ∈ A, G.Dist v

end Chapter3
end Causality
