import Chapter3_GraphTheory.Section3_1.Acyclicity

-- The verbatim TeX source of the LN definition is reproduced inside the
-- comments below; some of its lines exceed 100 characters. Disable the
-- style linter for this file so the TeX is kept byte-for-byte identical
-- to `Section3_1/main.tex`.
set_option linter.style.longLine false

/-!
# def_3_7 — The named families of graphs (CADMG / DMG / ADMG / CDG / DG / CDAG / DAG)

The seventh LN definition of subsection 3.1 cuts the cake of CDMGs into
the seven classical sub-families that the rest of the lecture notes —
and most of the causality literature — talks about. Each sub-family is a
predicate on a `CDMG J V` saying which of the three orthogonal
restrictions hold:

* acyclicity (`G.IsAcyclic`, from `def_3_6`),
* "no input nodes" (`IsEmpty J`, see the design-choice notes below),
* "no bidirected edges" (`G.L = ∅`).

The seven LN bullets are exactly the seven non-trivial combinations of
those three switches (the "all off" case is just an unrestricted CDMG,
so it has no name of its own).

We collect all seven predicates in one file because:

* they are tiny (one-line conjunctions),
* they are introduced together in a single `defmark` block in the LN, and
* every later subsection that needs one of them is overwhelmingly likely
  to need at least two, so splitting would only create more imports.

We share the `Causality.Chapter3` namespace with `def_3_1`–`def_3_6`.
-/

namespace Causality
namespace Chapter3

variable {J V : Type*}

/-
Source (verbatim from `Section3_1/main.tex`, under `% def_3_7`):

\begin{defmark}
\begin{Def}
    A  Conditional Directed Mixed Graph (CDMG)  $G=(J,V,E,L)$  is called:
   \begin{enumerate}
       \item Conditional Acyclic Directed Mixed Graph (CADMG) if $G$ is acyclic.
       \item Directed Mixed Graph (DMG) if $J = \emptyset$.
       \item Acyclic Directed Mixed Graph (ADMG) if $G$ is acyclic and $J = \emptyset$.
       \item Conditional Directed Graph (CDG) if $L = \emptyset$.
       \item Directed Graph (DG) if $J = \emptyset$ and $L = \emptyset$.
       \item Conditional Directed Acyclic Graph (CDAG) if $G$ is acyclic and $L = \emptyset$.
       \item Directed Acyclic Graph (DAG) if $G$ is acyclic, $J=\emptyset$ and $L = \emptyset$.
   \end{enumerate}
\end{Def}
\end{defmark}
-/

-- Shared design-choice notes for the seven predicates below. (Repeating
-- these in full above each `def` would be noisy; we reference them by
-- name from each predicate.)
--
-- Design choice — "G is acyclic" → `G.IsAcyclic`. This is the predicate
-- introduced in `def_3_6` (see `Acyclicity.lean`). It is itself a `Prop`,
-- so plugging it into a conjunction is straightforward.
--
-- Design choice — "$J = \emptyset$" → `IsEmpty J`, *not* `J = (∅ : …)`.
-- Per `def_3_1` the vertex set `J` is encoded as a Lean **type
-- parameter**, not as a `Set` of some ambient type. The LN's "$J =
-- \emptyset$" therefore translates to "the type `J` has no inhabitants",
-- which Lean spells `IsEmpty J`. The alternative `J = ∅` does not even
-- typecheck: `J : Type*`, not a set. Mathlib's `IsEmpty` is the canonical
-- typeclass-shaped way to express type-level emptiness and is the form
-- every downstream lemma (e.g. recovering a non-conditional graph from a
-- conditional one by dropping `J`) will want to pattern match on.
--
-- Design choice — "$L = \emptyset$" → `G.L = ∅`. In `def_3_1` we model
-- `L` as a literal `Set (V × V)` field of `CDMG`, *not* as a type, so
-- here the LN's "$L = \emptyset$" really does mean "the set `G.L` is the
-- empty set". This is the direct translation. We deliberately do *not*
-- write `IsEmpty G.L` (which would talk about the subtype of elements of
-- `G.L`): it would force callers to coerce between "no edges" as a set
-- statement and "no edges" as a type statement for no benefit.
--
-- Design choice — `Prop`, not `Type`, for each predicate. These are
-- properties of a CDMG, not data; downstream uses only ever ask *whether*
-- a graph is e.g. a DAG, never to inspect a witness.

-- def_3_7 (part 1/7) — CADMG.
-- LN bullet: "Conditional Acyclic Directed Mixed Graph (CADMG) if $G$ is acyclic."
-- One switch on: acyclicity. `J` and `L` are unrestricted (the "C" and
-- the "M" of CADMG).
def CDMG.IsCADMG (G : CDMG J V) : Prop :=
  G.IsAcyclic

-- def_3_7 (part 2/7) — DMG.
-- LN bullet: "Directed Mixed Graph (DMG) if $J = \emptyset$."
-- One switch on: no input nodes. `L` is unrestricted (the "M"); cycles
-- are still allowed (no "A").
def CDMG.IsDMG (_G : CDMG J V) : Prop :=
  IsEmpty J

-- def_3_7 (part 3/7) — ADMG.
-- LN bullet: "Acyclic Directed Mixed Graph (ADMG) if $G$ is acyclic and $J = \emptyset$."
-- Two switches on: acyclicity *and* no input nodes. `L` is still
-- unrestricted (the "M").
def CDMG.IsADMG (G : CDMG J V) : Prop :=
  G.IsAcyclic ∧ IsEmpty J

-- def_3_7 (part 4/7) — CDG.
-- LN bullet: "Conditional Directed Graph (CDG) if $L = \emptyset$."
-- One switch on: no bidirected edges. `J` is unrestricted (the "C");
-- cycles are still allowed (no "A").
def CDMG.IsCDG (G : CDMG J V) : Prop :=
  G.L = ∅

-- def_3_7 (part 5/7) — DG.
-- LN bullet: "Directed Graph (DG) if $J = \emptyset$ and $L = \emptyset$."
-- Two switches on: no input nodes *and* no bidirected edges. Cycles are
-- still allowed (no "A").
def CDMG.IsDG (G : CDMG J V) : Prop :=
  IsEmpty J ∧ G.L = ∅

-- def_3_7 (part 6/7) — CDAG.
-- LN bullet: "Conditional Directed Acyclic Graph (CDAG) if $G$ is acyclic and $L = \emptyset$."
-- Two switches on: acyclicity *and* no bidirected edges. `J` is
-- unrestricted (the "C").
def CDMG.IsCDAG (G : CDMG J V) : Prop :=
  G.IsAcyclic ∧ G.L = ∅

-- def_3_7 (part 7/7) — DAG.
-- LN bullet: "Directed Acyclic Graph (DAG) if $G$ is acyclic, $J=\emptyset$ and $L = \emptyset$."
-- All three switches on: acyclicity, no input nodes, no bidirected
-- edges. The most restrictive of the seven, and the workhorse of
-- classical causal graphical models.
def CDMG.IsDAG (G : CDMG J V) : Prop :=
  G.IsAcyclic ∧ IsEmpty J ∧ G.L = ∅

end Chapter3
end Causality
