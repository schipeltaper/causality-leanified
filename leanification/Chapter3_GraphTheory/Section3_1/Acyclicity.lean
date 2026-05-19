import Chapter3_GraphTheory.Section3_1.Walks

-- The verbatim TeX source of the LN definition is reproduced inside the
-- comments below; some of its lines exceed 100 characters. Disable the
-- style linter for this file so the TeX is kept byte-for-byte identical
-- to `Section3_1/main.tex`.
set_option linter.style.longLine false

/-!
# def_3_6 — Acyclicity

The sixth LN definition of subsection 3.1 introduces *acyclicity* of a CDMG:
the absence of any non-trivial directed walk from a node back to itself.
This concept is the gateway to `def_3_7` (CADMG / ADMG / DAG / …),
`def_3_8` (topological order), and `claim_3_2` (acyclic ⇔ has a topological
order), so we give it its own file rather than bolting it onto `Walks.lean`.

We share the `Causality.Chapter3` namespace with `def_3_1`–`def_3_5`.
-/

namespace Causality
namespace Chapter3

variable {J V : Type*}

/-
Source (verbatim from `Section3_1/main.tex`, under `% def_3_6`):

\begin{defmark}
\begin{Def}[Acyclicity]
    \label{def-acylic}
    A  CDMG  $G=(J,V,E,L)$  is called \emph{acyclic} if there does not exist
    any non-trivial directed walk from $v$ to itself in $G$ for any node $v \in G$.
\end{Def}
\end{defmark}
-/

-- def_3_6 — acyclicity of a CDMG.
--
-- LN fragment:
-- /- A CDMG `G = (J, V, E, L)` is called *acyclic* if there does not exist
--    any non-trivial directed walk from `v` to itself in `G` for any node
--    `v ∈ G`. -/
--
-- A `CDMG` `G` is `IsAcyclic` exactly when, for every node `v : J ⊕ V` and
-- every walk `p : Walk G v v`, if `p` is a directed walk
-- (`G.DirectedWalk p`, see `def_3_4` part 2/6) then `p` is the trivial
-- walk `Walk.nil v`. Equivalently: there is no non-trivial directed walk
-- from any `v` back to itself.
--
-- Design choice — `Prop`, not `Type`. Acyclicity is a property of the
-- graph, not data carried by it; every later use we anticipate
-- (`def_3_7`'s CADMG/ADMG/DAG predicates, `claim_3_2`'s ⇔ with topological
-- order, `def_3_8` topological orders themselves) only needs to know
-- *that* `G` is acyclic, not to inspect a witness of acyclicity.
--
-- Design choice — quantify `v : J ⊕ V`. The LN says "for any node
-- `v ∈ G`", and by `def_3_2` the nodes of `G` are exactly `J ∪ V`, which
-- we encode as `J ⊕ V` (matching the index types of `Walk` and the rest
-- of the section). Restricting to `v : V` would drop `J`-rooted self-loops
-- and would not match the LN.
--
-- Design choice — encode "non-trivial" by the universal form
-- `∀ p, DirectedWalk p → p = Walk.nil v` rather than the literal negated
-- existential `¬ ∃ v p, DirectedWalk p ∧ p ≠ Walk.nil v`. The two are
-- classically equivalent (and in fact `Iff` in Lean's logic for any
-- `Walk`), but the ∀-form is what every downstream proof actually wants
-- to apply: "I have a directed walk back to `v`, therefore it must be
-- trivial". Using `p = Walk.nil v` (rather than e.g. `p.stepKinds = []`
-- or `p.stepKinds.length = 0`) is the most direct rendering of LN's
-- "trivial walk" — the `Walk.nil` constructor *is* the trivial walk by
-- construction (`def_3_4` part 1b/6).
def CDMG.IsAcyclic (G : CDMG J V) : Prop :=
  ∀ (v : J ⊕ V) (p : Walk G v v), G.DirectedWalk p → p = Walk.nil v

end Chapter3
end Causality
