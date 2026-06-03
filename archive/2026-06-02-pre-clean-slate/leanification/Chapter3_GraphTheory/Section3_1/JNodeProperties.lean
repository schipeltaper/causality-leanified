import Chapter3_GraphTheory.Section3_1.EdgeRelations

-- TeX proof: claim_3_1_proof_JNodeProperties.tex

/-!
# Properties of input nodes (`J`) in a CDMG (claim_3_1)

This file formalises the lecture notes' remark immediately following
the definition of CDMGs (def_3_1) and their notation (def_3_2). The
remark spells out three structural restrictions imposed on the input
node set `J` by `def_3_1`'s `E_subset`, `L_subset`, `L_irrefl`, and
`disjoint_JV` fields:

  1. No edge can have an arrowhead at an input node — written
     `j \hus v ∉ G` in the LN, `¬ CDMG.hus G j v` here.
  2. Any directed edge whose tail is an input node must target an
     output node (`w ∈ V`).
  3. No two input nodes are adjacent.

These three lemmas are reused heavily throughout the rest of
chapter 3: every later definition that quantifies over `J ∪ V`
(walks `def_3_4`, parents/ancestors `def_3_5`, topological orders
`def_3_8`, predecessors `def_3_9`) eventually needs one of them to
rule out a spurious "edge ending at an input" case. They are
exactly the "already-derivable from def_3_1" sanity checks the LN
flags so the reader can recognise them on sight in later proofs.

## References

  * `lecture-notes/lecture_notes/graphs.tex`, lines 84-89 (the
    `\begin{claimmark}\begin{Rem}…\end{Rem}\end{claimmark}` block
    immediately after `not-cdmg`).
  * `def_3_1` — `Chapter3_GraphTheory.Section3_1.CDMG`: the `CDMG`
    structure with its `E_subset`, `L_subset`, `L_irrefl`,
    `disjoint_JV` fields.
  * `def_3_2` — `Chapter3_GraphTheory.Section3_1.CDMGNotation`:
    `hus`, `tuh`.
  * `def_3_3` — `Chapter3_GraphTheory.Section3_1.EdgeRelations`:
    `Adjacent`.

The three theorems below have bodies `sorry`; the proofs are the
job of a separate worker once the proof tex subfile is populated.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

-- claim_3_1 (part 1/3)
-- title: JNodeProperties -- no arrowheads into an input node
--
-- For any input node `j ∈ G.J` and any vertex `v : α`, there is no
-- edge with an arrowhead at `j`. The LN writes this as
-- `j \hus v \notin G`, which in our notation is `¬ hus G j v` --
-- recalling that `hus G j v` is "arrowhead at the first argument",
-- i.e. either `hut G j v` (a directed edge `j ← v`) or `huh G j v`
-- (a bidirected edge `j ↔ v`). The fact follows from `E_subset`
-- (every directed-edge target lives in `V`) and `L_subset`
-- (bidirected edges live in `V × V`), combined with `disjoint_JV`
-- to derive `j ∉ V` from `j ∈ J`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`:

\begin{Rem}
With the notations \ref{not-cdmg} the restrictions in definition
\ref{def-cdmg} mean that the nodes $j \in J$ will not have any
arrowheads pointing towards them: $ j \hus v \notin G$. Nodes
$j \in J$ can only point towards nodes $v \in V$: edges $j \tuh v$
are allowed. Furthermore, no two nodes in $J$ are adjacent.
\end{Rem}
-/
--
-- ## Design choice
--
-- * **Three separate theorems, not one conjunction.** The LN
--   bundles three independent sub-statements into one prose
--   paragraph for readability, but in Lean each one is wanted as a
--   *separately citable* lemma. A downstream proof using "directed
--   edges out of J target V" (part 2) almost never needs "no
--   arrowhead at J" (part 1) on the same line. Splitting them
--   into three theorems keeps each one a clean one-liner at the
--   use site and avoids the boilerplate of
--   `obtain ⟨h₁, h₂, h₃⟩ := …`.
--
-- * **`v` explicit.** The LN reads "for any $v$, $j \hus v \notin
--   G$": the universal quantifier is outside `hus`. Making `v`
--   explicit keeps the call-site phrasing `no_arrowhead_into_input
--   hj v` aligned with that reading. Callers that have only
--   `h : hus G j v` and want a contradiction will write
--   `no_arrowhead_into_input hj v h` directly. The alternative
--   (implicit `v`) would force the caller to either provide it
--   via `@`-syntax or let Lean unify against `h`'s type, which is
--   less readable.
--
-- * **`G` implicit, inferred from `hj : j ∈ G.J`.** Standard for
--   "fix a graph, then state a property of it" lemmas.
--
-- * **Phrased in terms of `hus`, not raw `G.E` / `G.L`
--   membership.** The LN's notation `j \hus v` is the prose-level
--   atom of the claim; downstream proofs that want to derive a
--   contradiction from an edge of either kind will already be
--   working with `hus`, `suh`, or `Adjacent`. Spelling the
--   conclusion in terms of `hus` lets them apply this lemma
--   without an extra unfolding step.
theorem no_arrowhead_into_input
    {G : CDMG α} {j : α} (hj : j ∈ G.J) (v : α) :
    ¬ hus G j v := by
  intro hhus
  have hjV : j ∈ G.V := by
    rcases hhus with h_hut | h_huh
    · exact (G.E_subset h_hut).2
    · exact (G.L_subset h_huh).1
  exact Set.disjoint_left.mp G.disjoint_JV hj hjV

-- claim_3_1 (part 2/3)
-- title: JNodeProperties -- directed edges out of J target V
--
-- For any input node `j ∈ G.J` and any vertex `w` such that there
-- is a directed edge `j \tuh w` in `G`, the target `w` lies in
-- `G.V`. The LN phrases this as "edges $j \tuh v$ are allowed
-- [only when $v \in V$]"; we state it as the implication.
-- Follows from `E_subset : G.E ⊆ (J ∪ V) ×ˢ V`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`:

\begin{Rem}
With the notations \ref{not-cdmg} the restrictions in definition
\ref{def-cdmg} mean that the nodes $j \in J$ will not have any
arrowheads pointing towards them: $ j \hus v \notin G$. Nodes
$j \in J$ can only point towards nodes $v \in V$: edges $j \tuh v$
are allowed. Furthermore, no two nodes in $J$ are adjacent.
\end{Rem}
-/
--
-- ## Design choice
--
-- * **Phrased as `tuh G j w → w ∈ G.V`, not as raw
--   `(j, w) ∈ G.E → w ∈ G.V`.** The LN's notation `j \tuh v` is
--   the prose-level atom (def_3_2); stating the conclusion in
--   terms of `tuh` lines up with what callers actually have in
--   hand. Unfolding to `(j, w) ∈ G.E` is one rewrite away via the
--   `tuh` definition, but that's the proof's business, not the
--   statement's.
--
-- * **No need for a separate "no `hut G j w` for `w ∈ J`" lemma.**
--   `hut G j w` is `(w, j) ∈ G.E`, which by `E_subset` forces
--   `j ∈ V`, contradicting `j ∈ J` via `disjoint_JV`. That's
--   exactly part (1) above specialised to the `hut`-disjunct of
--   `hus`, so it is already a consequence of
--   `no_arrowhead_into_input` and does not warrant its own
--   theorem.
--
-- * **`hj` explicit, `w` implicit.** `hj : j ∈ G.J` is the
--   side-condition the caller is providing; `w` is determined by
--   the edge hypothesis `h : tuh G j w` and so can be left to
--   unification. Note that the *proof* below does not use `hj` --
--   the inclusion `E ⊆ (J ∪ V) ×ˢ V` is strong enough on its own
--   to force `w ∈ V`. We still take `hj` as an explicit argument
--   because the lemma is prose-named for input nodes: removing
--   `hj` would broaden the statement to "the target of any
--   directed edge lies in `V`", which is a different lemma. The
--   `set_option` below silences the unused-variable linter for
--   exactly this case.
set_option linter.unusedVariables false in
theorem input_edge_target_mem_V
    {G : CDMG α} {j : α} (hj : j ∈ G.J) {w : α}
    (h : tuh G j w) : w ∈ G.V :=
  (G.E_subset h).2

-- claim_3_1 (part 3/3)
-- title: JNodeProperties -- no two input nodes are adjacent
--
-- For any two input nodes `j₁, j₂ ∈ G.J`, there is no edge of any
-- kind between them. By def_3_3, `Adjacent G j₁ j₂` is the prose
-- name for `sus G j₁ j₂`, which is the disjunction of
-- `tuh G j₁ j₂`, `hut G j₁ j₂`, and `huh G j₁ j₂`. Each disjunct
-- is forbidden by the structural restrictions of def_3_1:
--   * `tuh G j₁ j₂` forces `j₂ ∈ V` (via `E_subset`),
--     contradicting `j₂ ∈ J` and `disjoint_JV`.
--   * `hut G j₁ j₂` symmetrically forces `j₁ ∈ V`.
--   * `huh G j₁ j₂` forces both `j₁ ∈ V` and `j₂ ∈ V` (via
--     `L_subset`).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`:

\begin{Rem}
With the notations \ref{not-cdmg} the restrictions in definition
\ref{def-cdmg} mean that the nodes $j \in J$ will not have any
arrowheads pointing towards them: $ j \hus v \notin G$. Nodes
$j \in J$ can only point towards nodes $v \in V$: edges $j \tuh v$
are allowed. Furthermore, no two nodes in $J$ are adjacent.
\end{Rem}
-/
--
-- ## Design choice
--
-- * **Phrased with `Adjacent`, not `sus`.** def_3_3 introduces
--   `Adjacent` as the prose-level name for the LN's "adjacent in
--   $G$"; the LN sentence "no two nodes in $J$ are adjacent"
--   literally uses that word. Stating the conclusion in terms of
--   `Adjacent` matches the LN phrasing and lets downstream callers
--   keep their proofs at the prose layer rather than unfolding to
--   `sus`. `Adjacent` is definitionally `sus` (see
--   `EdgeRelations.adjacent_iff`), so this choice does not change
--   the proof obligation.
--
-- * **Both `j₁` and `j₂` implicit.** Both are pinned down by the
--   adjacency hypothesis the caller would feed into the negation
--   (or by the goal they are trying to close), so making either
--   explicit would just be call-site noise.
--
-- * **No `j₁ ≠ j₂` hypothesis.** The LN's "no two nodes" reads as
--   "for any two (possibly equal) input nodes, they are not
--   adjacent". When `j₁ = j₂`, `Adjacent G j₁ j₁` is still false:
--   the `tuh` / `hut` disjuncts both reduce to `(j₁, j₁) ∈ G.E`,
--   which by `E_subset` would force `j₁ ∈ V` (contradicting
--   `j₁ ∈ J` via `disjoint_JV`); the `huh` disjunct is ruled out
--   directly by `L_irrefl`. So adding `j₁ ≠ j₂` would weaken the
--   lemma unnecessarily.
theorem input_nodes_not_adjacent
    {G : CDMG α} {j₁ j₂ : α}
    (h₁ : j₁ ∈ G.J) (h₂ : j₂ ∈ G.J) :
    ¬ Adjacent G j₁ j₂ := by
  intro hAdj
  rcases hAdj with h_tuh | h_hut | h_huh
  · exact no_arrowhead_into_input h₂ j₁ (Or.inl h_tuh)
  · exact no_arrowhead_into_input h₁ j₂ (Or.inl h_hut)
  · exact no_arrowhead_into_input h₁ j₂ (Or.inr h_huh)

end CDMG

end Causality
