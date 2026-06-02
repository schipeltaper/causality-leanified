import Chapter3_GraphTheory.Section3_1.WalkPredicates

/-!
# Acyclicity of a CDMG (def 3.6)

This file formalises *definition 3.6* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`):
a Conditional Directed Mixed Graph is *acyclic* exactly when no node
admits a non-trivial directed walk back to itself.

The predicate `Causality.CDMG.IsAcyclic G` sits one floor above the
walk data layer of def_3_4: it quantifies over every node `v ∈ G` and
denies the existence of any directed walk `π : Walk G v v` whose
`length` is at least one. The two ingredients --
`Walk.IsDirected` from `WalkPredicates.lean` (def_3_4 item 2) and
`Walk.length` from `Walks.lean` (def_3_4 item 1) -- already capture
the LN's notions of "directed walk" and "non-trivial" exactly, so the
formalisation is a one-liner on top of them.

## Where this gets used downstream

Acyclicity is a recurring side condition throughout the lecture notes;
every later chapter pattern-matches against it:

* **def_3_7** -- the seven CDMG-shape names (CADMG, ADMG, CDG, DG,
  CDAG, DAG) are defined by combining `IsAcyclic` with `J = ∅` and/or
  `L = ∅`.
* **claim_3_2** -- "$G$ is acyclic iff $G$ has a topological order"
  (`AcyclicIffTopologicalOrder.lean`). The `←` direction unfolds
  `IsAcyclic` and derives a contradiction from `v_0 < v_1 < \cdots <
  v_n = v_0` along the witnessing directed walk; the `→` direction
  builds a topological order by repeatedly selecting a parent-free
  node, using `IsAcyclic` to keep the induced subgraphs cycle-free.
* **chapter 4 (CBNs)** -- causal Bayesian networks factorise along a
  DAG / CADMG, so the underlying CDMG is required acyclic.
* **chapter 5 (do-calculus)** -- the soundness of do-calculus rules is
  proved on acyclic graphs (`claim_3_8` shows acyclicity is preserved
  under hard interventions, so the algebra closes).
* **chapters 8 -- 10 (SCMs / iSCMs)** -- the unique-solution theory of
  structural causal models with inputs proceeds by recursion on a
  topological order of the underlying CDMG, which exists exactly when
  the graph is acyclic (claim_3_2 again).
* **chapter 11 -- 16 (causal discovery)** -- the FCI / IC algorithms
  and their soundness theorems assume an underlying acyclic ground
  truth (ADMG / CADMG), so every reduction goes through `IsAcyclic`.

The downstream uses are *all* via the LN's "$G$ is acyclic" prose,
which is exactly what the dot-projection `G.IsAcyclic` reads as. The
single Prop-valued predicate here is therefore the entry point for
every later acyclicity precondition in the Lean formalisation.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

-- def_3_6
-- title: Acyclicity
--
-- A CDMG `G` is *acyclic* iff no node has a non-trivial directed walk
-- back to itself. Concretely: for every `v ∈ G` (i.e. `v ∈ G.J ∪
-- G.V`), there is no `π : Walk G v v` with `π.IsDirected` and
-- `1 ≤ π.length`.
--
-- The three building blocks all line up with the LN vocabulary:
--   * `v ∈ G` -- the `Membership α (CDMG α)` instance from def_3_2
--     (`CDMGNotation.lean`) defines `v ∈ G` to mean
--     `v ∈ G.J ∪ G.V`, so the LN's shorthand "$v \in G$" lifts to
--     this `∀ v ∈ G, ...` quantifier verbatim.
--   * `Walk G v v` -- the umbrella walk inductive from def_3_4 item 1
--     (`Walks.lean`), with both endpoints `v`. The trivial walk
--     `Walk.nil v : Walk G v v` always exists and contributes
--     `length = 0`; non-trivial directed walks from `v` to itself
--     are the witnesses that acyclicity forbids.
--   * `π.IsDirected ∧ 1 ≤ π.length` -- the LN's "non-trivial directed
--     walk". `Walk.IsDirected` from def_3_4 item 2
--     (`WalkPredicates.lean`) requires every step to be a `forward`
--     step (LN's `\tuh`), matching "all arrowheads point in the
--     direction of $w$". `1 ≤ π.length` rules out the trivial walk;
--     see the design-choice block below for why we use length rather
--     than `π ≠ Walk.nil v`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.6):

\begin{defmark}
\begin{Def}[Acyclicity]
    \label{def-acylic}
    A  CDMG  $G=(J,V,E,L)$  is called \emph{acyclic} if there does not exist
    any non-trivial directed walk from $v$ to itself in $G$ for any node $v \in G$.
\end{Def}
\end{defmark}
-/
--
-- ## Design choice
--
-- * **Namespace `Causality.CDMG.IsAcyclic`, dot-projection `G.IsAcyclic`.**
--   The LN's prose -- "the CDMG $G$ is acyclic" -- treats acyclicity
--   as a property *of* the graph. Placing the predicate in the
--   `CDMG` namespace means downstream callers write `G.IsAcyclic`,
--   which reads as "$G$ is acyclic" and matches every later sentence
--   in the LN that invokes it (def_3_7's "if $G$ is acyclic",
--   claim_3_2's "$G$ is acyclic iff ...", claim_3_8's "if $G$ is
--   acyclic then $G_{\doit(W)}$ is acyclic", etc.). The convention
--   parallels the existing CDMG-level predicates in this folder --
--   `CDMG.Adjacent`, `CDMG.EdgeInto`, `CDMG.EdgeOutOf` from
--   `EdgeRelations.lean` and `CDMG.tuh` / `CDMG.hut` / ... from
--   `CDMGNotation.lean` -- so a reader familiar with those names
--   recognises this one on sight. The alternative `Causality.IsAcyclic
--   G` (top-level) would be slightly more compact but disconnect
--   acyclicity from the CDMG family of operators and read less like
--   the LN's "$G$ is ..." prose.
--
-- * **`v ∈ G` quantifier, not `v ∈ G.J ∪ G.V`.** Both unfold to the
--   same proposition via the `Membership α (CDMG α)` instance from
--   def_3_2 (`CDMG.mem_iff` is `Iff.rfl`). We prefer the `v ∈ G`
--   form because the LN literally writes "any node $v \in G$", and
--   the project's convention -- documented in `FamilyDirect.lean`
--   and used uniformly in all four `Family*.lean` operators -- is to
--   mirror that prose. Callers who need to peel `v ∈ G` back to
--   `v ∈ G.J ∪ G.V` reach for `simp [CDMG.mem_iff]` or
--   `Set.mem_union`.
--
-- * **"Non-trivial" as `1 ≤ π.length`, not `π ≠ Walk.nil v` or
--   `π.length ≠ 0`.** All three are propositionally equivalent (the
--   trivial walk is the unique walk of length zero from `v` to
--   itself once you discharge structural equality), but
--   `1 ≤ π.length` is the LN's own framing: def_3_4 parameterises
--   walks by `n ≥ 0` and `Walks.lean:294`'s docstring already
--   commits the project to "non-trivial directed walk means
--   `length ≥ 1`". Choosing `1 ≤ π.length` keeps the predicate
--   compositional with later length-based arguments -- claim_3_2's
--   `→` proof inducts on walk length, chapter 16's bifurcation
--   bounds compare `π.length` with `support.length`, etc. The
--   alternative `π ≠ Walk.nil v` would force an awkward `Walk.nil`
--   case distinction at every use site and is *not* equivalent
--   without the endpoint match `v = v` -- for `π : Walk G v w` with
--   `v ≠ w`, length zero is impossible structurally, but for
--   `π : Walk G v v` (our case) one must still produce the equality
--   witness. The `Nat`-level form sidesteps that bookkeeping.
--
-- * **`Prop`, not `Type _` (no `IsAcyclic` *witness* type).** The LN
--   uses acyclicity only as a precondition -- "if $G$ is acyclic,
--   then ..." -- never as data carrying constructive information.
--   A `Type _`-valued formulation would force every later "$G$ is
--   acyclic" hypothesis to carry an explicit witness around, which
--   would clutter signatures and serve no proof-theoretic purpose
--   (the predicate is decidable only in restricted settings anyway,
--   so the constructive content would not be useful). `Prop` matches
--   how acyclicity is used downstream and matches Mathlib's
--   `SimpleGraph.IsAcyclic` precedent.
--
-- * **Inline conjunction, no helper `IsNonTrivialDirectedCycle`.**
--   The inner predicate `π.IsDirected ∧ 1 ≤ π.length` reads
--   cleanly inline and is used in only this one place; introducing
--   a named alias would add a layer of unfolding for downstream
--   simp/rewrite steps without compensating readability gains. If a
--   later row repeatedly references the same conjunction (e.g.
--   claim_3_2 might want to name "directed cycle through $v$"),
--   that row can introduce the helper locally.
--
-- * **No simp characterisation lemma.** The defining body is the
--   shape downstream callers want to reason against; an
--   `isAcyclic_iff` lemma would just be `Iff.rfl` and offer no
--   rewriting power. The negation form `¬ G.IsAcyclic ↔ ∃ v ∈ G,
--   ∃ π : Walk G v v, π.IsDirected ∧ 1 ≤ π.length` (via
--   `push_neg`) is a one-line derivation any caller can do; we
--   leave it for the row that first needs it (most likely
--   `AcyclicIffTopologicalOrder.lean` for claim_3_2's `←`
--   direction) rather than pre-emptively committing this file to a
--   choice between bundled-`Exists` / unbundled-`bex` shapes.
/-- The CDMG `G` is *acyclic*: no node admits a non-trivial directed
walk to itself. Mirrors `lecture-notes/lecture_notes/graphs.tex` def
3.6 (`\label{def-acylic}`) verbatim, with "non-trivial" read as
`1 ≤ π.length` per `Walks.lean`'s `Walk.length` doc. The trivial walk
`Walk.nil v` is excluded by the `1 ≤ π.length` conjunct (it has
length zero), so a witness against acyclicity is genuinely a
directed cycle through `v` of one or more steps. Used as the
precondition for claim_3_2 (`AcyclicIffTopologicalOrder`), def_3_7
(graph type names), and pervasively in chapters 4 -- 16. -/
def IsAcyclic (G : CDMG α) : Prop :=
  ∀ v ∈ G, ¬ ∃ π : Walk G v v, π.IsDirected ∧ 1 ≤ π.length

end CDMG

end Causality
