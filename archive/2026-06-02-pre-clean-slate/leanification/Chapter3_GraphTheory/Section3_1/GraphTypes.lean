import Chapter3_GraphTheory.Section3_1.Acyclicity

/-!
# Names for special CDMGs (def 3.7)

This file formalises *definition 3.7* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`): a glossary
of seven *names* the LN attaches to a Conditional Directed Mixed
Graph `G = (J, V, E, L)`, obtained by combining at most three side
conditions:

  * `G.IsAcyclic` -- the acyclicity predicate of def_3_6 (no node
    admits a non-trivial directed walk back to itself).
  * `G.J = ∅` -- the graph has no input nodes.
  * `G.L = ∅` -- the graph has no bidirected edges.

The general CDMG of def_3_1 imposes *none* of these. The seven graph
types listed in the LN are exactly the named combinations of these
predicates that the rest of the notes actually use:

  | name  | acyclic | J = ∅ | L = ∅ |
  | ----- | ------- | ----- | ----- |
  | CADMG | ✓       |       |       |
  | DMG   |         | ✓     |       |
  | ADMG  | ✓       | ✓     |       |
  | CDG   |         |       | ✓     |
  | DG    |         | ✓     | ✓     |
  | CDAG  | ✓       |       | ✓     |
  | DAG   | ✓       | ✓     | ✓     |

(The eighth combination -- "no side conditions" -- is a plain CDMG
and so is not given a separate name by the LN.)

## Where this gets used downstream

Each of the seven names returns later in the notes as the precondition
of an entire result family; the LN consistently phrases preconditions
as "$G$ is a [acronym]". A few load-bearing examples (see
`lecture-notes/lecture_notes/main.tex` for the full chapter order):

* **chapter 4 (CBNs, `causal_bayesian_networks.tex`)** -- L-CBNs
  factorise along a *CDAG* in the latent-free case (cf. the LN's
  "Consider a causal Bayesian network with input variables with CDAG
  $G=(J,V,E)$") and along a *CADMG* once latents are marginalised
  (cf. "observational CADMG of $M$"). Both names are required side by
  side: a CADMG is a CDAG plus the possibility of bidirected edges.
* **chapter 5 (do-calculus, `do-calculus.tex`)** -- the do-calculus
  rules and their soundness theorem assume an *observational CADMG*
  ("Let $G=(J,V,E,L)$ be a CADMG and $B \subseteq V$ ..."). The
  acyclicity half of CADMG is what makes the do-operator algebra
  close (cf. `claim_3_8` in section 3.2: hard interventions preserve
  acyclicity).
* **chapter 6 (id-algorithm, `id-algorithm.tex`)** -- identification
  results take a CADMG and an output set `C ⊆ V`; every
  intermediate construction (the latent projection, the c-component
  decomposition, ...) is phrased on CADMGs.
* **chapters 8 -- 10 (SCMs / iSCMs, `scms*.tex`)** -- structural
  causal models specialise their underlying CDMG by either dropping
  bidirected edges (CDG / CDAG when acyclic) or assuming acyclicity
  (CADMG / ADMG when `J = ∅`).
* **chapters 11 -- 16 (causal discovery, `fci.tex` etc.)** -- the FCI
  algorithm and its soundness proofs take an *ADMG* as the ground
  truth; mixed-graph PAGs are equivalence classes of ADMGs.

So all seven names see real use later, and the LN's prose "$G$ is a
[acronym]" is what we want every later precondition to read as in
Lean. The `Is`-prefixed `Prop` predicates defined below give exactly
that:

  `theorem foo (G : CDMG α) (hG : G.IsCADMG) : ...`

mirrors

  "let $G$ be a CADMG. Then ..."

verbatim.

## Where the LN block lives

Verbatim source (entire definition, including the `defmark` wrapper):

```latex
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
```

Per-item verbatim quotes appear above each `def` below; the shared
preamble ("A CDMG $G = (J,V,E,L)$ is called: ...") is only repeated
here at the top, not seven times.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

-- def_3_7 (shared design block for items 1 -- 7)
--
-- ## Design choice
--
-- The seven items below share enough structure that a single design
-- block covers them all -- they are not independent choices, they are
-- one choice applied seven times.
--
-- * **`Prop`-valued predicates, not subtypes or new structures.**
--   Throughout chapters 4 -- 16 the LN takes an arbitrary CDMG `G`
--   and adds side conditions like "$G$ is acyclic" or "$J = \emptyset$"
--   as *hypotheses* on theorems, not as part of the ambient graph
--   type. A subtype `{G : CDMG α // G.IsAcyclic}` (or a parallel
--   `structure CADMG` with the acyclicity field bundled in) would
--   force every later signature through a coercion `↑G : CDMG α`,
--   break compatibility with the existing `G.IsAcyclic` predicate
--   from def_3_6, and not match the LN's own framing -- the LN
--   treats "CADMG", "DAG", etc. as *names attached to a CDMG that
--   happens to satisfy certain conditions*, not as separate
--   mathematical objects. `Prop` predicates are the lightest possible
--   encoding that supports the LN's "if $G$ is acyclic, then ..."
--   prose verbatim.
--
-- * **In the `Causality.CDMG` namespace, used via dot-projection.**
--   Every later occurrence in the LN reads as "$G$ is a CADMG", "$G$
--   is a DAG", etc. Placing the predicates inside the `CDMG`
--   namespace turns each name into a dot-projection: `G.IsCADMG`,
--   `G.IsDAG`, ..., matching the LN's "$G$ is ..." prose word for
--   word. This is the same convention already used by
--   `G.IsAcyclic` (def_3_6), `G.tuh` / `G.hut` / `G.huh`
--   (`CDMGNotation.lean`, def_3_2), `G.Adjacent`, `G.EdgeInto`,
--   `G.EdgeOutOf` (`EdgeRelations.lean`, def_3_3), and the entire
--   `Family*.lean` operator family (def_3_5).
--
-- * **`Is`-prefixed names mirroring the LN acronyms.** The LN
--   introduces each name as a capitalised acronym (CADMG, DMG, ADMG,
--   CDG, DG, CDAG, DAG); we preserve them verbatim and prepend `Is`
--   to follow both the existing `IsAcyclic` precedent in this folder
--   and Mathlib's pervasive `Is...` predicate convention
--   (`Mathlib.Order.Defs` `IsAntisymm`, `IsTrans`, ...;
--   `Mathlib.Combinatorics.SimpleGraph.Acyclic` `IsAcyclic`;
--   ...). Reading `G.IsDAG` aloud as "G is DAG" is awkward, but the
--   benefit -- a uniform prefix that flags "this is a property of `G`,
--   not a constructor or a field" -- pays off at every use site
--   downstream.
--
-- * **Inline conjunctions, *not* nested aliases.** Each predicate
--   inlines its full content (e.g. `IsDAG := IsAcyclic ∧ J = ∅
--   ∧ L = ∅`) rather than building on smaller pieces (e.g.
--   `IsDAG := IsADMG ∧ L = ∅`). Two reasons:
--     1. **Unfolding hygiene.** A nested alias would force callers
--        proving `G.IsDAG` from its three atomic ingredients to
--        unfold two layers (`IsDAG → IsADMG ∧ L = ∅ → (IsAcyclic ∧
--        J = ∅) ∧ L = ∅`) and re-associate the conjunctions every
--        time. The inline version reads the same on the page and
--        composes directly with `And.intro` / `obtain ⟨_, _, _⟩`.
--     2. **Readability.** With seven names and three atomic
--        ingredients there is no single "best" nesting -- e.g. is a
--        DAG an ADMG without bidirected edges, or a CDAG without
--        inputs, or both? The LN sidesteps the question by
--        listing each name's full content; we do the same.
--
-- * **All seven are kept, even though some logically imply others.**
--   `IsDAG → IsADMG → IsDMG` and `IsDAG → IsCDAG → IsCDG`, so a
--   minimal axiomatisation would only need the three atomic
--   ingredients plus an `And`. We keep all seven because *every one
--   of them* is the name a downstream chapter uses for its
--   preconditions (see the module-level "Where this gets used
--   downstream" list above); collapsing them into atomics would
--   force every later theorem statement to spell out the three
--   conjuncts instead of using the LN's name.
--
-- * **`def`, not `abbrev`.** An `abbrev` would unfold to
--   `G.IsAcyclic ∧ ...` automatically at every use site, which
--   sounds convenient but actually hurts: downstream callers would
--   see goals like `G.IsAcyclic ∧ G.J = ∅` instead of `G.IsADMG`,
--   losing the readable name. The `def` keeps the name on the page
--   in goals; callers who do need the underlying conjunction reach
--   for `unfold CDMG.IsADMG` (one-liner) or destructure the
--   hypothesis directly via `obtain ⟨_, _⟩ := hG`.

-- def_3_7 (item 1)
-- title: GraphTypes -- CADMG
--
-- A CDMG is a *Conditional Acyclic Directed Mixed Graph* (CADMG)
-- iff it is acyclic. Inputs `J` and bidirected edges `L` are
-- unrestricted: a CADMG may still have both. Used pervasively in
-- chapters 4 -- 6 as the canonical underlying graph for L-CBNs after
-- marginalising out latents and for the do-calculus / id-algorithm.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.7, item 1):

    \item Conditional Acyclic Directed Mixed Graph (CADMG) if $G$ is acyclic.
-/
/-- The CDMG `G` is a *Conditional Acyclic Directed Mixed Graph
(CADMG)*: it is acyclic. No restriction on inputs `J` or bidirected
edges `L`. -/
def IsCADMG (G : CDMG α) : Prop := G.IsAcyclic

-- def_3_7 (item 2)
-- title: GraphTypes -- DMG
--
-- A CDMG is a *Directed Mixed Graph* (DMG) iff it has no input
-- nodes (`J = ∅`). Acyclicity is *not* required, and bidirected
-- edges `L` are allowed. DMGs are the latent-variable graphs of the
-- LN's pre-causal-discovery chapters (chapters 11 -- 16 condition on
-- the no-inputs case).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.7, item 2):

    \item Directed Mixed Graph (DMG) if $J = \emptyset$.
-/
/-- The CDMG `G` is a *Directed Mixed Graph* (DMG): it has no input
nodes. Acyclicity is not assumed; bidirected edges `L` are
allowed. -/
def IsDMG (G : CDMG α) : Prop := G.J = ∅

-- def_3_7 (item 3)
-- title: GraphTypes -- ADMG
--
-- A CDMG is an *Acyclic Directed Mixed Graph* (ADMG) iff it is
-- acyclic and has no input nodes. Bidirected edges `L` are still
-- allowed. ADMGs are the canonical ground-truth graph type in the
-- causal-discovery chapters (FCI in chapter 16); a Partial Ancestral
-- Graph (PAG) is an equivalence class of ADMGs.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.7, item 3):

    \item Acyclic Directed Mixed Graph (ADMG) if $G$ is acyclic and $J = \emptyset$.
-/
/-- The CDMG `G` is an *Acyclic Directed Mixed Graph* (ADMG): it is
acyclic and has no input nodes. Bidirected edges `L` are
allowed. -/
def IsADMG (G : CDMG α) : Prop := G.IsAcyclic ∧ G.J = ∅

-- def_3_7 (item 4)
-- title: GraphTypes -- CDG
--
-- A CDMG is a *Conditional Directed Graph* (CDG) iff it has no
-- bidirected edges (`L = ∅`). Inputs `J` are still allowed, and
-- acyclicity is *not* required. CDGs are the natural "no latent
-- confounding, but interventions allowed" intermediary.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.7, item 4):

    \item Conditional Directed Graph (CDG) if $L = \emptyset$.
-/
/-- The CDMG `G` is a *Conditional Directed Graph* (CDG): it has no
bidirected edges. Inputs `J` are allowed; acyclicity is not
assumed. -/
def IsCDG (G : CDMG α) : Prop := G.L = ∅

-- def_3_7 (item 5)
-- title: GraphTypes -- DG
--
-- A CDMG is a *Directed Graph* (DG) iff it has neither input nodes
-- nor bidirected edges (`J = ∅` and `L = ∅`). Acyclicity is *not*
-- required, so a DG may contain directed cycles. This is the
-- classical "directed graph" of graph theory, embedded in our
-- CDMG framework.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.7, item 5):

    \item Directed Graph (DG) if $J = \emptyset$ and $L = \emptyset$.
-/
/-- The CDMG `G` is a *Directed Graph* (DG): no input nodes and no
bidirected edges. Acyclicity is not assumed; directed cycles are
allowed. -/
def IsDG (G : CDMG α) : Prop := G.J = ∅ ∧ G.L = ∅

-- def_3_7 (item 6)
-- title: GraphTypes -- CDAG
--
-- A CDMG is a *Conditional Directed Acyclic Graph* (CDAG) iff it
-- is acyclic and has no bidirected edges. Inputs `J` are still
-- allowed. The CDAG is the underlying graph of an L-CBN with input
-- variables in chapter 4 before any latent marginalisation; the LN
-- frequently writes "CDAG $G = (J, V, E)$" with no `L` component.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.7, item 6):

    \item Conditional Directed Acyclic Graph (CDAG) if $G$ is acyclic and $L = \emptyset$.
-/
/-- The CDMG `G` is a *Conditional Directed Acyclic Graph* (CDAG):
it is acyclic and has no bidirected edges. Inputs `J` are
allowed. -/
def IsCDAG (G : CDMG α) : Prop := G.IsAcyclic ∧ G.L = ∅

-- def_3_7 (item 7)
-- title: GraphTypes -- DAG
--
-- A CDMG is a *Directed Acyclic Graph* (DAG) iff it is acyclic and
-- has neither input nodes nor bidirected edges. This is the
-- classical DAG of probability theory and graphical models, and the
-- ground-truth graph type for plain (input-free, latent-free) Causal
-- Bayesian Networks in chapter 4.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.7, item 7):

    \item Directed Acyclic Graph (DAG) if $G$ is acyclic, $J=\emptyset$ and $L = \emptyset$.
-/
/-- The CDMG `G` is a *Directed Acyclic Graph* (DAG): it is acyclic,
has no input nodes and no bidirected edges. -/
def IsDAG (G : CDMG α) : Prop := G.IsAcyclic ∧ G.J = ∅ ∧ G.L = ∅

end CDMG

end Causality
