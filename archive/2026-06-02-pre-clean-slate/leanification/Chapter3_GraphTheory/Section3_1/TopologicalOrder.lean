import Chapter3_GraphTheory.Section3_1.FamilyDirect

/-!
# Topological order of a CDMG (def 3.8)

This file formalises *definition 3.8* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`): a CDMG
`G = (J, V, E, L)` carries a *topological order* iff there is a strict
total order `<` on `G.J ∪ G.V` along which every parent precedes its
children, i.e. `v ∈ Pa^G(w) → v < w` for all `v, w ∈ G`.

Two declarations are introduced, matching the two LN readings:

* `IsTopologicalOrder G r` -- the property of a candidate relation
  `r : α → α → Prop` saying that `r` *is* a topological order of `G`.
* `HasTopologicalOrder G` -- the existential closure, "*there is* a
  topological order of `G`".

## Where this gets used downstream

* **claim_3_2** (`claim_3_2_*_AcyclicIffTopologicalOrder.tex`) -- the
  flagship use: "$G$ is acyclic iff $G$ has a topological order". The
  iff reads as `G.IsAcyclic ↔ G.HasTopologicalOrder`. The `←`
  direction unpacks the topological order's `irrefl` and `trans` to
  contradict a non-trivial directed walk `v_0 < v_1 < … < v_n = v_0`;
  the `→` direction constructs a topological order by iteratively
  picking parent-free nodes from acyclic induced subgraphs.
* **claim_3_3** (`graphs.tex` Rem 311) -- "if $G$ is acyclic then
  also $G_{\doit(W)}$ is acyclic and a topological order for $G$ is
  also one for $G_{\doit(W)}$". Hard interventions preserve the
  ordering.
* **chapters 5 -- 6 (do-calculus, ID-algorithm,
  `id-algorithm.tex`)** -- the ID-algorithm and its soundness theorem
  take "a CADMG $G$ with a fixed topological order $<$" as a primary
  input; the preceding Markov blanket `MBl^G_<(v)` and the product
  over districts taken "in reverse topological order" are
  parameterised on a chosen `<`. Concrete examples in
  `id-algorithm.tex` lines 698, 786, 942 use prose like
  "we have the topological order $v_1 < v_2 < v_3$".
* **chapters 8 -- 10 (SCMs / iSCMs, `scms*.tex`)** -- the
  unique-solution theory for acyclic iSCMs proceeds by recursion
  *along* a topological order: given an acyclic iSCM with graph
  $G^+$, claim_3_2 yields a topological order $<$ on $G^+$, and the
  solution map is built inductively on $<$, evaluating each mechanism
  $f_v$ only after every parent's value is fixed (cf.
  `scms3.tex` line 296: "its graph $G^+$ is acyclic, and hence has a
  topological order $<$. Consider $f_v$, the causal mechanism for
  $v \in V$. The parents $\Pa^{G^+}(v)$ precede $v$ in the
  topological order.").

The downstream uses all read as either "`<` is a topological order of
`G`" (relation-level -- `IsTopologicalOrder G r`) or "`G` has a
topological order" (existential -- `HasTopologicalOrder G`). Both
shapes appear, so both are provided here.
-/

namespace Causality

open scoped Causality.CDMG

namespace CDMG

variable {α : Type*}

-- def_3_8
-- title: TopologicalOrder
--
-- A *topological order* of `G` is a strict total order on the nodes
-- `G.J ∪ G.V` of `G` that is compatible with the parent-of relation:
-- every parent precedes its children. Formally, a relation
-- `r : α → α → Prop` *is a topological order of* `G` iff
--
--   1. `r` is irreflexive on `G`: `∀ v ∈ G, ¬ r v v`,
--   2. `r` is transitive on `G`: `∀ v w x ∈ G, r v w → r w x → r v x`,
--   3. `r` is trichotomous on `G`: `∀ v w ∈ G, r v w ∨ v = w ∨ r w v`,
--   4. `r` respects parents: `v ∈ Pa^G(w) → r v w`.
--
-- The conditions only constrain `r` on `G.J ∪ G.V`; the behaviour
-- of `r` on the complement is irrelevant.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.8):

\begin{defmark}
\begin{Def}[Topological order]
    Let $G=(J,V,E,L)$ be a CDMG.
    A \emph{topological order} of $G$ is a total order $<$ of
    $J \cup V$ such that for all $v,w \in G$:
    \[ v \in \Pa^G(w) \; \implies \; v < w.\]
    Equivalently, it can be described as an indexing of the nodes
    $J \cup V = \{v_1,\dots,v_K\}$ where parents always precede
    their children.
\end{Def}
\end{defmark}
-/
--
-- ## Design choice
--
-- * **Relation `r : α → α → Prop`, not a `LinearOrder` on a subtype.**
--   The LN writes `v < w` for bare vertices `v, w ∈ J ∪ V`, so the
--   relation should accept the same vertex type that everything else
--   in the project (`Pa G w`, `v ∈ G`, `⟶[G]`, walks, …) reads.
--   The natural-looking alternative `LinearOrder ↥(G.J ∪ G.V)` would
--   force every downstream `v < w` statement to first inject `v` and
--   `w` into a subtype `↥(G.J ∪ G.V)`, breaking the LN's bare-vertex
--   prose `v_1 < v_2 < v_3` that the id-algorithm chapter relies on
--   (cf. `id-algorithm.tex` line 698: "we have the topological order
--   $v_1 < v_2$"). Carrying the relation as `α → α → Prop` and
--   constraining it *only on nodes of `G`* is the cheapest encoding
--   that supports both formal reasoning and the LN's notational
--   habits at the same time.
--
-- * **Conditions restricted to `v ∈ G`, not blanket over `α`.** The
--   LN says "*a total order $<$ of $J \cup V$*" -- only the nodes
--   of `G` are ordered. A blanket strict total order on the whole
--   `α` would be strictly stronger: it would, for example, force `r`
--   to trichotomise even non-graph vertices, which the LN does not
--   require and which would prevent us from extending any
--   topological order arbitrarily on `α \ (G.J ∪ G.V)`. The
--   restricted version is also the natural shape for claim_3_3's
--   "subgraph by intervention" reuse: the topological order of `G`
--   is reused on `G_{\doit(W)}`, where the node set is the same but
--   external behaviour does not matter.
--
-- * **`structure ... : Prop` with named fields, not
--   `def _ := _ ∧ _ ∧ _ ∧ _`.** Four conjuncts is the point where
--   named projections start to pay off: downstream proofs in
--   claim_3_2 and beyond will reach for `hr.parent_lt`, `hr.trans`,
--   `hr.irrefl` by name rather than peeling apart a four-deep
--   `And.intro`. The structure form mirrors Mathlib's `Std.Asymm` /
--   `Std.Trichotomous` / `IsTrans` style (single-field classes) and
--   keeps the LN-aligned `parent_lt` name visible at every use
--   site.
--
-- * **"At least one" trichotomy, not "exactly one".** We state
--   trichotomy as `r v w ∨ v = w ∨ r w v` (the standard form,
--   matching `Std.Trichotomous`). The LN's "total order" is the
--   *exactly-one* reading, but together with `irrefl` and `trans`
--   (also restricted to `G`) the exactly-one form is automatic: if
--   `r v w ∧ v = w` then substituting `w := v` gives `r v v`,
--   contradicting `irrefl`; if `r v w ∧ r w v` with `v, w ∈ G`,
--   then transitivity yields `r v v`, again contradicting
--   `irrefl`. Stating only "at least one" keeps the structure
--   lightweight without losing information.
--
-- * **`parent_lt` uses `v ∈ Pa G w` directly, with no extra
--   `v ∈ G` / `w ∈ G` hypotheses.** Both memberships are implicit
--   in `v ∈ Pa G w`: by `mem_Pa` it unfolds to
--   `v ∈ G ∧ v ⟶[G] w`, and `v ⟶[G] w` (i.e. `(v, w) ∈ G.E`)
--   together with `G.E_subset : G.E ⊆ (J ∪ V) ×ˢ V` forces
--   `w ∈ G.V ⊆ G`. The trimmed form matches the LN literally
--   ("$v \in \Pa^G(w) \implies v < w$") and shaves a hypothesis off
--   every caller of the field.
--
-- * **No `IsStrictTotalOrder` typeclass from Mathlib.** Mathlib's
--   `IsStrictTotalOrder α r` is a strict total order on *all* of
--   `α`, not on a subset. Forcing our relation into that typeclass
--   would require either restricting `α` to be exactly `G.J ∪ G.V`
--   (a subtype, see the first bullet) or extending `r` to the whole
--   `α` (extra structure not present in the LN). Spelling out the
--   three strict-total-order axioms inline -- restricted to nodes
--   of `G` -- is shorter and stays closer to the LN.
--
-- * **`Causality.CDMG.IsTopologicalOrder` namespacing,
--   dot-projection intended.** Downstream callers write
--   `G.IsTopologicalOrder r` and `G.HasTopologicalOrder`, matching
--   the LN prose "*a topological order of `G`*" / "*`G` has a
--   topological order*". This parallels `G.IsAcyclic` (def_3_6),
--   `G.IsCADMG` / `G.IsDAG` / … (def_3_7), and the entire
--   `Family*` operator family (def_3_5).

/-- `IsTopologicalOrder G r` -- the relation `r : α → α → Prop` is a
*topological order* of the CDMG `G`: restricted to the nodes
`G.J ∪ G.V` of `G`, the relation `r` is a strict total order
(irreflexive, transitive, trichotomous), and every parent precedes
its children (`v ∈ Pa^G(w) → r v w`). The behaviour of `r` on
vertices outside `G.J ∪ G.V` is left unconstrained. Mirrors
`lecture-notes/lecture_notes/graphs.tex` def 3.8 verbatim. -/
structure IsTopologicalOrder (G : CDMG α) (r : α → α → Prop) : Prop where
  /-- `r` is irreflexive on the nodes of `G`. -/
  irrefl : ∀ v ∈ G, ¬ r v v
  /-- `r` is transitive on the nodes of `G`. -/
  trans : ∀ v ∈ G, ∀ w ∈ G, ∀ x ∈ G, r v w → r w x → r v x
  /-- `r` is trichotomous on the nodes of `G`: for any two nodes
  `v, w ∈ G`, at least one of `r v w`, `v = w`, `r w v` holds.
  Combined with `irrefl` and `trans`, "exactly one" is automatic
  (see the design-choice block above). -/
  trichotomous : ∀ v ∈ G, ∀ w ∈ G, r v w ∨ v = w ∨ r w v
  /-- Every parent precedes its children under `r`. The LN's
  `v ∈ \Pa^G(w) \implies v < w`. The `v ∈ G` / `w ∈ G` hypotheses
  the LN's "for all $v, w \in G$" prose suggests are automatic from
  `v ∈ Pa G w`: see `mem_Pa` (which gives `v ∈ G`) and
  `G.E_subset` (which gives `w ∈ G.V ⊆ G`). -/
  parent_lt : ∀ {v w : α}, v ∈ Pa G w → r v w

-- def_3_8 (existential variant)
-- title: TopologicalOrder -- has-form
--
-- `G.HasTopologicalOrder` is the existential closure of
-- `IsTopologicalOrder G r` over the relation `r`. This is the prose
-- "`G` has a topological order" that powers claim_3_2's iff and the
-- iSCM solution theory of chapter 8.
/-
The LN does not name this predicate separately; it is the right-hand
side of the iff in claim_3_2 (`graphs.tex` Lem 224):

    "A CDMG $G=(J,V,E,L)$ is acyclic if and only if it has a
    topological order."
-/
--
-- ## Design choice
--
-- * **Pulled out as its own `def`, not inlined as `∃ r, ...`.**
--   claim_3_2's iff and every later chapter-5 / -6 / -8 statement
--   "let `G` be a CADMG with a fixed topological order" both want a
--   one-word spelling for the existential; introducing
--   `HasTopologicalOrder` gives both readings one canonical name and
--   lets `simp` / `obtain` destructuring work against a single
--   identifier. The relation-level form `IsTopologicalOrder G r` is
--   still the right shape when the LN names the order (e.g.
--   `id-algorithm.tex` line 156: "let `<` be a topological order").
--
-- * **No separate `IsTopologicalIndexing` predicate.** The LN's
--   "*equivalently, an indexing $v_1,\dots,v_K$*" is the same notion
--   restated in the *finite* case: an indexing is the choice of a
--   bijection `Fin K → α` whose image is `G.J ∪ G.V` and whose
--   inherited `(· < ·)` agrees with the topological order. We do
--   *not* formalise the indexing form as a separate Lean predicate
--   because (a) the LN treats the two descriptions as
--   interchangeable, not as distinct definitions; (b) doing so would
--   commit us to finiteness of `G.J ∪ G.V` at this layer, which the
--   def_3_1 CDMG does not require (the vertex type `α` is fully
--   polymorphic); and (c) downstream rows that genuinely need the
--   indexing -- e.g. the ID-algorithm's "let $v_1, \dots, v_K$ be
--   $J \cup V$ in increasing order" -- can derive it locally from
--   `IsTopologicalOrder G r` together with a `Fintype` hypothesis,
--   using Mathlib's `Fintype.equivFin` to transport the order onto
--   `Fin K`. Pre-emptively defining the indexing form would
--   bake-in a redundancy.

/-- `HasTopologicalOrder G` -- the existential statement "*there is*
a topological order of `G`". The right-hand side of the iff in
claim_3_2 (`lecture-notes/lecture_notes/graphs.tex`, Lem after
def_3_8): "$G$ is acyclic iff $G$ has a topological order". -/
def HasTopologicalOrder (G : CDMG α) : Prop :=
  ∃ r : α → α → Prop, IsTopologicalOrder G r

end CDMG

end Causality
