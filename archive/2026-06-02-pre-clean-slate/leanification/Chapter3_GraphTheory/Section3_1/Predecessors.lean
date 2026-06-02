import Chapter3_GraphTheory.Section3_1.CDMGNotation

/-!
# Predecessors of a node in a CDMG (def 3.9)

This file formalises *definition 3.9* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`): given a
CDMG `G = (J, V, E, L)`, a binary relation `<` (intended in context to
be a topological order of `G.J ∪ G.V` -- see `IsTopologicalOrder` of
def 3.8 -- but the definition itself does not need that), and a node
`v`, the *predecessors* of `v` in `G` are the nodes of `G` strictly
below `v`:

  Pred^G_<(v)  := { w ∈ G | w < v }
  Pred^G_≤(v)  := { w ∈ G | w < v } ∪ {v}

Two declarations are introduced, matching the two LN forms:

* `predLt G r v` -- the *strict* predecessors (LN's `Pred^G_<(v)`).
* `predLe G r v` -- the *weak* predecessors (LN's `Pred^G_≤(v)`):
  `predLt G r v` together with `v` itself, added unconditionally
  (i.e. even if `v ∉ G`), exactly mirroring the LN's `\cup \{v\}`.

The two `@[simp]` membership lemmas `mem_predLt` / `mem_predLe`
unfold each definition for downstream rewriting.

## Where this gets used downstream

* **id-algorithm.tex:160-241** -- both forms appear, intersected with
  ambient subsets and re-indexed against intervened subgraphs:
  `\Pred^{[C]}_<(v) := \Pred_<^{G_{\doit(C^\cmpl)}}(v) \cap C = \Pred_<^{G}(v) \cap C`,
  `\Di^G_<(v) \ins \MBl^G_<(v) \ins \Pred_<^G(v)`,
  `X_v \Indep \, X_{\Pred^G_<(v)} \given X_{\MBl^G_<(v)}`. Treating
  `Pred` as a `Set α` lets these intersections, abbreviations, and
  conditional-independence index sets compose without conversion.
* **scms3.tex:300-302** -- `\Pred_<^{G^+}(v)` is used as an *index
  set* for a product of co-domains
  `f_v : \CX_{\Pred_<^{G^+}(v)} \to \CX_v`. The set-valued shape is
  what's indexed against.
* **scms4.tex:42-48** -- big unions `\bigcup \Pred^S_\le(C)`,
  `\bigcup \Pred^S_<(C)` over an index set `C`. Again `Set`-valued.
* **proof-markov_property.tex:57-181** -- `X_{\Pred^G_<(v)}` as the
  index of a family of random variables for the joint distribution
  the Markov property reasons about.

All four uses treat `Pred^G_<` / `Pred^G_≤` as a *set of nodes*; none
needs `<` to be a topological order at the definitional layer, so we
do not impose that as a precondition here. The consuming claim is
free to add it.
-/

namespace Causality

open scoped Causality.CDMG

namespace CDMG

variable {α : Type*}

-- def_3_9
-- title: Predecessors -- strict form
--
-- `predLt G r v` is the set of nodes `w` of `G` (i.e. `w ∈ G`,
-- which by `CDMG.mem_iff` is `w ∈ G.J ∪ G.V`) that are strictly
-- below `v` under the relation `r`. The LN writes this as
-- `Pred^G_<(v)`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (def 3.9,
first equation):

\begin{defmark}
\begin{Def}[Predecessors]
   Let $G=(J,V,E,L)$ be a CDMG and $<$ a total order of $J \cup V$.
   The set of \emph{predecessors} of $v$ in $G$ are:
   \[\Pred^G_<(v) : = \lC w\in G\,|\, w < v \rC.\]
   We also put:
   \[\Pred^G_\le(v) : = \lC w\in G\,|\, w < v \rC \cup \{v\}.\]
\end{Def}
\end{defmark}
-/
--
-- ## Design choice
--
-- * **Relation `r : α → α → Prop`, not a `LinearOrder` / not a
--   subtype.** Mirrors the design of `IsTopologicalOrder` in
--   `TopologicalOrder.lean`: the LN writes `w < v` for bare
--   vertices, and every downstream caller wants the same bare-
--   vertex prose. A `LinearOrder` on `↥(G.J ∪ G.V)` would force
--   callers to inject `w` and `v` into a subtype, breaking the LN's
--   notational idiom (cf. `id-algorithm.tex` line 698: "we have the
--   topological order $v_1 < v_2 < v_3$"). The id-algorithm chapter
--   also re-uses `Pred` against substituted graphs --
--   `\Pred^{G_{\doit(C^\cmpl)}}_<(v)` -- which is trivially `predLt
--   G' r v` for the new graph `G'` when `r` is kept separate from
--   `G`.
--
-- * **`Set α`, not `Finset α`.** Downstream uses
--   (`id-algorithm.tex:160-241`, `scms3.tex:300`,
--   `scms4.tex:42-48`, `proof-markov_property.tex:57-181`) all
--   treat predecessors as a *set*: intersected with other subsets,
--   unioned across an index, used to index families of co-domains
--   and random variables. The CDMG layer keeps the vertex type `α`
--   fully polymorphic (see `CDMG.lean`'s design notes);
--   `DecidableEq α` / `Fintype` are deliberately not assumed.
--   Forcing `Finset` here would either impose `DecidableEq α`
--   everywhere (chapters 4+ use real-valued vertices) or require a
--   `Fintype (G.J ∪ G.V)` hypothesis the LN does not impose.
--
-- * **No `IsTopologicalOrder G r` precondition.** The LN's "let `<`
--   be a total order of `J ∪ V`" is documentational: the set
--   `{ w ∈ G | w < v }` is well-defined for any binary relation.
--   Bolting an order hypothesis into the signature would force
--   every caller to thread a proof witness for the same `Set`, and
--   would block using `predLt` in the *statement* of claim_3_2
--   (where the existence of a topological order is the conclusion,
--   not a hypothesis). Callers that need the order request it
--   separately, exactly as the LN does.
--
-- * **`v ∈ G` (the `Membership` instance from
--   `CDMGNotation.lean`), not `v ∈ G.J ∪ G.V`.** The LN literally
--   writes `w ∈ G`. The membership instance unfolds to
--   `w ∈ G.J ∪ G.V` by `CDMG.mem_iff`, so the two are
--   propositionally equal -- but writing `v ∈ G` keeps the Lean
--   code literally aligned with the LN.
--
-- * **Name `predLt` / `predLe`, not `Pred` or `Pred_lt`.** `Pred`
--   alone clashes with core Lean / Mathlib (`Nat.pred`,
--   `Order.Pred`, …) and would generate disambiguation noise.
--   camelCase `predLt` / `predLe` mirrors Mathlib's conventions
--   (`Set.image`, `Set.preimage`, `Finset.range`) and is
--   immediately recognisable as the LN's `\Pred^G_<` /
--   `\Pred^G_\le`.

/-- LN's `Pred^G_<(v)` -- the *strict predecessors* of `v` in `G`
under the relation `r`: the set of nodes `w ∈ G` with `r w v`.
Verbatim from `lecture-notes/lecture_notes/graphs.tex` def 3.9. -/
def predLt (G : CDMG α) (r : α → α → Prop) (v : α) : Set α :=
  { w | w ∈ G ∧ r w v }

-- def_3_9
-- title: Predecessors -- weak form
--
-- `predLe G r v` extends `predLt G r v` by adding `v` itself
-- unconditionally -- exactly the LN's `\cup \{v\}`. Note that the
-- LN does *not* gate this union on `v ∈ G`: `v` is added even if it
-- is not a node of `G`. The LN is silent about this boundary case
-- (in context, `v` is always a node), but staying literal is safer
-- than second-guessing.
/-
LN's second equation (same `defmark` block as above):

   \[\Pred^G_\le(v) : = \lC w\in G\,|\, w < v \rC \cup \{v\}.\]
-/
--
-- ## Design choice
--
-- * **Body is `{ w | w ∈ G ∧ r w v } ∪ {v}`, NOT
--   `{ w | w ∈ G ∧ (r w v ∨ w = v) }`.** The two forms differ when
--   `v ∉ G`: the former still adds `v`, the latter silently drops
--   it. The LN literally writes `\cup \{v\}`, so we follow the LN.
--   Downstream callers that have `v ∈ G` in context (which is the
--   common case in `id-algorithm.tex` etc.) get the equivalent set
--   via `mem_predLe`; callers that don't get exactly what the LN
--   gives them.
--
-- * **Re-use the existing `predLt` would be possible**
--   (`predLt G r v ∪ {v}`) and propositionally equivalent. We
--   inline the set comprehension so the definitional body matches
--   the LN equation character-for-character. `mem_predLt` /
--   `mem_predLe` give the same `simp` rewrites either way.

/-- LN's `Pred^G_≤(v)` -- the *weak predecessors* of `v` in `G`
under the relation `r`: the strict predecessors of `v`, together
with `v` itself (unconditionally, even if `v ∉ G`). Verbatim from
`lecture-notes/lecture_notes/graphs.tex` def 3.9. -/
def predLe (G : CDMG α) (r : α → α → Prop) (v : α) : Set α :=
  { w | w ∈ G ∧ r w v } ∪ {v}

/-- Membership in `predLt G r v` is exactly its defining
predicate: `w ∈ G.predLt r v ↔ w ∈ G ∧ r w v`. Holds by `Iff.rfl`
because `predLt` is set-builder notation. -/
@[simp] theorem mem_predLt {G : CDMG α} {r : α → α → Prop} {v w : α} :
    w ∈ G.predLt r v ↔ w ∈ G ∧ r w v := Iff.rfl

/-- Membership in `predLe G r v`: a node `w` lies in the weak
predecessors of `v` iff it is a strict predecessor or it equals `v`
itself. Discharged by `Set.mem_union` (`w ∈ s ∪ t ↔ w ∈ s ∨ w ∈ t`)
and `Set.mem_singleton_iff` (`w ∈ {v} ↔ w = v`). -/
@[simp] theorem mem_predLe {G : CDMG α} {r : α → α → Prop} {v w : α} :
    w ∈ G.predLe r v ↔ (w ∈ G ∧ r w v) ∨ w = v := by
  simp only [predLe, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]

end CDMG

end Causality
