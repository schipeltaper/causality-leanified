import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Mathlib.Order.Defs.LinearOrder

-- The verbatim TeX source of the LN definition is reproduced inside the
-- comments below; some of its lines exceed 100 characters. Disable the
-- style linter for this file so the TeX is kept byte-for-byte identical
-- to `Section3_1/main.tex`.
set_option linter.style.longLine false

/-!
# def_3_9 — Predecessors

The ninth LN definition of subsection 3.1 introduces *predecessors* of a
node `v` in a CDMG `G`, with respect to a total order `<` of `J ∪ V`. The
LN gives two flavours:

* `Pred^G_<(v)` — strict predecessors, the nodes `w` with `w < v`;
* `Pred^G_≤(v)` — non-strict predecessors, the strict predecessors together
  with `v` itself.

The total order `<` is *arbitrary*: the LN explicitly says "a total order
of `J ∪ V`", **not** "a topological order". So `def_3_9` must not be
parameterised by a `G.TopologicalOrder` (`def_3_8`) — it must accept any
`LinearOrder (J ⊕ V)`. Downstream rows that need the topological-order
case will pass `topOrder.toLinearOrder` explicitly.

We share the `Causality.Chapter3` namespace with `def_3_1`–`def_3_8`.
-/

namespace Causality
namespace Chapter3

variable {J V : Type*}

/-
Source (verbatim from `Section3_1/main.tex`, under `% def_3_9`):

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

/-!
## Design choices — common to both `PredLT` and `PredLE`

* **`Set (J ⊕ V)`, not `Finset (J ⊕ V)`.** The LN writes a set
  comprehension `{w ∈ G | w < v}` and never assumes the node set is
  finite, so `Set` is the faithful translation. `Finset` would force a
  `Fintype (J ⊕ V)` assumption that the LN does not make, and it would
  not compose with the rest of this section (`Pa`, `Ch`, `Anc`, …all
  return `Set (J ⊕ V)`).

* **`LinearOrder (J ⊕ V)` parameter, not `G.TopologicalOrder` or a bare
  `[IsStrictTotalOrder _ (· < ·)]`.** The LN takes an *arbitrary* total
  order on `J ∪ V` (not a topological order — that came in `def_3_8`).
  Mirroring `def_3_8`'s rationale (see `TopologicalOrder.lean`), we use
  Mathlib's `LinearOrder` as the canonical packaging of a strict total
  order: it bundles `≤`, `<`, decidability, trichotomy, and every
  `LinearOrder`-only lemma we may want later. Whenever a downstream row
  has a topological order in hand, it can supply
  `topOrder.toLinearOrder` directly.

* **`LinearOrder` passed as an *explicit term-level parameter*
  (`lo : LinearOrder (J ⊕ V)`), not as an instance `[LinearOrder _]`.**
  This matches `def_3_8`'s "structure-as-data" philosophy: a CDMG may
  admit several different total orders simultaneously (the LN's whole
  point of introducing `<` separately from `G` is that the *choice* of
  order matters), and an instance-style declaration would lock the type
  `J ⊕ V` into one canonical order. The trade-off is that we cannot use
  the bare `<` notation in the comprehension; we use `lo.lt w v`
  instead, which is exactly the form `TopologicalOrder.lean` uses for
  its `parent_lt` field. Callers can always recover `<` notation with a
  local `letI := lo` if they prefer.

* **The LN filter "`w ∈ G`" is kept *literally* in the comprehension.**
  Per `def_3_2` / `CDMGNotation.lean`, `w ∈ G` for `w : J ⊕ V` is
  literally `True` in our encoding (the `Membership` instance has body
  `True`, because `J ⊕ V` *is* the node-set type — there is no "outside
  `G`" inhabitant). The LN's `w ∈ G` clause is therefore vacuous on the
  nose. We could have dropped it — most of Section 3.1's other set
  comprehensions do (`CDMG.Pa`, `CDMG.Ch`, `CDMG.Sib` in
  `FamilyRelationships.lean`) — but for *this* row two considerations
  push the other way: (i) unlike `Pa` / `Ch` / `Sib`, the predecessor
  predicate `lo.lt w v` does not mention `G` at all, so dropping `w ∈ G`
  would leave the parameter `G` syntactically unused inside the body and
  the unused-variable linter would (correctly) flag it; (ii) the
  signature still needs `G` so that `def_3_8`-style notation `G.PredLT`
  reads exactly like the LN's `Pred^G_<`. Re-instating the LN's literal
  `w ∈ G` clause kills both birds: it keeps `G` syntactically present in
  the body for the linter, *and* it mirrors the LN byte-for-byte. The
  cost — a vacuous conjunct that `simp` strips on first use — is a
  fixed one-liner downstream and is documented here so the next manager
  knows to expect it.
-/

-- def_3_9 (part 1/2) — strict predecessors of `v` under the order `lo`.
--
-- LN fragment:
-- /- The set of *predecessors* of `v` in `G`:
--    `Pred^G_<(v) := { w ∈ G | w < v }`. -/
--
-- The set of nodes `w : J ⊕ V` that come strictly before `v` according to
-- the supplied total order `lo` on `J ⊕ V`. Note that this set does *not*
-- contain `v` itself.
--
-- We write `lo.lt w v` rather than `w < v` because `lo` is a term-level
-- parameter, not an `[instance]` argument — there is no ambient `<`
-- notation at the call site. See the design-choice block above for why
-- term-level is the right choice here.
def CDMG.PredLT (G : CDMG J V) (lo : LinearOrder (J ⊕ V)) (v : J ⊕ V) :
    Set (J ⊕ V) :=
  { w : J ⊕ V | w ∈ G ∧ lo.lt w v }

-- def_3_9 (part 2/2) — non-strict predecessors of `v` under the order `lo`.
--
-- LN fragment:
-- /- We also put:
--    `Pred^G_≤(v) := { w ∈ G | w < v } ∪ {v}`. -/
--
-- The strict predecessors together with `v` itself. The LN writes this as
-- `{w ∈ G | w < v} ∪ {v}` rather than `{w ∈ G | w ≤ v}`; the two are
-- equal (by trichotomy of the linear order), but we keep the LN's
-- definitional shape for traceability — a downstream rewrite to the `≤`
-- form is one `Set.ext` lemma away.
--
-- We *reuse* `G.PredLT lo v` for the strict part instead of inlining the
-- comprehension, so a future change to `PredLT` (e.g. adding the `w ∈ G`
-- clause back in) automatically propagates here, and the LN's "we also
-- put" phrasing is preserved literally.
def CDMG.PredLE (G : CDMG J V) (lo : LinearOrder (J ⊕ V)) (v : J ⊕ V) :
    Set (J ⊕ V) :=
  G.PredLT lo v ∪ {v}

end Chapter3
end Causality
