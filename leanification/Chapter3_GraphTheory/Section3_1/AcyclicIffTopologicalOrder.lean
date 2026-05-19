import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Mathlib.Data.Finite.Defs

-- TeX proof: claim_3_2_proof_AcyclicIffTopologicalOrder.tex

/-!
# Acyclicity iff existence of a topological order (claim_3_2)

This file formalises the lecture notes' Lemma immediately following
the definition of a topological order (def_3_8): a Conditional
Directed Mixed Graph `G = (J, V, E, L)` is *acyclic* (def_3_6) iff
it *has* a topological order (def_3_8). In Lean:

```
G.IsAcyclic ↔ G.HasTopologicalOrder
```

with `IsAcyclic` from `Acyclicity.lean` and `HasTopologicalOrder`
from `TopologicalOrder.lean`. The statement is the existential
reading of the LN's "has a topological order" — the relation-level
variant `IsTopologicalOrder G r` is *not* the right-hand side here,
because the LN's prose existentially quantifies the order (see the
design-choice block below).

The proof is out of scope for this row (only the statement is
written here; the body is `sorry`). The LN includes its own proof in
a `\Claude{...}` block at `graphs.tex:227--245`: the (⇐) direction
contradicts a hypothetical non-trivial directed cycle
`v_0 < v_1 < ... < v_n = v_0` against the topological order's
`irrefl` + `trans`; the (⇒) direction iteratively selects a
parent-free node from the induced subgraph on the still-unselected
nodes and uses *finiteness* of `J ∪ V` to terminate. The use of
finiteness in the LN proof drives the `[Finite α]` hypothesis on
the iff (see the design-choice block).

## Where this gets used downstream

The iff is one of the load-bearing equivalences of the whole
project: it lets every later chapter freely translate between the
graph-theoretic "$G$ is acyclic" precondition and the constructive
"let `<` be a topological order of $G$" hypothesis. Concretely:

* **claim_3_3** (`graphs.tex` Rem 311) — "if $G$ is acyclic then
  also $G_{\doit(W)}$ is acyclic, and a topological order for $G$ is
  also one for $G_{\doit(W)}$". Hard-intervention preservation of
  both sides of the iff is its own row but quotes claim_3_2 to
  bounce between the two predicates.
* **def_3_7** (graph-shape names CADMG / ADMG / DAG / …) — the iff
  lets these names be characterised either via "no directed cycle"
  or via "admits a topological order"; downstream rows that
  pattern-match on `G.IsCADMG` reach for whichever side is more
  convenient.
* **chapter 4 (CBNs, `causal_bayesian_networks.tex`)** — Causal
  Bayesian Networks factorise `P(V | J)` as a product indexed by
  parents *along a chosen topological order*. The iff is what
  guarantees the order exists from the CBN's acyclicity hypothesis,
  enabling the recursive factorisation.
* **chapter 5 (do-calculus, `do-calculus.tex`,
  `proof-do-calculus.tex`)** — the soundness proofs of the three
  do-calculus rules induct *along* a topological order of the CADMG.
  The iff is the bridge from "the underlying graph is acyclic" to
  "we have an order to induct on".
* **chapter 6 (ID-algorithm, `id-algorithm.tex`)** — the
  ID-algorithm takes "a CADMG `G` with a fixed topological order `<`"
  as input. Concrete examples in the chapter (lines 698, 786, 942)
  use prose like "we have the topological order `v_1 < v_2 < v_3`",
  derived from claim_3_2 applied to the CADMG.
* **chapters 8 -- 10 (SCMs / iSCMs, `scms.tex` -- `scms4.tex`)** —
  the unique-solution theory of acyclic iSCMs proceeds by recursion
  along a topological order of the underlying graph `G^+`. The
  recursion is *only* well-founded because `G^+` is acyclic, and the
  topological order is exactly what packages that well-foundedness
  (cf. `scms3.tex:296`: "its graph $G^+$ is acyclic, and hence has a
  topological order $<$. Consider $f_v$, the causal mechanism for
  $v \in V$. The parents $\Pa^{G^+}(v)$ precede $v$ in the
  topological order.").
* **chapters 11 -- 16 (causal discovery, `fci.tex`, `icdf.tex`,
  `proof-icdf.tex`)** — FCI / IC discovery algorithms assume an
  acyclic ground-truth graph and reason about it via topological
  orders of the candidate output graphs.

## References

  * `lecture-notes/lecture_notes/graphs.tex`, Lem at lines 222 -- 226
    (the `\begin{claimmark}\begin{Lem}...\end{Lem}\end{claimmark}`
    block immediately after `def_3_8` `TopologicalOrder`).
  * `def_3_6` — `Chapter3_GraphTheory.Section3_1.Acyclicity`:
    `CDMG.IsAcyclic`.
  * `def_3_8` — `Chapter3_GraphTheory.Section3_1.TopologicalOrder`:
    `CDMG.IsTopologicalOrder` (relation-level) and
    `CDMG.HasTopologicalOrder` (existential closure).
  * `def_3_1` — `Chapter3_GraphTheory.Section3_1.CDMG`: the `CDMG`
    structure with its polymorphic vertex type `α`; in particular,
    no built-in finiteness is supplied by `def_3_1`, motivating the
    extra `[Finite α]` instance hypothesis on this iff.

The theorem below has body `sorry`; the proof is the job of a
separate worker once the proof tex subfile is populated.
-/

namespace Causality

namespace CDMG

variable {α : Type*}

-- claim_3_2
-- title: AcyclicIffTopologicalOrder
--
-- A CDMG `G = (J, V, E, L)` is *acyclic* iff it *has* a topological
-- order. In Lean this is the iff `G.IsAcyclic ↔
-- G.HasTopologicalOrder`, using the existential-closure predicate
-- from `TopologicalOrder.lean` (def_3_8) on the right-hand side.
--
-- The (⇐) direction (topological order ⇒ acyclic) does not need
-- finiteness: a non-trivial directed walk
-- `v = v_0 ⟶ v_1 ⟶ ... ⟶ v_n = v` would force
-- `v_0 < v_1 < ... < v_n = v_0` via `parent_lt` + transitivity,
-- contradicting `irrefl` at `v_0`. The (⇒) direction (acyclic ⇒
-- topological order), however, *does* need finiteness — the LN
-- proof inducts over `K = |J ∪ V|` by repeatedly extracting a
-- parent-free node, which requires `J ∪ V` to be finite for
-- termination. We add a `[Finite α]` instance hypothesis on the
-- iff to cover this; see the design-choice block below for the
-- discussion of `Finite α` vs `Fintype α` vs `(G.J ∪ G.V).Finite`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem after
def 3.8, lines 222 -- 226):

\begin{claimmark}
\begin{Lem}
        A CDMG  $G=(J,V,E,L)$ is acyclic if and only if it has a topological order.
\end{Lem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **Existential right-hand side `G.HasTopologicalOrder`, not the
--   relation-level `IsTopologicalOrder G r`.** The LN's Lem reads
--   "G ... has a topological order" — the order is existentially
--   quantified. `HasTopologicalOrder` (def in
--   `TopologicalOrder.lean`) is exactly the unwrap
--   `∃ r, IsTopologicalOrder G r`, so it lines up verbatim with the
--   LN's "has". An alternative iff `G.IsAcyclic ↔ ∀ r,
--   IsTopologicalOrder G r` would be false (the trivial relation is
--   never a topological order of a non-empty graph), and
--   `G.IsAcyclic ↔ IsTopologicalOrder G r` for a *fixed* `r` would
--   be a strictly stronger statement that the LN does not make.
--   Both `Acyclicity.lean` (its `Where this gets used downstream`
--   block) and `TopologicalOrder.lean` (its `HasTopologicalOrder`
--   docstring) already commit the project to this exact shape, so
--   choosing the existential reading also keeps cross-file
--   references consistent.
--
-- * **`[Finite α]` instance hypothesis on the iff.** The LN's own
--   proof (lines 227 -- 245 of `graphs.tex`, inside the
--   `\Claude{...}` block) appeals to *finiteness* of `J ∪ V` in
--   the (⇒) direction — line 238 says explicitly "since `G_i` is
--   acyclic ... and finite, it has a node `v_i` with
--   `\Pa^{G_i}(v_i) = ∅`". Without finiteness the iterative
--   parent-free-node construction does not terminate, and the (⇒)
--   direction can fail for infinite graphs whose order-type does
--   not embed into a strict total order respecting parents (see
--   `claim_3_2_proof_*.tex` for the proof worker's discussion;
--   the key point is that the LN's constructive proof method
--   requires finiteness regardless).
--
--   def_3_1's `CDMG` is polymorphic in `α` and carries no
--   finiteness instance, so finiteness cannot be derived — it must
--   be added as a hypothesis somewhere.
--
-- * **Why `[Finite α]` (Prop-valued) rather than `[Fintype α]`
--   (data-valued)?** The iff's *type* is `G.IsAcyclic ↔
--   G.HasTopologicalOrder`, which is `Prop`-valued and does not
--   mention the data of any chosen enumeration. The Mathlib linter
--   `linter.unusedFintypeInType` flags `[Fintype α]` in exactly
--   this situation and suggests `[Finite α]` instead — the
--   propositional finiteness instance — since the concrete
--   enumeration is only needed inside the *proof*, not the
--   statement. Concretely, the proof worker can recover a
--   `Fintype α` via `Fintype.ofFinite α` (from
--   `Mathlib.Data.Fintype.EquivFin`) at the start of the (⇒)
--   direction. Choosing `[Finite α]` here:
--     (1) silences the linter warning,
--     (2) gives the statement the weakest finiteness hypothesis
--         the proof needs, and
--     (3) preserves callability from a `[Fintype α]` context (Lean
--         derives `Finite α` from `Fintype α` automatically via
--         `Finite.of_fintype`).
--
-- * **Alternative finiteness phrasing considered:**
--   `(G.J ∪ G.V).Finite` as an explicit `Set.Finite` hypothesis. The
--   trade-offs:
--     - *In favour of `(G.J ∪ G.V).Finite`:* it matches the LN proof
--       literally ("finiteness of `J ∪ V`"), is strictly weaker
--       than `[Finite α]` (does not force the whole ambient type
--       to be finite, only the node set), and is more honest about
--       what the proof actually uses. It would also extend more
--       cleanly to settings where `α` is uncountable (e.g. ℝ-valued
--       nodes in chapter 4 CBNs) but the chosen CDMG happens to
--       have a finite node set.
--     - *In favour of `[Finite α]`:* it is a typeclass (no extra
--       explicit argument at use sites), composes with all of
--       Mathlib's `Finite` / `Fintype` API the proof will want, and
--       matches the iSCM chapters' default ambient-type assumption.
--   We default to `[Finite α]` per the manager brief (modulo the
--   `Fintype → Finite` shift for the linter); if the proof worker
--   finds the `Set.Finite` phrasing materially cleaner, the
--   statement can be revisited then. The implication
--   `Finite α → (G.J ∪ G.V).Finite` is one `Set.toFinite` call
--   away.
--
-- * **Namespacing `Causality.CDMG.isAcyclic_iff_hasTopologicalOrder`,
--   dot-projection intended.** Downstream callers write
--   `G.isAcyclic_iff_hasTopologicalOrder.mp ha` (acyclic ⇒ has
--   topo order) and similarly `.mpr` for the reverse direction.
--   The name reads as the LN's prose "G is acyclic iff G has a
--   topological order" and parallels every other claim-of-`CDMG`
--   theorem in this section (`no_arrowhead_into_input`,
--   `input_edge_target_mem_V`, `input_nodes_not_adjacent` in
--   `JNodeProperties.lean`). Splitting into two separate lemmas
--   (`isAcyclic_of_hasTopologicalOrder` and
--   `hasTopologicalOrder_of_isAcyclic`) was considered, but the LN
--   states the equivalence as a single Lem; bundling them as one
--   iff matches that prose and lets `simp` / `rw` rewrite freely
--   between the two predicates.
--
-- * **`α` implicit, `G` explicit.** Standard for "fix a graph,
--   then state a property of it" theorems; matches every other
--   theorem in the section (`Acyclicity`, `TopologicalOrder`,
--   `JNodeProperties`, the `Family*` files).
--
-- * **`[Finite α]` placed *after* `α` and *before* `G`.** This is
--   the Mathlib convention for instance hypotheses: type-class
--   arguments immediately follow the type they constrain, before
--   any explicit data arguments. Lean's instance synthesis will
--   resolve `Finite α` at every use site that has either a `Finite`
--   or `Fintype` instance in scope, so callers writing
--   `G.isAcyclic_iff_hasTopologicalOrder` in a `[Fintype α]`
--   context do not need to supply anything extra.
/-- claim_3_2 (`AcyclicIffTopologicalOrder`): a CDMG `G` is acyclic
iff it has a topological order. Mirrors
`lecture-notes/lecture_notes/graphs.tex` Lem at line 224 verbatim,
using `CDMG.IsAcyclic` (def_3_6) on the left and the existential
`CDMG.HasTopologicalOrder` (def_3_8) on the right. The `[Finite α]`
hypothesis is needed for the (⇒) direction's parent-free-node
extraction; the (⇐) direction does not use finiteness. The proof
phase can recover a concrete `Fintype α` instance from `Finite α`
via `Fintype.ofFinite` if the constructive enumeration is needed. -/
theorem isAcyclic_iff_hasTopologicalOrder
    [Finite α] (G : CDMG α) :
    G.IsAcyclic ↔ G.HasTopologicalOrder := by
  sorry

end CDMG

end Causality
