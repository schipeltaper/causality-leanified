import Mathlib

namespace Causality

/-!
# Conditional Directed Mixed Graphs (CDMGs)

This file formalises the foundational definition of a *conditional directed
mixed graph* — the geometric substrate on which every later chapter of the
lecture notes (CBNs, do-calculus, iSCMs, causal discovery, …) is built.

The LN tex block for `def_3_1`:

```
A conditional directed mixed graph (CDMG) G —per definition— consists of two
(disjoint) sets of vertices (also called nodes):
  i.)  J, whose elements are called input nodes,
  ii.) V, whose elements are called output nodes,
and two (disjoint) sets of edges:
  i.)  E ⊆ (J ∪ V) × V,             the set of directed edges,
  ii.) L ⊆ V × V / ((v₁,v₂) ~ (v₂,v₁)), the set of bidirected edges,
       with: (v₁,v₂) ∈ L ⟹ v₁ ≠ v₂ ∧ (v₂,v₁) ∈ L.
```

Authoritative additions from the operator (treated as part of the LN):

* `[l_quotient_vs_ordered_pair_typing_inconsistent]` — `L` may be encoded
  either as a quotient of `V × V` under `(v₁,v₂) ~ (v₂,v₁)` or as a subset
  of `V × V` carrying the explicit symmetry constraint
  `(v₁,v₂) ∈ L ↔ (v₂,v₁) ∈ L`. Both encodings are admissible; irreflexivity
  `v₁ ≠ v₂` applies under either. We use the ordered-pair-plus-symmetry
  encoding here so that `E` and `L` share `Finset (Node × Node)` machinery.
* `[edge_set_disjointness_under_specified]` — the qualifier "disjoint"
  applied to `E` and `L` is purely *type-level* disjointness (the two fields
  inhabit distinct positions in the record). It imposes no graph-theoretic
  mutual-exclusion between `E` and `L`; the same ordered pair `(v, w)` may
  belong to both.
* `[manual_1]` — the node sets `J` and `V` are both finite.

The substantive design-choice rationale for every field — why this shape,
which alternatives were rejected, which downstream rows depend on the
choice — lives in the block of `--` comments immediately above the
`structure` declaration. Read that block before modifying a field; it is
the load-bearing contract for the rest of chapter 3.
-/

-- ref: def_3_1
--
-- A *conditional directed mixed graph* `G` over an ambient node type
-- `Node` is a tuple `(J, V, E, L)` of two disjoint finite vertex sets —
-- `J` (input nodes) and `V` (output nodes) — together with a finite set
-- of directed edges `E ⊆ (J ∪ V) × V` and a finite set of bidirected
-- edges `L ⊆ V × V` that is irreflexive and symmetric (encoding the
-- LN's quotient `V × V / ((v₁,v₂) ~ (v₂,v₁))` as ordered pairs with an
-- explicit symmetry constraint).
--
-- This is the foundational object the rest of the lecture notes builds
-- on; CBNs, do-calculus, iSCMs, σ/d-separation and the causal-discovery
-- algorithms all destructure a CDMG via the four fields `J, V, E, L`.
--
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- Each point below is the answer to a question the LN does not pin
-- down literally; a future row that touches a CDMG should read all of
-- them before deviating.
--
-- *Why a fresh `structure`, not `class` / `abbrev` / Mathlib
--   `SimpleGraph` / `Quiver`.*  A CDMG is data, not a typeclass-
--   resolvable property, so `class` is wrong — we never want Lean to
--   "infer the CDMG on `Node`".  No Mathlib graph type captures the
--   shape: `SimpleGraph` is undirected and has no J/V split and no
--   bidirected channel; `Quiver` carries parallel ordered edges only,
--   with no input/output partition and no symmetric sub-relation.  A
--   bespoke `structure` is the only encoding that holds (J-vs-V
--   partition, directed channel `E`, bidirected channel `L`) in one
--   record that `def_3_2`–`def_3_14` pattern-match against via
--   `G.J / G.V / G.E / G.L`.
--
-- *Why `Node : Type*` with `[DecidableEq Node]`, not `Fin n` / `ℕ` /
--   a concrete carrier.*  Downstream operations rewrite the vertex set
--   without a canonical numbering: `def_3_10` hard intervention moves
--   members between `J` and `V`, `def_3_11` node-splitting creates
--   fresh copies `w⁰, w¹` that have no `Fin n` index, `def_3_14`
--   marginalisation projects out subsets.  Locking `Node` to a
--   concrete carrier would force renumbering at every such operation.
--   `[DecidableEq Node]` is the minimal typeclass that lets `Finset`
--   carry the vertex and edge sets and decides equality of nodes /
--   edges in the kernel; stronger assumptions (`Fintype`,
--   `LinearOrder`) are deferred to the use site that needs them — for
--   instance `def_3_8` topological order pulls in a total order
--   per-graph rather than baking it into `Node`.
--
-- *Why `Finset Node` for `J` and `V`, not `Set` / subtype / `Sort`.*
--   Operator clarification `[manual_1]` makes finiteness part of the
--   spec.  `Finset` makes that computable and lets downstream defs
--   avoid re-deriving a finiteness instance: `def_3_5`'s family sets
--   (`Pa`, `Ch`, `Anc`, `Desc`, `Sib`, `Dist`) use `Finset.filter` /
--   `biUnion`; `def_3_8` topological order is a total order on the
--   underlying `Finset`; `def_3_10` uses `J ∪ W` and `V \ W` (both
--   `Finset` operations); `def_3_14` marginalisation sums / projects
--   over node subsets.  A two-sort encoding (`J, V : Type*`) was
--   rejected because the LN treats `J ∪ V` as a single ambient set
--   everywhere downstream (`v ∈ G` means `v ∈ J ∪ V` in `def_3_2`,
--   walks in `def_3_4` quantify uniformly over `Node`, topological
--   orders are total orders on `J ∪ V`); two sorts would force a
--   `Sum` / coproduct and coercions at every use site.
--
-- *Why `hJV_disj : Disjoint J V` is an explicit structure field.*  The
--   LN's parenthetical "(disjoint)" *is* the content of the input /
--   output distinction — without it, "input vs output" is meaningless
--   and `def_3_10` hard intervention (which converts members of `V`
--   into members of `J`) becomes ambiguous.  Disjointness has to live
--   on the structure rather than be derived from the types precisely
--   because we chose the single-`Node` encoding above; there is no
--   type-level wedge to lean on, so it must be a proof field.
--
-- *Why `E : Finset (Node × Node)` plus a separate `hE_subset`, not a
--   `Finset ((J ∪ V) × V)` subtype.*  Ordered pairs keep `E`'s carrier
--   identical to `L`'s, so the two share every `Finset (Node × Node)`
--   lemma and downstream destructuring is the uniform `(v, w) := e`.
--   Pushing `E ⊆ (J ∪ V) × V` into a subtype was rejected: every
--   consumer (`def_3_5`'s `Pa(v) = {w | w → v ∈ E}`, `def_3_10`'s
--   edge-removal via `Finset.filter`, `def_3_11`'s edge-rewriting)
--   would have to lift through the subtype coercion at every use.
--   Keeping `hE_subset` (and analogously `hL_subset`) as stand-alone
--   fields lets the constraint be invoked or rewritten on its own.
--
-- *Directed self-loops `(v, v) ∈ E` are admitted by the type.*  The
--   literal LN puts *no* irreflexivity constraint on `E` (contrast
--   with `L`).  Working-phase wording-check subtlety
--   `directed_self_loops_unrestricted_in_E` flagged this asymmetry
--   (standard ADMG literature typically excludes directed self-loops)
--   as potentially unintended; we follow the literal LN here.
--   Downstream defs that need to exclude `v → v` (acyclicity
--   `def_3_6`, ancestral sets in `def_3_5`) handle that locally
--   rather than this foundational type pre-empting them.
--
-- *Why `L : Finset (Node × Node)` with `hL_symm`, not the LN's
--   quotient `V × V / ((v_1,v_2) ~ (v_2,v_1))`.*  Operator
--   clarification `[l_quotient_vs_ordered_pair_typing_inconsistent]`
--   admits the ordered-pair-plus-symmetry encoding as equivalent.  We
--   pick it because Lean's `Quot` would force a `Quot.lift` /
--   `Quot.mk` dance at every downstream destructuring site —
--   `def_3_5`'s `Sib(v) = {w | v ↔ w ∈ L}`, `def_3_4`'s bidirected
--   walks, `def_3_10` and `def_3_11`'s edge-rewriting all pattern-
--   match on `(v_1, v_2) ∈ L` — whereas ordered pairs let `L` share
--   every `Finset (Node × Node)` lemma with `E`.  Working-phase
--   wording-check subtlety
--   `bidirected_edge_quotient_vs_implication_redundant` flagged that
--   the LN's literal text is internally inconsistent on this point
--   (quotient notation paired with a then-redundant symmetry
--   implication); the operator's clarification is the tie-breaker.
--
-- *Trade-off — each bidirected edge appears twice in `L`.*  Under the
--   ordered-pair encoding an undirected bidirected edge between
--   `v_1` and `v_2` appears in `L` as *both* `(v_1, v_2)` and
--   `(v_2, v_1)`.  Downstream rows that count or iterate over
--   bidirected edges (counting siblings, summing edge weights,
--   enumerating each undirected edge once) must either divide by two
--   or pick a canonical orientation (e.g. `v_1 < v_2` once a node
--   ordering is in scope).  This is the explicit cost of avoiding the
--   quotient — flagged here so a future consumer does not trip over
--   it.
--
-- *Why `hL_irrefl` is its own field, separate from `hL_subset` /
--   `hL_symm`.*  Irreflexivity (`(v_1, v_2) ∈ L → v_1 ≠ v_2`) is a
--   distinct LN constraint, and downstream defs sometimes need just
--   irreflexivity (`def_3_6` acyclicity, ruling out the trivial
--   bidirected loop) or just symmetry (`def_3_4`'s bidirected walks,
--   freely reversing direction) without the other.  Bundling them
--   would force every such call site to unpack a conjunction.
--
-- *No `E ∩ L = ∅` field, by intent.*  Operator clarification
--   `[edge_set_disjointness_under_specified]` reads the LN's
--   "(disjoint)" qualifier on the edge sets as *type-level only*.
--   The same ordered pair `(v, w)` may belong to both `E` and `L`
--   simultaneously — a directed edge and a bidirected edge between
--   the same vertex pair coexist.  This is *intentional*, not an
--   oversight.  Working-phase wording-check subtlety
--   `edge_sets_E_and_L_disjointness_ill_typed` flagged the literal
--   text as ambiguous (parts of the ADMG literature adopt the stricter
--   "no parallel directed+bidirected edge" reading); the operator
--   picked the permissive reading and we follow it.  A downstream row
--   that needs the stricter form adds the constraint at the use site.
--
-- *The empty CDMG (`J = V = ∅`, hence `E = L = ∅`) is a legal
--   inhabitant.*  The LN's would-be nonemptiness constraint
--   `J ∪ V ≠ ∅` is *commented out* in the LN source (visible in the
--   tex block above).  Working-phase wording-check subtlety
--   `empty_vertex_set_admitted` flagged this; we follow the literal
--   LN.  Downstream defs that need a non-empty graph (picking a
--   sink / source vertex, asserting a topological order exists via
--   `def_3_8`, marginalising over a non-empty subset) add that
--   hypothesis at the use site rather than baking it into the
--   foundational type.

-- def_3_1 -- start statement
structure CDMG (Node : Type*) [DecidableEq Node] where
  J : Finset Node
  V : Finset Node
  hJV_disj : Disjoint J V
  E : Finset (Node × Node)
  hE_subset : ∀ ⦃e : Node × Node⦄, e ∈ E → e.1 ∈ J ∪ V ∧ e.2 ∈ V
  L : Finset (Node × Node)
  hL_subset : ∀ ⦃e : Node × Node⦄, e ∈ L → e.1 ∈ V ∧ e.2 ∈ V
  hL_irrefl : ∀ ⦃v1 v2 : Node⦄, (v1, v2) ∈ L → v1 ≠ v2
  hL_symm : ∀ ⦃v1 v2 : Node⦄, (v1, v2) ∈ L → (v2, v1) ∈ L
-- def_3_1 -- end statement

end Causality
