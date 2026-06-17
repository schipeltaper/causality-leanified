import Mathlib

namespace Causality

/-!
# Conditional Directed Mixed Graphs (CDMGs)

This file formalises the foundational definition of a *conditional directed
mixed graph* (`def_3_1`) — the geometric substrate on which every later
chapter of the lecture notes (CBNs, do-calculus, iSCMs, σ/d-separation,
causal discovery) is built.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/def_3_1_CDMG.tex`,
which has been verified equivalent to the LN block (`graphs.tex`,
`\label{def-cdmg}`) augmented with three operator clarifications:

* `[l_quotient_vs_ordered_pair_typing_inconsistent]` — the bidirected
  edge set `L` may be encoded either as a subset of the quotient
  `(V × V) / ((v₁,v₂) ∼ (v₂,v₁))` or as a subset of `V × V` carrying
  the symmetry constraint `(v₁,v₂) ∈ L ↔ (v₂,v₁) ∈ L`. Both encodings
  are admissible; irreflexivity `v₁ ≠ v₂` applies under either.
* `[edge_set_disjointness_under_specified]` — the LN qualifier
  "disjoint" on `E` and `L` is *type-level only*. No graph-theoretic
  mutual-exclusion is imposed: the same ordered pair `(v, w)` over `V`
  may belong to both `E` and `L` simultaneously.
* `[manual_1]` — the node sets `J` and `V` are both finite.

The substantive design rationale (why this Lean shape, which Mathlib
alternatives were rejected, which downstream rows depend on each
choice) lives in the `--` comment block immediately above the
`structure` declaration. Read that block before changing a field — it
is the load-bearing contract for the rest of chapter 3.
-/

-- ref: def_3_1
--
-- A *conditional directed mixed graph* `G` over an ambient node type
-- `Node` is a tuple `(J, V, E, L)` consisting of two disjoint finite
-- vertex sets — `J` (input nodes) and `V` (output nodes) — together
-- with a finite set of directed edges `E ⊆ (J ∪ V) × V` and a finite
-- set of bidirected edges `L ⊆ V × V` that is irreflexive and
-- symmetric. The symmetry+irreflexivity constraints encode the LN's
-- quotient `(V × V) / ((v₁,v₂) ∼ (v₂,v₁))` in the ordered-pair form
-- admitted by addition `[l_quotient_vs_ordered_pair_typing_inconsistent]`.
--
-- CBNs (ch. 4), do-calculus (ch. 5), iSCMs (ch. 8–10), σ/d-separation
-- (ch. 6–7) and causal discovery (ch. 11+) all destructure a CDMG via
-- the four fields `J, V, E, L`; the shape below is chosen so those
-- destructurings remain syntactically uniform.
--
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- * **`structure`, not `class` / `abbrev` / Mathlib `SimpleGraph` /
--   `Quiver`.** A CDMG is data, not a typeclass-resolvable property,
--   so `class` is wrong (we never want Lean to "infer the CDMG on
--   `Node`"). `SimpleGraph` is undirected, single-sort, and has no
--   bidirected channel; `Quiver` carries parallel ordered edges only,
--   with no input/output partition and no symmetric sub-relation.
--   A bespoke `structure` is the cheapest encoding that holds all
--   four pieces (J/V partition, directed channel `E`, bidirected
--   channel `L`) in a single record that `def_3_2`–`def_3_8` and
--   downstream chapters destructure as `G.J / G.V / G.E / G.L`.
--
-- * **`Node : Type*` with `[DecidableEq Node]`, not a concrete
--   carrier such as `Fin n` / `ℕ`.** Downstream operations rewrite the
--   vertex set without a canonical numbering (hard intervention moves
--   members between `J` and `V`; node-splitting creates fresh copies;
--   marginalisation projects out subsets); locking `Node` to a
--   concrete carrier would force renumbering at every such operation.
--   `[DecidableEq Node]` is the minimal typeclass that lets `Finset`
--   carry the vertex/edge sets and decides equality of nodes/edges in
--   the kernel; stronger assumptions (`Fintype`, `LinearOrder`) are
--   deferred to use sites that need them.
--
-- * **`Finset Node` for `J` and `V`, not `Set Node` (with a
--   `Fintype`/`Set.Finite` instance) nor a subtype.** Addition
--   `[manual_1]` makes finiteness part of the spec. `Set Node` paired
--   with `Set.Finite` (or a bundled `Fintype`) was rejected on two
--   grounds: (i) the finiteness witness would be a *second* field
--   threaded through every consumer, whereas `Finset` bakes it into
--   the carrier; (ii) `Finset` carries decidable membership, which
--   downstream defs depend on for `Finset.filter` / `biUnion` /
--   `Finset.image` over the family sets (`Pa`, `Ch`, `Anc`, `Desc`,
--   `Sib`, `Dist` in `def_3_5`) and for the kernel-level comparisons
--   in topological order (`def_3_8`). A two-sort encoding
--   (`J, V : Type*`) was also rejected because the LN treats `J ∪ V`
--   as a single ambient set everywhere downstream — two sorts would
--   force a `Sum` coproduct and coercions at every use site.
--
-- * **`hJV_disj : Disjoint J V` is an explicit structure field.** The
--   LN-and-rewrite phrasing "two finite, disjoint sets … with
--   `J ∩ V = ∅`" is the content of the input/output distinction;
--   without it "input vs output" is meaningless and hard intervention
--   (which converts members of `V` into members of `J`) becomes
--   ambiguous. Disjointness must live on the structure rather than
--   on the types precisely because we chose the single-`Node`
--   encoding above; there is no type-level wedge to lean on.
--
-- * **`E : Finset (Node × Node)` plus a separate `hE_subset`, not a
--   `Finset ((J ∪ V) × V)` subtype.** Ordered pairs keep `E`'s carrier
--   identical to `L`'s, so the two share every `Finset (Node × Node)`
--   lemma and downstream destructuring is the uniform `(v, w) := e`.
--   Pushing `E ⊆ (J ∪ V) × V` into a subtype was rejected because
--   every consumer (`def_3_5`'s `Pa(v) = {w | (w, v) ∈ E}`,
--   intervention's edge-removal via `Finset.filter`, edge-rewriting
--   in node-splitting) would have to lift through the subtype
--   coercion at every use site. Keeping `hE_subset` (and analogously
--   `hL_subset`) as stand-alone fields lets the constraint be
--   invoked or rewritten on its own.
--
-- * **Directed self-loops `(v, v) ∈ E` are admitted by the type.**
--   The LN — and the rewritten tex spec — impose *no* irreflexivity
--   constraint on `E` (contrast with `L`). Wording-check subtlety
--   `directed_self_loops_allowed_but_bidirected_self_loops_forbidden`
--   flagged this asymmetry as potentially unintended (standard ADMG
--   literature often excludes directed self-loops); we follow the
--   literal LN. Downstream defs that need to exclude `v → v`
--   (acyclicity `def_3_6`, ancestral sets in `def_3_5`) handle that
--   locally rather than this foundational type pre-empting them.
--
-- * **`L : Finset (Node × Node)` plus `hL_symm`, not Mathlib's
--   `Sym2`.** Addition
--   `[l_quotient_vs_ordered_pair_typing_inconsistent]` admits the
--   ordered-pair-plus-symmetry encoding as equivalent to the LN's
--   quotient `(V × V) / ((v₁,v₂) ∼ (v₂,v₁))`. We pick the
--   ordered-pair form because Lean's `Sym2` (built on `Quot`) would
--   force a `Sym2.mk` / `Sym2.lift` dance at every downstream
--   destructuring site — `def_3_5`'s `Sib(v) = {w | (v, w) ∈ L}`,
--   bidirected walks in `def_3_4`, edge-rewriting in intervention /
--   splitting — whereas ordered pairs let `L` share every
--   `Finset (Node × Node)` lemma with `E`. Wording-check subtlety
--   `bidirected_edges_quotient_vs_symmetry_redundancy` flagged the
--   LN's literal text as internally inconsistent on this point
--   (quotient notation paired with a then-redundant symmetry
--   implication); the operator's clarification picks ordered pairs
--   as the canonical interpretation.
--
-- * **Trade-off: each bidirected edge appears twice in `L`.** Under
--   the ordered-pair encoding an undirected bidirected edge between
--   `v₁` and `v₂` appears in `L` as *both* `(v₁, v₂)` and `(v₂, v₁)`.
--   Downstream rows that count or iterate over bidirected edges
--   (counting siblings, summing edge weights, enumerating each
--   undirected edge once) must either divide by two or pick a
--   canonical orientation (e.g. `v₁ < v₂` once a node ordering is in
--   scope). This is the explicit cost of avoiding the quotient.
--
-- * **`hL_irrefl` is its own field, separate from `hL_subset` and
--   `hL_symm`.** Irreflexivity (`(v₁, v₂) ∈ L → v₁ ≠ v₂`) is a
--   distinct LN constraint, and downstream defs sometimes need just
--   irreflexivity (acyclicity, ruling out the trivial bidirected
--   loop) or just symmetry (bidirected walks freely reversing
--   direction) without the other. Bundling them would force every
--   such call site to unpack a conjunction.
--
-- * **No `E ∩ L = ∅` field, by intent.** Addition
--   `[edge_set_disjointness_under_specified]` reads the LN's
--   "(disjoint)" qualifier on the edge sets as *type-level only*.
--   The same ordered pair `(v, w)` over `V` may belong to both `E`
--   and `L` simultaneously. This is intentional; a downstream row
--   that needs the stricter form must add the constraint at the use
--   site.
--
-- * **The empty CDMG (`J = V = ∅`, hence `E = L = ∅`) is a legal
--   inhabitant.** The LN's would-be nonemptiness constraint
--   `J ∪ V ≠ ∅` is *commented out* in the source (and preserved as
--   commented in the rewritten tex spec). Wording-check subtlety
--   `empty_cdmg_admitted_by_active_definition` flagged this; we
--   follow the literal LN. Downstream defs that need a non-empty
--   graph (picking a sink/source vertex, asserting a topological
--   order exists via `def_3_8`, marginalising over a non-empty
--   subset) add that hypothesis at the use site rather than baking
--   it into the foundational type.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: CDMG
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
-- REFACTOR-BLOCK-ORIGINAL-END: CDMG

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: CDMG (was: refactor_CDMG)
-- ref: def_3_1
--
-- A *conditional directed mixed graph* `G` over an ambient node type
-- `Node` is a tuple `(J, V, E, L)` consisting of two disjoint finite
-- vertex sets — `J` (input nodes) and `V` (output nodes) — together
-- with a finite set of directed edges `E ⊆ (J ∪ V) × V` and a finite
-- set of bidirected edges `L`, each of which is an unordered pair of
-- distinct vertices in `V`. Bidirected edges live in `Sym2 Node`, the
-- Mathlib quotient `(Node × Node) / ((a,b) ∼ (b,a))`, which is
-- literally the `(V × V) / ((v₁,v₂) ∼ (v₂,v₁))` of the LN block
-- (addition `[l_quotient_vs_ordered_pair_typing_inconsistent]`
-- explicitly admits this quotient encoding as equivalent to the
-- ordered-pair-plus-symmetry form, and we commit to the quotient).
--
-- CBNs (ch. 4), do-calculus (ch. 5), iSCMs (ch. 8–10), σ/d-separation
-- (ch. 6–7) and causal discovery (ch. 11+) all destructure a CDMG via
-- the four fields `J, V, E, L`; the shape below is chosen so those
-- destructurings remain syntactically uniform, and so that
-- bidirected-edge processing (walk reversal, σ-separation symmetry,
-- collider classification) is structurally orientation-free.
--
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- * **`structure`, not `class` / `abbrev` / Mathlib `SimpleGraph` /
--   `Quiver`.** A CDMG is data, not a typeclass-resolvable property,
--   so `class` is wrong (we never want Lean to "infer the CDMG on
--   `Node`"). `SimpleGraph` is undirected, single-sort, and has no
--   bidirected channel; `Quiver` carries parallel ordered edges only,
--   with no input/output partition and no symmetric sub-relation. A
--   bespoke `structure` is the cheapest encoding that holds all four
--   pieces (J/V partition, directed channel `E`, bidirected channel
--   `L`) in a single record that `def_3_2`–`def_3_8` and downstream
--   chapters destructure as `G.J / G.V / G.E / G.L`.
--
-- * **`Node : Type*` with `[DecidableEq Node]`, not a concrete carrier
--   such as `Fin n` / `ℕ`.** Downstream operations rewrite the vertex
--   set without a canonical numbering (hard intervention moves members
--   between `J` and `V`; node-splitting creates fresh copies;
--   marginalisation projects out subsets); locking `Node` to a
--   concrete carrier would force renumbering at every such operation.
--   `[DecidableEq Node]` is the minimal typeclass that lets `Finset`
--   carry the vertex/edge sets, decides equality of nodes and ordered
--   pairs in the kernel, and (via Mathlib's derived instance) decides
--   equality of `Sym2 Node` so the `L` carrier is also computable.
--
-- * **`Finset` for `J`, `V`, `E`, and `L`, not `Set _` (with a
--   `Set.Finite` witness) nor a subtype.** Addition `[manual_1]` makes
--   finiteness of the vertex sets part of the spec, which then
--   propagates to the edge sets through `hE_subset` / `hL_subset`.
--   `Set _` paired with `Set.Finite` (or a bundled `Fintype`) was
--   rejected on two grounds: (i) the finiteness witness would be a
--   *second* field threaded through every consumer, whereas `Finset`
--   bakes it into the carrier; (ii) `Finset` carries decidable
--   membership, which downstream defs depend on for `Finset.filter`
--   / `biUnion` / `Finset.image` over the family sets (`Pa`, `Ch`,
--   `Anc`, `Desc`, `Sib`, `Dist` in `def_3_5`) and for kernel-level
--   comparisons in topological order (`def_3_8`). A two-sort encoding
--   (`J, V : Type*`) was also rejected because the LN treats `J ∪ V`
--   as a single ambient set everywhere downstream — two sorts would
--   force a `Sum` coproduct and coercions at every use site.
--
-- * **`hJV_disj : Disjoint J V` is an explicit structure field.** The
--   LN phrasing "two finite, disjoint sets … with `J ∩ V = ∅`" is the
--   content of the input/output distinction; without it "input vs
--   output" is meaningless and hard intervention (which converts
--   members of `V` into members of `J`) becomes ambiguous.
--   Disjointness must live on the structure rather than on the types
--   precisely because we chose the single-`Node` encoding above;
--   there is no type-level wedge to lean on.
--
-- * **`E : Finset (Node × Node)` plus a separate `hE_subset`, not a
--   `Finset ((J ∪ V) × V)` subtype.** Ordered pairs keep `E`'s
--   destructuring uniform with `def_3_4`'s typed `WalkStep`
--   constructors `.forwardE` / `.backwardE` and with `def_3_5`'s
--   `Pa(v) = {w | (w, v) ∈ G.E}`. Pushing `E ⊆ (J ∪ V) × V` into a
--   subtype was rejected because every consumer (`def_3_5`,
--   intervention's edge-removal via `Finset.filter`, edge-rewriting
--   in node-splitting) would have to lift through the subtype
--   coercion at every use site. Keeping `hE_subset` as a stand-alone
--   field lets the constraint be invoked or rewritten on its own.
--
-- * **Directed self-loops `(v, v) ∈ E` are admitted by the type.**
--   The LN — and the rewritten tex spec — impose *no* irreflexivity
--   constraint on `E` (contrast with `L`). Wording-check subtlety
--   `directed_self_loops_allowed_but_bidirected_self_loops_forbidden`
--   flagged this asymmetry as potentially unintended (standard ADMG
--   literature often excludes directed self-loops); we follow the
--   literal LN. Downstream defs that need to exclude `v → v`
--   (acyclicity `def_3_6`, ancestral sets in `def_3_5`) handle that
--   locally rather than this foundational type pre-empting them.
--
-- * **`L : Finset (Sym2 Node)`, not `Finset (Node × Node)` paired
--   with a `hL_symm` symmetry axiom.** This is the central encoding
--   commitment of the `cdmg_typed_edges` design (see
--   `leanification/refactors/refactor_cdmg_typed_edges.md` for the
--   driving rationale). `Sym2 α` is Mathlib's quotient of `α × α` by
--   the swap relation `(a,b) ∼ (b,a)`, so `Finset (Sym2 Node)` is
--   *literally* the `(V × V) / ((v₁,v₂) ∼ (v₂,v₁))` of the LN block.
--   Addition `[l_quotient_vs_ordered_pair_typing_inconsistent]`
--   explicitly admits this encoding as equivalent to the ordered-
--   pair-plus-symmetry form; we commit to the quotient because three
--   downstream consequences justify the extra `Sym2.lift` / `Sym2.mk`
--   boilerplate at L-manipulation sites:
--
--   - **Swap-symmetry is definitional.** The LN's
--     `(v₁,v₂) ∈ L ⟹ (v₂,v₁) ∈ L` implication is vacuous under the
--     quotient typing — `s(v₁,v₂) = s(v₂,v₁)` holds by construction
--     — so no `hL_symm` field is needed. Wording-check subtlety
--     `bidirected_edges_quotient_vs_symmetry_redundancy` flagged the
--     LN's literal text as internally inconsistent on this point
--     (quotient notation paired with a then-redundant symmetry
--     implication); the `Sym2` encoding resolves the redundancy
--     cleanly without picking a side of the LN's two-encoding
--     ambiguity at every consumer.
--
--   - **Walk reversal preserves channel.** In `def_3_4`'s typed
--     `WalkStep`, a bidirected step `.bidir (h : s(u,v) ∈ G.L)`
--     reverses to `.bidir` with the same `s(u,v) = s(v,u)` witness —
--     no `hL_symm` invocation, no orientation swap on the stored
--     pair, and structurally impossible for the reversed step to be
--     misclassified as a directed step. The ordered-pair-plus-
--     symmetry alternative would lose channel information on the
--     *writing-mirror* class of CDMGs (where some `(v,w)` sits in
--     both `E` and `L` simultaneously): a forced swap on reversal
--     could land the swapped pair in `E` coincidentally, and any
--     downstream predicate reading the channel off the stored pair
--     (e.g. `def_3_16`'s `IsBlockableNonCollider`) would
--     misclassify the L-step.
--
--   - **`claim_3_22` (σ-separation symmetry) closes by
--     construction.** Under the ordered-pair-plus-symmetry
--     alternative, the symmetry theorem hits an irreducible
--     obstruction on writing-mirror CDMGs — this is the *driving*
--     downstream consumer of the encoding choice. Under `Sym2`,
--     walk reversal and channel classification are structurally
--     orientation-free, so the symmetry argument reduces to a
--     straightforward induction over the typed `WalkStep`.
--
--   Trade-off: each L-manipulation site (`def_3_5`'s `Sib`, the §3.2
--   restriction / marginalisation / splitting constructors
--   `def_3_10`–`def_3_14`, `claim_3_16`–`claim_3_19`) threads through
--   `Sym2.mk` / `Sym2.lift` rather than destructuring ordered pairs
--   directly. We accept this boilerplate as the price of structural
--   symmetry — it converts a class of subtle semantic bugs (writing-
--   mirror channel misclassification) into mechanical `Sym2` API
--   calls that Mathlib already provides.
--
-- * **`hL_irrefl` is phrased as `¬ s.IsDiag`, not as
--   `∀ v₁ v₂, (v₁,v₂) ∈ L → v₁ ≠ v₂`.** `Sym2.IsDiag` is Mathlib's
--   canonical predicate for "this unordered pair is a self-pair"
--   (`Sym2.IsDiag s(x,y) ↔ x = y`), and is the right idiom on
--   `Sym2 _` because it doesn't force destructuring through
--   `Sym2.mk` at every irreflexivity-check site. The LN's `v₁ ≠ v₂`
--   clause (no bidirected self-loops `v ↔ v`) is preserved verbatim;
--   the redundant `(v₂,v₁) ∈ L` half of the LN's compound
--   implication disappears as noted above.
--
-- * **`hL_subset` quantifies via `Sym2.Mem` (`v ∈ s`), not by
--   destructuring `s = s(v₁,v₂)`.** Universally quantifying over
--   `v ∈ s` is the canonical Mathlib idiom for "every node mentioned
--   by `s` lies in `V`"; it handles both elements of the unordered
--   pair simultaneously and avoids picking a representative.
--   Destructuring via `Sym2.mk` was rejected because every consumer
--   would have to lift through the quotient at every use site, and
--   would force a choice of representative that — by the swap
--   quotient — has no canonical value.
--
-- * **No `E ∩ L = ∅` field, by intent.** Addition
--   `[edge_set_disjointness_under_specified]` reads the LN's
--   "(disjoint)" qualifier on the edge sets as *type-level only*:
--   `E : Finset (Node × Node)` and `L : Finset (Sym2 Node)` are
--   carriers over *distinct* types, so set-theoretic intersection
--   isn't even well-typed. No graph-theoretic mutual-exclusion is
--   imposed between directed and bidirected channels: the same
--   vertex pair `{v, w}` may simultaneously support an L-edge
--   `s(v,w) ∈ G.L` *and* a directed edge `(v,w) ∈ G.E` (or
--   `(w,v) ∈ G.E`). A downstream row that needs the stricter form
--   must add the constraint at the use site. The `Sym2` encoding
--   eliminates the *representation* overlap (an L-edge is an
--   unordered pair, an E-edge is an ordered one) while preserving
--   the *graph-theoretic* admissibility the LN intends.
--
-- * **The empty CDMG (`J = V = ∅`, hence `E = L = ∅`) is a legal
--   inhabitant.** The LN's would-be nonemptiness constraint
--   `J ∪ V ≠ ∅` is *commented out* in the source (and preserved as
--   commented in the rewritten tex spec). Wording-check subtlety
--   `empty_cdmg_admitted_by_active_definition` flagged this; we
--   follow the literal LN. Downstream defs that need a non-empty
--   graph (picking a sink/source vertex, asserting a topological
--   order exists via `def_3_8`, marginalising over a non-empty
--   subset) add that hypothesis at the use site rather than baking
--   it into the foundational type.
-- def_3_1 -- start statement
structure refactor_CDMG (Node : Type*) [DecidableEq Node] where
  J : Finset Node
  V : Finset Node
  hJV_disj : Disjoint J V
  E : Finset (Node × Node)
  hE_subset : ∀ ⦃e : Node × Node⦄, e ∈ E → e.1 ∈ J ∪ V ∧ e.2 ∈ V
  L : Finset (Sym2 Node)
  hL_subset : ∀ ⦃s : Sym2 Node⦄, s ∈ L → ∀ ⦃v : Node⦄, v ∈ s → v ∈ V
  hL_irrefl : ∀ ⦃s : Sym2 Node⦄, s ∈ L → ¬ s.IsDiag
-- def_3_1 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: CDMG

end Causality
