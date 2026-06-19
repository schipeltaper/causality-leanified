import Chapter3_GraphTheory.Section3_1.CDMG

namespace Causality

/-!
# Hard intervention on CDMGs (`def_3_10`)

This file formalises the LN definition `def_3_10`
(`\label{def:G_hard_intervention}`) — the *hard intervention*
operation `G ↦ G_{\doit(W)}` on a CDMG.  Given a CDMG
`G = (J, V, E, L)` and a subset of nodes `W ⊆ J ∪ V`, the intervened
CDMG has

* `J_{\doit(W)} := J ∪ W` (every node of `W` becomes an input node),
* `V_{\doit(W)} := V ∖ W`,
* `E_{\doit(W)} := E ∖ { (v₁, v₂) ∈ E | v₂ ∈ W }` (every directed
  edge whose head lies in `W` is removed),
* `L_{\doit(W)} := L ∖ { (v₁, v₂) ∈ L | v₂ ∈ W }`, *symmetrised*
  under the `hL_symm` axiom of `def_3_1` so that `L_{\doit(W)}` is a
  symmetric subset of `(V ∖ W) × (V ∖ W)`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/def_3_10_HardInterventionOn.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:G_hard_intervention}`).  The symmetrisation of item iv is
documented in the tex's *"Remark on item iv.\ and the symmetry of
`L`"*: under `def_3_1`'s ordered-pair encoding the literal one-sided
removal at item iv does NOT preserve `hL_symm`, so the constructor
*must* produce a symmetric `L_{\doit(W)}` in order to satisfy the
CDMG axioms.  The two-sided filter `fun e => e.1 ∉ W ∧ e.2 ∉ W` is
the unique reading consistent with both (a) the LN's natural-language
gloss "remove all edges into nodes from `W`" (a bidirected edge is
into *both* of its endpoints, `def_3_3` item ii) and (b) the LN's own
assertion that `G_{\doit(W)}` is itself a CDMG.

The substantive design rationale — why this Lean shape, why
`Finset.filter`, why the asymmetric `e.2 ∉ W` for `E` and the
symmetric `e.1 ∉ W ∧ e.2 ∉ W` for `L`, how `W ∩ J ≠ ∅` behaves —
lives in the `--` comment block immediately above the `def`
declaration.  Read that block before changing a field; it is the
load-bearing contract for the do-calculus chapters (ch. 5+) and the
iSCM intervention algebra (ch. 8+).
-/

namespace CDMG

-- def_3_10 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_10 --- end helper

-- ref: def_3_10
--
-- The *hard intervention on `G` with respect to `W`* is the
-- `CDMG` `G.hardInterventionOn W hW` whose four
-- components are
--
--   * `J' := G.J ∪ W`                                 — every node of
--     `W` is converted to an input node;
--   * `V' := G.V \ W`                                 — every node of
--     `W` is removed from `V`;
--   * `E' := { e ∈ G.E | e.2 ∉ W }`                   — every directed
--     edge whose head is in `W` is removed; every other directed edge
--     is retained;
--   * `L' := { s ∈ G.L | ∀ v ∈ s, v ∉ W }`            — every
--     bidirected edge incident at any node of `W` (any endpoint of the
--     unordered pair) is removed.
--
-- The hypothesis `hW : W ⊆ G.J ∪ G.V` is the LN's
-- "$W \subseteq J \cup V$" precondition.
--
-- This declaration is the post-refactor port of `def_3_10` against the
-- `cdmg_typed_edges` design (`def_3_1` shape:
-- `L : Finset (Sym2 Node)`, no `hL_symm` axiom).  The deviation
-- `hard_intervention_l_symmetrized_removal` recorded against the
-- pre-refactor encoding is structurally resolved here: under the
-- `Sym2` typing of `L`, the LN's item iv. set-builder
-- `L \sm \{ (v_1, v_2) \in L \mid v_2 \in W \}` and its
-- natural-language gloss "remove all edges into nodes from `W`"
-- collapse to a single LN-literal reading — there is no ordered
-- "second component" on a `Sym2 Node` value to test, so the only
-- sensible filter is "any endpoint of the unordered pair lies in
-- `W`", which is what the predicate
-- `fun s => ∀ v ∈ s, v ∉ W` (kept-condition) expresses.  No
-- symmetrisation step is required, because swap-symmetry is
-- *definitional* on `Sym2` (`s(v, w) = s(w, v)`).
/-
LN tex (rewritten `def_3_10_HardInterventionOn`, items i–iv):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq J \cup V$.
    The intervened CDMG of $G$ w.r.t. $W$ is
    $G_{\doit(W)} := (J_{\doit(W)}, V_{\doit(W)}, E_{\doit(W)},
                      L_{\doit(W)})$,
    where
      i.   $J_{\doit(W)} := J \cup W$;
      ii.  $V_{\doit(W)} := V \sm W$;
      iii. $E_{\doit(W)} := E \sm \{ (v_1, v_2) \in E \mid v_2 \in W \}$;
      iv.  $L_{\doit(W)} := L \sm \{ (v_1, v_2) \in L \mid v_2 \in W \}$.

LN block (verbatim, for backup):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq J \cup V$ a
    subset of nodes.  The *intervened CDMG* w.r.t. $W$ of $G$ is the
    CDMG $G_{\doit(W)} := (J_{\doit(W)}, V_{\doit(W)}, E_{\doit(W)},
    L_{\doit(W)})$, where i.) $J_{\doit(W)} := J \cup W$, ii.)
    $V_{\doit(W)} := V \sm W$, iii.) $E_{\doit(W)} := E \sm
    \{ v \tuh w \mid v \in G, w \in W \}$, iv.) $L_{\doit(W)} :=
    L \sm \{ v \huh w \mid v \in G, w \in W \}$, where we turn all
    nodes from $W$ into input nodes and remove all edges into nodes
    from $W$.
-/
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- * **`def`, not `structure` / `inductive` / `class`.**  A hard
--   intervention is a *function*
--   `CDMG Node → Finset Node → … → CDMG Node`, not
--   new data and not a typeclass-resolvable property.  The CDMG
--   already has its `structure` (`def_3_1`); this row simply produces
--   a new CDMG from an existing one.  Wrapping the result in a fresh
--   structure (e.g. a `HardInterventionOn` record carrying the
--   intervened graph as a field) was rejected because every downstream
--   consumer in ch. 5 / ch. 8+ destructures the intervened graph the
--   same way any other CDMG is destructured — via
--   `(G.hardInterventionOn W hW).J`, `…V`, `…E`, `…L` — and
--   an extra wrapping layer would force a re-destructuring step at
--   every such call site.  An `inductive` was rejected for the same
--   reason: it would force pattern-matching on the constructor where
--   the LN simply names the four fields.
--
-- * **`hW : W ⊆ G.J ∪ G.V` is an explicit argument, not a
--   sub-condition threaded through the body.**  The LN's
--   "Let $W \subseteq J \cup V$" is part of the *signature* of the
--   hard intervention operation; without it the resulting tuple would
--   still satisfy the four `CDMG` axioms (the typing
--   constraints on `G.E` and `G.L` alone are strong enough — see the
--   "$W \cap J \neq \emptyset$" bullet below for why `hW` is not
--   consumed in the proofs), but the LN-faithful *statement* requires
--   `hW` at the signature level.  Making it an explicit argument
--   keeps the precondition visible at every call site and is the
--   natural place for downstream lemmas about
--   `G.hardInterventionOn W` to plug it in.  Pushing `hW`
--   into an instance was rejected: subset facts are not
--   typeclass-resolvable in any general way and would force every
--   caller to manually discharge the membership.
--
-- * **`Finset.filter` for the edge-set removals, not `Finset.image` /
--   recursion / a quotient.**  The LN writes the removal sets in
--   set-builder form `E \setminus \{ … \mid … \}` (and analogously for
--   `L`).  Lean's `Finset.filter` is the closest primitive
--   (`Finset.mem_filter` gives exactly
--   `e ∈ s.filter p ↔ e ∈ s ∧ p e`), shares the
--   `Finset (Node × Node)` carrier for `E` with every other
--   chapter-3 consumer (`def_3_5`'s family-set filters, `def_3_8`'s
--   topological-order projections), and decidability of the filter
--   predicate follows from `[DecidableEq Node]` plus, for the `L`
--   filter, the locally-provided `Sym2.Mem`-based decidable
--   instance (see the "L-filter predicate decidability" bullet
--   below).  `Finset.image` was rejected because the LN takes a
--   *difference* with the original edge set, not a re-mapping;
--   recursion is overkill for a single set-comprehension.
--
-- * **Directed-edge removal is one-sided (`e.2 ∉ W`); bidirected-edge
--   removal is endpoint-universal (`∀ v ∈ s, v ∉ W`).**  Item iii of
--   the rewritten tex says "remove every directed edge whose head
--   lies in `W`": the head of `(v₁, v₂) ∈ G.E` is `v₂`, so the
--   kept-condition is `e.2 ∉ W` — no symmetrisation needed on the
--   directed channel because `G.E` itself is not symmetric.
--
--   Item iv now lives on `Finset (Sym2 Node)`.  A `Sym2 Node` value
--   is an *unordered* pair, so there is no "first" / "second"
--   component to test against `W` — both endpoints sit on the same
--   footing.  The LN's literal set-builder
--   `L \sm \{ (v_1, v_2) \in L \mid v_2 \in W \}` (and the verbatim
--   `\{ v \huh w \mid v \in G, w \in W \}` in the original block) is
--   *unambiguous* under this typing once we resolve "$v_2$" to "any
--   endpoint of the unordered pair", which is the only well-defined
--   reading.  The kept-condition is
--   `fun s => ∀ v ∈ s, v ∉ W` (i.e. "no endpoint of `s` lies in
--   `W`"), which is structurally symmetric *by construction* on the
--   `Sym2` quotient — there is no orientation to commute over, no
--   `hL_symm` axiom to preserve, and no two-sided workaround needed.
--
--   This is the load-bearing reason the post-refactor encoding is
--   strictly more LN-faithful than the pre-refactor encoding it
--   replaces: under the pre-refactor `L : Finset (Node × Node)` plus
--   `hL_symm` form, the LN's literal one-sided filter
--   `e.2 ∈ W` did not preserve symmetry on mirror pairs `(v, w)`
--   vs `(w, v)`, so the constructor had to *symmetrise* the removal
--   to `e.1 ∉ W ∧ e.2 ∉ W` in order to satisfy `hL_symm`.  That
--   symmetrisation was a registered deviation
--   (`hard_intervention_l_symmetrized_removal` in
--   `leanification/deviations.json`).  Under the `Sym2` encoding
--   there is no mirror-pair to symmetrise *over* — `s(v, w)` and
--   `s(w, v)` are *equal* elements of `Sym2 Node` — so the literal
--   LN filter reads cleanly as "any endpoint in `W`" and the
--   deviation is *structurally resolved*: the post-refactor Lean is
--   the literal reading of the LN under `def_3_1`'s post-refactor
--   shape.  The deviation register entry stays in
--   `deviations.json` for historical record (Phase 7 cleanup
--   handles its retirement); we do not remove it ourselves.
--
--   This also discharges wording-check subtlety
--   `bidirected_edge_removal_assumes_symmetric_representation`
--   (`leanification/working_subtlety_register.json`), which flagged
--   the LN's literal item iv as ambiguous between an
--   ordered-representation reading (only edges with the in-`W`
--   endpoint in the *second* slot are removed) and the symmetric
--   reading the natural-language gloss intends.  Under `Sym2 Node`
--   there are no slots, so the ambiguity is vacuous: the filter
--   `∀ v ∈ s, v ∉ W` is the only well-defined reading and matches
--   the intended symmetric semantics by construction.
--
--   The *load-bearing downstream consumer* driving this structural
--   orientation-freeness is `claim_3_22` (σ-separation symmetry).
--   Under the post-refactor typed `WalkStep` of `def_3_4`, a
--   bidirected step `.bidir (h : s ∈ G.L)` reverses to a `.bidir`
--   step on the *same* `s` (because `s(v, w) = s(w, v)` is
--   definitional on `Sym2`), so the symmetry theorem reduces to a
--   clean structural induction over typed walk steps — no
--   `hL_symm` invocation, no orientation swap, no case-split on
--   which endpoint sat in `W`.  Under the pre-refactor encoding the
--   same theorem hit an irreducible obstruction on writing-mirror
--   CDMGs (graphs where some `(v, w)` sits in both `E` and `L`
--   simultaneously); the `cdmg_typed_edges` refactor exists
--   primarily so that `claim_3_22` and its sibling rows
--   (`claim_3_16`–`claim_3_19`) can close.  Symmetric removal of
--   bidirected edges under hard intervention being *structural*
--   (not enforced by a side condition like the pre-refactor
--   `hL_symm`-driven two-sided filter) is the load-bearing
--   contract `claim_3_22`'s proof relies on at this row.
--
--   The `hL_irrefl` proof obligation of
--   `G.hardInterventionOn W hW` transports cleanly from
--   `G.hL_irrefl`: since `L' = G.L.filter (fun s => ∀ v ∈ s, v ∉ W)`
--   is a subset of `G.L`, every `s ∈ L'` satisfies
--   `¬ s.IsDiag` because `G.hL_irrefl` says so for every `s ∈ G.L`.
--   The `hL_subset` obligation likewise transports: for `s ∈ L'`
--   and `v ∈ s`, the filter predicate gives `v ∉ W`, and
--   `G.hL_subset` (applied to `s ∈ G.L` and `v ∈ s`) gives `v ∈ G.V`;
--   combine to land in `G.V \ W`.
--
--   Membership rule on `(G.hardInterventionOn W hW).L` is
--   now the clean, single-equation form
--     `s ∈ (G.hardInterventionOn W hW).L
--        ↔ s ∈ G.L ∧ ∀ v ∈ s, v ∉ W`,
--   directly from `Finset.mem_filter`.  No mirror-pair gotcha can
--   arise — the pre-refactor file had a WARNING block flagging the
--   gotcha under the `Finset (Node × Node)` encoding (a one-sided
--   convenience read silently mishandled the mirror pair and
--   contradicted `hL_symm`).  Under `Sym2`, there is no mirror pair
--   to mishandle.
--
-- * **Items i, ii are verbatim LN translations; item iii's `v ∈ G`
--   clause is folded into `def_3_1`'s `hE_subset` typing; item iv's
--   `v ∈ G` clause becomes vacuous under the `Sym2.Mem` quantifier.**
--   Items i (`J' := G.J ∪ W`) and ii (`V' := G.V \ W`) are direct,
--   literal translations of the LN set-builder formulae — no design
--   choice beyond the `Finset` carrier was made, and no deviation
--   exists there.  In item iii the LN's set-builder reads
--   `\{ v \tuh w \mid v \in G, w \in W \}`; per the tex's
--   "Disambiguation of the LN's `v ∈ G` quantifier" paragraph, the
--   informal `v ∈ G` abbreviates `v ∈ J ∪ V`.  Under `def_3_1`'s
--   `hE_subset`, the clause `v_1 ∈ J ∪ V` is *automatic* on every
--   element of `G.E`, so the `Finset.filter` predicate reduces to the
--   single conjunct `e.2 ∉ W`.  In item iv the LN's set-builder
--   reads `\{ v \huh w \mid v \in G, w \in W \}`; under the `Sym2`
--   typing the "$v$ and $w$" of the LN are both endpoints of an
--   unordered pair (no privileged role), and the bounded quantifier
--   `∀ v ∈ s, v ∉ W` ranges precisely over the two endpoints — the
--   "$v \in G$" clause is automatically discharged by
--   `def_3_1`'s `hL_subset` (every endpoint of every `s ∈ G.L`
--   lies in `G.V ⊆ G.J ∪ G.V`).
--
-- * **`hJV_disj` for `G_{\doit(W)}` is one line of set algebra.**
--   `(G.J ∪ W) ∩ (G.V \ W) = ∅` decomposes as the union of (i)
--   `G.J ∩ (G.V \ W) = ∅`, which follows from `G.hJV_disj`
--   (`G.J ∩ G.V = ∅`) and `(G.V \ W) ⊆ G.V`, and (ii)
--   `W ∩ (G.V \ W) = ∅`, which is immediate from `Finset.sdiff`.
--   The proof does not consume `hW`; the disjointness is structural,
--   independent of the `W ⊆ J ∪ V` precondition.  Unchanged from the
--   pre-refactor encoding (`J`, `V`, `hJV_disj` are untouched by the
--   refactor).
--
-- * **`hE_subset` for `G_{\doit(W)}` follows from `G.hE_subset`
--   plus the head-not-in-`W` filter.**  For every surviving
--   `e ∈ G.E.filter (fun e => e.2 ∉ W)`, the unfiltered axiom
--   `G.hE_subset` gives `e.1 ∈ G.J ∪ G.V` and `e.2 ∈ G.V`; the
--   filter clause gives `e.2 ∉ W`, so `e.2 ∈ G.V \ W` immediately.
--   For `e.1`, a case-split on which of `G.J`, `W ∩ G.V`, or
--   `G.V \ W` it belongs to lands it in `(G.J ∪ W) ∪ (G.V \ W)`.
--   No constraint on `e.1 ∈ W` is imposed by the filter — that is
--   intentional: directed edges *out of* a node in `W ∩ G.V` are
--   retained, matching the LN's "remove all edges *into* nodes
--   from `W`" gloss (a directed edge `(v, w)` is *into* `w`, not
--   *into* `v`, per `def_3_3` item i).  Unchanged from the
--   pre-refactor encoding (`E`'s ordered-pair typing is untouched
--   by the refactor; only the `L`-side filter changed).
--
-- * **`W ∩ J ≠ ∅` is admitted; behaviour matches the tex
--   case-analysis.**  The LN hypothesis is `W ⊆ J ∪ V`; we do *not*
--   additionally require `W ∩ J = ∅`.  Wording-check subtlety
--   `intervention_on_already_input_nodes_admits_nontrivial_edge_changes`
--   (`leanification/working_subtlety_register.json`) flagged the
--   LN's asymmetry between the node-set rule (idempotent on `W ∩ J`
--   for both `J' := G.J ∪ W` and `V' := G.V \ W`) and the edge-set
--   rule (literally fires on edges with an endpoint in `W ∩ J`) as
--   potentially diverging from the natural-language "we turn all
--   nodes from `W` into input nodes" intuition (which reads as if
--   nodes already in `J` are exempt).  We follow the literal LN's
--   reading; the divergence is harmless under `def_3_1`'s typing
--   constraints, as the next sentences explain.  The tex's "On the
--   case $W \cap J \neq \emptyset$" paragraph spells out the
--   behaviour:
--   items i and ii are *idempotent* on `W ∩ J` (`G.J ∪ W` is unchanged
--   at those nodes; `G.V \ W` is unaffected because `G.J` is disjoint
--   from `G.V` by `hJV_disj`); items iii and iv still mechanically
--   fire on edges with an endpoint in `W ∩ J`, but `def_3_1`'s typing
--   constraints `E ⊆ (J ∪ V) × V` and the `Sym2`-`hL_subset`
--   restriction of `L` to pairs in `G.V` forbid any edge from having
--   a relevant endpoint in `J` in the first place, so the filters
--   are *de facto* no-ops on `W ∩ J`.  We do not bake the idempotency
--   into the type; any downstream row that wants "intervening on a
--   subset of `J` is the identity" derives it as a lemma.  This is
--   also the reason `hW` is not consumed in the four proof
--   obligations below: the typing constraints from `G` already
--   exclude every problematic case, and `hW` is carried purely for
--   LN-faithfulness of the *signature*.
--
-- * **Argument order
--   `(G : CDMG Node) (W : Finset Node) (hW : …)`.**
--   `G` first matches the convention of every chapter-3 predicate
--   (`G.tuh`, `G.huh`, `G.adjacent`, `G.into`, `G.outOf`), enabling
--   dot-notation `G.hardInterventionOn W hW`.  `W` precedes
--   `hW` so the call site reads left-to-right like the LN's "let
--   `W ⊆ J ∪ V` be a subset".
--
-- * **`where` syntax with named fields, not anonymous-constructor
--   `⟨ … ⟩`.**  The `CDMG` `structure` has eight fields
--   (`J`, `V`, `hJV_disj`, `E`, `hE_subset`, `L`, `hL_subset`,
--   `hL_irrefl`) — one fewer than the pre-refactor nine, because
--   `hL_symm` is gone (swap-symmetry is definitional on `Sym2`).
--   An anonymous-constructor form would interleave data and proof
--   obligations in a positional list, making the correspondence with
--   `def_3_1`'s `structure` opaque at a glance.
--   `where … J := … V := …` keeps every field labelled and lets the
--   proof obligations sit next to the data they refer to.
--
-- * **L-filter predicate decidability.**  The filter
--   `G.L.filter (fun s => ∀ v ∈ s, v ∉ W)` requires
--   `DecidablePred (fun s => ∀ v ∈ s, v ∉ W)` to type-check.
--   `Sym2.Mem` is decidable on individual elements via
--   `Sym2.Mem.decidable [DecidableEq α]`, but a *bounded universal*
--   over `Sym2.Mem` (`∀ v ∈ s, P v`) needs its own
--   `DecidablePred` instance.  We supply one locally via
--   `Sym2.recOnSubsingleton` + `Sym2.ball` (the Mathlib lemma
--   `(∀ c ∈ s(a, b), p c) ↔ p a ∧ p b`): every `s : Sym2 Node` is
--   `s(a, b)` for some `a, b`; the universal reduces to
--   `a ∉ W ∧ b ∉ W`; conjunction of decidable propositions is
--   decidable.  This is preferable to (a) opening `Classical`
--   project-wide (which would silently desugar every decidable lookup
--   to `Classical.dec` and lose the kernel-computable behaviour the
--   `Finset` API depends on) and (b) reformulating the filter
--   predicate via `Sym2.lift` + a custom subtype-of-pair-function
--   (which would create boilerplate at every membership-reasoning
--   site).  No `[Decidable]` instance burden propagates to
--   consumers of `G.hardInterventionOn W hW`: this private
--   instance is found automatically by typeclass resolution at the
--   `Finset.filter` elaboration site, and the only typeclass
--   parameter consumers see remains `[DecidableEq Node]` — the same
--   one `def_3_1`'s `CDMG` already requires.
--
-- * **`def`, not `noncomputable def`.**  Both filters
--   (`G.E.filter (fun e => e.2 ∉ W)` and
--   `G.L.filter (fun s => ∀ v ∈ s, v ∉ W)`) are kernel-computable:
--   `Finset.filter` is computable whenever its predicate is
--   `Decidable`, and `Sym2 Node`'s `DecidableEq` is itself derived
--   from `[DecidableEq Node]` by Mathlib (so `s ∈ G.L` is
--   decidable, and the local `DecidablePred` instance above
--   handles the bounded universal `∀ v ∈ s, v ∉ W`).  The
--   intervened CDMG is therefore a *computable* construction,
--   matching the pre-refactor design and keeping
--   `#eval (G.hardInterventionOn W hW).L` available for
--   inspecting the intervened graph on small concrete examples
--   (the same channel `verify_with_examples` exercised to validate
--   this row).  No `Classical.dec`-style shortcut was needed —
--   opening `Classical` project-wide was rejected at the `def_3_1`
--   design stage precisely to keep the entire CDMG API
--   kernel-computable, and the local `DecidablePred` instance
--   above preserves that property for the `L`-side filter without
--   leaking anything to consumers.
--
-- * **Downstream consumers.**  Every do-calculus row of ch. 5 (the
--   interventional CBN factorisation `do(W)`, the three rules of
--   do-calculus, identifiability via the ID algorithm), the iSCM
--   intervention algebra of ch. 8–10 (composition of hard
--   interventions, disjoint-intervention commutativity), and the
--   marginalisation-intervention interaction of `claim_3_18`, as
--   well as the topological-order preservation of `claim_3_3` /
--   `claim_3_13`, all rest on the four field assignments above.
--   Post-refactor, these consumers see the `Sym2`-native L filter —
--   no symmetrisation step is needed in any of them, and the
--   membership rule on `(G.hardInterventionOn W hW).L`
--   reduces to a single `Finset.mem_filter` application without
--   case-splitting on which endpoint sat in `W`.  This is the
--   primary downstream payoff of the `cdmg_typed_edges` refactor
--   at the `def_3_10` row.
-- ## Proof helpers for the four CDMG axioms under hard intervention
--
-- The four private lemmas below discharge the four proof obligations
-- of `def_3_1`'s post-refactor `CDMG` structure
-- (`hJV_disj`, `hE_subset`, `hL_subset`, `hL_irrefl`) for the
-- hard-intervention construction.  One fewer than the pre-refactor
-- five, because the pre-refactor `hL_symm` obligation has gone away
-- — swap-symmetry is definitional on `Sym2`.  They are factored out
-- of the structure-literal body of `hardInterventionOn` so
-- the def body is pure data + lemma references — the website builder
-- renders the def's signature, and a reader sees the data
-- assignments without proof clutter.  Per the `W ∩ J ≠ ∅`
-- design-choice bullet above, none of the obligations consume `hW`;
-- `hW` is carried on the def's signature purely for LN-faithfulness.

private lemma hardInterventionOn_hJV_disj
    (G : CDMG Node) (W : Finset Node) :
    Disjoint (G.J ∪ W) (G.V \ W) := by
  refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
  · exact Finset.disjoint_left.mpr fun a haJ haVW =>
      Finset.disjoint_left.mp G.hJV_disj haJ (Finset.mem_sdiff.mp haVW).1
  · exact Finset.disjoint_left.mpr fun a haW haVW =>
      (Finset.mem_sdiff.mp haVW).2 haW

private lemma hardInterventionOn_hE_subset
    (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃e : Node × Node⦄, e ∈ G.E.filter (fun e => e.2 ∉ W) →
      e.1 ∈ (G.J ∪ W) ∪ (G.V \ W) ∧ e.2 ∈ G.V \ W := by
  intro e he
  obtain ⟨heE, he2⟩ := Finset.mem_filter.mp he
  obtain ⟨he1, he2V⟩ := G.hE_subset heE
  refine ⟨?_, Finset.mem_sdiff.mpr ⟨he2V, he2⟩⟩
  rcases Finset.mem_union.mp he1 with hJ | hV
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
  · by_cases hW1 : e.1 ∈ W
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hW1)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, hW1⟩)

-- Local decidability instance for the L-filter predicate.  See the
-- "L-filter predicate decidability" design-choice bullet above for
-- the rationale; the instance is `private` because no downstream
-- consumer should need to reach in and reference it by name (Lean's
-- typeclass resolution finds it automatically at the `Finset.filter`
-- elaboration site).
private instance hardInterventionOn_decidable_bAll
    (W : Finset Node) :
    DecidablePred (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W) := fun s =>
  s.recOnSubsingleton fun _ _ => decidable_of_iff' _ Sym2.ball

private lemma hardInterventionOn_hL_subset
    (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃s : Sym2 Node⦄, s ∈ G.L.filter (fun s => ∀ v ∈ s, v ∉ W) →
      ∀ ⦃v : Node⦄, v ∈ s → v ∈ G.V \ W := by
  intro s hs v hv
  obtain ⟨hsL, hsW⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_sdiff.mpr ⟨G.hL_subset hsL hv, hsW v hv⟩

private lemma hardInterventionOn_hL_irrefl
    (G : CDMG Node) (W : Finset Node) :
    ∀ ⦃s : Sym2 Node⦄, s ∈ G.L.filter (fun s => ∀ v ∈ s, v ∉ W) →
      ¬ s.IsDiag := by
  intro s hs
  exact G.hL_irrefl (Finset.mem_filter.mp hs).1

-- `hW` is bound on the signature for LN-faithfulness ("Let
-- `W ⊆ J ∪ V`") but is not consumed by any of the four obligations —
-- `def_3_1`'s typing constraints already exclude every problematic
-- case (see the `W ∩ J ≠ ∅` design-choice bullet above).  The
-- `set_option` keeps the linter quiet without dropping the binder
-- from the signature (which is part of the LN-faithful encoding and
-- the call-site contract `G.hardInterventionOn W hW`).
set_option linter.unusedVariables false in
-- def_3_10 -- start statement
def hardInterventionOn (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V) : CDMG Node where
  J := G.J ∪ W
  V := G.V \ W
  hJV_disj := hardInterventionOn_hJV_disj G W
  E := G.E.filter (fun e => e.2 ∉ W)
  hE_subset := hardInterventionOn_hE_subset G W
  L := G.L.filter (fun s => ∀ v ∈ s, v ∉ W)
  hL_subset := hardInterventionOn_hL_subset G W
  hL_irrefl := hardInterventionOn_hL_irrefl G W
-- def_3_10 -- end statement

end CDMG

end Causality
