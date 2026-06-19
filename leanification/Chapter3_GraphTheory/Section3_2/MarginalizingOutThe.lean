import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGTypes
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingHard
import Chapter3_GraphTheory.Section3_2.MarginalizationAK
import Chapter3_GraphTheory.Section3_2.TwoDisjointNode

-- The proof body uses `show` extensively to make definitional rewrites
-- explicit at the reader's level (rather than `change`, which the style
-- linter prefers — but where every `show` here is followed by a tactic
-- consuming the surfaced goal, so `show` reads more naturally).  The
-- linter is silenced file-wide to keep the build noise-free; semantics
-- are unchanged.
set_option linter.style.show false

namespace Causality

/-!
# Marginalizing out the output part of splitted nodes equals hard intervention (`claim_3_19`)

This file formalises the LN lemma `claim_3_19`
(`\label{marginalizing-out-the-output-part-of-splitted-nodes-equals-hard-intervention}`
in `graphs.tex`): for any CDMG `G = (J, V, E, L)` and any subset
`W ⊆ V` of output nodes, the CDMG obtained by first node-splitting on
`W` (SWIG, `def_3_12` `nodeSplittingHard`) and then marginalising out
the output-side copies `W^o` (`def_3_14` `marginalize`) is the same
CDMG as the hard-intervention `G_{doit(W)}` (`def_3_10`
`hardInterventionOn`):
`G_{doit(W)} ≅ (G_{swig(W)})^{∖ W^o}, w ↦ w^i`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_19_statement_MarginalizingOutThe.tex`, verified equivalent
to the LN block.  `addition_to_the_LN` is empty for this row.  The
rewrite spells the LN's literal one-clause map "`w ↦ w^i`" out as the
full three-case bijection
`φ : G_{doit(W)} → (G_{swig(W)})^{∖ W^o}` that is the identity on
`J`, the identity on `V ∖ W`, and `w ↦ w^i` on `W` (per the LN-critic
working-phase subtlety `isomorphism_map_unspecified_outside_W`,
made explicit by the rewrite).

## Carrier-mismatch wrinkle (the load-bearing Lean-shape decision)

The LHS `G.hardInterventionOn W _` lives in `CDMG Node` (hard
intervention preserves the carrier).  The RHS
`(G.nodeSplittingHard hG W hW).marginalize (W.image .copy0) _` lives
in `CDMG (SplitNode Node)`: `nodeSplittingHard` (`def_3_12`) lifts
the carrier from `Node` to `SplitNode Node`, and `marginalize`
(`def_3_14`) preserves the (lifted) carrier.  `Node` and
`SplitNode Node` are not Lean-equal as types, so a literal `=`
between the two CDMGs is not type-correct.  The LN's "$\cong$" is
rendered via `claim_3_7`'s `eqViaNodeMap` predicate, with the
bijection function `toCopy1 W : Node → SplitNode Node`
(`def_3_11` `NodeSplittingOn`) realising the LN's three-case `φ`
literally:
* `toCopy1 W v = .unsplit v` for `v ∉ W` (i.e.\ `v ∈ J ∪ (V ∖ W)`),
  which is the LN's "identity on `J ∪ (V ∖ W)`" branch under the
  carrier-lift `Node ↪ SplitNode Node`;
* `toCopy1 W w = .copy1 w` for `w ∈ W`, which is the LN's
  "`w ↦ w^i`" branch under the SWIG-side reading
  `.copy1 ↔ ^i` (the input-copy convention fixed by `def_3_12`).

Same paradigm as `claim_3_15` (`AddingInterventionNodesSwig`) and
`claim_3_7` (`TwoDisjointNode`); the choice of operand order on
`eqViaNodeMap` follows the LN's explicitly-stated direction
`φ : LHS → RHS` (see the Design choice block on the theorem for the
contrast with `claim_3_15`, which has no LN-specified direction).

The body is filled in by `prove_claim_in_lean` (Manager B), following
the to-be-written tex proof at
`tex/claim_3_19_proof_MarginalizingOutThe.tex`.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited from
--   `def_3_1` (`CDMG.lean`), `def_3_10` (`HardInterventionOn.lean`),
--   `def_3_11` (`NodeSplittingOn.lean` — the `SplitNode` inductive
--   and the `toCopy1` helper), `def_3_12` (`NodeSplittingHard.lean`)
--   and `def_3_14` (`MarginalizationAK.lean`).  Load-bearing because
--   the signature references `CDMG Node`, `CDMG (SplitNode Node)`,
--   `Finset.image SplitNode.copy0`, `toCopy1 W`, and the four
--   operators (`hardInterventionOn`, `nodeSplittingHard`,
--   `marginalize`, and `eqViaNodeMap` from `claim_3_7`'s
--   `TwoDisjointNode.lean`), each of which carries a `[DecidableEq]`
--   constraint into its return type's `CDMG` structure.  Stronger
--   instances (`Fintype`, `LinearOrder`) are not needed at the
--   statement level and are deferred to the proof body's use sites.

-- ## Helper — `W ⊆ G.J ∪ G.V` from `W ⊆ G.V`
--
-- Used once in the statement signature: the LHS
-- `G.hardInterventionOn W ?_` requires
-- `?_ : W ⊆ G.J ∪ G.V` (per `def_3_10`'s `hardInterventionOn`
-- signature, which admits any `W ⊆ G.J ∪ G.V`), while the LN's
-- standing hypothesis on this row only supplies `W ⊆ G.V`.  The
-- transport is the one-liner "`G.V ⊆ G.J ∪ G.V`" composed with
-- the standing `hW`.
--
-- ## Design choice
--
-- *Stand-alone helper, wrapped with three-dash markers — litmus test
--   for marker wrapping returns YES.*  The main theorem signature
--   reads `G.hardInterventionOn W (subset_J_union_V_of_subset_V hW)`;
--   without the named term, the wrapped main theorem head does not
--   type-check.  Mirrors the helper pattern in the sibling
--   `claim_3_15` (`AddingInterventionNodesSwig.lean`) and
--   `claim_3_18` (`MarginalizationAndIntervention.lean`).
--
-- *Implicit `G`, `W`; explicit `hW`.*  At the call site
--   `subset_J_union_V_of_subset_V hW`, the implicit `G` and `W` are
--   synthesised from the goal type, and the call reads left-to-right
--   as "transport `hW`".
--
-- *Term-mode one-liner via `Finset.mem_union_right`, not a tactic
--   proof.*  The conclusion is a direct restatement of "the right
--   summand of a union contains every element of itself"; a
--   `by`-block would add tactic-state noise for zero readability gain.

-- ## Helper — `W.image .copy0 ⊆ V_{swig(W)}`
--
-- Used once in the statement signature: the RHS's outer
-- `.marginalize (W.image SplitNode.copy0) ?_` (applied to the inner
-- SWIG `G.nodeSplittingHard hG W hW`) requires
-- `?_ : W.image .copy0 ⊆ (G.nodeSplittingHard hG W hW).V`.
-- By `def_3_12` item ii, the RHS-V is
-- `(G.V \ W).image .unsplit ∪ W.image .copy0`, so the conclusion is
-- "`W.image .copy0` sits in the right summand".  No disjointness
-- needed (only the structure of the union).
--
-- *`.copy0` is the "output" copy of the chapter-wide split
--   convention.*  In `def_3_11` `SplitNode` (`NodeSplittingOn.lean`)
--   and `def_3_12` `nodeSplittingHard` (`NodeSplittingHard.lean`),
--   the LN's tagged copies "$w^o$" and "$w^i$" are encoded as the
--   constructors `SplitNode.copy0` (output) and `SplitNode.copy1`
--   (input) respectively.  `W.image SplitNode.copy0 : Finset
--   (SplitNode Node)` is the literal Lean rendering of "$W^o$" — the
--   *output-side* copies of `W` that the outer `marginalize` strips
--   off.  This `.copy0 ↔ ^o` numeric/superscript correspondence is
--   genuinely arbitrary (the LN uses superscript suffixes, the
--   codebase picks `0`/`1` constructor indices) and is the kind of
--   indexing detail that bites readers later if left implicit, so the
--   helper's name and signature stay close to the LN's `W^o`
--   throughout.
--
-- ## Design choice
--
-- *Stand-alone helper, wrapped with three-dash markers — litmus test
--   returns YES.*  Without the named term the wrapped main theorem
--   head does not type-check (the inner marginalize's `hW`-argument
--   cannot be discharged inline without ballooning the rendered
--   statement).  Mirrors the
--   `image_unsplit_subset_nodeSplittingHard_carrier` helper pattern
--   in `claim_3_15` (`AddingInterventionNodesSwig.lean`).
--
-- *Implicit `G`, `hG`, `W`, `hW`.*  None of them is consumed in the
--   body; all appear only in the goal type
--   `(G.nodeSplittingHard hG W hW).V` and are inferred from the call
--   site's goal (`hG` and `hW` by proof irrelevance, `G` and `W` by
--   syntactic unification).  Matches the convention of
--   `image_unsplit_subset_extendingCDMGsWith_V` in
--   `AddingInterventionNodesSwig.lean`: when no hypothesis is
--   consumed in the body, every binder is implicit.
--
-- *`change`-then-`exact` tactic shape.*  The `change` step unfolds
--   the `(G.nodeSplittingHard hG W hW).V` projection into the
--   underlying union, after which `Finset.mem_union_right _ hx`
--   discharges the goal.  An alternative term-mode form would
--   require chasing the `where`-syntax field reduction by hand; the
--   two-line tactic form is shorter and reads identically to the
--   `claim_3_15` helper above.

-- Proof helper: structural observation from the verified tex proof.
-- No directed edge of `(G.nodeSplittingHard hG W hW).E` has its source
-- in `W.image SplitNode.copy0`.  Reason: every such edge has the form
-- `(toCopy1 W a, toCopy0 W b)` for some `(a, b) ∈ G.E`, and the source
-- slot `toCopy1 W a` is either `.unsplit a` (when `a ∉ W`) or `.copy1 a`
-- (when `a ∈ W`) — never `.copy0 _`.  This is the lynchpin observation
-- that the proof of clauses (c) and (d) repeatedly invokes.

-- Proof helper: any walk's vertex list is non-empty.  Mirrors
-- `Walk.vertices_ne_nil` of `MargPreservesAncestors.lean`, kept local
-- to avoid a chapter-wide cross-import in this file (which would only
-- be needed for this single utility).

-- Proof helper: middle vertex of a length-`≥ 2` walk `cons w a h q`
-- (with `q` non-trivial) appears in `p.vertices.tail.dropLast` — i.e.\
-- it is registered as a marginalisation intermediate.

-- Proof helper: `swig.MarginalizationΦE (W.image .copy0) u v` iff
-- `(u, v) ∈ swig.E`.  The structural observation collapses any
-- directed walk in `swig` with intermediates in `W^o` to a single
-- edge (a walk of length `≥ 2` would have a `copy0`-tagged
-- intermediate as the source of its next edge — impossible).  The
-- converse direction constructs the trivial length-1 walk.

-- Proof helper: q.IsBifurcationWithSplit i implies q is non-trivial (cons).

-- Proof helper: `swig.MarginalizationΦL (W.image .copy0) u v` iff
-- `(u, v) ∈ swig.L`.  Bifurcation walks in `swig` with intermediates
-- in `W^o` collapse to the `n = 1` (single bidirected edge) case for
-- the same structural reason: any intermediate in `W^o` would be the
-- source of a left-arm / hinge / right-arm directed edge.

-- ref: claim_3_19
--
-- For any CDMG `G : CDMG Node` and any subset `W ⊆ G.V` of output
-- nodes, the LN's displayed equivalence
--   `G_{doit(W)} ≅ (G_{swig(W)})^{∖ W^o}, w ↦ w^i`
-- is rendered (per the rewritten tex's "Distinct carriers and the
-- canonical relabelling identifying them" paragraph, paralleling
-- `claim_3_15`) as
-- `eqViaNodeMap LHS RHS (toCopy1 W)`: the four `Finset` data fields
-- of the LHS `G.hardInterventionOn W _`, after applying
-- `toCopy1 W : Node → SplitNode Node` field-wise, coincide with the
-- four data fields of the RHS
-- `(G.nodeSplittingHard hG W hW).marginalize (W.image .copy0) _`.
--
-- The `toCopy1 W` map is the literal Lean realisation of the LN's
-- three-case bijection `φ` from the rewritten canonical statement:
-- on `J ∪ (V ∖ W)` it returns `.unsplit v` (the LN's identity branch
-- under the `Node ↪ SplitNode Node` carrier-lift); on `W` it returns
-- `.copy1 w` (the LN's "`w ↦ w^i`" branch under the SWIG-side
-- reading `.copy1 ↔ ^i` fixed by `def_3_12`).  Because `toCopy1 W`
-- is total on `Node`, the LHS's input-node carrier `J ∪ W` and
-- output-node carrier `V ∖ W` are each lifted to the RHS in a single
-- pass — no separate case-split on the four (a)–(d) clauses of the
-- rewritten canonical statement is needed at the statement level
-- (the conjunctive unpacking into per-field bijection / edge-
-- preservation statements is deferred to the proof per the
-- rewritten tex's closing remark).
/-
LN tex (rewritten canonical statement for `claim_3_19`, in essence):

  Let `G = (J, V, E, L)` be a CDMG and `W ⊆ V`.  Then there is a
  CDMG-isomorphism `φ : G_{doit(W)} → (G_{swig(W)})^{∖ W^o}`
  defined by
    φ(v) := v          if v ∈ J,
    φ(v) := v          if v ∈ V ∖ W,
    φ(w) := w^i        if w ∈ W,
  whose four-clause unpacking states:
    (a) φ maps input nodes to input nodes;
    (b) φ maps output nodes to output nodes;
    (c) φ preserves directed edges (iff);
    (d) φ preserves bidirected edges (iff).

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CDMG and `W ⊆ V` a subset of output
  nodes from `G`.  Then the CDMG that arises by first splitting the
  nodes on `W` and then marginalizing out the nodes from `W^o` can
  be identified with the CDMG that arises by hard intervention on
  `W`:
    `G_{doit(W)} ≅ (G_{swig(W)})^{∖ W^o}, w ↦ w^i`.
-/
-- ## Design choice
--
-- *`eqViaNodeMap` (carrier-relabelling equality), NOT literal `=` of
--   CDMGs.*  The LHS `G.hardInterventionOn W _` lives in `CDMG Node`;
--   the RHS `(G.nodeSplittingHard hG W hW).marginalize _ _` lives
--   in `CDMG (SplitNode Node)`.  These two carriers are not
--   Lean-equal as types, so a literal `LHS = RHS` is not
--   type-correct.  The LN's "$\cong$" is implicitly modulo the
--   canonical bijection `φ : Node → SplitNode Node` realised by
--   `toCopy1 W`; we render that bijection explicitly via the
--   `eqViaNodeMap` predicate from `claim_3_7`
--   (`TwoDisjointNode.lean`), asserting componentwise equality of
--   the four `Finset` data fields under `toCopy1 W`.  Same paradigm
--   as `claim_3_15` (`AddingInterventionNodesSwig`) and `claim_3_7`
--   (`TwoDisjointNode`).  A literal-`=` form would require either
--   (i) lifting the LHS to `CDMG (SplitNode Node)` via an extra
--   `Finset.image SplitNode.unsplit` wrapper on every field, or
--   (ii) introducing quotient types — both rejected at the
--   `claim_3_7` design stage in favour of `eqViaNodeMap`.
--
-- *Operand order `eqViaNodeMap LHS RHS (toCopy1 W)` — LHS on the
--   left, RHS on the right — matching the LN's explicit
--   `φ : G_{doit(W)} → (G_{swig(W)})^{∖ W^o}` direction.*  This is a
--   deliberate departure from `claim_3_15`'s "RHS on the left"
--   convention (which puts the side being relabelled on the left).
--   The reason is that `claim_3_15`'s LN does not specify a
--   bijection direction at all (its $=$ is over isomorphic
--   iterated-tagged-sum carriers, with no canonical orientation),
--   so `claim_3_15` picks one arbitrarily.  `claim_3_19`'s LN, by
--   contrast, displays the bijection as
--   `G_{doit(W)} ≅ (G_{swig(W)})^{∖ W^o}, w ↦ w^i` —
--   with `G_{doit(W)}` (= LHS) as the *domain* of $w \mapsto w^i$
--   and `(G_{swig(W)})^{∖ W^o}` (= RHS) as the *codomain*.  In our
--   Lean signature this orientation lands as: the side whose carrier
--   `Node` is *the source of `toCopy1 W`* sits on the left of
--   `eqViaNodeMap`, and the side whose carrier `SplitNode Node` is
--   *the target* sits on the right.  Preserving the LN's
--   bijection-direction faithfully is the deciding factor; the
--   reverse direction (`eqViaNodeMap RHS LHS f`) would require a
--   partial inverse of `toCopy1 W` that is awkward to state
--   (`SplitNode Node → Node`-style relabellings collide on the
--   `.copy0` constructor which never appears in the LHS but does
--   appear in the RHS carrier).
--
-- *`toCopy1 W : Node → SplitNode Node` as the bijection.*  This is
--   the literal Lean realisation of the LN's three-case `φ`:
--     • on `J ∪ (V ∖ W)`: `toCopy1 W v = .unsplit v` (the LN's
--       "identity on `J ∪ (V ∖ W)`" branch lifts through the
--       carrier-injection `Node ↪ SplitNode Node` via the `.unsplit`
--       constructor of `def_3_11`'s `SplitNode`);
--     • on `W`: `toCopy1 W w = .copy1 w` (the LN's "`w ↦ w^i`"
--       branch under the SWIG-side reading `.copy1 ↔ ^i` fixed by
--       `def_3_12` `NodeSplittingHard`'s design block).
--   The same helper `toCopy1` is *already* used inside
--   `nodeSplittingHard`'s `E_{swig}` clause
--   `G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2))`, so the
--   bijection here lines up with the lift used by the operator
--   itself — a reader of the rendered statement sees the same
--   `toCopy1 W` shorthand on both the operator side and the
--   relabelling side.  Defining a fresh per-row `phi : Node →
--   SplitNode Node` was rejected because (i) it would diverge from
--   the chapter-wide `toCopy1` shorthand, and (ii) the LN's "implicit
--   identity on `J ∪ (V ∖ W)`" is *exactly* what `toCopy1`'s
--   `if v ∈ W then .copy1 v else .unsplit v` definition encodes.
--
-- *`hG : G.IsCADMG` on the signature, even though the rewritten tex
--   relaxes this to a CDMG-level reading.*  `def_3_12`
--   `nodeSplittingHard` requires `hG : G.IsCADMG` as a signature
--   binder (per its LN-faithful encoding — the LN's def_3_12 opens
--   with "Let $G$ be a CADMG").  The rewritten canonical statement
--   for this row explicitly notes that "the construction is
--   well-typed at the CDMG level using only the CDMG axioms, per
--   the 'Paradigm observation' paragraph of def_3_12" and reads the
--   RHS at the CDMG level — but at the Lean level we use the
--   existing `nodeSplittingHard` operator as-defined, which carries
--   the `hG` binder.  This is a *slight strengthening* of the
--   rewritten tex's hypothesis (`hG` is required here whereas the
--   tex reads at the bare CDMG level), but it does not change the
--   semantic content of the claim: the LN's $\cong$ holds for every
--   CDMG `G` and every `W ⊆ V`, and a fortiori for every CADMG `G`.
--   Downstream consumers always have `hG` available (the SWIG is
--   only ever constructed in contexts where `G.IsCADMG` is already
--   in scope), so the strengthening is harmless in practice.
--   Dropping `hG` would require either re-defining a CDMG-level
--   SWIG operator (a chapter-wide refactor, rejected) or duplicating
--   `nodeSplittingHard`'s four field assignments inline (rejected
--   for repetition / drift risk).  Matches the
--   `(G : CDMG Node) (hG : G.IsCADMG)` binder pattern of
--   `claim_3_15` (`AddingInterventionNodesSwig`).
--
-- *Hypotheses in the order `(G) (hG) (W) (hW)`.*  `G` comes first
--   (data); `hG : G.IsCADMG` is adjacent to `G` because it is a
--   side condition on `G` itself (per `claim_3_15`'s convention);
--   `W` follows (the parameter); `hW : W ⊆ G.V` is the standard
--   "subset of output nodes" precondition of the LN's "Let `W ⊆ V`",
--   matching `def_3_12`'s argument order
--   `(G) (hG) (W) (hW)` exactly.  Dot-notation
--   `G.marginalize_swig_eq_doit hG W hW` reads left-to-right like
--   the LN.
--
-- *No separate "output-node" predicate on `W` — `hW : W ⊆ G.V`
--   carries it.*  The LN's wording "Let `W ⊆ V` be a subset of
--   output nodes from `G`" qualifies `W` as a subset of *output*
--   nodes; one could imagine a richer encoding (e.g.\ a typeclass
--   or a `W ⊆ G.outputNodes` term) capturing the "output" aspect
--   separately from the subset relation.  None is needed: in
--   `def_3_1` (`CDMG.lean`), the field `G.V` *is* — by the LN's own
--   definition (def_3_1 names `V` the output-node set) — the
--   collection of output nodes of `G`.  Consequently `W ⊆ G.V` is
--   the literal Lean rendering of "subset of output nodes", and no
--   additional hypothesis is required at the signature level.  This
--   reading is the standing chapter-wide interpretation (cf.\ every
--   row in Section 3.2 that says "let `W ⊆ V` be …" — claim_3_15,
--   claim_3_17, claim_3_18 all share this collapse), and addresses
--   the LN-critic working-phase subtlety
--   `output_node_precondition_relies_on_external_definition`
--   raised against this row.  If a downstream chapter ever
--   re-partitioned `V` into output / something-else (none does
--   through chapter 16), this collapse would need revisiting.
--
-- *`W.image SplitNode.copy0` for the LN's `W^o`.*  The Lean
--   convention from `NodeSplittingHard.lean` (`def_3_12`): the
--   `^o` superscript is realised at the type level by the
--   `.copy0` constructor of `SplitNode`, and `W^o = {w^o | w ∈ W}`
--   lifts to `W.image SplitNode.copy0 : Finset (SplitNode Node)`.
--   No alternative considered — this is the chapter-wide encoding
--   of `W^o` (cf.\ the design block on `def_3_12`'s `J' :=
--   G.J.image .unsplit ∪ W.image .copy1`, `V' := (G.V \ W).image
--   .unsplit ∪ W.image .copy0`).
--
-- *Degenerate `W = ∅` case admitted.*  The quantifiers on `G` and
--   `W` are universal; `W = ∅` reduces both sides to (the
--   `.unsplit`-image of) `G` itself, with the bijection `toCopy1 ∅`
--   collapsing to `.unsplit` on all of `Node`.  `eqViaNodeMap`
--   reduces to "the four `Finset` fields of `G` lifted under
--   `.unsplit` equal the four fields of the doubly-trivial-operation
--   RHS", which holds for every `G`.  The signature does not
--   pre-emptively exclude this case (per the rewritten tex's
--   explicit admission of `W = ∅`).
--
-- *Conjunctive unpacking deferred to the proof.*  The rewritten
--   canonical tex enumerates four clauses (a)–(d):
--     (a) `φ` maps `J_{doit(W)} = J ∪ W` to
--         `J_{(G_{swig(W)})^{∖W^o}} = J ⊍ W^i` bijectively;
--     (b) `φ` maps `V_{doit(W)} = V ∖ W` to
--         `V_{(G_{swig(W)})^{∖W^o}} = V ∖ W` bijectively (identity);
--     (c) `φ` preserves directed edges (iff);
--     (d) `φ` preserves bidirected edges (iff).
--   These four clauses unpack into the four conjuncts of
--   `eqViaNodeMap LHS RHS (toCopy1 W)`:
--     `LHS.J.image (toCopy1 W) = RHS.J  ∧  LHS.V.image (toCopy1 W) = RHS.V`
--     `∧  LHS.E.image (Prod.map …) = RHS.E  ∧  LHS.L.image (Prod.map …) = RHS.L`.
--   The four-conjunct shape of `eqViaNodeMap` mirrors the four
--   clauses (a)–(d) of the rewrite literally, with the
--   field-by-field bijection / edge-preservation reasoning deferred
--   to the proof per the rewritten tex's closing remark.

end CDMG

-- ## Post-refactor port (`cdmg_typed_edges`)
--
-- The block below is the refactor twin of this row's declarations
-- against the `cdmg_typed_edges` redesign of `def_3_1` / `def_3_4` —
-- same mathematical content, retyped against `CDMG`,
-- `SplitNode`, and the typed `WalkStep` / `Walk`
-- inductives.  J / V / E sub-goals of the main theorem port mechanically;
-- the L sub-goal is restructured around `Sym2.map` and `Sym2.mem_iff`.
namespace CDMG
open CDMG

-- claim_3_19 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_19 --- end helper

-- Refactor port of `subset_J_union_V_of_subset_V` — mechanical rename
-- pass; body identical.
-- claim_3_19 --- start helper
private lemma subset_J_union_V_of_subset_V
    {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.V) : W ⊆ G.J ∪ G.V
-- claim_3_19 --- end helper
:= fun _ hv => Finset.mem_union_right _ (hW hv)

-- Refactor port of `image_copy0_subset_nodeSplittingHard_V` —
-- mechanical rename pass; `nodeSplittingHard.V` unchanged in shape.
-- claim_3_19 --- start helper
private lemma image_copy0_subset_nodeSplittingHard_V
    {G : CDMG Node} {hG : G.IsCADMG}
    {W : Finset Node} {hW : W ⊆ G.V} :
    W.image SplitNode.copy0 ⊆ (G.nodeSplittingHard hG W hW).V
-- claim_3_19 --- end helper
:= by
  intro x hx
  change x ∈ (G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
  exact Finset.mem_union_right _ hx

-- Refactor port of `swig_edge_source_notMem_W_copy0`.  The SWIG's E
-- field is unchanged in shape under the refactor (the refactor only
-- touches L), so this lemma carries over verbatim modulo the type
-- and helper renames.
private lemma swig_edge_source_notMem_W_copy0
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.V)
    {e : SplitNode Node × SplitNode Node}
    (he : e ∈ (G.nodeSplittingHard hG W hW).E) :
    e.1 ∉ W.image SplitNode.copy0 := by
  change e ∈ G.E.image (fun e => (toCopy1 W e.1, toCopy0 W e.2)) at he
  obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he
  intro hContra
  obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
  unfold toCopy1 at hweq
  split_ifs at hweq

-- Refactor port of `swig_vertices_ne_nil`.  The 4-arg `.cons _ _ _ _`
-- pattern collapses to the 3-arg `.cons _ _ _` pattern (the typed
-- `WalkStep` replaces the original's stored ordered-pair +
-- WalkStep Prop pair).
private lemma swig_vertices_ne_nil
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.V) :
    ∀ {a b : SplitNode Node}
      (p : Walk (G.nodeSplittingHard hG W hW) a b),
      p.vertices ≠ []
  | _, _, .nil _ _ => by simp [Walk.vertices]
  | _, _, .cons _ _ _ => by simp [Walk.vertices]

-- Refactor port of `swig_middle_vertex_mem_tail_dropLast`.  Signature
-- shape change: drops the pair `c : Node × Node` and the WalkStep Prop
-- `h : WalkStep`, replaced by the typed `s : WalkStep`
-- (mirroring the `Walk.cons` 3-arg shape).
private lemma swig_middle_vertex_mem_tail_dropLast
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.V)
    {a b : SplitNode Node} (w : SplitNode Node)
    (s : WalkStep (G.nodeSplittingHard hG W hW) a w)
    {bMid : SplitNode Node}
    (s' : WalkStep (G.nodeSplittingHard hG W hW) w bMid)
    (r : Walk (G.nodeSplittingHard hG W hW) bMid b) :
    w ∈ (Walk.cons w s
              (Walk.cons bMid s' r)).vertices.tail.dropLast := by
  have hr_ne : r.vertices ≠ [] := swig_vertices_ne_nil hG hW r
  change w ∈ (a :: w :: r.vertices).tail.dropLast
  rw [List.tail_cons]
  rw [List.dropLast_cons_of_ne_nil hr_ne]
  exact List.mem_cons.mpr (Or.inl rfl)

-- Refactor port of `swig_marginalization_phi_E_W_copy0_iff`.  The
-- `Walk.IsDirectedWalk` Prop-level conjunction collapses to a
-- constructor case-split on `WalkStep`: only `.forwardE`
-- survives in directed walks; `.backwardE` / `.bidir` reduce to
-- `False`.  Length-1 construction in the reverse direction uses
-- `Walk.cons _ (.forwardE _) (Walk.nil _ _)`.
private lemma swig_marginalization_phi_E_W_copy0_iff
    (G : CDMG Node) (hG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V)
    (u v : SplitNode Node) :
    (G.nodeSplittingHard hG W hW).MarginalizationΦE
        (W.image SplitNode.copy0) u v
      ↔ (u, v) ∈ (G.nodeSplittingHard hG W hW).E := by
  constructor
  · rintro ⟨p, hp_dir, hp_len, hp_inter⟩
    cases p with
    | nil v' hv' =>
      simp [Walk.length] at hp_len
    | cons mid s q =>
      cases s with
      | backwardE _ =>
        simp only [Walk.IsDirectedWalk] at hp_dir
      | bidir _ =>
        simp only [Walk.IsDirectedWalk] at hp_dir
      | forwardE h_edge =>
        cases q with
        | nil v' hv' =>
          exact h_edge
        | cons w' s' r =>
          cases s' with
          | backwardE _ =>
            simp only [Walk.IsDirectedWalk] at hp_dir
          | bidir _ =>
            simp only [Walk.IsDirectedWalk] at hp_dir
          | forwardE h_edge' =>
            have h_w_mem : mid ∈ W.image SplitNode.copy0 :=
              hp_inter mid
                (swig_middle_vertex_mem_tail_dropLast hG hW mid
                  (.forwardE h_edge) (.forwardE h_edge') r)
            exact (swig_edge_source_notMem_W_copy0 hG hW h_edge' h_w_mem).elim
  · intro h_edge
    have hv_in : v ∈ G.nodeSplittingHard hG W hW := by
      show v ∈ (G.nodeSplittingHard hG W hW).J
              ∪ (G.nodeSplittingHard hG W hW).V
      refine Finset.mem_union_right _ ?_
      exact ((G.nodeSplittingHard hG W hW).hE_subset h_edge).2
    refine ⟨Walk.cons v (.forwardE h_edge) (Walk.nil v hv_in),
      ?_, ?_, ?_⟩
    · trivial
    · show 0 + 1 ≥ 1; omega
    · intro x hx
      simp [Walk.vertices, List.tail] at hx

-- Refactor port of `swig_bif_with_split_cons_form` — pattern-match
-- structure shifts from 4-arg cons to 3-arg cons; existential drops
-- the ordered-pair / Prop pair, replaced by the typed `s`.
private lemma swig_bif_with_split_cons_form
    {G : CDMG Node} (hG : G.IsCADMG)
    {W : Finset Node} (hW : W ⊆ G.V) :
    ∀ {a b : SplitNode Node}
      (q : Walk (G.nodeSplittingHard hG W hW) a b) (i : ℕ),
      q.IsBifurcationWithSplit i →
      ∃ (mid : SplitNode Node)
        (s : WalkStep (G.nodeSplittingHard hG W hW) a mid)
        (r : Walk (G.nodeSplittingHard hG W hW) mid b),
        q = Walk.cons mid s r
  | _, _, .nil _ _, _, hSpl => by
      simp only [Walk.IsBifurcationWithSplit] at hSpl
  | _, _, .cons mid s r, _, _ => ⟨mid, s, r, rfl⟩

-- Refactor port of `swig_marginalization_phi_L_W_copy0_iff`.  The
-- bifurcation-walk Prop-level disjunction collapses to a constructor
-- case-split on `WalkStep`; the `hL_symm` invocation in the
-- reverse direction's "other-orientation" branch is replaced by
-- `Sym2.eq_swap` (`s(v, u) = s(u, v)` definitionally on `Sym2`).
-- The conclusion changes from `(u, v) ∈ swig.L` (ordered-pair) to
-- `s(u, v) ∈ swig.L` (`Sym2`-quotient).
private lemma swig_marginalization_phi_L_W_copy0_iff
    (G : CDMG Node) (hG : G.IsCADMG)
    (W : Finset Node) (hW : W ⊆ G.V)
    (u v : SplitNode Node) :
    (G.nodeSplittingHard hG W hW).MarginalizationΦL
        (W.image SplitNode.copy0) u v
      ↔ s(u, v) ∈ (G.nodeSplittingHard hG W hW).L := by
  have bifSplitAux :
      ∀ {a b : SplitNode Node} (i : ℕ)
        (p : Walk (G.nodeSplittingHard hG W hW) a b),
        p.IsBifurcationWithSplit i →
        (∀ x ∈ p.vertices.tail.dropLast, x ∈ W.image SplitNode.copy0) →
        s(a, b) ∈ (G.nodeSplittingHard hG W hW).L := by
    intro a b i
    induction i generalizing a b with
    | zero =>
      intro p hSpl hInter
      cases p with
      | nil v' hv' =>
        simp only [Walk.IsBifurcationWithSplit] at hSpl
      | cons mid s q =>
        cases q with
        | nil v' hv' =>
          cases s with
          | forwardE _ =>
            simp only [Walk.IsBifurcationWithSplit] at hSpl
          | backwardE _ =>
            simp only [Walk.IsBifurcationWithSplit] at hSpl
          | bidir h_L =>
            exact h_L
        | cons w' s' r =>
          cases s with
          | forwardE _ =>
            simp only [Walk.IsBifurcationWithSplit] at hSpl
          | backwardE h_first =>
            cases s' with
            | backwardE _ =>
              simp only [Walk.IsBifurcationWithSplit,
                Walk.IsDirectedWalk] at hSpl
            | bidir _ =>
              simp only [Walk.IsBifurcationWithSplit,
                Walk.IsDirectedWalk] at hSpl
            | forwardE h_edge' =>
              have h_w_mem : mid ∈ W.image SplitNode.copy0 :=
                hInter mid
                  (swig_middle_vertex_mem_tail_dropLast hG hW mid
                    (.backwardE h_first) (.forwardE h_edge') r)
              exact (swig_edge_source_notMem_W_copy0 hG hW h_edge' h_w_mem).elim
          | bidir h_first =>
            cases s' with
            | backwardE _ =>
              simp only [Walk.IsBifurcationWithSplit,
                Walk.IsDirectedWalk] at hSpl
            | bidir _ =>
              simp only [Walk.IsBifurcationWithSplit,
                Walk.IsDirectedWalk] at hSpl
            | forwardE h_edge' =>
              have h_w_mem : mid ∈ W.image SplitNode.copy0 :=
                hInter mid
                  (swig_middle_vertex_mem_tail_dropLast hG hW mid
                    (.bidir h_first) (.forwardE h_edge') r)
              exact (swig_edge_source_notMem_W_copy0 hG hW h_edge' h_w_mem).elim
    | succ k ih =>
      intro p hSpl hInter
      cases p with
      | nil v' hv' =>
        simp only [Walk.IsBifurcationWithSplit] at hSpl
      | cons mid s q =>
        cases s with
        | forwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
        | bidir _ =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
        | backwardE h_edge =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
          obtain ⟨wMid, s', r, hq_eq⟩ :=
            swig_bif_with_split_cons_form hG hW q k hSpl
          have h_w_mem : mid ∈ W.image SplitNode.copy0 := by
            apply hInter
            rw [hq_eq]
            exact swig_middle_vertex_mem_tail_dropLast hG hW mid
              (.backwardE h_edge) s' r
          exact (swig_edge_source_notMem_W_copy0 hG hW h_edge h_w_mem).elim
  constructor
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · obtain ⟨_, _, _, i, hi⟩ := hp_bif
      exact bifSplitAux i p hi hp_inter
    · obtain ⟨_, _, _, i, hi⟩ := hp_bif
      have h := bifSplitAux i p hi hp_inter
      rwa [show (s(u, v) : Sym2 (SplitNode Node)) = s(v, u) from Sym2.eq_swap]
  · intro h_edge
    have hv_in : v ∈ G.nodeSplittingHard hG W hW := by
      show v ∈ (G.nodeSplittingHard hG W hW).J
              ∪ (G.nodeSplittingHard hG W hW).V
      refine Finset.mem_union_right _ ?_
      exact (G.nodeSplittingHard hG W hW).hL_subset h_edge (Sym2.mem_mk_right u v)
    have hu_ne_v : u ≠ v := fun h_eq =>
      (G.nodeSplittingHard hG W hW).hL_irrefl h_edge
        (Sym2.mk_isDiag_iff.mpr h_eq)
    refine Or.inl ⟨Walk.cons v (.bidir h_edge) (Walk.nil v hv_in),
      ?_, ?_⟩
    · refine ⟨hu_ne_v, ?_, ?_, 0, ?_⟩
      · intro h_mem
        exact hu_ne_v (List.mem_singleton.mp h_mem)
      · intro h_mem
        exact hu_ne_v (List.mem_singleton.mp h_mem).symm
      · trivial
    · intro x hx
      exact (List.not_mem_nil hx).elim

-- Refactor port of `marginalize_swig_eq_doit`.  J / V / E sub-goals
-- port mechanically (the refactor leaves these fields untouched);
-- the L sub-goal is restructured around `Sym2.map` and `Sym2.ind`.
set_option maxHeartbeats 800000 in
-- claim_3_19 -- start statement
theorem marginalize_swig_eq_doit (G : CDMG Node)
    (hG : G.IsCADMG) (W : Finset Node) (hW : W ⊆ G.V) :
    eqViaNodeMap
        (G.hardInterventionOn W (subset_J_union_V_of_subset_V hW))
        ((G.nodeSplittingHard hG W hW).marginalize
            (W.image SplitNode.copy0)
            image_copy0_subset_nodeSplittingHard_V)
        (toCopy1 W)
-- claim_3_19 -- end statement
:= by
  refine ⟨?_, ?_, ?_, ?_⟩
  -- ===== Clause (a): J equality =====
  · change (G.J ∪ W).image (toCopy1 W)
        = G.J.image SplitNode.unsplit ∪ W.image SplitNode.copy1
    rw [Finset.image_union]
    have hGJ : G.J.image (toCopy1 W) = G.J.image SplitNode.unsplit := by
      refine Finset.image_congr ?_
      intro j hj
      have hjJ : j ∈ G.J := Finset.mem_coe.mp hj
      have hj_notW : j ∉ W := by
        intro hjW
        exact Finset.disjoint_left.mp G.hJV_disj hjJ (hW hjW)
      show toCopy1 W j = SplitNode.unsplit j
      unfold toCopy1
      rw [if_neg hj_notW]
    have hW1 : W.image (toCopy1 W) = W.image SplitNode.copy1 := by
      refine Finset.image_congr ?_
      intro w hw
      have hwW : w ∈ W := Finset.mem_coe.mp hw
      show toCopy1 W w = SplitNode.copy1 w
      unfold toCopy1
      rw [if_pos hwW]
    rw [hGJ, hW1]
  -- ===== Clause (b): V equality =====
  · change (G.V \ W).image (toCopy1 W)
        = ((G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0)
            \ (W.image SplitNode.copy0)
    have hLHS : (G.V \ W).image (toCopy1 W)
                  = (G.V \ W).image SplitNode.unsplit := by
      refine Finset.image_congr ?_
      intro v hv
      have hvSdiff : v ∈ G.V \ W := Finset.mem_coe.mp hv
      have hv_notW : v ∉ W := (Finset.mem_sdiff.mp hvSdiff).2
      show toCopy1 W v = SplitNode.unsplit v
      unfold toCopy1
      rw [if_neg hv_notW]
    rw [hLHS]
    apply Finset.ext
    intro x
    constructor
    · intro hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hx, ?_⟩
      intro hx_inW
      obtain ⟨v, _, hveq⟩ := Finset.mem_image.mp hx
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hx_inW
      rw [← hveq] at hweq
      cases hweq
    · intro hx
      obtain ⟨hx_union, hx_notC0⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp hx_union with hxA | hxB
      · exact hxA
      · exact absurd hxB hx_notC0
  -- ===== Clause (c): E directed-edge equality =====
  · change (G.E.filter (fun e => e.2 ∉ W)).image
            (Prod.map (toCopy1 W) (toCopy1 W))
        = (((G.nodeSplittingHard hG W hW).J
              ∪ ((G.nodeSplittingHard hG W hW).V \
                  (W.image SplitNode.copy0)))
              ×ˢ
              ((G.nodeSplittingHard hG W hW).V \
                (W.image SplitNode.copy0))).filter
            (fun e =>
              (G.nodeSplittingHard hG W hW).MarginalizationΦE
                (W.image SplitNode.copy0) e.1 e.2)
    have hC0eqC1 : ∀ {x : Node}, x ∉ W → toCopy0 W x = toCopy1 W x := by
      intro x hx
      unfold toCopy0 toCopy1
      rw [if_neg hx, if_neg hx]
    apply Finset.ext
    intro pair
    constructor
    · intro hpair
      obtain ⟨e, he, hPM⟩ := Finset.mem_image.mp hpair
      obtain ⟨he_E, he_notW⟩ := Finset.mem_filter.mp he
      obtain ⟨he1_in, he2_V⟩ := G.hE_subset he_E
      have hPM_eq : pair = (toCopy1 W e.1, toCopy1 W e.2) := by
        rw [← hPM]; rfl
      have h_swig_E : pair ∈ (G.nodeSplittingHard hG W hW).E := by
        change pair ∈ G.E.image
          (fun e => (toCopy1 W e.1, toCopy0 W e.2))
        refine Finset.mem_image.mpr ⟨e, he_E, ?_⟩
        rw [hPM_eq]
        rw [hC0eqC1 he_notW]
      have hSub := (G.nodeSplittingHard hG W hW).hE_subset h_swig_E
      have hpair1_notC0 : pair.1 ∉ W.image SplitNode.copy0 :=
        swig_edge_source_notMem_W_copy0 hG hW h_swig_E
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · rcases Finset.mem_union.mp hSub.1 with hJ | hV
          · exact Finset.mem_union_left _ hJ
          · exact Finset.mem_union_right _
              (Finset.mem_sdiff.mpr ⟨hV, hpair1_notC0⟩)
        · refine Finset.mem_sdiff.mpr ⟨hSub.2, ?_⟩
          rw [hPM_eq]
          show toCopy1 W e.2 ∉ W.image SplitNode.copy0
          unfold toCopy1
          rw [if_neg he_notW]
          intro hContra
          obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
          cases hweq
      · exact (swig_marginalization_phi_E_W_copy0_iff
          G hG W hW _ _).mpr h_swig_E
    · intro hpair
      obtain ⟨hProd, hPhi⟩ := Finset.mem_filter.mp hpair
      have h_swig_E : pair ∈ (G.nodeSplittingHard hG W hW).E :=
        (swig_marginalization_phi_E_W_copy0_iff G hG W hW _ _).mp hPhi
      change pair ∈ G.E.image
        (fun e => (toCopy1 W e.1, toCopy0 W e.2)) at h_swig_E
      obtain ⟨e, he_E, hpair_eq⟩ := Finset.mem_image.mp h_swig_E
      obtain ⟨_, hv⟩ := Finset.mem_product.mp hProd
      obtain ⟨_, hv_notC0⟩ := Finset.mem_sdiff.mp hv
      have he2_notW : e.2 ∉ W := by
        intro he2W
        apply hv_notC0
        have h2 : pair.2 = toCopy0 W e.2 := by rw [← hpair_eq]
        rw [h2]
        show toCopy0 W e.2 ∈ W.image SplitNode.copy0
        unfold toCopy0
        rw [if_pos he2W]
        exact Finset.mem_image.mpr ⟨e.2, he2W, rfl⟩
      refine Finset.mem_image.mpr ⟨e, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨he_E, he2_notW⟩
      · show Prod.map (toCopy1 W) (toCopy1 W) e = pair
        rw [← hpair_eq]
        show (toCopy1 W e.1, toCopy1 W e.2)
              = (toCopy1 W e.1, toCopy0 W e.2)
        rw [hC0eqC1 he2_notW]
  -- ===== Clause (d): L bidirected-edge equality =====
  · change (G.L.filter (fun s => ∀ v ∈ s, v ∉ W)).image
            (Sym2.map (toCopy1 W))
        = ((((G.nodeSplittingHard hG W hW).V \
                (W.image SplitNode.copy0))
              ×ˢ
              ((G.nodeSplittingHard hG W hW).V \
                (W.image SplitNode.copy0))).filter
            (fun e => e.1 ≠ e.2
              ∧ (G.nodeSplittingHard hG W hW).MarginalizationΦL
                  (W.image SplitNode.copy0) e.1 e.2)).image
            (fun e => s(e.1, e.2))
    have hToCopy1_unsplit : ∀ {x : Node}, x ∉ W →
        toCopy1 W x = SplitNode.unsplit x := by
      intro x hx
      unfold toCopy1
      rw [if_neg hx]
    have hToCopy0_unsplit : ∀ {x : Node}, x ∉ W →
        toCopy0 W x = SplitNode.unsplit x := by
      intro x hx
      unfold toCopy0
      rw [if_neg hx]
    apply Finset.ext
    refine Sym2.ind (fun a b => ?_)
    constructor
    · -- Forward (⇒): s(a, b) ∈ image of G.L.filter → s(a, b) ∈ image of (... filter ...)
      intro hLHS
      obtain ⟨s_src, hs_src_filter, hs_src_map⟩ := Finset.mem_image.mp hLHS
      obtain ⟨hs_src_L, hs_src_notW⟩ := Finset.mem_filter.mp hs_src_filter
      induction s_src using Sym2.ind with | _ a₀ b₀ =>
      -- hs_src_map : Sym2.map (toCopy1 W) s(a₀, b₀) = s(a, b)
      have ha₀_notW : a₀ ∉ W := hs_src_notW a₀ (Sym2.mem_mk_left _ _)
      have hb₀_notW : b₀ ∉ W := hs_src_notW b₀ (Sym2.mem_mk_right _ _)
      have ha₀_V : a₀ ∈ G.V := G.hL_subset hs_src_L (Sym2.mem_mk_left _ _)
      have hb₀_V : b₀ ∈ G.V := G.hL_subset hs_src_L (Sym2.mem_mk_right _ _)
      have hab₀_ne : a₀ ≠ b₀ := fun h_eq =>
        G.hL_irrefl hs_src_L (Sym2.mk_isDiag_iff.mpr h_eq)
      -- Build swig.L membership of s(.unsplit a₀, .unsplit b₀)
      have h_swig_L : s(SplitNode.unsplit a₀, SplitNode.unsplit b₀)
                        ∈ (G.nodeSplittingHard hG W hW).L := by
        change s(SplitNode.unsplit a₀, SplitNode.unsplit b₀)
                ∈ G.L.image (Sym2.map (toCopy0 W))
        refine Finset.mem_image.mpr ⟨s(a₀, b₀), hs_src_L, ?_⟩
        show Sym2.map (toCopy0 W) s(a₀, b₀)
              = s(SplitNode.unsplit a₀, SplitNode.unsplit b₀)
        rw [Sym2.map_mk, hToCopy0_unsplit ha₀_notW, hToCopy0_unsplit hb₀_notW]
      -- Use witness pair (toCopy1 W a₀, toCopy1 W b₀)
      refine Finset.mem_image.mpr
        ⟨(toCopy1 W a₀, toCopy1 W b₀), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
        · refine Finset.mem_product.mpr ⟨?_, ?_⟩
          · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · show toCopy1 W a₀ ∈ (G.nodeSplittingHard hG W hW).V
              change toCopy1 W a₀ ∈
                (G.V \ W).image SplitNode.unsplit
                  ∪ W.image SplitNode.copy0
              rw [hToCopy1_unsplit ha₀_notW]
              refine Finset.mem_union_left _ ?_
              exact Finset.mem_image.mpr
                ⟨a₀, Finset.mem_sdiff.mpr ⟨ha₀_V, ha₀_notW⟩, rfl⟩
            · rw [hToCopy1_unsplit ha₀_notW]
              intro hContra
              obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
              cases hweq
          · refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · change toCopy1 W b₀ ∈
                (G.V \ W).image SplitNode.unsplit
                  ∪ W.image SplitNode.copy0
              rw [hToCopy1_unsplit hb₀_notW]
              refine Finset.mem_union_left _ ?_
              exact Finset.mem_image.mpr
                ⟨b₀, Finset.mem_sdiff.mpr ⟨hb₀_V, hb₀_notW⟩, rfl⟩
            · rw [hToCopy1_unsplit hb₀_notW]
              intro hContra
              obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hContra
              cases hweq
        · show toCopy1 W a₀ ≠ toCopy1 W b₀
          rw [hToCopy1_unsplit ha₀_notW, hToCopy1_unsplit hb₀_notW]
          intro h_eq
          injection h_eq with h_inj
          exact hab₀_ne h_inj
        · -- Φ_L: use the iff helper
          refine (swig_marginalization_phi_L_W_copy0_iff
            G hG W hW _ _).mpr ?_
          show s(toCopy1 W a₀, toCopy1 W b₀)
                ∈ (G.nodeSplittingHard hG W hW).L
          rw [hToCopy1_unsplit ha₀_notW, hToCopy1_unsplit hb₀_notW]
          exact h_swig_L
      · -- s(toCopy1 W a₀, toCopy1 W b₀) = s(a, b)
        show s(toCopy1 W a₀, toCopy1 W b₀) = s(a, b)
        rw [← Sym2.map_mk]
        exact hs_src_map
    · -- Reverse (⇐)
      intro hRHS
      obtain ⟨pair, hpair_filter, hpair_eq⟩ := Finset.mem_image.mp hRHS
      obtain ⟨hpair_prod, hpair_ne, hPhi⟩ := Finset.mem_filter.mp hpair_filter
      have h_swig_L : s(pair.1, pair.2) ∈ (G.nodeSplittingHard hG W hW).L :=
        (swig_marginalization_phi_L_W_copy0_iff G hG W hW _ _).mp hPhi
      change s(pair.1, pair.2)
        ∈ G.L.image (Sym2.map (toCopy0 W)) at h_swig_L
      obtain ⟨s₀, hs₀_L, hs₀_map⟩ := Finset.mem_image.mp h_swig_L
      induction s₀ using Sym2.ind with | _ a₀ b₀ =>
      -- hs₀_map : Sym2.map (toCopy0 W) s(a₀, b₀) = s(pair.1, pair.2)
      have hpair1_notC0 : pair.1 ∉ W.image SplitNode.copy0 :=
        (Finset.mem_sdiff.mp (Finset.mem_product.mp hpair_prod).1).2
      have hpair2_notC0 : pair.2 ∉ W.image SplitNode.copy0 :=
        (Finset.mem_sdiff.mp (Finset.mem_product.mp hpair_prod).2).2
      -- Derive a₀ ∉ W using the contradiction approach
      have ha₀_notW : a₀ ∉ W := by
        intro ha₀W
        have h_tc0_eq : toCopy0 W a₀ = SplitNode.copy0 a₀ := by
          unfold toCopy0; rw [if_pos ha₀W]
        have h_mem : toCopy0 W a₀ ∈ s(pair.1, pair.2) := by
          rw [← hs₀_map, Sym2.map_mk]
          exact Sym2.mem_mk_left _ _
        rcases Sym2.mem_iff.mp h_mem with h_eq | h_eq
        · apply hpair1_notC0
          rw [← h_eq, h_tc0_eq]
          exact Finset.mem_image.mpr ⟨a₀, ha₀W, rfl⟩
        · apply hpair2_notC0
          rw [← h_eq, h_tc0_eq]
          exact Finset.mem_image.mpr ⟨a₀, ha₀W, rfl⟩
      have hb₀_notW : b₀ ∉ W := by
        intro hb₀W
        have h_tc0_eq : toCopy0 W b₀ = SplitNode.copy0 b₀ := by
          unfold toCopy0; rw [if_pos hb₀W]
        have h_mem : toCopy0 W b₀ ∈ s(pair.1, pair.2) := by
          rw [← hs₀_map, Sym2.map_mk]
          exact Sym2.mem_mk_right _ _
        rcases Sym2.mem_iff.mp h_mem with h_eq | h_eq
        · apply hpair1_notC0
          rw [← h_eq, h_tc0_eq]
          exact Finset.mem_image.mpr ⟨b₀, hb₀W, rfl⟩
        · apply hpair2_notC0
          rw [← h_eq, h_tc0_eq]
          exact Finset.mem_image.mpr ⟨b₀, hb₀W, rfl⟩
      -- Use s(a₀, b₀) as witness in G.L.filter
      refine Finset.mem_image.mpr ⟨s(a₀, b₀), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨hs₀_L, ?_⟩
        intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact ha₀_notW
        · exact hb₀_notW
      · -- Sym2.map (toCopy1 W) s(a₀, b₀) = s(a, b)
        show Sym2.map (toCopy1 W) s(a₀, b₀) = s(a, b)
        rw [Sym2.map_mk, hToCopy1_unsplit ha₀_notW, hToCopy1_unsplit hb₀_notW]
        -- Goal: s(.unsplit a₀, .unsplit b₀) = s(a, b)
        -- From hs₀_map: s(toCopy0 W a₀, toCopy0 W b₀) = s(pair.1, pair.2)
        -- After rewriting hToCopy0: s(.unsplit a₀, .unsplit b₀) = s(pair.1, pair.2)
        -- From hpair_eq: s(pair.1, pair.2) = s(a, b)
        rw [show (s(SplitNode.unsplit a₀, SplitNode.unsplit b₀) : Sym2 _)
                = s(pair.1, pair.2) by
              rw [← hToCopy0_unsplit ha₀_notW, ← hToCopy0_unsplit hb₀_notW,
                  ← Sym2.map_mk]
              exact hs₀_map]
        exact hpair_eq

end CDMG

end Causality
