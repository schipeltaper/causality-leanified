import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn

namespace Causality

/-!
# Disjoint hard interventions and node-splittings commute (`claim_3_8`)

This file formalises the LN lemma `claim_3_8` (`DisjointHardInterventions`)
in section 3.2 of `graphs.tex`:

> Let `G = (J, V, E, L)` be a CDMG and `W₁ ⊆ J ∪ V`, `W₂ ⊆ V` two
> subsets of nodes of `G` with `W₁ ∩ W₂ = ∅`.  Then
> `(G_{doit(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{doit(W₁)}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_8_statement_DisjointHardInterventions.tex`, verified
equivalent to the LN block (`addition_to_the_LN` empty).

## Carrier reading (load-bearing for this row's Lean signature)

`def_3_10` (`hardInterventionOn`) preserves the node carrier (`Node → Node`)
while `def_3_11` (`nodeSplittingOn`) lifts the carrier
(`Node → SplitNode Node`).  Both sides of the asserted equality therefore
land in `CDMG (SplitNode Node)`:

* LHS `(G.hardInterventionOn W₁ hW₁).nodeSplittingOn W₂ _` — the inner
  hard intervention keeps the carrier as `Node`; the outer
  `nodeSplittingOn` lifts to `SplitNode Node`.
* RHS `(G.nodeSplittingOn W₂ hW₂).hardInterventionOn (W₁.image .unsplit) _`
  — the inner `nodeSplittingOn` lifts to `SplitNode Node`, and the outer
  hard intervention operates on the lifted carrier.  `W₁` is lifted to
  the split-graph carrier via `.image SplitNode.unsplit`, faithful to the
  tex spec's "carrier-reading" paragraph: every `w ∈ W₁` satisfies
  `w ∈ J ∪ V` (by `hW₁`) and `w ∉ W₂` (by disjointness), so `w` injects
  as its unsplit copy `.unsplit w` in the split-graph carrier.

Both sides have the same Lean type `CDMG (SplitNode Node)`, so the
equality is a *literal* `=` of CDMGs — NOT the
`eqViaNodeMap`/`flattenSplit` shape used by `claim_3_7`
(`TwoDisjointNode`), where iterating `nodeSplittingOn` twice produces
the nested carrier `SplitNode (SplitNode Node)` and required a
canonical-flatten relabelling.  Mirrors the literal-`=` pattern of
`claim_3_4` (`HardInterventionsCommute`).

The body is filled in by `prove_claim_in_lean` (Manager B), following
the to-be-written tex proof at
`tex/claim_3_8_proof_DisjointHardInterventions.tex` (the LN already
ships a worked proof at `graphs.tex` L504–534).
-/

namespace CDMG

-- `Node : Type*` with `[DecidableEq Node]`.  Inherited from `def_3_1`
-- (`CDMG.lean`).  Load-bearing because the signature references
-- `CDMG Node`, `G.hardInterventionOn` (`def_3_10`), and
-- `G.nodeSplittingOn` (`def_3_11`), each of which depends on
-- `[DecidableEq Node]` through `Finset`-backed membership and image
-- operations.  The split-graph carrier `SplitNode Node` inherits
-- `[DecidableEq (SplitNode Node)]` automatically via the `deriving
-- DecidableEq` clause on `SplitNode` (`NodeSplittingOn.lean`).
-- claim_3_8 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_8 --- end helper

-- ## Helper — `W₂` sits inside the carrier of the inner hard intervention
--
-- The LHS `(G.hardInterventionOn W₁ hW₁).nodeSplittingOn W₂ ?_` requires
-- `?_ : W₂ ⊆ (G.hardInterventionOn W₁ hW₁).V`, i.e.\
-- `W₂ ⊆ G.V \ W₁` per `def_3_10` item ii.  The rewritten tex's
-- "Well-typedness of the inner splitting on the LHS" paragraph proves
-- this from `W₂ ⊆ G.V` and `W₁ ∩ W₂ = ∅` (`Disjoint W₁ W₂`).
--
-- ## Design choice
--
-- *Standalone helper, not an inline `by`-block in the theorem signature.*
--   The LHS's outer `nodeSplittingOn W₂ ?_` needs a *proof term* for
--   the inner-`hW` argument of `def_3_11`'s constructor, not a tactic
--   blob.  Inlining a `by`-block in the type was rejected because
--   (i) it would clutter the rendered statement on the website with
--   pure carrier-subset bookkeeping, and (ii) it would duplicate the
--   same `(G.V ∖ W₁)`-arithmetic at every future `doit`-then-`spl`
--   use site.  Mirrors the `subset_carrier_of_hardInterventionOn`
--   pattern from `claim_3_4` (`HardInterventionsCommute`).
--
-- *Hypothesis shape `Disjoint W₁ W₂`, not `W₁ ∩ W₂ = ∅` or
--   `W₂ ⊆ G.V ∖ W₁`.*  `Disjoint W₁ W₂` is the canonical Mathlib
--   `Finset` form and feeds `Finset.disjoint_right.mp hDisj hv : v ∉ W₁`
--   in one step.  Encoding the LN's "$W_1 \cap W_2 = \emptyset$" as a
--   raw `Finset.inter` equality would force a `Finset.mem_inter`
--   rewrite at every use site; encoding it as `W₂ ⊆ G.V ∖ W₁` would
--   couple this helper to the LHS-only reading and would not survive
--   a `Disjoint.symm` swap.  The `Disjoint` form is also what the
--   main theorem's `hDisj` binder ships, so no conversion is needed
--   at the call site.
--
-- *Implicit `G`, `W₁`, `W₂`; explicit `hW₁`, `hW₂`, `hDisj`.*  Mirrors
--   the binder convention of `def_3_10` and `def_3_11`.  At the call
--   site `subset_V_of_hardInterventionOn hW₁ hW₂ hDisj`, the implicit
--   arguments are synthesised from the goal and the call reads
--   left-to-right as "the inner intervention is on `W₁` via `hW₁`;
--   the carrier-target is `W₂` via `hW₂`; disjointness via `hDisj`".
--
-- *`private`, with helper markers.*  Localises the lemma to this file
--   so the `CDMG` namespace stays clean.  Helper markers wrap it so
--   the website builder pulls it out alongside the rendered statement
--   (without which the theorem head would reference an undefined
--   symbol).  Downstream `doit`-then-`spl` rows (chapter 5 do-calculus,
--   the disjoint-intervention algebra of ch.\ 8+) should re-introduce
--   the same private helper at their use site rather than reach
--   across files; if a chapter-wide reuse pattern emerges, it can be
--   promoted in a later refactor.
--
-- *Mathlib re-use.*  Built directly on `Finset.mem_sdiff` and
--   `Finset.disjoint_right`; no rolled-our-own abstraction is needed.
-- claim_3_8 --- start helper
private lemma subset_V_of_hardInterventionOn
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.J ∪ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₂ ⊆ (G.hardInterventionOn W₁ hW₁).V
-- claim_3_8 --- end helper
:= by
  intro v hv
  change v ∈ G.V \ W₁
  exact Finset.mem_sdiff.mpr ⟨hW₂ hv, Finset.disjoint_right.mp hDisj hv⟩

-- ## Helper — `W₁.image .unsplit` sits inside the carrier of the inner node-splitting
--
-- The RHS `(G.nodeSplittingOn W₂ hW₂).hardInterventionOn
-- (W₁.image SplitNode.unsplit) ?_` requires
-- `?_ : W₁.image .unsplit ⊆
--        (G.nodeSplittingOn W₂ hW₂).J ∪ (G.nodeSplittingOn W₂ hW₂).V`.
-- For each `v ∈ W₁`: `v ∈ G.J ∪ G.V` by `hW₁`; if `v ∈ G.J` then
-- `.unsplit v ∈ G.J.image .unsplit = (G.nodeSplittingOn W₂ hW₂).J`; if
-- `v ∈ G.V` then `v ∉ W₂` by `Disjoint W₁ W₂`, so `v ∈ G.V \ W₂` and
-- `.unsplit v ∈ (G.V \ W₂).image .unsplit ⊆
-- (G.nodeSplittingOn W₂ hW₂).V`.  The rewritten tex's "Carrier reading
-- of the equality" paragraph spells this out.
--
-- ## Design choice
--
-- *Standalone helper, not an inline `by`-block in the theorem signature.*
--   Symmetric reason to the LHS helper above: the RHS's outer
--   `hardInterventionOn (W₁.image .unsplit) ?_` needs a *proof term*
--   for the inner-`hW` argument of `def_3_10`'s constructor, not a
--   tactic blob.  Inlining a `by`-block in the type would clutter the
--   website-rendered statement with split-graph carrier arithmetic and
--   would duplicate the same `.unsplit`-injection reasoning at every
--   future `spl`-then-`doit` use site.  Mirrors the
--   `subset_carrier_of_hardInterventionOn` pattern from `claim_3_4`
--   and the sibling LHS helper above.
--
-- *Lift `W₁` via `Finset.image SplitNode.unsplit`, not via a fresh
--   `Finset` on the split carrier.*  The `unsplit` constructor of
--   `def_3_11`'s `SplitNode` is the type-level realisation of the LN's
--   "$v \in J \cup (V \sm W)$ stays in the carrier as itself" reading
--   — so `.image SplitNode.unsplit` tags each `w ∈ W₁` as a node that
--   the inner splitting on `W₂` left alone, faithful to the rewritten
--   tex's "Carrier reading of the equality" paragraph.  Forcing the
--   consumer to construct a fresh `Finset (SplitNode Node)` of "the
--   right copies of the nodes in `W₁`" and re-prove its
--   carrier-subset relation from scratch was rejected because it
--   discards the structural fact that *no* node of `W₁` is split (by
--   disjointness), losing the LN's clean "unsplit-injection" reading.
--   The same lift convention is used in `claim_3_7` for its
--   `W₂.image .unsplit` argument; reusing it here keeps the
--   formalisations parallel.
--
-- *Disjointness `Disjoint W₁ W₂` is load-bearing for the `V`-piece,
--   inert on the `J`-piece.*  When `v ∈ W₁ ∩ G.J`, the lift lands
--   directly in `G.J.image .unsplit = (G.nodeSplittingOn W₂ hW₂).J`,
--   *without* using disjointness — `def_3_11` leaves the input-node
--   side untouched.  Disjointness only enters when `v ∈ W₁ ∩ G.V`,
--   where we need `v ∉ W₂` to place the lift in
--   `(G.V ∖ W₂).image .unsplit` (the only piece of `(split).V` that
--   contains `.unsplit` constructors).  Surfacing this asymmetry in
--   the lemma body — the two `rcases` branches — keeps the consumer's
--   reading aligned with `def_3_11`'s carrier construction.
--
-- *`private`, with helper markers.*  Same rationale as the LHS
--   helper: file-local so the `CDMG` namespace stays clean, pulled by
--   the website builder alongside the rendered statement so the
--   theorem head does not reference an undefined symbol.  Downstream
--   `spl`-then-`doit` rows with a disjointness side condition (this
--   row's converse, and the do-calculus interactions in ch.\ 5)
--   should re-introduce the same pattern at their use site rather
--   than reach across files.
--
-- *Mathlib re-use.*  Built on `Finset.mem_image`, `Finset.mem_union`,
--   `Finset.mem_sdiff`, and `Finset.disjoint_left`; the case-split on
--   `v ∈ G.J ∪ G.V` uses `Finset.mem_union.mp (hW₁ hv)`.  No
--   rolled-our-own abstraction is needed.
-- claim_3_8 --- start helper
private lemma image_unsplit_subset_carrier_of_nodeSplittingOn
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.J ∪ G.V)
    {W₂ : Finset Node} (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    W₁.image SplitNode.unsplit ⊆
      (G.nodeSplittingOn W₂ hW₂).J ∪ (G.nodeSplittingOn W₂ hW₂).V
-- claim_3_8 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  rcases Finset.mem_union.mp (hW₁ hv) with hJ | hV
  · -- `v ∈ G.J` → `.unsplit v ∈ G.J.image .unsplit = (split).J`.
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · -- `v ∈ G.V`: disjointness gives `v ∉ W₂`, so `v ∈ G.V \ W₂` and
    -- `.unsplit v` lands in the `(G.V \ W₂).image .unsplit` piece of
    -- `(split).V = (G.V \ W₂).image .unsplit ∪ W₂.image .copy0
    --   ∪ W₂.image .copy1`.
    have hv_notW₂ : v ∉ W₂ := Finset.disjoint_left.mp hDisj hv
    refine Finset.mem_union_right _ ?_
    refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hV, hv_notW₂⟩, rfl⟩

-- ref: claim_3_8
-- For any CDMG `G : CDMG Node` and any two subsets `W₁ ⊆ G.J ∪ G.V`,
-- `W₂ ⊆ G.V` with `Disjoint W₁ W₂`, the LN equality
--   `(G_{doit(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{doit(W₁)}`
-- holds as a literal `=` of CDMGs over the split-graph carrier
-- `SplitNode Node`.
/-
LN tex (rewritten canonical statement for `claim_3_8`):

  Let `G = (J, V, E, L)` be a CDMG and `W₁ ⊆ J ∪ V`, `W₂ ⊆ V` subject
  to `W₁ ∩ W₂ = ∅`.  Then
    `(G_{doit(W₁)})_{spl(W₂)} = (G_{spl(W₂)})_{doit(W₁)}`,
  read as a literal `=` of CDMGs over the split-graph carrier (NOT up
  to a carrier-relabelling map): the inner `spl(W₂)` on the LHS is
  well-defined because `W₂ ⊆ V \ W₁ = V_{doit(W₁)}`; the outer
  `doit(W₁)` on the RHS is well-defined because `W₁`'s nodes inject
  into the split-graph carrier as their unsplit copies `.unsplit w`
  (every `w ∈ W₁` lies in `J ∪ (V ∖ W₂)` by disjointness).

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CDMG and `W_1 ⊆ J ∪ V` and `W_2 ⊆ V` two
  disjoint subsets of nodes of `G`.  Then the CDMG obtained from first
  hard intervening on `W_1` and then node-splitting `W_2` is the same
  CDMG that arises from first node-splitting `W_2` and then hard
  intervening on `W_1`:
    `(G_{doit(W_1)})_{spl(W_2)} = (G_{spl(W_2)})_{doit(W_1)}`.
-/
-- ## Design choice
--
-- *Literal `=` of CDMGs over `SplitNode Node`, NOT
--   `eqViaNodeMap` / `flattenSplit`.*  This is the single most
--   important shape decision for this row and the reason the
--   formalisation is structurally simpler than `claim_3_7`
--   (`TwoDisjointNode`).  Both sides take a *single* node-splitting
--   on the same `W₂`, and `hardInterventionOn` preserves the node
--   carrier (`CDMG α → CDMG α` per `def_3_10`), so both sides land in
--   `CDMG (SplitNode Node)` — no carrier mismatch arises and the
--   asserted equality is a literal `=` between two terms of identical
--   Lean type.  Contrast with `claim_3_7`, where iterating
--   `nodeSplittingOn` twice produces `CDMG (SplitNode (SplitNode Node))`
--   on both sides with the constructor wrappings of the same
--   underlying graph node disagreeing between the two iteration orders
--   (`.unsplit (.copy0 w)` vs `.copy0 (.unsplit w)`), forcing the
--   `eqViaNodeMap` / `flattenSplit` workaround.  Here the LN's "the
--   same CDMG" reading is delivered by Lean's structural `=`; no
--   carrier-relabelling map, no `Finset.image` chase through a
--   flatten function, no quotient types.  Mirrors the literal-`=`
--   pattern of `claim_3_4` (`HardInterventionsCommute`), now lifted
--   to the `SplitNode Node` carrier.
--
-- *Disjointness `Disjoint W₁ W₂` is genuinely load-bearing, not a
--   convenience hypothesis.*  Two distinct uses inside the signature:
--   (i) the LHS's inner `spl(W₂)` needs
--   `W₂ ⊆ G.V ∖ W₁ = V_{doit(W_1)}` (discharged by
--   `subset_V_of_hardInterventionOn`); (ii) the RHS's outer
--   `doit(W₁.image .unsplit)` needs the unsplit-lifted `W₁` to sit
--   inside `G.J.image .unsplit ∪ (G.V ∖ W₂).image .unsplit`
--   (discharged by `image_unsplit_subset_carrier_of_nodeSplittingOn`).
--   Both helpers consume `Disjoint W₁ W₂`.  Without it, a node
--   `w ∈ W₁ ∩ W₂` would simultaneously be hard-intervened (becomes an
--   input on one side) and split (gets new copies `w⁰`, `w¹` on the
--   other), and the iterated operations would commit to incompatible
--   carrier placements; the equality would no longer hold even
--   set-theoretically.  Encoded as Mathlib's `Disjoint W₁ W₂` rather
--   than as a raw `Finset.inter` equality, mirroring the helper
--   convention and matching `claim_3_7`'s hypothesis shape.
--
-- *`W₁.image SplitNode.unsplit` on the RHS, not a fresh `Finset` on
--   the split carrier.*  Faithful to the rewritten tex's "Carrier
--   reading of the equality" paragraph: every `w ∈ W₁` lies in
--   `J ∪ (V ∖ W₂)` (by `hW₁` and disjointness with `W₂`), i.e.\ the
--   untagged piece of the split-graph carrier under `def_3_11`'s
--   shorthand "$v^0 := v^1 := v$ for $v \in J \cup (V \sm W_2)$".
--   At the Lean level this untagged piece is exactly the image of
--   `SplitNode.unsplit`.  Lifting via `.image .unsplit` lets the
--   RHS's outer `hardInterventionOn` be expressed in terms of the
--   *original* `W₁` (rather than forcing the consumer to construct a
--   fresh `Finset (SplitNode Node)` and re-prove its carrier-subset
--   relation from scratch).  The same lift convention is used in
--   `claim_3_7` for its `W₂.image .unsplit` argument; reusing it here
--   keeps the two formalisations parallel and makes downstream
--   composition lemmas easier to state.
--
-- *Single theorem, not a conjunction.*  The LN statement is a single
--   equality `LHS = RHS`, not a triple equality `A = B = C` of the
--   kind that `claim_3_4` and `claim_3_7` decomposed into `(a) ∧ (b)`.
--   There is no "joint intervention" form analogous to
--   `G_{do(W₁ ∪ W₂)}` here, because `doit` and `spl` are
--   structurally distinct operations (different carriers, different
--   field equations) and do not admit a single combined invocation.
--   Hence the natural Lean rendering is a single `theorem` with a
--   single `=`, with no `.1` / `.2` projection split.
--
-- *`addition_to_the_LN` is empty.*  No deviation or addition drove
--   any shape choice; the LN block's wording is the entire spec.
--   The `def_3_10` registered deviation
--   `hard_intervention_l_symmetrized_removal` (two-sided filter on
--   `L` instead of one-sided) is inherited from the operation level
--   but does not surface as a hypothesis at the statement level — it
--   only affects the bidirected-edge componentwise check inside the
--   proof body (Manager B's responsibility).
--
-- *Mathlib re-use.*  `Finset.image`, `Disjoint`, `Finset.mem_sdiff`,
--   `Finset.disjoint_left` / `_right` underpin both helpers and the
--   theorem signature.  `Finset.union_subset` is not needed at the
--   statement level because no joint intervention form appears.  The
--   split-graph carrier `SplitNode` is our own construction from
--   `def_3_11`; no Mathlib analogue exists.
--
-- *Downstream consequences.*  Once proven, this row enables clean
--   normalisation of `doit`-then-`spl` compositions for any later
--   chapter that mixes hard interventions with node-splitting (e.g.\
--   ch.\ 5 do-calculus combined with the latent-projection
--   interpretation of `spl`, and the iterated-intervention algebra of
--   ch.\ 8+).  The literal-`=` shape means the resulting CDMG
--   equalities can be `rw`'d in place at consumer sites rather than
--   transported via an `eqViaNodeMap` predicate — significantly
--   easier to consume than the carrier-relabelling form used by
--   `claim_3_7`.  Future composition rows mixing both operations
--   should aim to preserve this literal-`=` shape whenever the
--   underlying `nodeSplittingOn` depth is constant on both sides.
-- claim_3_8 -- start statement
theorem disjointHardInterventionsAndNodeSplittingsCommute (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (G.hardInterventionOn W₁ hW₁).nodeSplittingOn W₂
        (subset_V_of_hardInterventionOn hW₁ hW₂ hDisj)
      = (G.nodeSplittingOn W₂ hW₂).hardInterventionOn
          (W₁.image SplitNode.unsplit)
          (image_unsplit_subset_carrier_of_nodeSplittingOn hW₁ hW₂ hDisj)
-- claim_3_8 -- end statement
:= by
  -- CDMG extensionality: two CDMGs over the split-graph carrier are equal
  -- once their four data fields `(J, V, E, L)` agree.  The five
  -- propositional fields (`hJV_disj`, `hE_subset`, `hL_subset`,
  -- `hL_irrefl`, `hL_symm`) have types determined by the data fields, so
  -- proof irrelevance discharges them automatically.  Mirrors the
  -- inline-`cdmgExt` pattern of `claim_3_4`.
  have cdmgExt : ∀ {G₁ G₂ : CDMG (SplitNode Node)},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨J₁, V₁, hJV₁, E₁, hE₁, L₁, hL₁, hLi₁, hLs₁⟩
           ⟨J₂, V₂, hJV₂, E₂, hE₂, L₂, hL₂, hLi₂, hLs₂⟩ hJ hV hE hL
    obtain rfl := hJ
    obtain rfl := hV
    obtain rfl := hE
    obtain rfl := hL
    rfl
  -- Key membership lemma: under disjointness, the `toCopy0 W₂`-lift of a
  -- `Node` lies outside `W₁.image .unsplit` iff the original `Node` lies
  -- outside `W₁`.  Implements the tex proof's "$v_k^0 \notin W_1
  -- \Leftrightarrow v_k \notin W_1$" cross-check (used both in the
  -- *directed edges* section for the `e.2` head of each generator, and
  -- twice in the *bidirected edges* section for the two endpoints of
  -- each generator).
  --
  -- Case-split on `v ∈ W₂` mirrors the tex's case-split:
  --   * `v ∈ W₂`: `toCopy0 W₂ v = .copy0 v`, which is never in
  --     `W₁.image .unsplit` by constructor mismatch; on the other side
  --     `Disjoint W₁ W₂` rules out `v ∈ W₁`.  Both sides true.
  --   * `v ∉ W₂`: `toCopy0 W₂ v = .unsplit v`, which is in
  --     `W₁.image .unsplit` iff `v ∈ W₁` by injectivity of `.unsplit`.
  have toCopy0_notMem_iff : ∀ (v : Node),
      toCopy0 W₂ v ∉ W₁.image SplitNode.unsplit ↔ v ∉ W₁ := by
    intro v
    unfold toCopy0
    by_cases hW₂ : v ∈ W₂
    · rw [if_pos hW₂]
      refine ⟨fun _ hW₁ => Finset.disjoint_left.mp hDisj hW₁ hW₂,
              fun _ hMem => ?_⟩
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp hMem
      cases hweq
    · rw [if_neg hW₂]
      refine ⟨fun h hW₁ => h (Finset.mem_image.mpr ⟨v, hW₁, rfl⟩),
              fun h hMem => ?_⟩
      obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hMem
      cases hweq
      exact h hw
  refine cdmgExt ?_ ?_ ?_ ?_
  -- ===== Node sets: `J` =====
  -- LHS `J`: `(G.J ∪ W₁).image .unsplit` (after unfolding `nodeSplittingOn`
  -- applied to `G.hardInterventionOn W₁ hW₁`).
  -- RHS `J`: `G.J.image .unsplit ∪ W₁.image .unsplit` (after unfolding
  -- `hardInterventionOn` applied to `G.nodeSplittingOn W₂ hW₂`).
  -- Equal by `Finset.image_union`.
  · change (G.J ∪ W₁).image SplitNode.unsplit
          = G.J.image SplitNode.unsplit ∪ W₁.image SplitNode.unsplit
    exact Finset.image_union _ _
  -- ===== Node sets: `V` =====
  -- LHS `V`: `((G.V \ W₁) \ W₂).image .unsplit ∪ W₂.image .copy0
  --          ∪ W₂.image .copy1`.
  -- RHS `V`: `((G.V \ W₂).image .unsplit ∪ W₂.image .copy0
  --          ∪ W₂.image .copy1) \ W₁.image .unsplit`.
  -- Per the tex's "Output nodes" section: the three pieces of the
  -- split-graph carrier decompose under set-difference with
  -- `W₁.image .unsplit`:
  --   * `W₂.image .copy0 \ W₁.image .unsplit = W₂.image .copy0`
  --     (constructor mismatch),
  --   * `W₂.image .copy1 \ W₁.image .unsplit = W₂.image .copy1`
  --     (constructor mismatch),
  --   * `(G.V \ W₂).image .unsplit \ W₁.image .unsplit =
  --     ((G.V \ W₂) \ W₁).image .unsplit = ((G.V \ W₁) \ W₂).image .unsplit`
  --     (by injectivity of `.unsplit` and commutativity of two-step
  --     removal).
  -- We prove the equality directly via element-wise `ext` to keep the
  -- tex's case-on-constructor reading explicit.
  · change (((G.V \ W₁) \ W₂).image SplitNode.unsplit
              ∪ W₂.image SplitNode.copy0 ∪ W₂.image SplitNode.copy1)
          = ((G.V \ W₂).image SplitNode.unsplit
              ∪ W₂.image SplitNode.copy0 ∪ W₂.image SplitNode.copy1)
            \ W₁.image SplitNode.unsplit
    ext x
    constructor
    · -- LHS → RHS direction.
      intro hx
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · -- `x` is in the inner V (RHS-pre-sdiff).
        rcases Finset.mem_union.mp hx with hx12 | hx3
        · rcases Finset.mem_union.mp hx12 with hx1 | hx2
          · -- `x = .unsplit v`, `v ∈ (G.V \ W₁) \ W₂` ⊆ `G.V \ W₂`.
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
            obtain ⟨hv_VW₁, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
            obtain ⟨hv_V, _⟩ := Finset.mem_sdiff.mp hv_VW₁
            refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            exact Finset.mem_image.mpr
              ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₂⟩, rfl⟩
          · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            exact hx2
        · refine Finset.mem_union_right _ ?_
          exact hx3
      · -- `x ∉ W₁.image .unsplit`: case on which piece of LHS V holds x.
        rcases Finset.mem_union.mp hx with hx12 | hx3
        · rcases Finset.mem_union.mp hx12 with hx1 | hx2
          · -- `x = .unsplit v`, `v ∉ W₁` from `v ∈ G.V \ W₁`.
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
            obtain ⟨hv_VW₁, _⟩ := Finset.mem_sdiff.mp hv
            obtain ⟨_, hv_notW₁⟩ := Finset.mem_sdiff.mp hv_VW₁
            intro h
            obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp h
            cases hweq
            exact hv_notW₁ hw
          · -- `x = .copy0 w`: constructor mismatch with `.unsplit`.
            obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx2
            intro h
            obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
            cases hweq
        · -- `x = .copy1 w`: constructor mismatch with `.unsplit`.
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx3
          intro h
          obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
          cases hweq
    · -- RHS → LHS direction.
      intro hx
      obtain ⟨hx_inner, hx_notW₁'⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp hx_inner with hx12 | hx3
      · rcases Finset.mem_union.mp hx12 with hx1 | hx2
        · -- `x = .unsplit v`, `v ∈ G.V \ W₂`, and `v ∉ W₁` from
          -- `hx_notW₁'` (`.unsplit v ∉ W₁.image .unsplit` by injectivity).
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx1
          obtain ⟨hv_V, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
          have hv_notW₁ : v ∉ W₁ := fun h =>
            hx_notW₁' (Finset.mem_image.mpr ⟨v, h, rfl⟩)
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_sdiff.mpr ⟨hv_V, hv_notW₁⟩, hv_notW₂⟩
        · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          exact hx2
      · refine Finset.mem_union_right _ ?_
        exact hx3
  -- ===== Directed edges: `E` =====
  -- LHS `E`: `(G.E.filter (e.2 ∉ W₁)).image (toCopy1 W₂ ·.1, toCopy0 W₂ ·.2)
  --          ∪ W₂.image (·.copy0, ·.copy1)`.
  -- RHS `E`: `(G.E.image (toCopy1 W₂ ·.1, toCopy0 W₂ ·.2)
  --          ∪ W₂.image (·.copy0, ·.copy1)).filter (e.2 ∉ W₁.image .unsplit)`.
  -- Per the tex's "Directed edges" section:
  --   * Push the outer `.filter` through the union with `Finset.filter_union`.
  --   * For the lifted-`G.E` piece: `Finset.filter_image` swaps to a
  --     pre-image-filter form, and the predicate matches `e.2 ∉ W₁` via
  --     `toCopy0_notMem_iff` applied to `e.2`.
  --   * For the transfer-edge piece `W₂.image (·.copy0, ·.copy1)`: the
  --     head `.copy1 w` of each transfer edge is never in `W₁.image
  --     .unsplit` (constructor mismatch), so the filter is vacuous and
  --     leaves the set unchanged.
  · change ((G.E.filter (fun e : Node × Node => e.2 ∉ W₁)).image
              (fun e : Node × Node => (toCopy1 W₂ e.1, toCopy0 W₂ e.2))
            ∪ W₂.image (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w)))
          = (G.E.image
                (fun e : Node × Node => (toCopy1 W₂ e.1, toCopy0 W₂ e.2))
              ∪ W₂.image
                (fun w : Node => (SplitNode.copy0 w, SplitNode.copy1 w))).filter
              (fun e : SplitNode Node × SplitNode Node =>
                e.2 ∉ W₁.image SplitNode.unsplit)
    rw [Finset.filter_union, Finset.filter_image]
    congr 1
    · -- Lifted-`G.E` piece: filter-pred agreement under `Finset.filter_congr`.
      congr 1
      refine Finset.filter_congr ?_
      intro e he
      exact (toCopy0_notMem_iff e.2).symm
    · -- Transfer-edge piece: filter is vacuous on `W₂.image (·.copy0, ·.copy1)`.
      symm
      refine Finset.filter_true_of_mem ?_
      intro x hx
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx
      intro h
      obtain ⟨_, _, hweq⟩ := Finset.mem_image.mp h
      cases hweq
  -- ===== Bidirected edges: `L` =====
  -- LHS `L`: `(G.L.filter (e.1 ∉ W₁ ∧ e.2 ∉ W₁)).image
  --          (toCopy0 W₂ ·.1, toCopy0 W₂ ·.2)`.
  -- RHS `L`: `(G.L.image (toCopy0 W₂ ·.1, toCopy0 W₂ ·.2)).filter
  --          (e.1 ∉ W₁.image .unsplit ∧ e.2 ∉ W₁.image .unsplit)`.
  -- Per the tex's "Bidirected edges" section: `Finset.filter_image`
  -- swaps to a pre-image-filter form, and `toCopy0_notMem_iff` applies
  -- to both endpoints (the bidirected-edge case has no transfer-edge
  -- analogue — `def_3_11` item iv has a single image clause).  The
  -- two-sided filter convention here is the registered deviation
  -- `hard_intervention_l_symmetrized_removal` from `def_3_10`; per the
  -- tex's "Registered two-sided removal of `L`" paragraph, the two-sided
  -- and LN-literal one-sided readings agree under `L`'s symmetry axiom,
  -- so the tex's iff `v_k^0 ∉ W_1 ↔ v_k ∉ W_1` applied to both `k = 1, 2`
  -- closes the goal.
  · change (G.L.filter (fun e : Node × Node => e.1 ∉ W₁ ∧ e.2 ∉ W₁)).image
              (fun e : Node × Node => (toCopy0 W₂ e.1, toCopy0 W₂ e.2))
          = (G.L.image
                (fun e : Node × Node => (toCopy0 W₂ e.1, toCopy0 W₂ e.2))).filter
              (fun e : SplitNode Node × SplitNode Node =>
                e.1 ∉ W₁.image SplitNode.unsplit
                  ∧ e.2 ∉ W₁.image SplitNode.unsplit)
    rw [Finset.filter_image]
    congr 1
    refine Finset.filter_congr ?_
    intro e he
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(toCopy0_notMem_iff e.1).mpr h1, (toCopy0_notMem_iff e.2).mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(toCopy0_notMem_iff e.1).mp h1, (toCopy0_notMem_iff e.2).mp h2⟩

end CDMG

end Causality
