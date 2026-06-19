import Chapter3_GraphTheory.Section3_1.CDMG

namespace Causality

/-!
# Extending CDMGs with intervention nodes (`def_3_13`)

This file formalises the LN definition `def_3_13`
(`\label{def:cdmg_intervention_nodes}` in `graphs.tex`) — the
*extended CDMG* operation `G ↦ G_{\doit(I_W)}` on a CDMG.  Given a CDMG
`G = (J, V, E, L)` and a subset `W ⊆ J ∪ V` of nodes, the extended
CDMG has

* `J_{\doit(I_W)} := J ⊍ { I_w | w ∈ W ∖ J }` — every `w ∈ W ∖ J`
  contributes a fresh intervention node `I_w` to the input-node side;
* `V_{\doit(I_W)} := V` — the output side is unchanged;
* `E_{\doit(I_W)} := E ⊍ { (I_w, w) | w ∈ W ∖ J }` — every fresh `I_w`
  comes with a single new directed edge `I_w → w`;
* `L_{\doit(I_W)} := L` — the bidirected side is unchanged.

The convention `I_j := j` for `j ∈ J ∩ W` is purely notational: no new
node is introduced on the `J ∩ W` branch, and the pre-existing `j`
plays the role of its own intervention node.  The set `I_W` is thus
`(J ∩ W) ∪ { I_w | w ∈ W ∖ J }` — a mix of pre-existing context nodes
on the `J ∩ W` branch and fresh symbols on the `W ∖ J` branch.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/def_3_13_ExtendingCDMGsWith.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:cdmg_intervention_nodes}`) augmented with the operator
clarification
`[I_W_mixes_fresh_nodes_and_existing_context_nodes]`:
the disjointness assertions `{ I_w | w ∈ W ∖ J } ∩ (J ∪ V) = ∅`
and `I_w ≠ I_{w'}` for distinct `w ≠ w'` in `W ∖ J` are realised
**at the type level** — `{ I_w | w ∈ W ∖ J }` is constructed as a
*tagged copy* via an `inductive` `IntExtNode Node` with two distinct
constructors `unsplit` (lifting every original node of `J ∪ V`) and
`intCopy` (producing the fresh `I_w` for each `w ∈ W ∖ J`).
Disjointness is thus a *typing* fact rather than a side condition.

The substantive design rationale — the choice of a *fresh*
two-constructor `inductive IntExtNode` rather than reusing `def_3_11`'s
three-constructor `SplitNode` (which would leave one constructor
unused for this row), the literal `Finset.image`-based set-builders
for `J_{\doit(I_W)}` and `E_{\doit(I_W)}`, and how each CDMG axiom of
`def_3_1` is discharged on the tagged-sum carrier — lives in the `--`
comment block immediately above the `def` declaration.  Read that
block before changing a field; it is the load-bearing contract for the
downstream chapter-3 rows (claim_3_14, claim_3_15) and the do-calculus
chapters that compose this operation with hard intervention and SWIG.

## Refactor (in progress) — `cdmg_typed_edges`

The upstream `def_3_1` refactor moves the bidirected-edge field of
`CDMG` from `Finset (Node × Node)` (plus an explicit `hL_symm`
symmetry axiom) to `Finset (Sym2 Node)` (swap-symmetry definitional
under the `Sym2` quotient).  The post-refactor declarations live
alongside the originals in this file, wrapped in `REFACTOR-BLOCK-
REPLACEMENT` markers (`refactor_extendingCDMGsWith` and four
`refactor_extendingCDMGsWith_h*` private lemmas — the pre-refactor
`_hL_symm` helper has no refactor twin).  The `L` field of the
extended CDMG is now `G.L.image (Sym2.map IntExtNode.unsplit)`, which
realises the LN's `L_{\doit(I_W)} := L` clause directly under the new
encoding: every unordered bidirected edge of `G` lifts to the
extended carrier with both endpoints carrying the `unsplit` tag, with
no `.intCopy`-incident bidirected edge ever produced.  Phase 7
cleanup will delete the ORIGINAL blocks and strip the `refactor_`
prefix from every replacement.
-/

namespace CDMG

-- ## Helper: variable binders for this row's declarations
--
-- One-sentence summary: a `variable` block introducing the implicit
-- node type `Node : Type*` and the decidable-equality instance
-- `[DecidableEq Node]` that every downstream declaration in this
-- file inherits.
--
-- *`variable` block, not `def`-local binders on each declaration.*
--   Mirrors the convention of every other chapter-3 section-3.2
--   operator (`def_3_10` `HardInterventionOn`, `def_3_11`
--   `NodeSplittingOn`, `def_3_12` `NodeSplittingHard`): the typeclass
--   binder auto-binds into both the helper `inductive IntExtNode`
--   and the main `extendingCDMGsWith` `def`, keeping their
--   signatures readable.  Inlining `{Node : Type*} [DecidableEq
--   Node]` on each declaration was rejected because it would
--   (i) re-state the typeclass binder on every sibling helper and
--   downstream consumer that pattern-matches on this file's API,
--   and (ii) drift away from section 3.2's shared implicit-`Node`
--   convention.
--
-- *Why `DecidableEq`, not weaker (no instance / `BEq`) or stronger
--   (`Fintype`, `LinearOrder`).*  Load-bearing for `Finset`-backed
--   image / union / membership-decidability operations on the four
--   data fields `J'`, `V'`, `E'`, `L'` of the extended CDMG; the
--   `Finset.image f` constructor on `Node`-indexed sets, together
--   with the `Finset.union` of two such images for `J'` and `E'`,
--   each require `DecidableEq` on the target type.  Load-bearing
--   also for the strict-equivalence example-verifier path, which
--   decides membership on concrete finite samples.  The
--   `IntExtNode`-side `[DecidableEq (IntExtNode Node)]` instance
--   that `CDMG (IntExtNode Node)` requires is lifted automatically
--   through `IntExtNode`'s `deriving DecidableEq` clause; the
--   `[DecidableEq Node]` binder here is the input that lifts
--   consumes.  Stronger constraints (`Fintype`, `LinearOrder`) are
--   not needed at this row's level — downstream consumer
--   responsibility — and adding them here would couple every
--   consumer to the stronger constraint unnecessarily.
-- def_3_13 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_13 --- end helper

-- ## Helper: the tagged-sum node universe of the extended graph
--
-- One-sentence summary: `IntExtNode Node` is the carrier type of the
-- extended CDMG `G_{doit(I_W)}` — a two-constructor tagged sum whose
-- `unsplit` constructor lifts every node of the original `Node`
-- carrier into the extended graph, and whose `intCopy` constructor
-- produces a fresh intervention symbol `I_w` for each
-- `w ∈ W ∖ G.J`.
--
-- ## Authoritative encoding context (LN + `addition_to_the_LN` + LN-critic)
--
-- The LN's clause i.) `J ⊍ {I_w | w ∈ W ∖ J}` uses the disjoint-
-- union symbol `\dot\cup` to enforce disjointness only between `J`
-- and the fresh-intervention image set — it does *not* explicitly
-- require `I_w ∉ V` for `w ∈ W ∖ J`, nor does it require
-- `I_{w₁} ≠ I_{w₂}` for distinct `w₁, w₂ ∈ W ∖ J`.  The operator's
-- `addition_to_the_LN` clause
-- `[I_W_mixes_fresh_nodes_and_existing_context_nodes]` and the
-- LN-critic working-phase subtlety
-- `fresh_intervention_nodes_not_required_disjoint_from_V` both
-- spell out the author's intent explicitly: each `I_w` (for
-- `w ∈ W ∖ J`) is a brand-new symbol, distinct from every element
-- of `J ∪ V` and from every other `I_{w'}`.  We satisfy that intent
-- **at the type level**: `IntExtNode.unsplit` and
-- `IntExtNode.intCopy` are distinct constructors of an `inductive`
-- type, so `intCopy w ≠ unsplit v` (constructor disjointness) and
-- `intCopy w₁ = intCopy w₂ → w₁ = w₂` (constructor injectivity)
-- hold for free.  No side-condition `Finset.Disjoint` proof
-- obligation, no freshness hypothesis on `Node`, no quotient — the
-- encoding turns the LN's *intent* into the *typing* of the carrier,
-- so the downstream `hJV_disj` / `hE_subset` / `hL_subset`
-- obligations on `def_3_1`'s `CDMG` structure reduce to constructor
-- pattern-matching plus `G`'s own axioms.
--
-- *`inductive` with two named constructors, not `Sum Node Node` /
--   `Option Node` / a subtype.*  The LN's "for each `w ∈ W ∖ J`
--   introduce a *fresh* intervention symbol `I_w`" reads as two
--   distinguishable kinds of element: the original nodes of `J ∪ V`
--   (lifted via `unsplit`) and the new intervention nodes `I_w`
--   (produced via `intCopy`).  Named constructors mirror the LN
--   symbols `v`, `I_w` one-for-one and let downstream pattern matches
--   read `| .unsplit v => …` / `| .intCopy w => …` instead of
--   `Sum.inl` / `Sum.inr` destructuring.  A `Sum Node Node` or
--   `Option`-based encoding was rejected because either requires a
--   translation table at every use site.
--
-- *Fresh two-constructor `IntExtNode`, NOT reusing `def_3_11`'s
--   three-constructor `SplitNode`.*  `SplitNode` has constructors
--   `unsplit`, `copy0`, `copy1`, designed for node-splitting where
--   each `w ∈ W` gets *two* tagged copies.  For this row each
--   `w ∈ W ∖ J` needs only *one* fresh symbol, so the third
--   constructor would be permanently unused.  Introducing a fresh
--   two-constructor `IntExtNode` keeps the carrier minimal and the
--   constructor semantics one-for-one with the LN's
--   intervention-node concept.  Downstream rows that compose this
--   operation with SWIG (`claim_3_15`) or hard intervention will deal
--   with the carrier mismatch via explicit lifts — they do that
--   anyway across every two-different-lifting composition.
--
-- *`deriving DecidableEq`.*  `def_3_1`'s `CDMG` carrier requires
--   `[DecidableEq Node]`; the extended graph lives over
--   `IntExtNode Node`, so we need `[DecidableEq (IntExtNode Node)]`
--   to satisfy `CDMG (IntExtNode Node)`.  The `deriving` handler
--   generates the instance `[DecidableEq Node] → DecidableEq
--   (IntExtNode Node)` for free; the alternative (a hand-written
--   instance) is pure boilerplate.
--
-- *No `W`-parameterised constructor or `Finset`-membership witness
--   baked into the type.*  A richer
--   `inductive IntExtNode (Node : Type*) (W : Set Node)` carrying a
--   per-constructor `w ∈ W ∖ J` proof would force every consumer to
--   manipulate that proof through every pattern match.  Whether a
--   `.intCopy w` is "valid" (i.e. `w ∈ W ∖ J`) is then enforced by
--   the *`Finset`* level of `J_{\doit(I_W)}` membership rather than
--   by the *type* itself.  This matches the LN reading: the fresh
--   intervention set `{I_w | w ∈ W ∖ J}` is a `Finset` inside the
--   carrier `IntExtNode Node`, not a separate type.
--
-- *Constructor naming: `unsplit` borrowed from `def_3_11`'s
--   `SplitNode`; `intCopy` chosen as a self-documenting tag for the
--   fresh intervention symbol.*  `unsplit` is the established
--   chapter-3 name for "lift a pre-existing `J ∪ V` node into the
--   extended carrier" (cf.\ `SplitNode.unsplit` in `def_3_11`,
--   `def_3_12`); reusing the constructor name across the
--   two-constructor and three-constructor carriers in this section
--   keeps cross-row pattern matches readable
--   (`(.unsplit v) => …` reads identically here as in the SWIG /
--   node-split files).  `intCopy` is chosen over candidate
--   alternatives `IW`, `Iw`, `iCopy`, `IntervCopy`: (i) `intCopy`
--   reads at the call site as "intervention copy of `w`", matching
--   the LN's "intervention node `I_w`" prose; (ii) it does not
--   carry the numerical labelling that `SplitNode.copy0` /
--   `SplitNode.copy1` use (which would mislead here — extension is
--   not a two-sided split; there is only *one* fresh tag per
--   `w ∈ W ∖ J`); (iii) it preserves the dot-notation idiom
--   `(.intCopy w) => …` for downstream pattern matches.
--
-- *The LN's notational shorthand `I_j := j` for `j ∈ J ∩ W` is
--   realised at the carrier level by ranging every
--   `intCopy`-image in the main def over `W ∖ G.J`, never over
--   `W`.*  The LN paragraph "Notational shorthand `I_j := j` for
--   `j ∈ J ∩ W`" stipulates that `I_j` is purely a label for the
--   pre-existing `j ∈ J` and that no new structure is introduced
--   on the `J ∩ W` branch.  We honour this at the carrier level by
--   restricting *every* `intCopy`-image in the main def (in `J'`
--   and in `E'`) to `W \ G.J` — never to `W` — so no
--   `IntExtNode.intCopy j` is ever created for `j ∈ J ∩ W`.  The
--   pre-existing `IntExtNode.unsplit j` (lifted from
--   `G.J.image .unsplit`) is the sole inhabitant of the
--   `I_W`-slot for `j ∈ J ∩ W`, automatically satisfying the LN's
--   `I_j := j` identification with no runtime conditional and no
--   extra wiring — the carrier shape *encodes* the convention.
--
-- *Mathlib re-use.*  Rolled our own.  Mathlib's `Sum` / `Option`
--   would not give named-constructor pattern matching, and Mathlib
--   has no general "tagged sum with two named constructors"
--   combinator.  The `deriving DecidableEq` handler is the only
--   Mathlib piece we lean on, and that piece is automatic.
--
-- *Constraints / known limitations.*  Distinct-constructor
--   disjointness gives us all the freshness facts the LN intends,
--   *but* the carrier inflates the cardinality:
--   `|IntExtNode Node| = 2 · |Node|`, so downstream consumers
--   iterating over the carrier (e.g.\ counting / summation
--   arguments) see twice the data the LN does.  Any consumer that
--   cares about cardinality will need to restrict to the
--   *inhabited* slice `G.J.image .unsplit ∪ G.V.image .unsplit ∪
--   (W ∖ G.J).image .intCopy` — the `J'` and `V'` sets together —
--   rather than range over the full type.  This is the standard
--   tagged-sum trade-off and matches the pattern set by
--   `def_3_11`'s `SplitNode`.
-- def_3_13 --- start helper
inductive IntExtNode (Node : Type*) where
  | unsplit (v : Node) : IntExtNode Node
  | intCopy (w : Node) : IntExtNode Node
  deriving DecidableEq
-- def_3_13 --- end helper

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: extendingCDMGsWith_hJV_disj
-- ## Proof helpers for the five CDMG axioms under extension
--
-- The five private lemmas below discharge the five proof obligations
-- of `def_3_1`'s `CDMG` structure (`hJV_disj`, `hE_subset`,
-- `hL_subset`, `hL_irrefl`, `hL_symm`) for the extension construction.
-- They are factored out of the structure-literal body of
-- `extendingCDMGsWith` so the def body is pure data + lemma
-- references — the website builder renders the def's signature, and a
-- reader sees the data assignments without proof clutter.  Only
-- `hE_subset` consumes `hW`: it is needed to derive `w ∈ G.V` from
-- `w ∈ W \ G.J` for the target of each new edge `(.intCopy w,
-- .unsplit w)`.  The other four obligations are discharged by the
-- type-level disjointness of `IntExtNode`'s two constructors together
-- with `G`'s own CDMG axioms.

private lemma extendingCDMGsWith_hJV_disj (G : CDMG Node) (W : Finset Node) :
    Disjoint (G.J.image IntExtNode.unsplit ∪ (W \ G.J).image IntExtNode.intCopy)
        (G.V.image IntExtNode.unsplit) := by
  rw [Finset.disjoint_left]
  rintro x hxJ hxV
  obtain ⟨v, hvV, rfl⟩ := Finset.mem_image.mp hxV
  rcases Finset.mem_union.mp hxJ with hJ | hI
  · -- `x = .unsplit v` is in `G.J.image .unsplit`: preimage `j ∈ G.J`
    -- with `.unsplit j = .unsplit v`, so `j = v` by constructor
    -- injectivity, contradicting `G.hJV_disj`.
    obtain ⟨j, hjJ, hjEq⟩ := Finset.mem_image.mp hJ
    cases hjEq
    exact Finset.disjoint_left.mp G.hJV_disj hjJ hvV
  · -- `x = .unsplit v` is in `(W \ G.J).image .intCopy`: preimage
    -- `w ∈ W \ G.J` with `.intCopy w = .unsplit v` — constructor
    -- mismatch, `cases` closes.
    obtain ⟨_, _, hwEq⟩ := Finset.mem_image.mp hI
    cases hwEq
-- REFACTOR-BLOCK-ORIGINAL-END: extendingCDMGsWith_hJV_disj

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: extendingCDMGsWith_hE_subset
private lemma extendingCDMGsWith_hE_subset (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ ⦃e : IntExtNode Node × IntExtNode Node⦄,
      e ∈ G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
          ∪ (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w)) →
      e.1 ∈ (G.J.image IntExtNode.unsplit ∪ (W \ G.J).image IntExtNode.intCopy) ∪
              G.V.image IntExtNode.unsplit ∧
        e.2 ∈ G.V.image IntExtNode.unsplit := by
  intro e he
  rcases Finset.mem_union.mp he with hImg | hNew
  · -- Lifted edge `(.unsplit e'.1, .unsplit e'.2)`, `e' ∈ G.E`.
    obtain ⟨e', he'E, rfl⟩ := Finset.mem_image.mp hImg
    obtain ⟨he'1, he'2⟩ := G.hE_subset he'E
    refine ⟨?_, ?_⟩
    · -- `e'.1 ∈ G.J ∪ G.V`: split into J / V branches.
      rcases Finset.mem_union.mp he'1 with hJ | hV
      · -- `e'.1 ∈ G.J`: `.unsplit e'.1` lands in `J' ⊆ J' ∪ V'`.
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨e'.1, hJ, rfl⟩
      · -- `e'.1 ∈ G.V`: `.unsplit e'.1` lands in `V' ⊆ J' ∪ V'`.
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨e'.1, hV, rfl⟩
    · -- `e'.2 ∈ G.V`: `.unsplit e'.2 ∈ G.V.image .unsplit = V'`.
      exact Finset.mem_image.mpr ⟨e'.2, he'2, rfl⟩
  · -- New edge `(.intCopy w, .unsplit w)`, `w ∈ W \ G.J`.
    obtain ⟨w, hwWJ, rfl⟩ := Finset.mem_image.mp hNew
    obtain ⟨hwW, hwNJ⟩ := Finset.mem_sdiff.mp hwWJ
    -- `w ∈ W ⊆ G.J ∪ G.V` and `w ∉ G.J`, so `w ∈ G.V` — this is the
    -- one place `hW` is genuinely consumed.
    have hwV : w ∈ G.V := by
      rcases Finset.mem_union.mp (hW hwW) with h | h
      · exact absurd h hwNJ
      · exact h
    refine ⟨?_, ?_⟩
    · -- `.intCopy w` lands in `(W \ G.J).image .intCopy ⊆ J' ⊆ J' ∪ V'`.
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨w, hwWJ, rfl⟩
    · -- `.unsplit w` lands in `G.V.image .unsplit = V'` (uses `hwV`).
      exact Finset.mem_image.mpr ⟨w, hwV, rfl⟩
-- REFACTOR-BLOCK-ORIGINAL-END: extendingCDMGsWith_hE_subset

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: extendingCDMGsWith_hL_subset
private lemma extendingCDMGsWith_hL_subset (G : CDMG Node) :
    ∀ ⦃e : IntExtNode Node × IntExtNode Node⦄,
      e ∈ G.L.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) →
      e.1 ∈ G.V.image IntExtNode.unsplit ∧
        e.2 ∈ G.V.image IntExtNode.unsplit := by
  intro e he
  obtain ⟨e', he'L, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨he'1, he'2⟩ := G.hL_subset he'L
  exact ⟨Finset.mem_image.mpr ⟨e'.1, he'1, rfl⟩,
         Finset.mem_image.mpr ⟨e'.2, he'2, rfl⟩⟩
-- REFACTOR-BLOCK-ORIGINAL-END: extendingCDMGsWith_hL_subset

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: extendingCDMGsWith_hL_irrefl
private lemma extendingCDMGsWith_hL_irrefl (G : CDMG Node) :
    ∀ ⦃v1 v2 : IntExtNode Node⦄,
      (v1, v2) ∈ G.L.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) →
      v1 ≠ v2 := by
  intro v1 v2 h
  obtain ⟨e', he'L, heq⟩ := Finset.mem_image.mp h
  have hne : e'.1 ≠ e'.2 := G.hL_irrefl he'L
  intro hv12
  apply hne
  have h1 : IntExtNode.unsplit e'.1 = v1 := by
    have := congrArg Prod.fst heq; simpa using this
  have h2 : IntExtNode.unsplit e'.2 = v2 := by
    have := congrArg Prod.snd heq; simpa using this
  have hUnsplitEq : IntExtNode.unsplit e'.1 = IntExtNode.unsplit e'.2 := by
    rw [h1, h2, hv12]
  injection hUnsplitEq
-- REFACTOR-BLOCK-ORIGINAL-END: extendingCDMGsWith_hL_irrefl

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: extendingCDMGsWith_hL_symm
private lemma extendingCDMGsWith_hL_symm (G : CDMG Node) :
    ∀ ⦃v1 v2 : IntExtNode Node⦄,
      (v1, v2) ∈ G.L.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) →
      (v2, v1) ∈ G.L.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) := by
  intro v1 v2 h
  obtain ⟨e', he'L, heq⟩ := Finset.mem_image.mp h
  have h1 : IntExtNode.unsplit e'.1 = v1 := by
    have := congrArg Prod.fst heq; simpa using this
  have h2 : IntExtNode.unsplit e'.2 = v2 := by
    have := congrArg Prod.snd heq; simpa using this
  have hsym : (e'.2, e'.1) ∈ G.L := G.hL_symm he'L
  refine Finset.mem_image.mpr ⟨(e'.2, e'.1), hsym, ?_⟩
  simp [h1, h2]
-- REFACTOR-BLOCK-ORIGINAL-END: extendingCDMGsWith_hL_symm

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: extendingCDMGsWith
-- ref: def_3_13
--
-- The *extended CDMG* of `G` w.r.t. `W` — the LN's
-- `G_{\doit(I_W)}` — is the CDMG `G.extendingCDMGsWith W hW` over the
-- carrier `IntExtNode Node` whose four components are
--
--   * `J' := G.J.image .unsplit ∪ (W \ G.J).image .intCopy` — the
--     original input nodes (lifted via `unsplit`) together with the
--     fresh intervention symbols `.intCopy w` for each
--     `w ∈ W \ G.J`;
--   * `V' := G.V.image .unsplit` — the output nodes are unchanged
--     (each lifted via `unsplit`);
--   * `E' := G.E.image (fun e => (.unsplit e.1, .unsplit e.2)) ∪
--             (W \ G.J).image (fun w => (.intCopy w, .unsplit w))` —
--     every directed edge of `G` is lifted with both endpoints
--     carrying the `unsplit` tag, plus a single new edge
--     `(.intCopy w, .unsplit w)` for each `w ∈ W \ G.J`;
--   * `L' := G.L.image (fun e => (.unsplit e.1, .unsplit e.2))` —
--     every bidirected edge of `G` is lifted with both endpoints
--     carrying the `unsplit` tag; no element of `(W \ G.J).image
--     .intCopy` ever appears in `L'`.
--
-- The hypothesis `hW : W ⊆ G.J ∪ G.V` is the LN's
-- "$W \subseteq J \cup V$" precondition.
/-
LN tex (rewritten `def_3_13_ExtendingCDMGsWith`, items i–iv):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq J \cup V$.
    The extended CDMG of $G$ w.r.t. nodes $W$ and corresponding
    intervention nodes $I_W := \{ I_w \mid w \in W \}$ (with the
    convention $I_j := j$ for $j \in J \cap W$, and fresh symbols
    `I_w` for `w ∈ W \setminus J`, realised at the type level via a
    tagged-sum carrier) is the CDMG
    $G_{\doit(I_W)} := (J_{\doit(I_W)}, V_{\doit(I_W)},
                        E_{\doit(I_W)}, L_{\doit(I_W)})$,
    where:
      i.   $J_{\doit(I_W)} := J \cup \{ I_w \mid w \in W \setminus J \}$;
      ii.  $V_{\doit(I_W)} := V$;
      iii. $E_{\doit(I_W)} := E \cup \{ (I_w, w) \mid w \in W \setminus J \}$;
      iv.  $L_{\doit(I_W)} := L$.

LN block (verbatim, for backup):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq J \cup V$ a
    subset of nodes.  The extended CDMG of $G$ w.r.t. nodes
    $W \subseteq J \cup V$ and corresponding intervention nodes
    $I_W = \{ I_w \mid w \in W \}$ with $I_j := j$ for
    $j \in J \cap W$, is the CDMG $G_{\doit(I_W)} := (J_{\doit(I_W)},
    V_{\doit(I_W)}, E_{\doit(I_W)}, L_{\doit(I_W)})$, where:
      i.   $J_{\doit(I_W)} := J \dcup \{ I_w \mid w \in W \setminus J \}$,
      ii.  $V_{\doit(I_W)} := V$,
      iii. $E_{\doit(I_W)} := E \dcup \{ I_w \tuh w \mid w \in W \setminus J \}$,
      iv.  $L_{\doit(I_W)} := L$,
    where we just add nodes $I_w$ for $w \in W \setminus J$ and edges
    $I_w \tuh w$ for $w \in W \setminus J$.
-/
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- * **`def`, not `structure` / `inductive` / `class`.**  Extending
--   with intervention nodes is a *function* `CDMG Node → Finset Node
--   → … → CDMG (IntExtNode Node)`, not new data and not a typeclass-
--   resolvable property.  The CDMG already has its `structure`
--   (`def_3_1`); this row produces a new CDMG over the tagged-sum
--   carrier `IntExtNode Node` from an existing one.  Mirrors the
--   sibling row pattern (`def_3_10` `HardInterventionOn`, `def_3_11`
--   `NodeSplittingOn`, `def_3_12` `NodeSplittingHard`): every CDMG
--   operator is a `def`, never a wrapper structure.
--
-- * **Carrier of the result is `IntExtNode Node`, NOT `Node`.**  This
--   is the load-bearing departure from `def_3_10`: hard intervention
--   keeps the same node universe (`Finset Node` operations on
--   `J ∪ W` / `V \ W`), whereas extending creates *fresh new nodes*
--   `I_w` that must be type-level distinct from the original `Node`
--   and from each other.  The `addition_to_the_LN`
--   `[I_W_mixes_fresh_nodes_and_existing_context_nodes]` fixes the
--   semantics: disjointness is at the *type level*, encoded via a
--   fresh `inductive IntExtNode` with two named constructors so the
--   LN's
--     `{I_w | w ∈ W ∖ J} ∩ (J ∪ V) = ∅`
--     `I_w ≠ I_{w'}` for distinct `w ≠ w' ∈ W ∖ J`
--   become typing facts, not `Disjoint` proof obligations.
--   Downstream consumers see the carrier change in the return type
--   `CDMG (IntExtNode Node)` and pattern-match on `.unsplit` /
--   `.intCopy` as needed.  Resolves the LN-critic working-phase
--   subtlety `fresh_intervention_nodes_not_required_disjoint_from_V`
--   by typing rather than as a side condition.
--
-- * **Fresh `IntExtNode` rather than reusing `def_3_11`'s
--   `SplitNode`.**  `SplitNode` has *three* named constructors
--   `unsplit`, `copy0`, `copy1` because node-splitting introduces two
--   tagged copies per `w ∈ W`.  Extension introduces only *one*
--   fresh symbol per `w ∈ W ∖ J`, so reusing `SplitNode` would leave
--   one constructor permanently unused.  Keeping the carrier minimal
--   (two constructors, semantically `original / intervention`) makes
--   the type's intent self-documenting and saves the `.copy1`
--   constructor for the SWIG-side semantics it was designed for.
--   Downstream rows that compose extension with SWIG or node
--   splitting (`claim_3_15`) will deal with the carrier mismatch via
--   explicit lifts — they do that anyway across every
--   two-different-lifting composition.
--
-- * **The notational convention `I_j := j` for `j ∈ J ∩ W` is
--   captured *implicitly* by NOT introducing `.intCopy` constructors
--   for the `J ∩ W` slice.**  The image clauses `(W \ G.J).image
--   .intCopy` and `(W \ G.J).image (fun w => (.intCopy w, .unsplit
--   w))` are *both* restricted to `W \ G.J` — never `W` — so no
--   fresh symbol is created for `j ∈ J ∩ W`.  The pre-existing
--   `.unsplit j` (from `G.J.image .unsplit`) is the sole inhabitant
--   of the `I_W`-slot for `j ∈ J ∩ W`.  This is exactly the LN's
--   "$I_j := j$ purely as a notational shorthand" reading: the
--   notational identification adds no new structure on the `J ∩ W`
--   branch.
--
-- * **`hW : W ⊆ G.J ∪ G.V` is an explicit argument, genuinely
--   consumed in `hE_subset`.**  The LN's "Let $W \subseteq J \cup V$"
--   is part of the *signature* of the extension operation.  Unlike
--   `def_3_10` `hardInterventionOn` and `def_3_11`
--   `nodeSplittingOn` (where `hW` is purely a signature constraint
--   and not consumed by the obligations), here `hW` is genuinely
--   needed for `hE_subset`: each new edge `(.intCopy w, .unsplit w)`
--   has target `w`, and we need `w ∈ G.V` to land it in
--   `V' = G.V.image .unsplit`.  The derivation is `w ∈ W \ G.J →
--   w ∈ W ⊆ G.J ∪ G.V`, and `w ∉ G.J` from the `W \ G.J`
--   membership, so `w ∈ G.V`.
--
-- * **`Finset.image` for every set-builder, not `Finset.filter`.**
--   The LN writes the four components as set-builders ranging over
--   `G.J` / `G.V` / `W \ G.J` / `G.E` / `G.L`; the construction
--   *creates* new elements via constructors, not selects subsets.
--   Lean's `Finset.image` is the closest primitive
--   (`Finset.mem_image` gives `b ∈ s.image f ↔ ∃ a ∈ s, f a = b`),
--   shares the `Finset (IntExtNode Node × IntExtNode Node)` carrier
--   between the `E'` and `L'` image clauses, and decidability of
--   `Finset.image` construction follows from the `DecidableEq`
--   instances on `Node` and `IntExtNode Node`.  Same rationale as
--   `def_3_11` / `def_3_12`.
--
-- * **Items i–iv literal translations.**  Item i's two-piece union
--   `G.J.image .unsplit ∪ (W \ G.J).image .intCopy` spells out the
--   LN's `J \dcup \{I_w | w ∈ W ∖ J\}` literally, in the same
--   left-to-right order.  Item ii is the single-image
--   `G.V.image .unsplit` (the LN's `V` unchanged, lifted into
--   `IntExtNode Node` via `unsplit`).  Item iii's two-clause union
--   matches the LN's `E \dcup \{I_w → w | w ∈ W ∖ J\}` literally:
--   the first clause `G.E.image (fun e => (.unsplit e.1, .unsplit
--   e.2))` lifts every directed edge of `G` (both endpoints carry
--   the `unsplit` tag, since `G.E ⊆ (G.J ∪ G.V) × G.V` lives
--   entirely in the original carrier); the second clause adds the
--   single new edge `(.intCopy w, .unsplit w)` per `w ∈ W ∖ J`.
--   Item iv `G.L.image (fun e => (.unsplit e.1, .unsplit e.2))` is
--   the LN's `L` unchanged, lifted with both endpoints via `unsplit`
--   (since `G.L ⊆ G.V × G.V`, the lift is again entirely on the
--   original-carrier branch).  No `.intCopy`-incident bidirected
--   edges are ever created.
--
-- * **Type-level disjointness collapses the `hJV_disj` /
--   `hE_subset` / `hL_subset` proof obligations.**  Because
--   `IntExtNode.unsplit` and `IntExtNode.intCopy` are distinct
--   constructors of an `inductive` type, any cross-constructor case
--   in the proofs (e.g. `J ∩ V'` reduces to constructor mismatch on
--   the `intCopy` vs `unsplit` branch) is closed by `cases` on the
--   equality.  The only non-trivial case in `hJV_disj` is the
--   `G.J vs G.V` branch where both Finsets route through `unsplit`;
--   there the injectivity of `unsplit` reduces the obligation to
--   `G.hJV_disj`.  Same paradigm as `def_3_11` / `def_3_12`.
--
-- * **`hL_irrefl` and `hL_symm` transport pointwise from `G`.**
--   `L'` is the literal image of `G.L` under both-endpoints-via-
--   `unsplit`, so each pair in `L'` is the lift of a unique pair in
--   `G.L`.  Irreflexivity transports via `G.hL_irrefl` and
--   constructor injectivity of `unsplit`.  Symmetry transports
--   directly: if `(.unsplit a, .unsplit b) ∈ L'` then `(a, b) ∈ G.L`,
--   `G.hL_symm` gives `(b, a) ∈ G.L`, and the lift gives
--   `(.unsplit b, .unsplit a) ∈ L'`.
--
-- * **Argument order `(G : CDMG Node) (W : Finset Node) (hW : …)`.**
--   Matches the convention of every chapter-3 operator
--   (`G.hardInterventionOn`, `G.nodeSplittingOn`,
--   `G.nodeSplittingHard`), enabling dot-notation
--   `G.extendingCDMGsWith W hW`.  `W` precedes `hW` so the call site
--   reads left-to-right like the LN's "let `W ⊆ J ∪ V` be a subset".
--
-- * **`where` syntax with named fields, not anonymous-constructor
--   `⟨ … ⟩`.**  The `CDMG` `structure` has nine fields; named-field
--   `where` syntax keeps the four data assignments aligned with the
--   LN's items i–iv and the five proof-obligation references aligned
--   with `def_3_1`'s axioms.  Same convention as every other
--   chapter-3 CDMG operator.
--
-- * **Constructor-proof obligations live outside the def
--   (`extendingCDMGsWith_hJV_disj`, `extendingCDMGsWith_hE_subset`,
--   `extendingCDMGsWith_hL_subset`, `extendingCDMGsWith_hL_irrefl`,
--   `extendingCDMGsWith_hL_symm` — five `private lemma`s above the
--   def).**  Mirrors the "Constructor-proof obligations live
--   outside the def" pattern of `def_3_12` `NodeSplittingHard`: the
--   def body is pure data + named-lemma references, so the
--   website-rendered statement shows the four LN clauses
--   (items i / ii / iii / iv) on the right of the `:=` without any
--   tactic clutter, and a future reader sees the data assignments
--   aligned line-for-line with the LN.  Each helper is named after
--   the `def_3_1` `CDMG`-axiom field it discharges
--   (`_hJV_disj` ↔ `hJV_disj`, `_hE_subset` ↔ `hE_subset`, …), so a
--   reader who wants to inspect "why does `J' ∩ V' = ∅` hold"
--   reaches for the eponymous lemma rather than chasing a tactic
--   block buried inside a structure literal.  Only `_hE_subset`
--   genuinely consumes `hW` (to derive `w ∈ G.V` from
--   `w ∈ W ∖ G.J` for the target of each new edge
--   `(.intCopy w, .unsplit w)`); the other four obligations close
--   on constructor-disjointness / injectivity of `IntExtNode` plus
--   `G`'s own CDMG axioms.  Trade-off: the five private lemmas are
--   *unmarked* (no `-- start helper / end helper` wrappers), so
--   they are not part of the statement-marker-wrapped contract — a
--   downstream refactor that touches the field shapes will need to
--   re-derive each helper accordingly.  This is the same trade-off
--   `def_3_12` takes; it pays for itself in def-body readability.
--
-- * **Downstream consumers.**  `claim_3_14` (AddingInterventionNodes)
--   and `claim_3_15` (composition with SWIG / hard intervention) are
--   the immediate consumers; the do-calculus chapters (ch. 5+) and
--   iSCM intervention algebra (ch. 8+) build on the extended CDMG
--   when reasoning about identification graphs that thread soft and
--   hard interventions through a common ambient graph.  Each of
--   these rests on the four field assignments above; the tagged-sum
--   carrier `IntExtNode Node` is the contract those rows rely on.
-- def_3_13 -- start statement
def extendingCDMGsWith (G : CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V) : CDMG (IntExtNode Node) where
  J := G.J.image IntExtNode.unsplit ∪ (W \ G.J).image IntExtNode.intCopy
  V := G.V.image IntExtNode.unsplit
  hJV_disj := extendingCDMGsWith_hJV_disj G W
  E := G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
        ∪ (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w))
  hE_subset := extendingCDMGsWith_hE_subset G W hW
  L := G.L.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
  hL_subset := extendingCDMGsWith_hL_subset G
  hL_irrefl := extendingCDMGsWith_hL_irrefl G
  hL_symm := extendingCDMGsWith_hL_symm G
-- def_3_13 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: extendingCDMGsWith

-- ## Proof helpers for the four CDMG axioms under extension (post-refactor)
--
-- The four private lemmas below discharge the four proof obligations
-- of `def_3_1`'s post-refactor `refactor_CDMG` structure (`hJV_disj`,
-- `hE_subset`, `hL_subset`, `hL_irrefl`) for the extension
-- construction.  **One fewer than the pre-refactor five** — the
-- pre-refactor `_hL_symm` obligation is gone because `refactor_CDMG`'s
-- `L : Finset (Sym2 Node)` makes swap-symmetry definitional via the
-- `Sym2` quotient (`s(v₁, v₂) = s(v₂, v₁)` by construction), so the
-- LN's compound `(v₁, v₂) ∈ L ⟹ (v₂, v₁) ∈ L` axiom disappears from
-- `refactor_CDMG` entirely.  Only `hE_subset` consumes `hW`: it is
-- needed to derive `w ∈ G.V` from `w ∈ W \ G.J` for the target of
-- each new edge `(.intCopy w, .unsplit w)`.  The J/V/E ports are
-- mechanical line-for-line transports of the pre-refactor proofs (the
-- refactor leaves `G.J`, `G.V`, `G.E`, `G.hJV_disj`, `G.hE_subset`
-- untouched), so the only substantive proof rewrites land on the
-- L-side helpers, where the new shape (`Sym2`-typed `L`, `Sym2.Mem`
-- quantifier on `hL_subset`, `¬ s.IsDiag` on `hL_irrefl`) replaces
-- `Finset (Node × Node)` ordered-pair manipulation with a one-line
-- `Sym2.mem_map` / `Sym2.isDiag_map` invocation.

-- Discharges `refactor_CDMG.hJV_disj` for the extension construction:
-- `J' = G.J.image .unsplit ∪ (W \ G.J).image .intCopy` and
-- `V' = G.V.image .unsplit` are disjoint as `Finset (IntExtNode Node)`s.
-- *Mechanical port from the pre-refactor lemma*: the `cdmg_typed_edges`
-- refactor leaves `G.J`, `G.V`, and `G.hJV_disj` untouched, so the
-- tactic body is verbatim — only the `G : CDMG Node` binder swaps to
-- `G : refactor_CDMG Node`.  Strategy: `Finset.disjoint_left` reduces
-- to "no element of `J'` also lies in `V'`"; the cross-constructor case
-- (`.intCopy w` purportedly equal to `.unsplit v`) closes by
-- constructor mismatch (`cases hwEq`); the same-constructor case
-- (`.unsplit j = .unsplit v`) reduces to `G.hJV_disj` via `unsplit`'s
-- constructor injectivity.  No `Sym2` API enters here — `J`/`V` are
-- the `Finset Node` carriers that the refactor leaves alone.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: extendingCDMGsWith_hJV_disj (was: refactor_extendingCDMGsWith_hJV_disj)
private lemma refactor_extendingCDMGsWith_hJV_disj
    (G : refactor_CDMG Node) (W : Finset Node) :
    Disjoint (G.J.image IntExtNode.unsplit ∪ (W \ G.J).image IntExtNode.intCopy)
        (G.V.image IntExtNode.unsplit) := by
  rw [Finset.disjoint_left]
  rintro x hxJ hxV
  obtain ⟨v, hvV, rfl⟩ := Finset.mem_image.mp hxV
  rcases Finset.mem_union.mp hxJ with hJ | hI
  · obtain ⟨j, hjJ, hjEq⟩ := Finset.mem_image.mp hJ
    cases hjEq
    exact Finset.disjoint_left.mp G.hJV_disj hjJ hvV
  · obtain ⟨_, _, hwEq⟩ := Finset.mem_image.mp hI
    cases hwEq
-- REFACTOR-BLOCK-REPLACEMENT-END: extendingCDMGsWith_hJV_disj

-- Discharges `refactor_CDMG.hE_subset` for the extension construction:
-- every edge of `E' = G.E.image (both endpoints via .unsplit) ∪
-- (W \ G.J).image (fun w => (.intCopy w, .unsplit w))` has source in
-- `J' ∪ V'` and target in `V'`.  *Mechanical port from the
-- pre-refactor lemma*: the `cdmg_typed_edges` refactor restructures
-- only the `L` channel, leaving `G.E`, `G.hE_subset`, the LN's
-- directed-edge constraint `E ⊆ (J ∪ V) × V`, and the intervention-
-- edge channel itself (which lives in `E`, not `L` — see the main-def
-- block below for why directed-vs-bidirected typing matters at this
-- row) all untouched.  Strategy: case-split the union; for the
-- lifted-edge branch transport `G.hE_subset` pointwise through
-- `.unsplit`; for the new-intervention-edge branch derive
-- `w ∈ G.V` from `w ∈ W ⊆ G.J ∪ G.V` and `w ∉ G.J` — the *only*
-- place across the four post-refactor helpers where the `hW`
-- hypothesis is genuinely consumed.  No `Sym2` API enters here either.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: extendingCDMGsWith_hE_subset (was: refactor_extendingCDMGsWith_hE_subset)
private lemma refactor_extendingCDMGsWith_hE_subset
    (G : refactor_CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ ⦃e : IntExtNode Node × IntExtNode Node⦄,
      e ∈ G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
          ∪ (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w)) →
      e.1 ∈ (G.J.image IntExtNode.unsplit ∪ (W \ G.J).image IntExtNode.intCopy) ∪
              G.V.image IntExtNode.unsplit ∧
        e.2 ∈ G.V.image IntExtNode.unsplit := by
  intro e he
  rcases Finset.mem_union.mp he with hImg | hNew
  · obtain ⟨e', he'E, rfl⟩ := Finset.mem_image.mp hImg
    obtain ⟨he'1, he'2⟩ := G.hE_subset he'E
    refine ⟨?_, ?_⟩
    · rcases Finset.mem_union.mp he'1 with hJ | hV
      · refine Finset.mem_union_left _ ?_
        refine Finset.mem_union_left _ ?_
        exact Finset.mem_image.mpr ⟨e'.1, hJ, rfl⟩
      · refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨e'.1, hV, rfl⟩
    · exact Finset.mem_image.mpr ⟨e'.2, he'2, rfl⟩
  · obtain ⟨w, hwWJ, rfl⟩ := Finset.mem_image.mp hNew
    obtain ⟨hwW, hwNJ⟩ := Finset.mem_sdiff.mp hwWJ
    have hwV : w ∈ G.V := by
      rcases Finset.mem_union.mp (hW hwW) with h | h
      · exact absurd h hwNJ
      · exact h
    refine ⟨?_, ?_⟩
    · refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨w, hwWJ, rfl⟩
    · exact Finset.mem_image.mpr ⟨w, hwV, rfl⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: extendingCDMGsWith_hE_subset

-- Discharges `refactor_CDMG.hL_subset` for the extension construction:
-- every endpoint of every unordered bidirected edge of `L' =
-- G.L.image (Sym2.map .unsplit)` lies in `V' = G.V.image .unsplit`.
-- *Substantive port from the pre-refactor lemma*: this is one of the
-- two helpers (with `_hL_irrefl`) whose body actually changes shape,
-- because the LN field obligation itself migrates from
-- `(e.1 ∈ V) ∧ (e.2 ∈ V)` on `Finset (Node × Node)` to
-- `∀ ⦃v⦄, v ∈ s → v ∈ V` on `Finset (Sym2 Node)`.  The post-refactor
-- `Sym2.Mem` quantifier is the *canonical* Mathlib idiom for "every
-- endpoint of an unordered pair lies in this set": it handles both
-- endpoints simultaneously without forcing a choice of representative
-- via `Sym2.mk`, mirrors the underlying root-side `refactor_CDMG.
-- hL_subset` shape one-for-one, and discharges in one pass over
-- `Sym2.mem_map`.  Strategy: `Finset.mem_image` extracts the
-- underlying `s' : Sym2 Node` with `s' ∈ G.L` and `Sym2.map
-- IntExtNode.unsplit s' = s`; Mathlib's
-- `Sym2.mem_map : v ∈ Sym2.map f s ↔ ∃ w ∈ s, f w = v` extracts a
-- preimage endpoint `w ∈ s'` with `.unsplit w = v` (no representative
-- chosen; both endpoints of `s'` are handled by the existential);
-- `G.hL_subset hs'L hwS` (the post-refactor `Sym2.Mem`-shaped axiom on
-- `G`) gives `w ∈ G.V`; conclude `v = .unsplit w ∈ G.V.image .unsplit`
-- via `Finset.mem_image.mpr`.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: extendingCDMGsWith_hL_subset (was: refactor_extendingCDMGsWith_hL_subset)
private lemma refactor_extendingCDMGsWith_hL_subset (G : refactor_CDMG Node) :
    ∀ ⦃s : Sym2 (IntExtNode Node)⦄,
      s ∈ G.L.image (Sym2.map IntExtNode.unsplit) →
      ∀ ⦃v : IntExtNode Node⦄, v ∈ s →
      v ∈ G.V.image IntExtNode.unsplit := by
  intro s hs v hv
  obtain ⟨s', hs'L, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨w, hwS, rfl⟩ := Sym2.mem_map.mp hv
  exact Finset.mem_image.mpr ⟨w, G.hL_subset hs'L hwS, rfl⟩
-- REFACTOR-BLOCK-REPLACEMENT-END: extendingCDMGsWith_hL_subset

-- Discharges `refactor_CDMG.hL_irrefl` for the extension construction:
-- no element of `L' = G.L.image (Sym2.map .unsplit)` is a self-pair
-- `s(v, v)`.  *Substantive port from the pre-refactor lemma*: phrased
-- as `¬ s.IsDiag` (Mathlib's canonical `Sym2 _` self-pair predicate,
-- `s.IsDiag ↔ ∃ v, s = s(v, v)`), NOT the pre-refactor `v₁ ≠ v₂` on
-- ordered pairs.  `Sym2.IsDiag` is the right idiom on unordered pairs:
-- it doesn't force destructuring through `Sym2.mk` representatives at
-- every irreflexivity-check site, and it mirrors the underlying root-
-- side `refactor_CDMG.hL_irrefl` shape one-for-one.  This preserves
-- the LN's "no bidirected self-loops `v ↔ v`" clause verbatim; the
-- redundant `(v₂, v₁) ∈ L` half of the LN's compound implication
-- (`(v₁, v₂) ∈ L → (v₂, v₁) ∈ L ∧ v₁ ≠ v₂` in the literal-LN reading)
-- disappears entirely under the `Sym2` quotient — symmetry is
-- definitional, so only the irreflexivity half survives.  Strategy:
-- `Finset.mem_image` extracts `s' ∈ G.L` with `Sym2.map .unsplit s' =
-- s`; Mathlib's
-- `Sym2.isDiag_map : Function.Injective f →
--    (Sym2.map f s).IsDiag ↔ s.IsDiag`
-- pulls `s.IsDiag` back to `s'.IsDiag`; constructor injectivity of
-- `IntExtNode.unsplit` supplies the injectivity premise inline;
-- `G.hL_irrefl hs'L` (the post-refactor `¬ s'.IsDiag`-shaped axiom on
-- `G`) closes by contradiction.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: extendingCDMGsWith_hL_irrefl (was: refactor_extendingCDMGsWith_hL_irrefl)
private lemma refactor_extendingCDMGsWith_hL_irrefl (G : refactor_CDMG Node) :
    ∀ ⦃s : Sym2 (IntExtNode Node)⦄,
      s ∈ G.L.image (Sym2.map IntExtNode.unsplit) →
      ¬ s.IsDiag := by
  intro s hs hDiag
  obtain ⟨s', hs'L, rfl⟩ := Finset.mem_image.mp hs
  have hinj : Function.Injective (@IntExtNode.unsplit Node) := fun _ _ h => by
    injection h
  have hs'Diag : s'.IsDiag := (Sym2.isDiag_map hinj).mp hDiag
  exact G.hL_irrefl hs'L hs'Diag
-- REFACTOR-BLOCK-REPLACEMENT-END: extendingCDMGsWith_hL_irrefl

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: extendingCDMGsWith_hL_symm
-- The pre-refactor CDMG carried an `hL_symm` axiom because `L` was
-- encoded as a `Finset (Node × Node)` that needed a separate
-- symmetry obligation.  Under `cdmg_typed_edges` the new `L` is a
-- `Finset (Sym2 Node)`, which is symmetric by construction, so the
-- `hL_symm` field — and every proof obligation that previously
-- discharged it — disappears from the refactor.  This empty
-- REPLACEMENT block exists only so the finalize-time marker validator
-- can pair the ORIGINAL `extendingCDMGsWith_hL_symm` block with a
-- same-named REPLACEMENT.
-- REFACTOR-BLOCK-REPLACEMENT-END: extendingCDMGsWith_hL_symm

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: extendingCDMGsWith (was: refactor_extendingCDMGsWith)
-- ref: def_3_13
--
-- The *extended CDMG* of `G` w.r.t. `W` — the LN's
-- `G_{\doit(I_W)}` — is the `refactor_CDMG`
-- `G.refactor_extendingCDMGsWith W hW` over the carrier
-- `IntExtNode Node` whose four components are
--
--   * `J' := G.J.image .unsplit ∪ (W \ G.J).image .intCopy` — the
--     original input nodes (lifted via `unsplit`) together with the
--     fresh intervention symbols `.intCopy w` for each
--     `w ∈ W \ G.J`;
--   * `V' := G.V.image .unsplit` — the output nodes are unchanged
--     (each lifted via `unsplit`);
--   * `E' := G.E.image (fun e => (.unsplit e.1, .unsplit e.2)) ∪
--             (W \ G.J).image (fun w => (.intCopy w, .unsplit w))` —
--     every directed edge of `G` is lifted with both endpoints
--     carrying the `unsplit` tag, plus a single new edge
--     `(.intCopy w, .unsplit w)` for each `w ∈ W \ G.J`;
--   * `L' := G.L.image (Sym2.map .unsplit)` — every (unordered)
--     bidirected edge of `G` is lifted via `Sym2.map .unsplit`, so
--     both endpoints carry the `unsplit` tag; no element of
--     `(W \ G.J).image .intCopy` ever appears in `L'`.
--
-- The hypothesis `hW : W ⊆ G.J ∪ G.V` is the LN's
-- "$W \subseteq J \cup V$" precondition.
/-
LN tex (rewritten `def_3_13_ExtendingCDMGsWith`, items i–iv):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq J \cup V$.
    The extended CDMG of $G$ w.r.t. nodes $W$ and corresponding
    intervention nodes $I_W := \{ I_w \mid w \in W \}$ (with the
    convention $I_j := j$ for $j \in J \cap W$, and fresh symbols
    `I_w` for `w ∈ W \setminus J`, realised at the type level via a
    tagged-sum carrier) is the CDMG
    $G_{\doit(I_W)} := (J_{\doit(I_W)}, V_{\doit(I_W)},
                        E_{\doit(I_W)}, L_{\doit(I_W)})$,
    where:
      i.   $J_{\doit(I_W)} := J \cup \{ I_w \mid w \in W \setminus J \}$;
      ii.  $V_{\doit(I_W)} := V$;
      iii. $E_{\doit(I_W)} := E \cup \{ (I_w, w) \mid w \in W \setminus J \}$;
      iv.  $L_{\doit(I_W)} := L$.

LN block (verbatim, for backup):

    Let $G = (J, V, E, L)$ be a CDMG and $W \subseteq J \cup V$ a
    subset of nodes.  The extended CDMG of $G$ w.r.t. nodes
    $W \subseteq J \cup V$ and corresponding intervention nodes
    $I_W = \{ I_w \mid w \in W \}$ with $I_j := j$ for
    $j \in J \cap W$, is the CDMG $G_{\doit(I_W)} := (J_{\doit(I_W)},
    V_{\doit(I_W)}, E_{\doit(I_W)}, L_{\doit(I_W)})$, where:
      i.   $J_{\doit(I_W)} := J \dcup \{ I_w \mid w \in W \setminus J \}$,
      ii.  $V_{\doit(I_W)} := V$,
      iii. $E_{\doit(I_W)} := E \dcup \{ I_w \tuh w \mid w \in W \setminus J \}$,
      iv.  $L_{\doit(I_W)} := L$,
    where we just add nodes $I_w$ for $w \in W \setminus J$ and edges
    $I_w \tuh w$ for $w \in W \setminus J$.
-/
-- ## Design choice (load-bearing contract for downstream chapter 3 rows)
--
-- This is the post-refactor port of `def_3_13` against the
-- `cdmg_typed_edges` design (`def_3_1` post-refactor shape:
-- `L : Finset (Sym2 Node)`, no `hL_symm` axiom).  The substantive
-- design choices below are identical to the pre-refactor encoding for
-- J/V/E (those fields are untouched by the refactor) and adjust only
-- the L-side construction + proof obligations.
--
-- * **`def`, not `structure` / `inductive` / `class`.**  Extending
--   with intervention nodes is a *function* `refactor_CDMG Node →
--   Finset Node → … → refactor_CDMG (IntExtNode Node)`, not new data
--   and not a typeclass-resolvable property.  The CDMG already has
--   its `structure` (`def_3_1`); this row produces a new CDMG over
--   the tagged-sum carrier `IntExtNode Node` from an existing one.
--   Mirrors the sibling row pattern (`def_3_10`–`def_3_12`): every
--   CDMG operator is a `def`, never a wrapper structure.
--
-- * **Carrier of the result is `IntExtNode Node`, NOT `Node`.**  This
--   is the load-bearing departure from `def_3_10`: hard intervention
--   keeps the same node universe, whereas extending creates *fresh
--   new nodes* `I_w` that must be type-level distinct from the
--   original `Node` and from each other.  The
--   `addition_to_the_LN`
--   `[I_W_mixes_fresh_nodes_and_existing_context_nodes]` fixes the
--   semantics: disjointness is at the *type level*, encoded via the
--   shared `inductive IntExtNode` (defined above) with two named
--   constructors so the LN's
--     `{I_w | w ∈ W ∖ J} ∩ (J ∪ V) = ∅`
--     `I_w ≠ I_{w'}` for distinct `w ≠ w' ∈ W ∖ J`
--   become typing facts, not `Disjoint` proof obligations.  See the
--   pre-refactor design block on the ORIGINAL def above for the
--   tagged-sum-vs-`SplitNode` rationale; the carrier choice does not
--   change in this refactor.
--
-- * **`hW : W ⊆ G.J ∪ G.V` is an explicit argument, genuinely
--   consumed in `hE_subset`.**  Same role as in the pre-refactor
--   encoding: the LN's "Let $W \subseteq J \cup V$" is part of the
--   *signature*, and `hE_subset` consumes it to derive `w ∈ G.V`
--   from `w ∈ W \ G.J` for the target of each new edge
--   `(.intCopy w, .unsplit w)`.
--
-- * **`Finset.image` for the four set-builders.**  Items i–iii are
--   `Finset.image`-based exactly as in the pre-refactor encoding
--   (those fields are untouched).  Item iv migrates from
--   `G.L.image (fun e => (.unsplit e.1, .unsplit e.2))` (a
--   `Finset (Node × Node) → Finset (IntExtNode Node × IntExtNode
--   Node)` map) to `G.L.image (Sym2.map IntExtNode.unsplit)` (a
--   `Finset (Sym2 Node) → Finset (Sym2 (IntExtNode Node))` map).
--   `Sym2.map : (α → β) → Sym2 α → Sym2 β` is Mathlib's quotient-lift
--   of a function from ordered pairs to unordered pairs; applied
--   here, it carries each unordered bidirected edge of `G` to the
--   extended carrier with both endpoints tagged `.unsplit`, exactly
--   matching the LN's `L_{\doit(I_W)} := L` clause (the bidirected
--   side is unchanged, lifted into `IntExtNode Node` only via
--   `unsplit`).  No `.intCopy`-incident bidirected edges are ever
--   produced.
--
-- * **`Sym2.map IntExtNode.unsplit` for the new `L'`, NOT `Sym2.lift`
--   paired with a swap-symmetry obligation, NOT destructuring through
--   `Sym2.mk` representatives.**  Three options were considered for
--   lifting `G.L : Finset (Sym2 Node)` to `Finset (Sym2 (IntExtNode
--   Node))`, and `Sym2.map` won on every axis:
--   (i) **`Sym2.lift`** packages an ordered-pair function
--       `f : Node × Node → β` with a swap-symmetry proof
--       `∀ a b, f (a, b) = f (b, a)` and quotient-lifts to
--       `Sym2 Node → β`.  Applied here it would force us to write
--       out the function-of-pairs `(a, b) ↦ s(.unsplit a, .unsplit b)`
--       and the (trivial) swap-symmetry proof at every L-manipulation
--       site, where `Sym2.map` exists precisely to short-circuit both.
--       Strictly more boilerplate, no benefit; rejected.
--   (ii) **Destructuring `s = Sym2.mk (a, b)` via a chosen
--        representative** would force picking a canonical
--        ordered-pair-of-endpoints that the `Sym2` quotient has *no*
--        canonical choice for — the entire point of adopting `Sym2`
--        at the root (`def_3_1`) is that there is no canonical
--        representative.  Any consumer downstream of the chosen
--        representative would then have to verify that the choice
--        doesn't leak into subsequent reasoning, dragging
--        `Quot.sound` / `Sym2.eq_swap` invocations into proofs that
--        the LN treats as orientation-free.  Rejected.
--   (iii) **`Sym2.map IntExtNode.unsplit`** (the chosen encoding) is
--        the canonical Mathlib quotient-functorial lift; it satisfies
--        `Sym2.map f s(a, b) = s(f a, f b)` definitionally, composes
--        with `Finset.image` to give the set-image in one line, and
--        comes paired with the exact API the four proof obligations
--        need (`Sym2.mem_map`, `Sym2.isDiag_map`) so each discharge
--        is a one-liner that never picks a representative.
--   The same `Sym2.map` choice is mirrored across every L-channel
--   operator in §3.2 (`def_3_10`–`def_3_14`), so a reader switching
--   between sibling files sees a uniform idiom.
--
-- * **The intervention-edge channel is *directed*, living in `E'`,
--   NOT *bidirected* in `L'`.**  LN clause iii adds the edges
--   `I_w \tuh w` for `w ∈ W ∖ J` — a typed *directed* arrow — encoded
--   as the new `Node × Node` union summand `(W \ G.J).image (fun w =>
--   (.intCopy w, .unsplit w))` of `E'`.  Two facts about this
--   placement matter at this row:
--   (i) The directed-vs-bidirected typing is irreducible: the LN's
--       `\tuh` arrow is asymmetric (source `I_w`, target `w`), so an
--       unordered-pair encoding via `Sym2` would lose direction and
--       falsely admit the reversed edge `w \tuh I_w` — which the LN
--       explicitly does *not* introduce.  A `Sym2`-typed alternative
--       for the new intervention edges was never on the table.
--   (ii) The `cdmg_typed_edges` refactor only restructures `L`, not
--        `E`.  The intervention-edge clause is therefore *unchanged*
--        from the pre-refactor original; the post-refactor `L'` lift
--        (`Sym2.map .unsplit` over `G.L`) never sees `.intCopy`-
--        incident vertices because every endpoint of `G.L`-images
--        comes through `.unsplit`.
--   Downstream walk-reversal arguments (`claim_3_22` σ-separation
--   symmetry) classify the channel by carrier type — `E'` carries
--   directed edges, `L'` carries bidirected edges — and rely on this
--   typing to never misclassify a `.intCopy w → .unsplit w` directed
--   intervention edge as a bidirected one.
--
-- * **Items i–iv literal translations.**  Items i, ii, iii are
--   verbatim translations of the pre-refactor encoding (J/V/E
--   unchanged by the refactor); item iv now lives on
--   `Finset (Sym2 (IntExtNode Node))` via `Sym2.map IntExtNode.unsplit`
--   instead of `Finset (IntExtNode Node × IntExtNode Node)` via a
--   pointwise-on-both-slots ordered-pair lift.  Both encodings carry
--   the same content: every bidirected edge of `G` lifts with both
--   endpoints tagged `unsplit`.  Under the post-refactor `Sym2`
--   quotient, the LN-literal symmetry of the bidirected edge
--   `v_1 \huh v_2 \Leftrightarrow v_2 \huh v_1` is *definitional* —
--   `s(.unsplit a, .unsplit b) = s(.unsplit b, .unsplit a)` holds by
--   construction — so the explicit `_hL_symm` field of the pre-
--   refactor `CDMG` (and the corresponding `_hL_symm` private lemma)
--   disappears entirely.
--
-- * **Type-level disjointness collapses the `hJV_disj` /
--   `hE_subset` / `hL_subset` proof obligations.**  Identical to the
--   pre-refactor encoding: distinct constructors `IntExtNode.unsplit`
--   and `IntExtNode.intCopy` of the `inductive` carrier discharge
--   every cross-constructor case in the proofs by constructor
--   mismatch (`cases hEq`), and `unsplit`'s constructor injectivity
--   reduces `J vs V` to `G.hJV_disj`.
--
-- * **`hL_subset` and `hL_irrefl` transport pointwise from `G` via
--   `Sym2.map`-and-injectivity-of-`unsplit`.**  The post-refactor
--   `hL_subset` is universally quantified via `Sym2.Mem`
--   (`∀ ⦃s⦄, s ∈ L → ∀ ⦃v⦄, v ∈ s → v ∈ V`) rather than the pre-
--   refactor `e.1 ∈ V ∧ e.2 ∈ V` on ordered pairs.  The discharge
--   uses `Sym2.mem_map` to extract a preimage endpoint, then
--   `G.hL_subset` pointwise.  The post-refactor `hL_irrefl` is
--   `¬ s.IsDiag` (Mathlib's `Sym2 _` self-pair predicate) rather
--   than the pre-refactor `v_1 ≠ v_2` on ordered pairs.  The
--   discharge uses `Sym2.isDiag_map` with constructor injectivity of
--   `IntExtNode.unsplit` to collapse `(Sym2.map .unsplit s').IsDiag
--   ↔ s'.IsDiag`, then `G.hL_irrefl`.  The pre-refactor `_hL_symm`
--   has no refactor variant — swap-symmetry is definitional on
--   `Sym2`, so the `refactor_CDMG` structure has no `hL_symm` field
--   to discharge.
--
-- * **Argument order
--   `(G : refactor_CDMG Node) (W : Finset Node) (hW : …)`.**  Matches
--   the convention of every chapter-3 operator (`def_3_10`–
--   `def_3_12`), enabling dot-notation
--   `G.refactor_extendingCDMGsWith W hW`.  `W` precedes `hW` so the
--   call site reads left-to-right like the LN's "let
--   `W ⊆ J ∪ V` be a subset".
--
-- * **`where` syntax with named fields, not anonymous-constructor
--   `⟨ … ⟩`.**  The `refactor_CDMG` `structure` has eight fields
--   (one fewer than the pre-refactor nine because `hL_symm` is gone);
--   named-field `where` syntax keeps the four data assignments
--   aligned with the LN's items i–iv and the four proof-obligation
--   references aligned with `def_3_1`'s post-refactor axioms.
--
-- * **Constructor-proof obligations live outside the def
--   (`refactor_extendingCDMGsWith_hJV_disj`, `…_hE_subset`,
--   `…_hL_subset`, `…_hL_irrefl` — four `private lemma`s above the
--   def, one fewer than the pre-refactor five).**  Mirrors the
--   pre-refactor pattern: the def body is pure data + named-lemma
--   references, so the website-rendered statement shows the four LN
--   clauses (items i / ii / iii / iv) on the right of the `:=`
--   without any tactic clutter, and a future reader sees the data
--   assignments aligned line-for-line with the LN.  Each helper is
--   named after the `def_3_1` post-refactor `refactor_CDMG`-axiom
--   field it discharges, so a reader who wants to inspect "why does
--   `J' ∩ V' = ∅` hold" reaches for the eponymous lemma rather than
--   chasing a tactic block buried inside a structure literal.  Only
--   `_hE_subset` genuinely consumes `hW`; the other three obligations
--   close on constructor-disjointness / injectivity of `IntExtNode`
--   plus `G`'s own (post-refactor) CDMG axioms and the `Sym2` API
--   (`Sym2.mem_map`, `Sym2.isDiag_map`).  Trade-off: the four private
--   lemmas are *unmarked* (no `-- start helper / end helper`
--   wrappers); this is the same trade-off as the pre-refactor
--   pattern.
--
-- * **Downstream consumers.**  `claim_3_14` (AddingInterventionNodes)
--   and `claim_3_15` (composition with SWIG / hard intervention) are
--   the immediate consumers; the do-calculus chapters (ch. 5+) and
--   iSCM intervention algebra (ch. 8+) build on the extended CDMG
--   when reasoning about identification graphs that thread soft and
--   hard interventions through a common ambient graph.  Each of
--   these rests on the four field assignments above; the tagged-sum
--   carrier `IntExtNode Node` is the contract those rows rely on,
--   and after the `cdmg_typed_edges` refactor finalises the L field
--   is structurally swap-symmetric — no `hL_symm` invocation, no
--   orientation swap, no mirror-pair gotcha.  This is the primary
--   downstream payoff of the refactor at this row.
--
-- ## Refactor port (cdmg_typed_edges)
--
-- Bidirected edges of the extended CDMG now live in
-- `Finset (Sym2 (IntExtNode Node))`; the lift is `Sym2.map
-- IntExtNode.unsplit`, which carries the LN's "both endpoints get
-- the `unsplit` tag" intent definitionally under the `Sym2` quotient
-- (`Sym2.map_mk : Sym2.map f s(a, b) = s(f a, f b)`).  The pre-
-- refactor `_hL_symm` helper has no refactor variant because
-- `refactor_CDMG` has no `hL_symm` field — swap-symmetry holds by
-- construction on `Sym2`.  The J/V/E fields and their three
-- discharges (`_hJV_disj`, `_hE_subset`) port mechanically because
-- those fields are untouched by the refactor.
-- def_3_13 -- start statement
def refactor_extendingCDMGsWith (G : refactor_CDMG Node) (W : Finset Node)
    (hW : W ⊆ G.J ∪ G.V) : refactor_CDMG (IntExtNode Node)
-- def_3_13 -- end statement
    where
  J := G.J.image IntExtNode.unsplit ∪ (W \ G.J).image IntExtNode.intCopy
  V := G.V.image IntExtNode.unsplit
  hJV_disj := refactor_extendingCDMGsWith_hJV_disj G W
  E := G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
        ∪ (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w))
  hE_subset := refactor_extendingCDMGsWith_hE_subset G W hW
  L := G.L.image (Sym2.map IntExtNode.unsplit)
  hL_subset := refactor_extendingCDMGsWith_hL_subset G
  hL_irrefl := refactor_extendingCDMGsWith_hL_irrefl G
-- REFACTOR-BLOCK-REPLACEMENT-END: extendingCDMGsWith

end CDMG

end Causality
