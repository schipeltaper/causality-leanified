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

end CDMG

end Causality
