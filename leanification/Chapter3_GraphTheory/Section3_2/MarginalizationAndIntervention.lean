import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_2.MarginalizationAK
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.NodeSplittingOn
import Chapter3_GraphTheory.Section3_2.ExtendingCDMGsWith
import Chapter3_GraphTheory.Section3_2.MargPreservesAncestors

namespace Causality

/-!
# Marginalization and intervention commute (`claim_3_18`)

This file formalises the LN lemma `claim_3_18`
(`\label{marginalization-and-intervention-commute}` in `graphs.tex`).
Per the row's `addition_to_the_LN` the LN block bundles three
distinct commutativity claims under one `\begin{Lem}` heading — one
per intervention operator (hard intervention, adding intervention
nodes, node-splitting), each commuting with marginalization
(`def_3_14`).  The authoritative spec is the rewritten canonical tex
statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_18_statement_MarginalizationAndIntervention.tex`, verified
equivalent to the LN block plus the operator's
`addition_to_the_LN` clarification
`[trailing_similar_statement_two_unstated_claims]`.  The rewritten
tex spells the lemma out as a three-part enumerate with a single
equation per part:

* (i)  *(hard intervention)*       `(G_{doit(W₁)})^{∖W₂}    = (G^{∖W₂})_{doit(W₁)}`;
* (ii) *(adding intervention nodes)* `(G_{doit(I_{W₁})})^{∖W₂} = (G^{∖W₂})_{doit(I_{W₁})}`;
* (iii) *(node-splitting)*           `(G_{spl(W₁)})^{∖W₂}     = (G^{∖W₂})_{spl(W₁)}`.

The typing on `W₁` varies by part — `W₁ ⊆ J ∪ V` for (i) and (ii)
matching `def_3_10` / `def_3_13`, `W₁ ⊆ V` for (iii) matching
`def_3_11`.  `W₂ ⊆ V` in all three parts (so the inner / outer
marginalization is well-typed), and the disjointness side condition
`Disjoint W₁ W₂` is in force throughout.  The result-carrier varies
by part: `CDMG Node` for (i), `CDMG (IntExtNode Node)` for (ii),
`CDMG (SplitNode Node)` for (iii) — each side of each equation lives
in the same carrier (no `eqViaNodeMap` workaround needed; see the
"Carrier matching" paragraphs in the design blocks below).

The bodies of the three theorems are filled in by `prove_claim_in_lean`
(Manager B), following the to-be-written tex proofs at
`tex/claim_3_18_proof_MarginalizationAndIntervention.tex`.
-/

namespace CDMG

-- ## Design choice — row-level shape (three theorems in one file)
--
-- *Three separate theorems, not one parametric "for every intervention
--   operator" statement.*  The row's `addition_to_the_LN` clause
--   `[trailing_similar_statement_two_unstated_claims]` factors the LN's
--   single Lemma into three sub-claims with **different result
--   carriers** — `CDMG Node` for Part (i), `CDMG (IntExtNode Node)` for
--   Part (ii), `CDMG (SplitNode Node)` for Part (iii).  Lean has no
--   natural way to host a parametric quantification over "intervention
--   operator" that lets the return type vary by operator (each
--   operator's signature already fixes its return carrier), so the
--   three-theorem shape mirrors the addition's enumeration verbatim —
--   and the addition is the spec we must satisfy.  Bundling into one
--   conjunction would over-couple the three parts and obstruct
--   selective downstream citation: chapter 5's ID-algorithm
--   manipulation `G_{\doit(C)}^{\sm B}` (`id-algorithm.tex` 159-161,
--   485-498) cites only Part (i), and counterfactuals at
--   `counterfactuals.tex` 238-241 rest on the same Part (i) shape.
--   Contrast `claim_3_17` (MarginalizationsCommute), which the LN
--   states as a triple equality `=…=…` and is therefore formalized as
--   a single conjunctive theorem.
--
-- *One Lean file, not three per-part files.*  The three parts share
--   the same upstream-def chain (`def_3_1`, `def_3_10` / `_11` / `_13`,
--   `def_3_14`), the same shared lift helpers below
--   (`subset_sdiff_of_disjoint`, `subset_carrier_of_marginalize`, and
--   the two `image_unsplit_subset_*` helpers), and the same proof-
--   strategy template (CDMG-`ext` field-by-field).  Splitting per-part
--   would re-import the same chain three times and scatter the lift
--   helpers across files.  Split decision is deferred to a post-proof
--   refactor if the file passes ~3000 lines (cf.
--   `MarginalizationsCommute.lean` at 3639 lines).

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited from `def_3_1`
--   (`CDMG.lean`), `def_3_10` (`HardInterventionOn.lean`), `def_3_11`
--   (`NodeSplittingOn.lean`), `def_3_13` (`ExtendingCDMGsWith.lean`),
--   and `def_3_14` (`MarginalizationAK.lean`); load-bearing because the
--   signatures of all three theorems below construct `Finset`-backed
--   subsets of `G.J ∪ G.V` / `G.V`, applications of `Finset.image`
--   under `IntExtNode.unsplit` / `SplitNode.unsplit`, and the
--   marginalize / hardInterventionOn / extendingCDMGsWith /
--   nodeSplittingOn operators (each of which carries a `[DecidableEq]`
--   constraint into its return type's `CDMG` structure).  Stronger
--   instances (`Fintype`, `LinearOrder`) are not needed at the
--   statement level and are deferred to the proof body's use sites.
-- claim_3_18 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_18 --- end helper

-- ## Helper — `S ⊆ U \ T` from `S ⊆ U` and `Disjoint S T`
--
-- Used twice in the statement signatures: Part (i)'s LHS inner
-- `marginalize W₂` (needs `W₂ ⊆ (G.hardInterventionOn W₁ hW₁).V =
-- G.V \ W₁`) and Part (iii)'s RHS outer `nodeSplittingOn W₁` (needs
-- `W₁ ⊆ (G.marginalize W₂ hW₂).V = G.V \ W₂`).  The lemma is the
-- direct `.mpr` of mathlib's `Finset.subset_sdiff` and lives here so
-- the theorem signatures stay free of inline term-mode plumbing.
--
-- ## Design choice
--
-- *Re-prove locally rather than import from `MarginalizationsCommute.lean`.*
--   The sibling row's `subset_sdiff_of_disjoint` (claim_3_17) is
--   `private` to that file; per the per-row scope discipline
--   (`claude.md` rule 4) we re-prove it here under the same name
--   rather than promote it to a chapter-wide public helper.  The proof
--   is a one-liner Mathlib iff direction, so the duplication has
--   near-zero maintenance cost.
--
-- *Disjointness orientation `Disjoint S T`, matching the mathlib
--   iff.*  At the call sites the caller's `hDisj : Disjoint W₁ W₂`
--   (LN-symmetric phrasing) is composed with `.symm` when the
--   operator's argument order flips — see the call sites in Parts (i)
--   and (iii).

-- ## Helper — `S ⊆ G.J ∪ (G.V ∖ W)` from `S ⊆ G.J ∪ G.V` and `Disjoint S W`
--
-- Used twice in the statement signatures: Part (i)'s RHS outer
-- `hardInterventionOn W₁` and Part (ii)'s RHS outer
-- `extendingCDMGsWith W₁`, both applied to `G.marginalize W₂ hW₂`.
-- The outer constructor in each case requires `W₁ ⊆
-- (G.marginalize W₂ hW₂).J ∪ (G.marginalize W₂ hW₂).V`, which
-- unfolds (per `def_3_14`'s items i / ii) to `W₁ ⊆ G.J ∪ (G.V ∖ W₂)`.
-- This lemma discharges that subset from the available hypotheses
-- `hW₁ : W₁ ⊆ G.J ∪ G.V`, `hW₂ : W₂ ⊆ G.V`, and `hDisj : Disjoint W₁
-- W₂` via a per-element case split on `v ∈ G.J ∨ v ∈ G.V`.
--
-- ## Design choice
--
-- *Stand-alone helper, not an inline `by`-block in the theorem
--   signature.*  Mirrors the helper pattern in the sibling
--   `MarginalizationsCommute.lean` (`subset_sdiff_of_disjoint`),
--   `HardInterventionsCommute.lean` (`subset_carrier_of_hard…`), and
--   `AddingInterventionNodes.lean`
--   (`image_unsplit_subset_extendingCDMGsWith_carrier`): keeps the
--   rendered theorem on the website free of bookkeeping clutter, and
--   shares the lift between Parts (i) and (ii) at one definition
--   site.
--
-- *Disjointness orientation `Disjoint S W`* (`S` first, marginalize-
--   out `W` second).  Matches the LN's symmetric phrasing and the
--   natural call-site `subset_carrier_of_marginalize hW₂ hW₁ hDisj`
--   with `S := W₁`, `W := W₂`, `hDisj := claim_3_18's hDisj : Disjoint
--   W₁ W₂`.
--
-- *Implicit `G`, `W`, `S`; explicit `hW`, `hS`, `hDisj`.*  At the call
--   site `subset_carrier_of_marginalize hW₂ hW₁ hDisj`, the implicit
--   arguments are synthesised from the goal type, and the call reads
--   left-to-right as "the inner marginalization is on `W₂` via `hW₂`;
--   the transported set is `W₁` via `hW₁`; the disjointness witness
--   is `hDisj`".

-- ## Helper — `S.image .unsplit ⊆ (G.extendingCDMGsWith W hW).V`
--
-- Used once in the statement signatures: Part (ii)'s LHS inner
-- `marginalize (W₂.image .unsplit)` applied to
-- `G.extendingCDMGsWith W₁ hW₁`.  The marginalization requires
-- `W₂.image .unsplit ⊆ (G.extendingCDMGsWith W₁ hW₁).V`, which
-- unfolds (per `def_3_13` item ii) to `W₂.image .unsplit ⊆
-- G.V.image .unsplit`.  This lemma is the per-element witness from
-- `S ⊆ G.V`: `v ∈ S → v ∈ G.V → .unsplit v ∈ G.V.image .unsplit`.
--
-- ## Design choice
--
-- *Stand-alone helper, not an inline `by`-block in the theorem
--   signature.*  Same rationale as `subset_carrier_of_marginalize`
--   above.  Mirrors `image_unsplit_subset_extendingCDMGsWith_V` from
--   `AddingInterventionNodesSwig.lean` (privately re-defined; we
--   re-prove locally per the per-row scope discipline).
--
-- *No disjointness consumed.*  The `Finset.image .unsplit` lift only
--   needs the per-element membership `v ∈ G.V`; it does not interact
--   with the `W` of `extendingCDMGsWith` because `(extendingCDMGsWith
--   W hW).V` does not depend on `W` (only `J` does, via the
--   `intCopy`-image addition).  `hW` is bound on the signature for
--   uniformity with the call site `image_unsplit_subset_extendingCDMGs
--   With_V hW₁ hW₂`; the `set_option` keeps the linter quiet.

-- ## Helper — `S.image .unsplit ⊆ (G.nodeSplittingOn W₁ hW₁).V`
--
-- Used once in the statement signatures: Part (iii)'s LHS inner
-- `marginalize (W₂.image .unsplit)` applied to
-- `G.nodeSplittingOn W₁ hW₁`.  The marginalization requires
-- `W₂.image .unsplit ⊆ (G.nodeSplittingOn W₁ hW₁).V`, which
-- unfolds (per `def_3_11` item ii) to
-- `W₂.image .unsplit ⊆ (G.V \ W₁).image .unsplit ∪ W₁.image .copy0 ∪
--    W₁.image .copy1`.  This lemma routes the lift through the
-- `(G.V \ W₁).image .unsplit` piece: from `v ∈ S ⊆ G.V` and `Disjoint
-- S W₁` we get `v ∈ G.V \ W₁`, and `.unsplit v` lands in the
-- corresponding image piece.
--
-- ## Design choice
--
-- *Stand-alone helper, not an inline `by`-block in the theorem
--   signature.*  Same rationale as the sibling helpers above.
--   Mirrors `image_unsplit_subset_carrier_of_nodeSplittingOn` from
--   `DisjointHardInterventions.lean` (privately re-defined; we
--   re-prove locally per the per-row scope discipline) but lifts to
--   `(...).V` rather than `(...).J ∪ (...).V` because our lifted set
--   `W₂` lives in `G.V` (not `G.J ∪ G.V`).
--
-- *Disjointness consumed.*  Unlike `image_unsplit_subset_extendingCDMGs
--   With_V`, this lift needs `Disjoint S W₁` to route the lifted
--   `.unsplit v` through the `(G.V \ W₁).image .unsplit` piece of
--   `(G.nodeSplittingOn W₁ hW₁).V`.  Without disjointness, a `v ∈ S
--   ∩ W₁` would have `.unsplit v` *not* in `(G.V \ W₁).image .unsplit`
--   (it would belong to `W₁.image .copy0 / .copy1` after the lift
--   through `toCopy0 / toCopy1`, but the bare `.unsplit v` lifted from
--   `S` does not factor through `toCopy{0,1}`).
--
-- *Disjointness orientation `Disjoint S W₁`* (`S` first, split-on
--   `W₁` second).  Matches `subset_carrier_of_marginalize`'s
--   convention and the natural call-site
--   `image_unsplit_subset_nodeSplittingOn_V_of_disjoint hW₁ hW₂
--   hDisj.symm` (with claim_3_18's `hDisj : Disjoint W₁ W₂`).

-- ## Walk surgery for hard intervention (proof-only helpers for Part i).
--
-- The `hardInterventionOn` operator removes edges via `Finset.filter`:
--   `E_{doit(W)} := G.E.filter (e.2 ∉ W)`, `L_{doit(W)} := G.L.filter (e.1 ∉ W ∧ e.2 ∉ W)`.
-- A walk in `G.hardInterventionOn W hW` therefore canonically casts down to
-- a walk in `G` (each filtered-edge membership implies the original membership).
-- The reverse cast — a walk in `G` becomes a walk in `G.hardInterventionOn W hW`
-- — needs a per-edge filter-survival side condition; for directed walks it
-- collapses to "every head (every tail vertex) lies outside `W`", and for
-- general walks (bifurcations) it strengthens to "every vertex lies outside `W`".












-- ## Predicate iff lemmas for Part (i): Φ_E and Φ_L through doit + marg.
--
-- Each direction is handled separately:
--   * `(⇒)` direction uses `walk_ofDoit` (a structurally simple downward cast,
--     no side conditions).
--   * `(⇐)` direction lifts the walk from `G` back into `G.hardInterventionOn W₁ hW₁`,
--     done inline via `induction` on the walk (this avoids a separate
--     `walk_toDoit` def whose `by`-block body would block subsequent reduction
--     for preservation lemmas).





-- ## Field-equality lemmas for Part (i).



-- ref: claim_3_18 (part i / 3 — hard intervention)
-- For any CDMG `G : CDMG Node`, subsets `W₁ ⊆ G.J ∪ G.V` and
-- `W₂ ⊆ G.V` with `Disjoint W₁ W₂`, marginalization and hard
-- intervention commute as a literal `=` of CDMGs over the original
-- `Node` carrier:
--   `(G_{doit(W₁)})^{∖W₂} = (G^{∖W₂})_{doit(W₁)}`.
/-
LN tex (rewritten canonical statement for `claim_3_18`, part (i)):

  For every `W₁ ⊆ J ∪ V` and `W₂ ⊆ V` with `W₁ ∩ W₂ = ∅`:
    `(G_{doit(W₁)})^{∖W₂} = (G^{∖W₂})_{doit(W₁)}`.

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CDMG and `W_1 ⊆ J ∪ V` and `W_2 ⊆ V`
  two disjoint subsets of nodes from `G`.  Then we have:
    `(G_{doit(W_1)})^{∖W_2} = (G^{∖W_2})_{doit(W_1)}`.
-/
-- ## Design choice
--
-- *Literal `=` of CDMGs over `Node`, NOT `eqViaNodeMap`.*  Both sides
--   live in `CDMG Node`: `hardInterventionOn` preserves the node
--   carrier (`CDMG α → CDMG α`), and `marginalize` likewise preserves
--   it.  So the LHS `(G.hardInterventionOn W₁ hW₁).marginalize W₂ _`
--   and the RHS `(G.marginalize W₂ hW₂).hardInterventionOn W₁ _` are
--   two CDMGs of identical Lean type, and the asserted equality is a
--   literal `=`.  Matches `claim_3_4` (HardInterventionsCommute) and
--   `claim_3_17` (MarginalizationsCommute) — the carrier-preservation
--   pattern of the original-`Node`-carrier operators.
--
-- *Inner-`marginalize` carrier transport via `subset_sdiff_of_disjoint`.*
--   The LHS's outer `.marginalize W₂` needs a subset proof against
--   the inner-intervened CDMG's `V`, not against `G.V`.  The helper
--   `subset_sdiff_of_disjoint hW₂ hDisj.symm` transports the
--   hypothesis from `W₂ ⊆ G.V` to `W₂ ⊆ G.V \ W₁ =
--   (G.hardInterventionOn W₁ hW₁).V`, consuming `Disjoint W₂ W₁`
--   (the symmetric of the LN's `Disjoint W₁ W₂`).
--
-- *Outer-`hardInterventionOn` carrier transport via
--   `subset_carrier_of_marginalize`.*  The RHS's outer
--   `.hardInterventionOn W₁` needs a subset proof against the
--   marginalized CDMG's `J ∪ V = G.J ∪ (G.V \ W₂)`.  The helper
--   `subset_carrier_of_marginalize hW₂ hW₁ hDisj` discharges this from
--   `hW₁ : W₁ ⊆ G.J ∪ G.V` and `Disjoint W₁ W₂`.
--
-- *Disjointness binder `Disjoint W₁ W₂` (LN-symmetric phrasing).*
--   Matches the LN block's "two disjoint subsets of nodes from `G`"
--   and the sibling rows' (claim_3_17, claim_3_4, claim_3_8)
--   convention.  At the lift-helper call sites the orientation is
--   composed with `.symm` as needed.
--
-- *CDMG equality (`=`) is read field-wise.*  Equality of two `CDMG`s
--   unfolds via the `structure` injectivity from `def_3_1` to the
--   conjunction of equalities on the four data fields `J`, `V`, `E`,
--   `L` (the five propositional fields are determined by the data
--   and discharged by proof irrelevance).  We do not bake the
--   field-wise unpacking into the statement; it is deferred to the
--   proof per the rewritten tex's closing remark.

-- ref: claim_3_18 (part ii / 3 — adding intervention nodes)
-- For any CDMG `G : CDMG Node`, subsets `W₁ ⊆ G.J ∪ G.V` and
-- `W₂ ⊆ G.V` with `Disjoint W₁ W₂`, marginalization and the
-- intervention-node extension commute as a literal `=` of CDMGs over
-- the extended carrier `IntExtNode Node`:
--   `(G_{doit(I_{W₁})})^{∖W₂} = (G^{∖W₂})_{doit(I_{W₁})}`.
/-
LN tex (rewritten canonical statement for `claim_3_18`, part (ii)):

  For every `W₁ ⊆ J ∪ V` and `W₂ ⊆ V` with `W₁ ∩ W₂ = ∅`:
    `(G_{doit(I_{W₁})})^{∖W₂} = (G^{∖W₂})_{doit(I_{W₁})}`.

LN block (verbatim, for backup): the LN's lemma block (graphs.tex,
`\label{marginalization-and-intervention-commute}`) closes with
"A similar statement holds for marginalizations and adding
intervention nodes, ..."; per the row's `addition_to_the_LN` clause
`[trailing_similar_statement_two_unstated_claims]`, that trailer is
authoritative and asserts this part (ii).
-/
-- ## Design choice
--
-- *Literal `=` of CDMGs over `IntExtNode Node`, NOT `eqViaNodeMap`.*
--   Carrier analysis: the LHS's outermost operator is `marginalize`
--   applied to `G.extendingCDMGsWith W₁ hW₁ : CDMG (IntExtNode Node)`,
--   which preserves the carrier — so LHS : `CDMG (IntExtNode Node)`.
--   The RHS's outermost operator is `extendingCDMGsWith` applied to
--   `G.marginalize W₂ hW₂ : CDMG Node`, which carries to `CDMG
--   (IntExtNode Node)` — so RHS : `CDMG (IntExtNode Node)` also.  Both
--   sides have identical Lean type, so the asserted equality is a
--   literal `=` (no `flattenIntExt` workaround needed, unlike
--   `claim_3_14`'s iterated extension).
--
-- *Inner-`marginalize` lifted set `W₂.image IntExtNode.unsplit`.*  The
--   inner CDMG `G.extendingCDMGsWith W₁ hW₁` lives over `IntExtNode
--   Node`, so the LHS marginalization's `W` argument must inhabit
--   `Finset (IntExtNode Node)`.  The natural lift of `W₂ : Finset
--   Node` is `W₂.image IntExtNode.unsplit`, which targets the
--   `G.V.image IntExtNode.unsplit = (G.extendingCDMGsWith W₁ hW₁).V`
--   slice.  The subset proof is discharged by
--   `image_unsplit_subset_extendingCDMGsWith_V hW₁ hW₂` (no
--   disjointness needed for this lift).
--
-- *Outer-`extendingCDMGsWith` carrier transport via
--   `subset_carrier_of_marginalize`.*  Same helper as Part (i)'s RHS:
--   `extendingCDMGsWith` requires its `W₁` argument to sit in
--   `(G.marginalize W₂ hW₂).J ∪ (G.marginalize W₂ hW₂).V = G.J ∪
--   (G.V \ W₂)`, discharged by `subset_carrier_of_marginalize hW₂ hW₁
--   hDisj`.
--
-- *Why the LHS marginalizes by `W₂.image .unsplit` and the RHS
--   extends by the *original* `W₁`.*  This mirrors the LN's "$I_{W_1}$"
--   semantics: the intervention symbol set lives over the *original*
--   nodes `W₁`, so `extendingCDMGsWith W₁ _` is applied with the bare
--   `W₁ : Finset Node` on the RHS.  The LHS's inner extension already
--   produced the `IntExtNode`-carrier CDMG; from there the only thing
--   that can be marginalized are `IntExtNode`-flavoured nodes — and
--   the natural lift of "marginalize the original `W₂`" is the
--   `.unsplit`-image.  No new "intervention copy" element of
--   `W₂` is ever marginalized, only the original-side copies.
--   `verify_equivalence_strict` is the natural place to gate this
--   carrier-matching choice during Phase A.
-- ## Walk surgery for `extendingCDMGsWith` (proof-only helpers for Part ii).
--
-- Extension adds nodes and edges (no edge removal): every walk in `G` lifts to
-- a walk in `G.extendingCDMGsWith W hW` via the `.unsplit` constructor.  The
-- reverse cast — descending a walk in the extension back to a walk in `G` —
-- needs a per-vertex side condition that no vertex is `.intCopy`-tagged,
-- equivalently no edge is the fresh transfer edge `(.intCopy w, .unsplit w)`.









-- ## Walk descent: extension to G, when source is `.unsplit` and walk avoids fresh edges.
--
-- Given `p : Walk extension x y` with `x = .unsplit u`, every step's source is
-- the previous walk vertex.  If the walk's source is `.unsplit`-tagged AND
-- every intermediate is `.unsplit`-tagged (e.g., all interior vertices lie in
-- `W₂.image .unsplit`), then no fresh edge `(.intCopy w, .unsplit w)` can
-- appear (its source `.intCopy w` would have to equal a `.unsplit`-tagged
-- vertex, contradicting constructor disjointness).
-- We package this as a recursive lemma that, given proofs that all of `p`'s
-- vertices are `.unsplit`-tagged, descends `p` to a walk in `G`.


-- ## Image-sdiff identity for injective `.unsplit`.

-- ## `.unsplit v ∈ ext` ⟹ `v ∈ G` (carrier descent through `.unsplit`).

-- ## List utility: `(l.map .unsplit).tail = l.tail.map .unsplit`.

-- ## List utility: `(l.map .unsplit).dropLast = l.dropLast.map .unsplit`.

-- ## List utility: `(l.map .unsplit).tail.dropLast = l.tail.dropLast.map .unsplit`.

-- ## Two helpers: a `.unsplit_pair`-lifted edge in `ext.E` / `ext.L` lifts back
-- to a `G.E` / `G.L` edge.  Fresh edges cannot contribute (their source is
-- `.intCopy`, not `.unsplit`).


-- ## Helper: equality of pairs through `.unsplit`.

-- ## Walk descent: ext → G, when source/target are `.unsplit` and all
-- vertices are `.unsplit`-tagged.  Returns the descended walk `q` plus
-- length / vertex-list / edge-list / `IsDirectedWalk` / `IsBifurcationWithSplit`
-- preservation, in a single unified existence statement.

-- ## Helper: walk in ext from .unsplit u to .unsplit v with interior in
-- W₂.image .unsplit ⟹ all vertices are .unsplit-tagged.

-- ## Φ_E iff for Part (ii), .unsplit-source case.

-- ## Φ_L iff for Part (ii), .unsplit-endpoints case.

-- ## Helper: a directed walk in ext from `.intCopy w` (for `w ∈ W \ G.J`)
-- with interior in `W₂.image .unsplit` (and `Disjoint W W₂`) has its target
-- forced to be `.unsplit w` (i.e., is the single fresh edge).

-- ## E-field equality for Part (ii).

-- ## L-field equality for Part (ii).


-- ref: claim_3_18 (part iii / 3 — node-splitting)
-- For any CDMG `G : CDMG Node`, subsets `W₁, W₂ ⊆ G.V` with `Disjoint
-- W₁ W₂`, marginalization and node-splitting commute as a literal
-- `=` of CDMGs over the split carrier `SplitNode Node`:
--   `(G_{spl(W₁)})^{∖W₂} = (G^{∖W₂})_{spl(W₁)}`.
/-
LN tex (rewritten canonical statement for `claim_3_18`, part (iii)):

  For every `W₁ ⊆ V` and `W₂ ⊆ V` with `W₁ ∩ W₂ = ∅`:
    `(G_{spl(W₁)})^{∖W₂} = (G^{∖W₂})_{spl(W₁)}`.

LN block (verbatim, for backup): the LN's lemma block closes with
"A similar statement holds for ..., and also for marginalizations
and node-splitting interventions"; per the row's `addition_to_the_LN`
clause `[trailing_similar_statement_two_unstated_claims]`, that
trailer is authoritative and asserts this part (iii) with the typing
on `W₁` tightened to `W₁ ⊆ V` (matching `def_3_11`'s precondition).
-/
-- ## Design choice
--
-- *Typing on `W₁` is `W₁ ⊆ G.V`, NOT `W₁ ⊆ G.J ∪ G.V`.*  Departure
--   from Parts (i) and (ii): `nodeSplittingOn` (`def_3_11`) requires
--   `W₁ ⊆ G.V` strictly (the construction *removes* `W₁` from `V` and
--   creates tagged copies, which only makes sense on output nodes).
--   So Part (iii)'s `W₁`-binder is `hW₁ : W₁ ⊆ G.V`.  Confirmed by
--   the rewritten canonical statement tex.
--
-- *Literal `=` of CDMGs over `SplitNode Node`.*  Carrier analysis:
--   the LHS's outermost operator is `marginalize` applied to
--   `G.nodeSplittingOn W₁ hW₁ : CDMG (SplitNode Node)`, preserving
--   the carrier — so LHS : `CDMG (SplitNode Node)`.  The RHS's
--   outermost operator is `nodeSplittingOn` applied to `G.marginalize
--   W₂ hW₂ : CDMG Node`, carrying to `CDMG (SplitNode Node)` — so
--   RHS : `CDMG (SplitNode Node)` also.  Both sides have identical
--   Lean type; the equality is a literal `=`.  Same carrier-matching
--   pattern as Part (ii), now over `SplitNode Node`.
--
-- *Inner-`marginalize` lifted set `W₂.image SplitNode.unsplit`.*  The
--   inner CDMG `G.nodeSplittingOn W₁ hW₁` lives over `SplitNode
--   Node`, so the LHS marginalization's `W` argument must inhabit
--   `Finset (SplitNode Node)`.  The natural lift of `W₂ : Finset
--   Node` is `W₂.image SplitNode.unsplit`, which targets the
--   `(G.V \ W₁).image .unsplit` slice of `(G.nodeSplittingOn W₁
--   hW₁).V` (after `W₂ ⊆ G.V` + `Disjoint W₁ W₂` give `W₂ ⊆
--   G.V \ W₁`).  The subset proof is discharged by
--   `image_unsplit_subset_nodeSplittingOn_V_of_disjoint hW₁ hW₂
--   hDisj.symm` (note the `.symm`: the helper consumes
--   `Disjoint W₂ W₁`, the LN's symmetric phrasing here is `Disjoint
--   W₁ W₂`).
--
-- *Outer-`nodeSplittingOn` carrier transport via
--   `subset_sdiff_of_disjoint`.*  The RHS's outer `.nodeSplittingOn
--   W₁` requires `W₁ ⊆ (G.marginalize W₂ hW₂).V = G.V \ W₂`,
--   discharged by `subset_sdiff_of_disjoint hW₁ hDisj` (LN-direct
--   `Disjoint W₁ W₂` orientation, no `.symm` needed).
--
-- *No `W₂` -side marginalization on `W₁.image .copy0 / .copy1`.*  The
--   lifted set is `W₂.image SplitNode.unsplit`, not `W₂.image
--   SplitNode.copy0` or `.copy1`.  This is the LN-faithful reading:
--   the marginalization is over the *original* output nodes `W₂`,
--   none of which is a tagged copy — and by disjointness with `W₁`,
--   none of `W₂`'s elements has a `copy0` / `copy1` in the split
--   graph anyway.  `verify_equivalence_strict` is the natural place
--   to gate this carrier-matching choice during Phase A.
-- ## Image-sdiff identity for injective `SplitNode.unsplit`.

-- ## SplitNode constructor-disjointness helpers (Part iii V field).
--
-- `.unsplit v`, `.copy0 w`, `.copy1 w` are constructors of distinct cases of
-- the `SplitNode` inductive, so the three images do not share elements.



-- ## `.unsplit v ∈ split` ⟹ `v ∈ G` (carrier descent through `.unsplit`).

-- ## `toCopy0 W v = .unsplit v` when v ∉ W.


-- ## Lifted edge `(toCopy1 W₁ u, .unsplit v) ∈ split.E` from `(u, v) ∈ G.E`
-- when `v ∉ W₁` (target untagged in split).

-- ## Φ_E iff for Part (iii), source/target lifted via toCopy1/toCopy0.
-- This handles BOTH cases simultaneously: the source/target may be `.unsplit u` or
-- `.copy1 w` (for source) and `.unsplit v` or `.copy0 w` (for target).  We express
-- it uniformly via the toCopy lifts.
--
-- The lifted equivalence: marg-Φ_E on split (with source toCopy1 W₁ u and target
-- toCopy0 W₁ v) iff marg-Φ_E on G for (u, v), provided the marg-W₂ side is
-- compatible (W₁ ∩ W₂ = ∅, W₂ interior on G is also W₂-image-unsplit interior on split).

-- ## `v ∈ G` ⟹ `.unsplit v ∈ split` (carrier ascent for non-`W₁` vertices).
-- For `v ∈ J ∪ (G.V \ W₁)`, `.unsplit v` lives in `split.J ∪ split.V`.

-- ## `.copy0 w ∈ split` for `w ∈ W₁`.

-- ## `.copy1 w ∈ split` for `w ∈ W₁`.

-- ## Generic E-field lifted edge: `(toCopy1 W₁ u, toCopy0 W₁ v) ∈ split.E`
-- from `(u, v) ∈ G.E`.  No `W₁`-side condition needed (the toCopy{0,1} helpers
-- handle the case split internally).

-- ## Generic L-field lifted edge: `(toCopy0 W₁ u, toCopy0 W₁ v) ∈ split.L`
-- from `(u, v) ∈ G.L`.

-- ## `.unsplit v ∈ split` ⟹ `v ∈ G` AND `v ∉ W₁` (only the `(V\W₁).image .unsplit`
-- piece of split.V contains `.unsplit`-tagged elements with V-typed underlying).

-- ## `.copy0 w ∈ split` ⟹ `w ∈ W₁`.

-- ## `.copy1 w ∈ split` ⟹ `w ∈ W₁`.

-- ## Walk-step lift: directed step in G lifts to directed step in split via
-- `(toCopy1 W₁ a.1, toCopy0 W₁ a.2)`.  For the *forward* (Or.inl with E)
-- case this is direct; for Or.inl with L we get an L-edge lifted via copy0/copy0;
-- for Or.inr (backward E) we get the reversed lift.  This lemma handles the
-- generic case (no W₁ restriction); cases where intermediate consistency matters
-- are handled by the walk-level lift below.

-- ## Walk lift: G-walk u → v with ALL vertices in (J ∪ V) \ W₁ lifts to a
-- split-walk from `.unsplit u` to `.unsplit v` with all vertices `.unsplit`-tagged
-- and edges via `(toCopy1, toCopy0)`.






-- ## Helpers extracting underlying node from toCopy{0,1} equation with `.unsplit`.


-- ## Walk-step descent: split-step with `.unsplit` source AND target lifts
-- back to a G-walk-step.  The split-edge data `a : SplitNode × SplitNode` may
-- be either a lifted edge `(toCopy1 W₁ e.1, toCopy0 W₁ e.2)` (then `e.1, e.2`
-- must satisfy toCopy{0,1} = .unsplit, i.e., not in W₁) or a lifted L-edge
-- `(toCopy0 W₁ e.1, toCopy0 W₁ e.2)`.  Transfer edges `(.copy0 w, .copy1 w)`
-- are excluded because their endpoints are NOT `.unsplit`-tagged.

-- ## List utility: `(l.map .unsplit).tail = l.tail.map .unsplit` for SplitNode.



-- ## Helper: equality of pairs through `.unsplit` (SplitNode variant).

-- ## Two helpers analogous to Part (ii)'s: a `.unsplit`-pair-lifted edge in
-- split.E / split.L descends to a G.E / G.L edge.  Transfer edges cannot
-- contribute (their source is `.copy0`, not `.unsplit`).


-- ## Walk descent: split → G, when source/target are `.unsplit` and all
-- vertices are `.unsplit`-tagged.  Returns descended walk + length + vertex
-- list + edge list + IsDirectedWalk + IsBifurcationWithSplit preservation.

-- ## Helper: walk in split from .unsplit u to .unsplit v with interior in
-- W₂.image .unsplit ⟹ all vertices are .unsplit-tagged.

-- =====================================================================
-- ## Walk-surgery helpers for Part (iii) — toCopy0 endpoints.
--
-- These extend the .unsplit-endpoint machinery above to handle endpoints
-- landing in W₁ (which then map under toCopy0 to .copy0).  Used by the
-- E-field and L-field equalities in `marginalize_nodeSplittingOn_comm`.
-- =====================================================================

-- ## `toCopy0 W₁ v ∈ split` for v ∈ G.

-- ## `toCopy0 W₁` is injective on `Node`.

-- ## `toCopy0 W₁ v ∈ split.V \ W₂.image .unsplit` for `v ∈ G.V \ W₂`.

-- ## A `toCopy0 W₁ x` element of split.V \ W₂.image .unsplit is NOT a .copy1.

-- ## Recover underlying `v' ∈ G.V \ W₂` from a non-.copy1 split.V \ W₂.image .unsplit element.

-- ## Helper 1: lift a G-directed walk u → v whose interior lies in W₂ to a
-- split-walk from `.unsplit u` to `toCopy0 W₁ v`.  Source u ∉ W₁ is required
-- (so .unsplit u sits in split.V).  Interior vertices ∈ W₂ are automatically
-- ∉ W₁ via disjointness, so each intermediate lifts via the
-- `.unsplit`-pair edge.  Only the LAST edge may land in W₁ (when v ∈ W₁); there
-- the target lifts to `.copy0 v`, handled by `lifted_E_in_split_E_generic`.

-- ## Helper 2: lift a G-bifurcationWithSplit walk u → v whose interior lies in W₂
-- to a split-walk from `toCopy0 W₁ u` to `toCopy0 W₁ v`.  Sources/targets may be
-- in W₁ (lifted to .copy0), interior is in W₂ (so ∉ W₁, lifts via .unsplit).
-- Three sub-cases inside the cons step (matching `IsBifurcationWithSplit` shape):
--   * `i = 0, p' = nil`: single bidirected edge (a ∈ G.L).
--   * `i = 0, p' = cons`: hinge + directed right-arm (uses Helper 1).
--   * `i = k+1, p' anything`: left-arm reverse-E step + recurse via ih.

-- ## Helper 3: bifurcation lift (combining helpers).  Wraps Helper 2 by
-- extracting the split index and rebuilding the IsBifurcation conjunction.
-- The vertex constraints follow because every interior vertex in the lifted
-- walk is `.unsplit`-tagged (by Helper 1's all-.unsplit-interior structure
-- and Helper 2's all-.unsplit-interior structure).  We restate the constraint
-- via a vertex-list-tracking argument on the lifted walk.

-- ## Helper: a directed walk in split from `.copy0 w` (for `w ∈ W₁`)
-- with interior in `W₂.image .unsplit` (and `Disjoint W₁ W₂`) forces target
-- to be `.copy1 w` (i.e., is the single transfer edge).
--
-- Analogue of Part (ii)'s `walk_intCopy_target_unsplit`: the only outgoing
-- edge from `.copy0 w` in `split.E` is either the transfer edge
-- `(.copy0 w, .copy1 w)` or a lifted G-edge `(toCopy1 W₁ a, toCopy0 W₁ b)`
-- with `toCopy1 W₁ a = .copy0 w` — but `toCopy1 W₁ a ∈ {.unsplit a, .copy1 a}`,
-- never `.copy0`, so the lifted-edge case is impossible.  Hence the first
-- (and, by the interior constraint, only) edge is the transfer edge.

-- ## Walk ascent: lift G-walk to split with `toCopy1/toCopy0` endpoints.
--
-- Given a G-walk `q : Walk G u v` of positive length (directed, interior in W₂),
-- produce a split-walk from `toCopy1 W₁ u` to `toCopy0 W₁ v` with interior in
-- `W₂.image .unsplit`.  Each step lifts the underlying G-edge to its lifted form
-- `(toCopy1 W₁ a, toCopy0 W₁ b)` ∈ split.E via `lifted_E_in_split_E_generic`.
-- The length-positivity is required: a 0-length lift would need a walk from
-- `toCopy1 W₁ u` to `toCopy0 W₁ u`, which doesn't exist when u ∈ W₁
-- (then `.copy1 u` ≠ `.copy0 u`).

-- ## Walk descent: split → G with `toCopy1/toCopy0` endpoints.
--
-- Dual to `walk_G_lift_to_split`.  Given a split walk `p : Walk split x y` with
-- `x = toCopy1 W₁ u` and `y = toCopy0 W₁ v`, directed, interior in
-- `W₂.image .unsplit`, produce a G-walk `q : Walk G u v` of equal length with
-- interior in W₂.  The key observation: the source `toCopy1 W₁ u` is never a
-- `.copy0` constructor (it's `.unsplit` or `.copy1`), so no transfer edge can
-- start at `x`; every edge is a lifted G-edge.  Interior `.unsplit z` (z ∈ W₂,
-- so z ∉ W₁) acts as `toCopy1 W₁ z = toCopy0 W₁ z`, allowing the recursion to
-- continue with the same `toCopy1/toCopy0` discipline.

-- ## The Part (iii) Φ_E iff for `toCopy1`-source / `toCopy0`-target.
--
-- Direct bijection between a directed walk in `G.nodeSplittingOn W₁ hW₁` from
-- `toCopy1 W₁ u` to `toCopy0 W₁ v` (interior in `W₂.image .unsplit`) and a
-- directed walk in `G` from `u` to `v` (interior in `W₂`).  Uses the descent
-- and ascent helpers above.

-- ## Helper: a directed walk in split ending at `.copy1 w` (for `w ∈ W₁`),
-- with positive length and interior in `W₂.image .unsplit`, has its source equal
-- to `.copy0 w` (and is the single transfer edge).
--
-- Symmetric / dual to `walk_copy0_target_copy1`: the only incoming edge to
-- `.copy1 w` in `split.E` is either the transfer edge `(.copy0 w, .copy1 w)`
-- or a lifted G-edge `(toCopy1 W₁ a, toCopy0 W₁ b)` with `toCopy0 W₁ b = .copy1 w` —
-- but `toCopy0 W₁ b ∈ {.copy0 b, .unsplit b}`, never `.copy1`, so the lifted-edge
-- case is impossible.  Hence the last edge into `.copy1 w` is the transfer edge,
-- and any preceding edges must have been impossible (since interior `.unsplit z`
-- can't be `.copy0 w`).

-- ## E-field equality for Part (iii).
--
-- Mirrors Part (ii)'s `ext_marg_E_field_eq`.  The carrier of the LHS includes
-- a `W₁.image .copy0` summand (transfer-edge source), handled separately via
-- `walk_copy0_target_copy1` (forces target = `.copy1 w` for the same w).  The
-- other sources (`.unsplit j ∈ G.J`, `.unsplit v' ∈ (G.V \ W₁) \ W₂`, `.copy1 w`)
-- all factor through `toCopy1 W₁`, and `split_marg_PhiE_iff` bridges them to the
-- G-side Φ_E predicate.

-- =====================================================================
-- ## Part (iii) L-field helpers
--
-- The L-field iff and equality.  Both endpoints are `toCopy0`-tagged (which
-- collapses to `.unsplit`/`.copy0` depending on `W₁`-membership), and we
-- exclude `.copy1`-tagged endpoints via a bifurcation-walk analysis.
-- =====================================================================

















end CDMG

-- ## `open CDMG` — bring `IntExtNode`, `SplitNode` and the
-- function-style refactor twins (`extendingCDMGsWith`,
-- `nodeSplittingOn`, `SplitNode`, `toCopy0/1`)
-- into scope for the refactor twin block below.
--
-- Same rationale as `AddingInterventionNodes.lean:1043-1063`:
-- `extendingCDMGsWith` lives in `namespace CDMG` (not
-- `CDMG`), so dot-notation on `G : CDMG Node`
-- would not resolve it.  Bringing `CDMG` into scope lets us call
-- both `extendingCDMGsWith G W hW` (function-style) and
-- `G.hardInterventionOn / G.marginalize` (dot-style,
-- since those live in `namespace CDMG`).
namespace CDMG
open CDMG

-- claim_3_18 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_18 --- end helper

-- ## Refactor replacements — Phase 0 (shared helpers H1-H4).
--
-- All four shared helpers port mechanically modulo the `refactor_`
-- prefix and the upstream-name retargets (`CDMG → CDMG`,
-- `marginalize → marginalize`, `extendingCDMGsWith →
-- extendingCDMGsWith`, `nodeSplittingOn →
-- nodeSplittingOn`, `SplitNode → SplitNode`).
-- The bodies are byte-identical (modulo those retargets) to the
-- originals — no constructor case-splits, no Sym2 dance, no
-- WalkStep destructuring at the helper level.

-- claim_3_18 --- start helper
private lemma subset_sdiff_of_disjoint {S T : Finset Node}
    {U : Finset Node} (hS : S ⊆ U) (hDisj : Disjoint S T) :
    S ⊆ U \ T
-- claim_3_18 --- end helper
:= Finset.subset_sdiff.mpr ⟨hS, hDisj⟩

-- claim_3_18 --- start helper
private lemma subset_carrier_of_marginalize
    {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.V) {S : Finset Node} (hS : S ⊆ G.J ∪ G.V)
    (hDisj : Disjoint S W) :
    S ⊆ (G.marginalize W hW).J ∪ (G.marginalize W hW).V
-- claim_3_18 --- end helper
:= by
  intro v hv
  change v ∈ G.J ∪ (G.V \ W)
  rcases Finset.mem_union.mp (hS hv) with hJ | hV
  · exact Finset.mem_union_left _ hJ
  · refine Finset.mem_union_right _ ?_
    exact Finset.mem_sdiff.mpr ⟨hV, Finset.disjoint_left.mp hDisj hv⟩

-- claim_3_18 --- start helper
set_option linter.unusedVariables false in
private lemma image_unsplit_subset_extendingCDMGsWith_V
    {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V)
    {S : Finset Node} (hS : S ⊆ G.V) :
    S.image IntExtNode.unsplit ⊆ (extendingCDMGsWith G W hW).V
-- claim_3_18 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change IntExtNode.unsplit v ∈ G.V.image IntExtNode.unsplit
  exact Finset.mem_image.mpr ⟨v, hS hv, rfl⟩

-- claim_3_18 --- start helper
private lemma image_unsplit_subset_nodeSplittingOn_V_of_disjoint
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V)
    {S : Finset Node} (hS : S ⊆ G.V) (hDisj : Disjoint S W₁) :
    S.image SplitNode.unsplit ⊆ (G.nodeSplittingOn W₁ hW₁).V
-- claim_3_18 --- end helper
:= by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  change SplitNode.unsplit v ∈
    (G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_union_left _ ?_
  exact Finset.mem_image.mpr ⟨v,
    Finset.mem_sdiff.mpr ⟨hS hv, Finset.disjoint_left.mp hDisj hv⟩, rfl⟩

-- ## Refactor replacements — Phase i.A (walk surgery for hard intervention).
--
-- Body shifts:
--   1. `WalkStep` destructure changes from the ordered-pair-plus-Prop
--      disjunction to a constructor case-split on `.forwardE / .backwardE
--      / .bidir`.  The `.cons _ a hStep p` cons-cell pattern (4-arg)
--      becomes `.cons _ s p` (3-arg), and the `IsDirectedWalk` triple
--      `⟨ha, hE, hRec⟩` collapses to a direct `hRec`.
--   2. L-filter under `hardInterventionOn` is now
--      `G.L.filter (fun s => ∀ v ∈ s, v ∉ W)` (a `Sym2.ball`-shaped
--      predicate).  The `.bidir` branch of `walkStep_toDoit`
--      threads this via `Sym2.mem_iff.mp` → case-split on
--      `v = u ∨ v = v_mid`.
--   3. The 10-branch `IsBifurcationWithSplit` pattern-match
--      replaces the original's 3-clause `match i, p', hSpl`.

private lemma mem_doit_of_mem_G {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {v : Node} (hv : v ∈ G) :
    v ∈ G.hardInterventionOn W hW := by
  change v ∈ (G.J ∪ W) ∪ (G.V \ W)
  change v ∈ G.J ∪ G.V at hv
  rcases Finset.mem_union.mp hv with hJ | hV
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
  · by_cases hW' : v ∈ W
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hW')
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, hW'⟩)

private lemma mem_G_of_mem_doit {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {v : Node}
    (hv : v ∈ G.hardInterventionOn W hW) : v ∈ G := by
  change v ∈ (G.J ∪ W) ∪ (G.V \ W) at hv
  change v ∈ G.J ∪ G.V
  rcases Finset.mem_union.mp hv with h | h
  · rcases Finset.mem_union.mp h with hJ | hW'
    · exact Finset.mem_union_left _ hJ
    · exact hW hW'
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp h).1

-- WalkStep G_{doit} → G: descent through the filter.
-- Now a `def` returning `WalkStep` (a `Type`), case-splitting
-- on the typed constructor instead of the original's `Or`-destructure.
private def walkStep_ofDoit {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {u v : Node}
    (s : WalkStep (G.hardInterventionOn W hW) u v) :
    WalkStep G u v :=
  match s with
  | .forwardE h => .forwardE (Finset.mem_filter.mp h).1
  | .backwardE h => .backwardE (Finset.mem_filter.mp h).1
  | .bidir h => .bidir (Finset.mem_filter.mp h).1

/-- Cast a walk in `G.hardInterventionOn W hW` to a walk in `G`. -/
private def walk_ofDoit {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node},
      Walk (G.hardInterventionOn W hW) u v → Walk G u v
  | _, _, .nil v hv => Walk.nil v (mem_G_of_mem_doit (hW := hW) hv)
  | _, _, .cons v s p =>
      Walk.cons v (walkStep_ofDoit (hW := hW) s)
        (walk_ofDoit hW p)

private lemma walk_ofDoit_length {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      (walk_ofDoit hW p).length = p.length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p => by
      change (walk_ofDoit hW p).length + 1 = p.length + 1
      rw [walk_ofDoit_length hW p]

private lemma walk_ofDoit_vertices {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      (walk_ofDoit hW p).vertices = p.vertices
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p => by
      change _ :: (walk_ofDoit hW p).vertices = _ :: p.vertices
      rw [walk_ofDoit_vertices hW p]

private lemma walk_ofDoit_isDirectedWalk {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v),
      p.IsDirectedWalk → (walk_ofDoit hW p).IsDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons _ (.forwardE _) p, hDir =>
      walk_ofDoit_isDirectedWalk hW p hDir
  | _, _, .cons _ (.backwardE _) _, hDir => hDir.elim
  | _, _, .cons _ (.bidir _) _, hDir => hDir.elim

-- Port of the original 4-branch pattern-match into a tactic-mode
-- proof: `induction p`, then `cases s` to split on the constructor
-- tag of the cons-cell's WalkStep, then `match` on `i` and the tail.
-- Each branch uses `simp only [IsBifurcationWithSplit]` (or
-- the corresponding equation lemmas) to unfold the predicate
-- definitionally — Lean's equation-compiler-generated def-equations
-- don't reduce automatically under arbitrary patterns.
private lemma walk_ofDoit_isBifurcationWithSplit {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk (G.hardInterventionOn W hW) u v) (i : ℕ),
      p.IsBifurcationWithSplit i →
        (walk_ofDoit hW p).IsBifurcationWithSplit i := by
  intro u v p
  induction p with
  | nil _ _ =>
      intro i hSpl
      simp only [Walk.IsBifurcationWithSplit] at hSpl
  | @cons u' w' vMid s p' ih =>
      intro i hSpl
      cases s with
      | forwardE h_E =>
          match i, p', hSpl with
          | 0, .nil _ _, hSpl =>
              simp only [Walk.IsBifurcationWithSplit] at hSpl
          | 0, .cons _ _ _, hSpl =>
              simp only [Walk.IsBifurcationWithSplit] at hSpl
          | _ + 1, _, hSpl =>
              simp only [Walk.IsBifurcationWithSplit] at hSpl
      | backwardE h_E =>
          match i, p', hSpl, ih with
          | 0, .nil _ _, hSpl, _ =>
              simp only [Walk.IsBifurcationWithSplit] at hSpl
          | 0, .cons vI sI pI, hDir, _ =>
              simp only [Walk.IsBifurcationWithSplit] at hDir
              simp only [walk_ofDoit, walkStep_ofDoit,
                Walk.IsBifurcationWithSplit]
              exact walk_ofDoit_isDirectedWalk hW _ hDir
          | k + 1, p'', hRec, ih =>
              simp only [Walk.IsBifurcationWithSplit] at hRec
              simp only [walk_ofDoit, walkStep_ofDoit,
                Walk.IsBifurcationWithSplit]
              exact ih k hRec
      | bidir h_L =>
          match i, p', hSpl with
          | 0, .nil _ _, _ =>
              simp only [walk_ofDoit, walkStep_ofDoit,
                Walk.IsBifurcationWithSplit]
          | 0, .cons vI sI pI, hDir =>
              simp only [Walk.IsBifurcationWithSplit] at hDir
              simp only [walk_ofDoit, walkStep_ofDoit,
                Walk.IsBifurcationWithSplit]
              exact walk_ofDoit_isDirectedWalk hW _ hDir
          | _ + 1, _, hSpl =>
              simp only [Walk.IsBifurcationWithSplit] at hSpl

private lemma walk_ofDoit_isBifurcation {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) {u v : Node}
    (p : Walk (G.hardInterventionOn W hW) u v)
    (hp : p.IsBifurcation) : (walk_ofDoit hW p).IsBifurcation := by
  obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hp
  refine ⟨hne, ?_, ?_, i, walk_ofDoit_isBifurcationWithSplit hW p i hi⟩
  · rw [walk_ofDoit_vertices hW p]; exact hu_tail
  · rw [walk_ofDoit_vertices hW p]; exact hv_drop

-- WalkStep G → G_{doit}, both-endpoints constraint.  Case-split on
-- `s : WalkStep`; the `.bidir` branch is the Sym2 dance: the
-- L-filter predicate is `fun s => ∀ v ∈ s, v ∉ W`, discharged via
-- `Sym2.mem_iff.mp` → `rcases ... with rfl | rfl` on the two
-- endpoints.  Pattern-match `def` (not tactic-mode) so consumers can
-- unfold it via `simp only [walkStep_toDoit]` to see the
-- transparent constructor `.forwardE / .backwardE / .bidir`.
private def walkStep_toDoit {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {u v : Node} :
    WalkStep G u v → u ∉ W → v ∉ W →
      WalkStep (G.hardInterventionOn W hW) u v
  | .forwardE h_E, _, hv =>
      .forwardE (Finset.mem_filter.mpr ⟨h_E, hv⟩)
  | .backwardE h_E, hu, _ =>
      .backwardE (Finset.mem_filter.mpr ⟨h_E, hu⟩)
  | .bidir h_L, hu, hv =>
      .bidir (Finset.mem_filter.mpr ⟨h_L, fun w hw => by
        rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact hu
        · exact hv⟩)

-- WalkStep G → G_{doit}, directed (forward-E) case: only head matters.
private def walkStep_toDoit_dir {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {u v : Node}
    (h_E : (u, v) ∈ G.E) (hv : v ∉ W) :
    WalkStep (G.hardInterventionOn W hW) u v :=
  .forwardE (Finset.mem_filter.mpr ⟨h_E, hv⟩)

/-- Lift a directed walk in `G` to a directed walk in
`G.hardInterventionOn W hW`, preserving length and vertices. -/
private lemma lift_dir_walk_to_doit {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {a b : Node} (r : Walk G a b),
      r.IsDirectedWalk →
      (∀ x ∈ r.vertices.tail, x ∉ W) →
      ∃ s : Walk (G.hardInterventionOn W hW) a b,
        s.IsDirectedWalk ∧ s.length = r.length ∧
        s.vertices = r.vertices := by
  intro a b r
  induction r with
  | nil v hv =>
      intro _ _
      refine ⟨Walk.nil v (mem_doit_of_mem_G (hW := hW) hv),
              trivial, rfl, rfl⟩
  | @cons u' w' vMid s p' ih =>
      intro hr_dir hNotW
      cases s with
      | backwardE _ => exact hr_dir.elim
      | bidir _ => exact hr_dir.elim
      | forwardE h_E =>
          have hp'_dir : p'.IsDirectedWalk := hr_dir
          have hvMid_notW : vMid ∉ W :=
            hNotW vMid (Walk.head_mem_vertices p')
          have h_inner : ∀ x ∈ p'.vertices.tail, x ∉ W := fun x hx =>
            hNotW x (List.mem_of_mem_tail hx)
          obtain ⟨s', hs'_dir, hs'_len, hs'_vs⟩ := ih hp'_dir h_inner
          refine ⟨Walk.cons vMid
            (walkStep_toDoit_dir (hW := hW) h_E hvMid_notW) s', ?_, ?_, ?_⟩
          · show s'.IsDirectedWalk
            exact hs'_dir
          · show s'.length + 1 = p'.length + 1
            rw [hs'_len]
          · show u' :: s'.vertices = u' :: p'.vertices
            rw [hs'_vs]

/-- Lift `IsBifurcationWithSplit` through the doit-cast.  The
inner case-split shrinks from the original's 3-clause `match i, p', hSpl`
to a nested `match` whose inner cases case-split on `s : WalkStep`.
Each branch uses `simp only [IsBifurcationWithSplit]` to
unfold the predicate definition where the kernel doesn't reduce
automatically through equation-compiled defs. -/
private lemma lift_bifWithSplit_to_doit_aux {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    ∀ {a b : Node} (r : Walk G a b) (i : ℕ),
      (∀ x ∈ r.vertices, x ∉ W) →
      r.IsBifurcationWithSplit i →
      ∃ s : Walk (G.hardInterventionOn W hW) a b,
        s.IsBifurcationWithSplit i ∧ s.vertices = r.vertices := by
  intro a b r
  induction r with
  | nil _ _ =>
      intro i _ h
      simp only [Walk.IsBifurcationWithSplit] at h
  | @cons u' w' vMid s p' ih =>
      intro i hNotW hSpl
      have hu'_notW : u' ∉ W := hNotW u' List.mem_cons_self
      have hvMid_notW : vMid ∉ W :=
        hNotW vMid (List.mem_cons_of_mem _ (Walk.head_mem_vertices p'))
      have h_inner_all : ∀ x ∈ p'.vertices, x ∉ W := fun x hx =>
        hNotW x (List.mem_cons_of_mem _ hx)
      match i, p', s, hSpl with
      | 0, .nil v hv, .bidir h_L, _ =>
          have hv_notW : v ∉ W :=
            hNotW v (List.mem_cons_of_mem _ List.mem_cons_self)
          refine ⟨Walk.cons v
            (walkStep_toDoit (hW := hW) (.bidir h_L) hu'_notW hvMid_notW)
            (Walk.nil v (mem_doit_of_mem_G (hW := hW) hv)),
            ?_, rfl⟩
          -- Goal: (cons _ (walkStep_toDoit ...) (nil v _)).IsBifurcationWithSplit 0
          -- After unfolding walkStep_toDoit, the outer step is `.bidir _`,
          -- and the pattern (cons _ (.bidir _) (.nil _ _)) 0 reduces to True.
          show True
          trivial
      | 0, .nil _ _, .forwardE _, hSpl =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
      | 0, .nil _ _, .backwardE _, hSpl =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
      | 0, .cons vMidInner sInner pInner, .backwardE h_E, hDir =>
          simp only [Walk.IsBifurcationWithSplit] at hDir
          -- `hDir : (.cons vMidInner sInner pInner).IsDirectedWalk`
          -- — case-split on `sInner`; only `.forwardE` survives.
          cases sInner with
          | backwardE _ => exact (hDir : False).elim
          | bidir _ => exact (hDir : False).elim
          | forwardE h_EInner =>
              have hpInner_dir : pInner.IsDirectedWalk := hDir
              have hvMidInner_notW : vMidInner ∉ W :=
                h_inner_all vMidInner
                  (List.mem_cons_of_mem _ (Walk.head_mem_vertices pInner))
              have h_innerInner : ∀ x ∈ pInner.vertices.tail, x ∉ W := fun x hx =>
                h_inner_all x (List.mem_cons_of_mem _ (List.mem_of_mem_tail hx))
              obtain ⟨s'', hs''_dir, _, hs''_vs⟩ :=
                lift_dir_walk_to_doit hW pInner hpInner_dir h_innerInner
              refine ⟨Walk.cons vMid
                (walkStep_toDoit (hW := hW) (.backwardE h_E) hu'_notW hvMid_notW)
                (Walk.cons vMidInner
                  (walkStep_toDoit_dir (hW := hW) h_EInner hvMidInner_notW)
                  s''), ?_, ?_⟩
              · simp only [walkStep_toDoit, walkStep_toDoit_dir,
                  Walk.IsBifurcationWithSplit,
                  Walk.IsDirectedWalk]
                exact hs''_dir
              · simp only [Walk.vertices]
                rw [hs''_vs]
      | 0, .cons vMidInner sInner pInner, .bidir h_L, hDir =>
          simp only [Walk.IsBifurcationWithSplit] at hDir
          cases sInner with
          | backwardE _ => exact (hDir : False).elim
          | bidir _ => exact (hDir : False).elim
          | forwardE h_EInner =>
              have hpInner_dir : pInner.IsDirectedWalk := hDir
              have hvMidInner_notW : vMidInner ∉ W :=
                h_inner_all vMidInner
                  (List.mem_cons_of_mem _ (Walk.head_mem_vertices pInner))
              have h_innerInner : ∀ x ∈ pInner.vertices.tail, x ∉ W := fun x hx =>
                h_inner_all x (List.mem_cons_of_mem _ (List.mem_of_mem_tail hx))
              obtain ⟨s'', hs''_dir, _, hs''_vs⟩ :=
                lift_dir_walk_to_doit hW pInner hpInner_dir h_innerInner
              refine ⟨Walk.cons vMid
                (walkStep_toDoit (hW := hW) (.bidir h_L) hu'_notW hvMid_notW)
                (Walk.cons vMidInner
                  (walkStep_toDoit_dir (hW := hW) h_EInner hvMidInner_notW)
                  s''), ?_, ?_⟩
              · simp only [walkStep_toDoit, walkStep_toDoit_dir,
                  Walk.IsBifurcationWithSplit,
                  Walk.IsDirectedWalk]
                exact hs''_dir
              · simp only [Walk.vertices]
                rw [hs''_vs]
      | 0, .cons _ _ _, .forwardE _, hSpl =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
      | k+1, p'', .backwardE h_E, hRec =>
          simp only [Walk.IsBifurcationWithSplit] at hRec
          obtain ⟨s', hs'_split, hs'_vs⟩ := ih k h_inner_all hRec
          refine ⟨Walk.cons vMid
            (walkStep_toDoit (hW := hW) (.backwardE h_E) hu'_notW hvMid_notW) s',
            ?_, ?_⟩
          · simp only [walkStep_toDoit,
              Walk.IsBifurcationWithSplit]
            exact hs'_split
          · simp only [Walk.vertices]
            rw [hs'_vs]
      | k+1, _, .forwardE _, hSpl =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl
      | k+1, _, .bidir _, hSpl =>
          simp only [Walk.IsBifurcationWithSplit] at hSpl

-- ## Refactor replacements — Phase i.B (Φ iff lemmas).
--
-- These two iff lemmas thread the walk-surgery results above:
-- `doit_marg_PhiE_iff` uses `refactor_walk_ofDoit_*` for
-- the (⇒) descent and `lift_dir_walk_to_doit` for the
-- (⇐) ascent; `doit_marg_PhiL_iff` uses
-- `walk_ofDoit_isBifurcation` and
-- `lift_bifWithSplit_to_doit_aux`.  Body identical to the
-- original modulo upstream-name retargets.

private lemma doit_marg_PhiE_iff {G : CDMG Node}
    (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂)
    {u v : Node} (hv_notW₁ : v ∉ W₁) :
    (G.hardInterventionOn W₁ hW₁).MarginalizationΦE W₂ u v ↔
      G.MarginalizationΦE W₂ u v := by
  constructor
  · rintro ⟨p, hp_dir, hp_pos, hp_inter⟩
    refine ⟨walk_ofDoit hW₁ p,
      walk_ofDoit_isDirectedWalk hW₁ p hp_dir, ?_, ?_⟩
    · rw [walk_ofDoit_length hW₁ p]; exact hp_pos
    · rw [walk_ofDoit_vertices hW₁ p]; exact hp_inter
  · rintro ⟨q, hq_dir, hq_pos, hq_inter⟩
    have hNotW : ∀ x ∈ q.vertices.tail, x ∉ W₁ := by
      intro x hx
      have h_tail_ne : q.vertices.tail ≠ [] :=
        Walk.tail_vertices_ne_nil_of_pos q hq_pos
      have h_x_drop_or_last : x ∈ q.vertices.tail.dropLast ∨ x = v := by
        rw [← List.dropLast_append_getLast h_tail_ne] at hx
        rcases List.mem_append.mp hx with h_drop | h_last
        · exact Or.inl h_drop
        · refine Or.inr ?_
          rw [List.mem_singleton] at h_last
          rw [h_last, Walk.tail_getLast_of_pos q hq_pos]
      rcases h_x_drop_or_last with h_drop | h_last
      · exact Finset.disjoint_right.mp hDisj (hq_inter x h_drop)
      · rw [h_last]; exact hv_notW₁
    obtain ⟨s, hs_dir, hs_len, hs_vs⟩ :=
      lift_dir_walk_to_doit hW₁ q hq_dir hNotW
    refine ⟨s, hs_dir, ?_, ?_⟩
    · rw [hs_len]; exact hq_pos
    · rw [hs_vs]; exact hq_inter

private lemma doit_marg_PhiL_iff {G : CDMG Node}
    (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂)
    {u v : Node} (hu_notW₁ : u ∉ W₁) (hv_notW₁ : v ∉ W₁) :
    (G.hardInterventionOn W₁ hW₁).MarginalizationΦL W₂ u v ↔
      G.MarginalizationΦL W₂ u v := by
  constructor
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · refine Or.inl ⟨walk_ofDoit hW₁ p,
        walk_ofDoit_isBifurcation hW₁ p hp_bif, ?_⟩
      rw [walk_ofDoit_vertices hW₁ p]; exact hp_inter
    · refine Or.inr ⟨walk_ofDoit hW₁ p,
        walk_ofDoit_isBifurcation hW₁ p hp_bif, ?_⟩
      rw [walk_ofDoit_vertices hW₁ p]; exact hp_inter
  · rintro (⟨q, hq_bif, hq_inter⟩ | ⟨q, hq_bif, hq_inter⟩)
    · have hNotW : ∀ x ∈ q.vertices, x ∉ W₁ := by
        intro x hx
        rw [Walk.vertices_eq_head_cons_tail q] at hx
        rcases List.mem_cons.mp hx with h_eq_u | h_in_tail
        · rw [h_eq_u]; exact hu_notW₁
        · have h_pos : q.length ≥ 1 :=
            Walk.length_pos_of_isBifurcation hq_bif
          have h_tail_ne : q.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos q h_pos
          have h_x_drop_or_last : x ∈ q.vertices.tail.dropLast ∨ x = v := by
            rw [← List.dropLast_append_getLast h_tail_ne] at h_in_tail
            rcases List.mem_append.mp h_in_tail with h_drop | h_last
            · exact Or.inl h_drop
            · refine Or.inr ?_
              rw [List.mem_singleton] at h_last
              rw [h_last, Walk.tail_getLast_of_pos q h_pos]
          rcases h_x_drop_or_last with h_drop | h_last
          · exact Finset.disjoint_right.mp hDisj (hq_inter x h_drop)
          · rw [h_last]; exact hv_notW₁
      obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hq_bif
      obtain ⟨s, hs_split, hs_vs⟩ :=
        lift_bifWithSplit_to_doit_aux hW₁ q i hNotW hi
      refine Or.inl ⟨s, ⟨hne, ?_, ?_, i, hs_split⟩, ?_⟩
      · rw [hs_vs]; exact hu_tail
      · rw [hs_vs]; exact hv_drop
      · rw [hs_vs]; exact hq_inter
    · have hNotW : ∀ x ∈ q.vertices, x ∉ W₁ := by
        intro x hx
        rw [Walk.vertices_eq_head_cons_tail q] at hx
        rcases List.mem_cons.mp hx with h_eq_v | h_in_tail
        · rw [h_eq_v]; exact hv_notW₁
        · have h_pos : q.length ≥ 1 :=
            Walk.length_pos_of_isBifurcation hq_bif
          have h_tail_ne : q.vertices.tail ≠ [] :=
            Walk.tail_vertices_ne_nil_of_pos q h_pos
          have h_x_drop_or_last : x ∈ q.vertices.tail.dropLast ∨ x = u := by
            rw [← List.dropLast_append_getLast h_tail_ne] at h_in_tail
            rcases List.mem_append.mp h_in_tail with h_drop | h_last
            · exact Or.inl h_drop
            · refine Or.inr ?_
              rw [List.mem_singleton] at h_last
              rw [h_last, Walk.tail_getLast_of_pos q h_pos]
          rcases h_x_drop_or_last with h_drop | h_last
          · exact Finset.disjoint_right.mp hDisj (hq_inter x h_drop)
          · rw [h_last]; exact hu_notW₁
      obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hq_bif
      obtain ⟨s, hs_split, hs_vs⟩ :=
        lift_bifWithSplit_to_doit_aux hW₁ q i hNotW hi
      refine Or.inr ⟨s, ⟨hne, ?_, ?_, i, hs_split⟩, ?_⟩
      · rw [hs_vs]; exact hu_tail
      · rw [hs_vs]; exact hv_drop
      · rw [hs_vs]; exact hq_inter

-- ## Refactor replacements — Phase i.C (field equality lemmas).
--
-- Pi16 (`E-field`) is structural-light: the E-side carrier shape is
-- unchanged (still `Finset (Node × Node)`), only the upstream-name
-- retargets propagate.  Pi17 (`L-field`) is the Sym2-image dance:
-- both sides are `Finset (Sym2 Node)`, but the LHS is
-- `(filter_LHS).image Sym2.mk` while the RHS is
-- `((filter_RHS).image Sym2.mk).filter ball_pred`.  The proof goes via
-- `Finset.ext` on `s : Sym2 Node`, peels the image layer via
-- `Sym2.ind`, and reduces to an ordered-pair filter equivalence.

private lemma doit_marg_E_field_eq {G : CDMG Node}
    (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    ((G.hardInterventionOn W₁ hW₁).marginalize W₂
        (subset_sdiff_of_disjoint hW₂ hDisj.symm)).E
      = ((G.marginalize W₂ hW₂).hardInterventionOn W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)).E := by
  apply Finset.ext
  intro e
  change
    e ∈ (((G.J ∪ W₁) ∪ ((G.V \ W₁) \ W₂)) ×ˢ ((G.V \ W₁) \ W₂)).filter
          (fun e => (G.hardInterventionOn W₁ hW₁).MarginalizationΦE W₂ e.1 e.2)
    ↔ e ∈ (((G.J ∪ (G.V \ W₂)) ×ˢ (G.V \ W₂)).filter
              (fun e => G.MarginalizationΦE W₂ e.1 e.2)).filter
            (fun e => e.2 ∉ W₁)
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_product, Finset.mem_product]
  constructor
  · rintro ⟨⟨hu, hv⟩, hPhi⟩
    have hv_W₂_notW₁ : e.2 ∈ G.V ∧ e.2 ∉ W₁ ∧ e.2 ∉ W₂ := by
      have h1 := Finset.mem_sdiff.mp hv
      have h2 := Finset.mem_sdiff.mp h1.1
      exact ⟨h2.1, h2.2, h1.2⟩
    have hv_RHS : e.2 ∈ G.V \ W₂ :=
      Finset.mem_sdiff.mpr ⟨hv_W₂_notW₁.1, hv_W₂_notW₁.2.2⟩
    have hu_RHS : e.1 ∈ G.J ∪ (G.V \ W₂) := by
      rcases Finset.mem_union.mp hu with hJW₁ | hVW
      · rcases Finset.mem_union.mp hJW₁ with hJ | hW₁'
        · exact Finset.mem_union_left _ hJ
        · rcases Finset.mem_union.mp (hW₁ hW₁') with hJ | hV
          · exact Finset.mem_union_left _ hJ
          · refine Finset.mem_union_right _ ?_
            refine Finset.mem_sdiff.mpr ⟨hV, ?_⟩
            exact Finset.disjoint_left.mp hDisj hW₁'
      · have h1 := Finset.mem_sdiff.mp hVW
        have h2 := Finset.mem_sdiff.mp h1.1
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h2.1, h1.2⟩)
    refine ⟨⟨⟨hu_RHS, hv_RHS⟩,
        (doit_marg_PhiE_iff W₁ W₂ hW₁ hW₂ hDisj hv_W₂_notW₁.2.1).mp hPhi⟩,
      hv_W₂_notW₁.2.1⟩
  · rintro ⟨⟨⟨hu, hv⟩, hPhi⟩, hv_notW₁⟩
    have hv_LHS : e.2 ∈ (G.V \ W₁) \ W₂ := by
      have h1 := Finset.mem_sdiff.mp hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨h1.1, hv_notW₁⟩, h1.2⟩
    have hu_LHS : e.1 ∈ (G.J ∪ W₁) ∪ ((G.V \ W₁) \ W₂) := by
      rcases Finset.mem_union.mp hu with hJ | hVW
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
      · have h1 := Finset.mem_sdiff.mp hVW
        by_cases hW₁' : e.1 ∈ W₁
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hW₁')
        · refine Finset.mem_union_right _ ?_
          refine Finset.mem_sdiff.mpr ⟨?_, h1.2⟩
          exact Finset.mem_sdiff.mpr ⟨h1.1, hW₁'⟩
    refine ⟨⟨hu_LHS, hv_LHS⟩,
      (doit_marg_PhiE_iff W₁ W₂ hW₁ hW₂ hDisj hv_notW₁).mpr hPhi⟩

set_option maxHeartbeats 2400000 in
set_option linter.style.longLine false in
private lemma doit_marg_L_field_eq {G : CDMG Node}
    (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    ((G.hardInterventionOn W₁ hW₁).marginalize W₂
        (subset_sdiff_of_disjoint hW₂ hDisj.symm)).L
      = ((G.marginalize W₂ hW₂).hardInterventionOn W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)).L := by
  -- LHS = (innerL_LHS).image Sym2.mk
  --   where innerL_LHS = (((G.V\W₁)\W₂) ×ˢ ((G.V\W₁)\W₂)).filter
  --           (fun e => e.1 ≠ e.2 ∧ Φ_L_doit W₂ e.1 e.2)
  -- RHS = ((innerL_RHS).image Sym2.mk).filter (ball_pred W₁)
  --   where innerL_RHS = ((G.V\W₂) ×ˢ (G.V\W₂)).filter
  --           (fun e => e.1 ≠ e.2 ∧ G.Φ_L W₂ e.1 e.2)
  -- Strategy: ext on s : Sym2 Node, induct via Sym2.ind to reduce to (u,v),
  -- then prove the iff between LHS membership and RHS membership.
  change ((((G.V \ W₁) \ W₂) ×ˢ ((G.V \ W₁) \ W₂)).filter
            (fun e => e.1 ≠ e.2 ∧
              (G.hardInterventionOn W₁ hW₁).MarginalizationΦL W₂ e.1 e.2)).image
              (fun e => s(e.1, e.2))
        = ((((G.V \ W₂) ×ˢ (G.V \ W₂)).filter
              (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W₂ e.1 e.2)).image
                (fun e => s(e.1, e.2))).filter
            (fun s => ∀ v ∈ s, v ∉ W₁)
  apply Finset.ext
  refine Sym2.ind (fun u v => ?_)
  constructor
  · intro hLHS
    rw [Finset.mem_image] at hLHS
    obtain ⟨e, he_filter, he_eq⟩ := hLHS
    rw [Finset.mem_filter, Finset.mem_product] at he_filter
    obtain ⟨⟨hu_, hv_⟩, hNe, hPhi⟩ := he_filter
    have hu_W₂_notW₁ : e.1 ∈ G.V ∧ e.1 ∉ W₁ ∧ e.1 ∉ W₂ := by
      have h1 := Finset.mem_sdiff.mp hu_
      have h2 := Finset.mem_sdiff.mp h1.1
      exact ⟨h2.1, h2.2, h1.2⟩
    have hv_W₂_notW₁ : e.2 ∈ G.V ∧ e.2 ∉ W₁ ∧ e.2 ∉ W₂ := by
      have h1 := Finset.mem_sdiff.mp hv_
      have h2 := Finset.mem_sdiff.mp h1.1
      exact ⟨h2.1, h2.2, h1.2⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨e, ?_, he_eq⟩
      refine Finset.mem_filter.mpr ⟨?_, hNe, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hu_W₂_notW₁.1, hu_W₂_notW₁.2.2⟩,
           Finset.mem_sdiff.mpr ⟨hv_W₂_notW₁.1, hv_W₂_notW₁.2.2⟩⟩
      · exact (doit_marg_PhiL_iff W₁ W₂ hW₁ hW₂ hDisj
          hu_W₂_notW₁.2.1 hv_W₂_notW₁.2.1).mp hPhi
    · -- ball_pred (s(u, v)): need u ∉ W₁ ∧ v ∉ W₁.
      -- s = s(u, v) = s(e.1, e.2), so the pair (u, v) is the same
      -- unordered pair as (e.1, e.2).  Use Sym2.eq_iff (or Sym2.mk_eq).
      intro w hw
      have h_sym : s(u, v) = s(e.1, e.2) := he_eq.symm
      have hw' : w ∈ s(e.1, e.2) := h_sym ▸ hw
      rcases Sym2.mem_iff.mp hw' with rfl | rfl
      · exact hu_W₂_notW₁.2.1
      · exact hv_W₂_notW₁.2.1
  · intro hRHS
    rw [Finset.mem_filter] at hRHS
    obtain ⟨h_inImg, h_ball⟩ := hRHS
    rw [Finset.mem_image] at h_inImg
    obtain ⟨e, he_filter, he_eq⟩ := h_inImg
    rw [Finset.mem_filter, Finset.mem_product] at he_filter
    obtain ⟨⟨hu_, hv_⟩, hNe, hPhi⟩ := he_filter
    -- ball gives: e.1 ∉ W₁ ∧ e.2 ∉ W₁ (after Sym2.mk).
    have he1_notW₁ : e.1 ∉ W₁ := by
      have h1 : e.1 ∈ s(e.1, e.2) := Sym2.mem_mk_left _ _
      rw [he_eq] at h1
      exact h_ball _ h1
    have he2_notW₁ : e.2 ∉ W₁ := by
      have h2 : e.2 ∈ s(e.1, e.2) := Sym2.mem_mk_right _ _
      rw [he_eq] at h2
      exact h_ball _ h2
    refine Finset.mem_image.mpr ⟨e, ?_, he_eq⟩
    refine Finset.mem_filter.mpr ⟨?_, hNe, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · have h1 := Finset.mem_sdiff.mp hu_
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨h1.1, he1_notW₁⟩, h1.2⟩
      · have h1 := Finset.mem_sdiff.mp hv_
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨h1.1, he2_notW₁⟩, h1.2⟩
    · exact (doit_marg_PhiL_iff W₁ W₂ hW₁ hW₂ hDisj
        he1_notW₁ he2_notW₁).mpr hPhi

-- ## Refactor replacements — Phase i.D (main theorem, Part i).
--
-- Two structural shifts from the original:
--   1. `CDMG` → `CDMG`: the structure drops from 9 fields to
--      8 (no `hL_symm`).  The local `cdmgExt` `have`-lemma's `rintro`
--      destructure shrinks to 8 anonymous slots.
--   2. `hardInterventionOn`, `marginalize` retarget to their
--      `refactor_*` twins; `subset_sdiff_of_disjoint`,
--      `subset_carrier_of_marginalize` likewise; the E/L field
--      equalities call the Phase i.C twins.
-- ref: claim_3_18 (part i / 3 — hard intervention) — refactor
-- claim_3_18 -- start statement
theorem marginalize_hardInterventionOn_comm (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (G.hardInterventionOn W₁ hW₁).marginalize W₂
        (subset_sdiff_of_disjoint hW₂ hDisj.symm)
      = (G.marginalize W₂ hW₂).hardInterventionOn W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)
-- claim_3_18 -- end statement
:= by
  have cdmgExt : ∀ {G₁ G₂ : CDMG Node},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨_, _, _, _, _, _, _, _⟩
           ⟨_, _, _, _, _, _, _, _⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL; rfl
  refine cdmgExt ?_ ?_ ?_ ?_
  · -- J: both sides = G.J ∪ W₁
    rfl
  · -- V: (G.V \ W₁) \ W₂ = (G.V \ W₂) \ W₁
    change (G.V \ W₁) \ W₂ = (G.V \ W₂) \ W₁
    ext x
    simp only [Finset.mem_sdiff]
    tauto
  · -- E: filter equality via Φ_E iff
    exact doit_marg_E_field_eq W₁ W₂ hW₁ hW₂ hDisj
  · -- L: filter equality via Φ_L iff
    exact doit_marg_L_field_eq W₁ W₂ hW₁ hW₂ hDisj

-- ## Refactor replacements — Phase ii.A (walk ascent G → ext).
--
-- Body shifts mirror the Phase i.A pattern, now over
-- `extendingCDMGsWith`:
--   1. `Walk.cons _ a hStep p` (4-arg) collapses to `Walk.cons _ s p`
--      (3-arg, typed step).
--   2. WalkStep ascent case-splits on `s : WalkStep`; the
--      `.bidir` branch is the **Sym2 reshape**: the LN-side L-edge
--      `s(u,v) ∈ G.L` lifts via `Sym2.map IntExtNode.unsplit` (the
--      `extendingCDMGsWith.L`-field shape).  Since `Sym2.map f s(a,b) =
--      s(f a, f b)` holds definitionally on the `Sym2.mk` quotient, the
--      witness reduces to `rfl` after `Finset.mem_image.mpr`.
--   3. The 10-branch `IsBifurcationWithSplit` pattern-match
--      replaces the original's 4-clause `match i, p', hSpl`; only the
--      `.bidir _, (.nil _ _), 0`, `.backwardE _, .cons, 0`,
--      `.bidir _, .cons, 0`, and `.backwardE _, _, k+1` cases carry
--      content — the rest are vacuous (`hSpl.elim` / pattern-False).

private lemma mem_ext_of_mem_G_unsplit {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) {v : Node} (hv : v ∈ G) :
    IntExtNode.unsplit v ∈ extendingCDMGsWith G W hW := by
  change _ ∈ ((G.J.image IntExtNode.unsplit ∪
      (W \ G.J).image IntExtNode.intCopy) ∪ G.V.image IntExtNode.unsplit)
  change v ∈ G.J ∪ G.V at hv
  rcases Finset.mem_union.mp hv with hJ | hV
  · refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, hJ, rfl⟩
  · refine Finset.mem_union_right _ ?_
    exact Finset.mem_image.mpr ⟨v, hV, rfl⟩

-- WalkStep G → ext: case-split on `s : WalkStep`.  The
-- `.bidir` branch reshapes the L-membership: under the refactor,
-- `extendingCDMGsWith.L = G.L.image (Sym2.map IntExtNode.unsplit)`,
-- so we lift `s(u,v) ∈ G.L` via `Finset.mem_image.mpr ⟨s(u,v), h, rfl⟩`
-- (the `Sym2.map f s(a,b) = s(f a, f b)` reduction is definitional).
private def walkStep_toExt {G : CDMG Node} {W : Finset Node}
    {hW : W ⊆ G.J ∪ G.V} {u v : Node} :
    WalkStep G u v →
      WalkStep (extendingCDMGsWith G W hW)
        (IntExtNode.unsplit u) (IntExtNode.unsplit v)
  | .forwardE h => .forwardE (by
      change _ ∈ G.E.image _ ∪ _
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr ⟨(u, v), h, rfl⟩)
  | .backwardE h => .backwardE (by
      change _ ∈ G.E.image _ ∪ _
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr ⟨(v, u), h, rfl⟩)
  | .bidir h => .bidir (by
      change _ ∈ G.L.image (Sym2.map IntExtNode.unsplit)
      exact Finset.mem_image.mpr ⟨s(u, v), h, rfl⟩)

/-- Lift a walk in `G` to a walk in `G.extendingCDMGsWith W hW`
via `.unsplit`. -/
private def walk_toExt {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node}, Walk G u v →
      Walk (extendingCDMGsWith G W hW)
        (IntExtNode.unsplit u) (IntExtNode.unsplit v)
  | _, _, .nil v hv =>
      Walk.nil (IntExtNode.unsplit v)
        (mem_ext_of_mem_G_unsplit hW hv)
  | _, _, .cons v s p =>
      Walk.cons (IntExtNode.unsplit v)
        (walkStep_toExt (hW := hW) s) (walk_toExt hW p)

private lemma walk_toExt_length {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk G u v),
      (walk_toExt hW p).length = p.length
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p => by
      change (walk_toExt hW p).length + 1 = p.length + 1
      rw [walk_toExt_length hW p]

private lemma walk_toExt_vertices {G : CDMG Node} {W : Finset Node}
    (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk G u v),
      (walk_toExt hW p).vertices
        = p.vertices.map IntExtNode.unsplit
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ p => by
      change _ :: (walk_toExt hW p).vertices = _ :: _
      rw [walk_toExt_vertices hW p]

private lemma walk_toExt_isDirectedWalk {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → (walk_toExt hW p).IsDirectedWalk
  | _, _, .nil _ _, _ => trivial
  | _, _, .cons _ (.forwardE _) p, hDir =>
      walk_toExt_isDirectedWalk hW p hDir
  | _, _, .cons _ (.backwardE _) _, hDir => hDir.elim
  | _, _, .cons _ (.bidir _) _, hDir => hDir.elim

private lemma walk_toExt_isBifurcationWithSplit {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    ∀ {u v : Node} (p : Walk G u v) (i : ℕ),
      p.IsBifurcationWithSplit i →
        (walk_toExt hW p).IsBifurcationWithSplit i := by
  intro u v p
  induction p with
  | nil _ _ =>
      intro i hSpl
      simp only [Walk.IsBifurcationWithSplit] at hSpl
  | @cons u' w' vMid s p' ih =>
      intro i hSpl
      cases s with
      | forwardE h_E =>
          match i, p', hSpl with
          | 0, .nil _ _, hSpl =>
              simp only [Walk.IsBifurcationWithSplit] at hSpl
          | 0, .cons _ _ _, hSpl =>
              simp only [Walk.IsBifurcationWithSplit] at hSpl
          | _ + 1, _, hSpl =>
              simp only [Walk.IsBifurcationWithSplit] at hSpl
      | backwardE h_E =>
          match i, p', hSpl, ih with
          | 0, .nil _ _, hSpl, _ =>
              simp only [Walk.IsBifurcationWithSplit] at hSpl
          | 0, .cons vI sI pI, hDir, _ =>
              simp only [Walk.IsBifurcationWithSplit] at hDir
              simp only [walk_toExt, walkStep_toExt,
                Walk.IsBifurcationWithSplit]
              exact walk_toExt_isDirectedWalk hW _ hDir
          | k + 1, p'', hRec, ih =>
              simp only [Walk.IsBifurcationWithSplit] at hRec
              simp only [walk_toExt, walkStep_toExt,
                Walk.IsBifurcationWithSplit]
              exact ih k hRec
      | bidir h_L =>
          match i, p', hSpl with
          | 0, .nil _ _, _ =>
              simp only [walk_toExt, walkStep_toExt,
                Walk.IsBifurcationWithSplit]
          | 0, .cons vI sI pI, hDir =>
              simp only [Walk.IsBifurcationWithSplit] at hDir
              simp only [walk_toExt, walkStep_toExt,
                Walk.IsBifurcationWithSplit]
              exact walk_toExt_isDirectedWalk hW _ hDir
          | _ + 1, _, hSpl =>
              simp only [Walk.IsBifurcationWithSplit] at hSpl

private lemma walk_toExt_isBifurcation {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) {u v : Node}
    (p : Walk G u v) (hp : p.IsBifurcation) :
    (walk_toExt hW p).IsBifurcation := by
  obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hp
  refine ⟨?_, ?_, ?_, i, walk_toExt_isBifurcationWithSplit hW p i hi⟩
  · intro heq
    apply hne
    have : IntExtNode.unsplit u = IntExtNode.unsplit v := heq
    injection this
  · rw [walk_toExt_vertices hW p]
    intro h
    rw [show (p.vertices.map IntExtNode.unsplit).tail
            = p.vertices.tail.map IntExtNode.unsplit from
        by cases p.vertices with
        | nil => rfl
        | cons _ _ => rfl] at h
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h
    have : a = u := by injection ha_eq
    exact hu_tail (this ▸ ha_in)
  · rw [walk_toExt_vertices hW p]
    intro h
    have hMap : ∀ (l : List Node),
        (l.map IntExtNode.unsplit).dropLast = l.dropLast.map IntExtNode.unsplit := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
          cases xs with
          | nil => rfl
          | cons y ys =>
              simp only [List.map_cons, List.dropLast_cons₂]
              change _ :: ((y :: ys).map _).dropLast
                = _ :: ((y :: ys).dropLast).map IntExtNode.unsplit
              rw [ih]
    rw [hMap p.vertices] at h
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h
    have : a = v := by injection ha_eq
    exact hv_drop (this ▸ ha_in)

-- ## Refactor replacements — Phase ii.B (walk descent ext → G + list/edge helpers).
--
-- The descent goes through `walkStep_ofExt_unsplit` (Pii9),
-- which is now a pattern-matching `def` so that its result reduces
-- structurally to `.forwardE / .backwardE / .bidir` based on the
-- input's tag.  The `.bidir` branch is the **Sym2 reshape**:
-- `s' ∈ G.L` is recovered from `Sym2.map .unsplit s' = s(.unsplit u, .unsplit v)`
-- via `Sym2.ind` + `Sym2.eq_iff` + `Sym2.eq_swap` (the two `(a, b) = (u, v)`
-- vs `(a, b) = (v, u)` orientations are handled symmetrically).

-- Walk-step descent ext → G with both endpoints `.unsplit`-tagged.
-- Pattern-matching `def` so consumers can recover the constructor
-- tag of the result by reducing under `simp [walkStep_ofExt_unsplit]`.
private def walkStep_ofExt_unsplit {G : CDMG Node}
    {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} {u v : Node} :
    WalkStep (extendingCDMGsWith G W hW)
      (IntExtNode.unsplit u) (IntExtNode.unsplit v) →
    WalkStep G u v
  | .forwardE h_E => .forwardE (by
      change (IntExtNode.unsplit u, IntExtNode.unsplit v) ∈
          G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) ∪
            (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w)) at h_E
      rcases Finset.mem_union.mp h_E with hLift | hFresh
      · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
        have h1 : a'.1 = u := by injection congrArg Prod.fst ha'_eq
        have h2 : a'.2 = v := by injection congrArg Prod.snd ha'_eq
        have h_pair : a' = (u, v) := Prod.ext h1 h2
        rw [← h_pair]; exact ha'_in
      · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hFresh
        have : IntExtNode.intCopy w = IntExtNode.unsplit u := congrArg Prod.fst hw_eq
        cases this)
  | .backwardE h_E => .backwardE (by
      change (IntExtNode.unsplit v, IntExtNode.unsplit u) ∈
          G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) ∪
            (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w)) at h_E
      rcases Finset.mem_union.mp h_E with hLift | hFresh
      · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
        have h1 : a'.1 = v := by injection congrArg Prod.fst ha'_eq
        have h2 : a'.2 = u := by injection congrArg Prod.snd ha'_eq
        have h_pair : a' = (v, u) := Prod.ext h1 h2
        rw [← h_pair]; exact ha'_in
      · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hFresh
        have : IntExtNode.intCopy w = IntExtNode.unsplit v := congrArg Prod.fst hw_eq
        cases this)
  | .bidir h_L => .bidir (by
      change s(IntExtNode.unsplit u, IntExtNode.unsplit v) ∈
          G.L.image (Sym2.map IntExtNode.unsplit) at h_L
      obtain ⟨s', hs'_in, hs'_eq⟩ := Finset.mem_image.mp h_L
      induction s' using Sym2.ind with
      | _ b c =>
          change s(IntExtNode.unsplit b, IntExtNode.unsplit c) =
                 s(IntExtNode.unsplit u, IntExtNode.unsplit v) at hs'_eq
          rcases Sym2.eq_iff.mp hs'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hb : b = u := by injection h1
            have hc : c = v := by injection h2
            rw [hb, hc] at hs'_in
            exact hs'_in
          · have hb : b = v := by injection h1
            have hc : c = u := by injection h2
            rw [hb, hc] at hs'_in
            rwa [Sym2.eq_swap])

private lemma image_unsplit_sdiff {S T : Finset Node} :
    S.image IntExtNode.unsplit \ T.image IntExtNode.unsplit
      = (S \ T).image IntExtNode.unsplit := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, hAS, rfl⟩, h_notT⟩
    refine ⟨a, ⟨hAS, ?_⟩, rfl⟩
    intro hAT
    exact h_notT ⟨a, hAT, rfl⟩
  · rintro ⟨a, ⟨hAS, hANotT⟩, rfl⟩
    refine ⟨⟨a, hAS, rfl⟩, ?_⟩
    rintro ⟨b, hBT, hEq⟩
    apply hANotT
    have : b = a := by injection hEq
    exact this ▸ hBT

private lemma mem_G_of_unsplit_mem_ext {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) {v : Node}
    (hv : IntExtNode.unsplit v ∈ extendingCDMGsWith G W hW) : v ∈ G := by
  change v ∈ G.J ∪ G.V
  change IntExtNode.unsplit v ∈
    ((G.J.image IntExtNode.unsplit ∪ (W \ G.J).image IntExtNode.intCopy)
     ∪ G.V.image IntExtNode.unsplit) at hv
  rcases Finset.mem_union.mp hv with hJI | hV
  · rcases Finset.mem_union.mp hJI with hJ | hI
    · obtain ⟨j, hjJ, hjEq⟩ := Finset.mem_image.mp hJ
      have hju : j = v := by injection hjEq
      subst hju
      exact Finset.mem_union_left _ hjJ
    · obtain ⟨_, _, hwEq⟩ := Finset.mem_image.mp hI
      cases hwEq
  · obtain ⟨v', hvV, hvEq⟩ := Finset.mem_image.mp hV
    have hvu : v' = v := by injection hvEq
    subst hvu
    exact Finset.mem_union_right _ hvV

private lemma list_unsplit_tail (l : List Node) :
    (l.map IntExtNode.unsplit).tail = l.tail.map IntExtNode.unsplit := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

private lemma list_unsplit_dropLast :
    ∀ (l : List Node),
      (l.map IntExtNode.unsplit).dropLast = l.dropLast.map IntExtNode.unsplit
  | [] => rfl
  | _ :: [] => rfl
  | x :: y :: rest => by
      change IntExtNode.unsplit x :: (((y :: rest).map IntExtNode.unsplit).dropLast)
          = IntExtNode.unsplit x :: ((y :: rest).dropLast.map IntExtNode.unsplit)
      rw [list_unsplit_dropLast (y :: rest)]

private lemma list_unsplit_tail_dropLast (l : List Node) :
    (l.map IntExtNode.unsplit).tail.dropLast
      = l.tail.dropLast.map IntExtNode.unsplit := by
  rw [list_unsplit_tail, list_unsplit_dropLast]

-- E-field shape is unchanged by the refactor (still `Finset (Node × Node)`),
-- so this helper ports byte-identical modulo `extendingCDMGsWith →
-- extendingCDMGsWith`.
private lemma a_in_G_E_of_lifted_in_ext {G : CDMG Node}
    {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} {a' : Node × Node}
    {a : IntExtNode Node × IntExtNode Node}
    (ha_eq : a = (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2))
    (ha_E : a ∈ (extendingCDMGsWith G W hW).E) : a' ∈ G.E := by
  change a ∈ G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
          ∪ (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w))
          at ha_E
  rcases Finset.mem_union.mp ha_E with hLift | hFresh
  · obtain ⟨e', he'E, he'_eq⟩ := Finset.mem_image.mp hLift
    rw [ha_eq] at he'_eq
    have h1 : IntExtNode.unsplit e'.1 = IntExtNode.unsplit a'.1 :=
      congrArg Prod.fst he'_eq
    have h2 : IntExtNode.unsplit e'.2 = IntExtNode.unsplit a'.2 :=
      congrArg Prod.snd he'_eq
    have he1 : e'.1 = a'.1 := by injection h1
    have he2 : e'.2 = a'.2 := by injection h2
    have heq : e' = a' := Prod.ext he1 he2
    rw [← heq]; exact he'E
  · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hFresh
    rw [ha_eq] at hw_eq
    have hcontra : IntExtNode.intCopy w = IntExtNode.unsplit a'.1 :=
      congrArg Prod.fst hw_eq
    cases hcontra

-- L-field shape changes from `Finset (Node × Node)` to `Finset (Sym2 Node)`.
-- The original ordered-pair API is bridged via `s(a.1, a.2)` notation;
-- the proof uses `Sym2.ind` to destructure the lifted edge into an
-- ordered pair representative, then `Sym2.eq_iff` to align orientations.
private lemma a_in_G_L_of_lifted_in_ext {G : CDMG Node}
    {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} {a' : Node × Node}
    {a : IntExtNode Node × IntExtNode Node}
    (ha_eq : a = (IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2))
    (ha_L : s(a.1, a.2) ∈ (extendingCDMGsWith G W hW).L) :
    s(a'.1, a'.2) ∈ G.L := by
  change s(a.1, a.2) ∈ G.L.image (Sym2.map IntExtNode.unsplit) at ha_L
  obtain ⟨s', hs'_in, hs'_eq⟩ := Finset.mem_image.mp ha_L
  rw [ha_eq] at hs'_eq
  induction s' using Sym2.ind with
  | _ b c =>
      change s(IntExtNode.unsplit b, IntExtNode.unsplit c) =
             s(IntExtNode.unsplit a'.1, IntExtNode.unsplit a'.2) at hs'_eq
      rcases Sym2.eq_iff.mp hs'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hb : b = a'.1 := by injection h1
        have hc : c = a'.2 := by injection h2
        rw [hb, hc] at hs'_in
        exact hs'_in
      · have hb : b = a'.2 := by injection h1
        have hc : c = a'.1 := by injection h2
        rw [hb, hc] at hs'_in
        rwa [Sym2.eq_swap]

private lemma pair_eq_of_unsplit_eq {a : Node × Node} {u v : Node}
    (h : (IntExtNode.unsplit a.1, IntExtNode.unsplit a.2)
        = (IntExtNode.unsplit u, IntExtNode.unsplit v)) :
    a = (u, v) := by
  have h1 : IntExtNode.unsplit a.1 = IntExtNode.unsplit u := congrArg Prod.fst h
  have h2 : IntExtNode.unsplit a.2 = IntExtNode.unsplit v := congrArg Prod.snd h
  have ha1 : a.1 = u := by injection h1
  have ha2 : a.2 = v := by injection h2
  exact Prod.ext ha1 ha2

-- Walk descent ext → G with both endpoints `.unsplit`-tagged.  The
-- original packaged length / vertices / edges / IsDirectedWalk /
-- IsBifurcationWithSplit preservations.  Under refactor, the
-- `Walk` type has no `edges` accessor (typed `WalkStep`
-- carries the edge info structurally), so the `edges` clause is
-- dropped.  Consumers (Pii20, Pii21) only used length / vertices /
-- IsDirectedWalk / IsBifurcationWithSplit, so the API contract is
-- preserved.
set_option maxHeartbeats 400000 in
private lemma walk_ofExt_unsplit_full {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.J ∪ G.V) :
    ∀ {x y : IntExtNode Node}
      (p : Walk (extendingCDMGsWith G W hW) x y),
      (∀ z ∈ p.vertices, ∃ z' : Node, z = IntExtNode.unsplit z') →
      ∀ (u v : Node), x = IntExtNode.unsplit u → y = IntExtNode.unsplit v →
      ∃ q : Walk G u v, q.length = p.length ∧
        q.vertices.map IntExtNode.unsplit = p.vertices ∧
        (p.IsDirectedWalk → q.IsDirectedWalk) ∧
        (∀ i, p.IsBifurcationWithSplit i →
          q.IsBifurcationWithSplit i) := by
  intro x y p
  induction p with
  | nil w hw =>
      intro _ u v hxu hyv
      have hu_eq_v : IntExtNode.unsplit u = (IntExtNode.unsplit v : IntExtNode Node) := by
        rw [← hxu, hyv]
      have huv : u = v := by injection hu_eq_v
      subst huv
      subst hxu
      have hu_in_G : u ∈ G := mem_G_of_unsplit_mem_ext hW hw
      refine ⟨Walk.nil u hu_in_G, rfl, rfl, fun _ => trivial, ?_⟩
      intro i h
      simp only [Walk.IsBifurcationWithSplit] at h
  | @cons x' y' mid sStep p' ih =>
      intro h_all u v hxu hyv
      subst hxu
      have hmid_in : mid ∈ (Walk.cons
              (G := extendingCDMGsWith G W hW)
              mid sStep p').vertices := by
        change mid ∈ (IntExtNode.unsplit u :: p'.vertices)
        exact List.mem_cons_of_mem _ (Walk.head_mem_vertices p')
      obtain ⟨m', hmid_eq⟩ := h_all mid hmid_in
      subst hmid_eq
      have h_all_p' : ∀ z ∈ p'.vertices, ∃ z' : Node, z = IntExtNode.unsplit z' := by
        intro z hz
        exact h_all z (List.mem_cons_of_mem _ hz)
      obtain ⟨q', hq'_len, hq'_vs, hq'_dir, hq'_bif⟩ :=
        ih h_all_p' m' v rfl hyv
      cases sStep with
      | forwardE h_E =>
          have h_E_G : (u, m') ∈ G.E := by
            change (IntExtNode.unsplit u, IntExtNode.unsplit m') ∈
                G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) ∪
                  (W \ G.J).image
                    (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w)) at h_E
            rcases Finset.mem_union.mp h_E with hLift | hFresh
            · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
              have h1 : a'.1 = u := by injection congrArg Prod.fst ha'_eq
              have h2 : a'.2 = m' := by injection congrArg Prod.snd ha'_eq
              have h_pair : a' = (u, m') := Prod.ext h1 h2
              rw [← h_pair]; exact ha'_in
            · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hFresh
              have : IntExtNode.intCopy w = IntExtNode.unsplit u := congrArg Prod.fst hw_eq
              cases this
          refine ⟨Walk.cons m' (.forwardE h_E_G) q', ?_, ?_, ?_, ?_⟩
          · change q'.length + 1 = p'.length + 1
            rw [hq'_len]
          · change IntExtNode.unsplit u :: (q'.vertices.map IntExtNode.unsplit)
                  = IntExtNode.unsplit u :: p'.vertices
            rw [hq'_vs]
          · intro hp_dir
            change q'.IsDirectedWalk
            exact hq'_dir hp_dir
          · intro i hPi
            match i, p', hPi with
            | 0, .nil _ _, hPi =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
            | 0, .cons _ _ _, hPi =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
            | _ + 1, _, hPi =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
      | backwardE h_E =>
          have h_E_G : (m', u) ∈ G.E := by
            change (IntExtNode.unsplit m', IntExtNode.unsplit u) ∈
                G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) ∪
                  (W \ G.J).image
                    (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w)) at h_E
            rcases Finset.mem_union.mp h_E with hLift | hFresh
            · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
              have h1 : a'.1 = m' := by injection congrArg Prod.fst ha'_eq
              have h2 : a'.2 = u := by injection congrArg Prod.snd ha'_eq
              have h_pair : a' = (m', u) := Prod.ext h1 h2
              rw [← h_pair]; exact ha'_in
            · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hFresh
              have : IntExtNode.intCopy w = IntExtNode.unsplit m' :=
                congrArg Prod.fst hw_eq
              cases this
          refine ⟨Walk.cons m' (.backwardE h_E_G) q', ?_, ?_, ?_, ?_⟩
          · change q'.length + 1 = p'.length + 1
            rw [hq'_len]
          · change IntExtNode.unsplit u :: (q'.vertices.map IntExtNode.unsplit)
                  = IntExtNode.unsplit u :: p'.vertices
            rw [hq'_vs]
          · intro hp_dir
            exact hp_dir.elim
          · intro i hPi
            match i, p', hPi, q', hq'_len, hq'_dir, hq'_bif with
            | 0, .nil _ _, hPi, _, _, _, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
            | 0, .cons _ _ _, _, .nil _ _, hlen, _, _ =>
                simp [Walk.length] at hlen
            | 0, .cons _ _ _, hDir, .cons _ _ _, _, hq'_dir, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hDir
                simp only [Walk.IsBifurcationWithSplit]
                exact hq'_dir hDir
            | k + 1, _, hRec, _, _, _, hq'_bif =>
                simp only [Walk.IsBifurcationWithSplit] at hRec
                simp only [Walk.IsBifurcationWithSplit]
                exact hq'_bif k hRec
      | bidir h_L =>
          have h_L_G : (s(u, m') : Sym2 Node) ∈ G.L := by
            change s(IntExtNode.unsplit u, IntExtNode.unsplit m') ∈
                G.L.image (Sym2.map IntExtNode.unsplit) at h_L
            obtain ⟨s', hs'_in, hs'_eq⟩ := Finset.mem_image.mp h_L
            induction s' using Sym2.ind with
            | _ b c =>
                change s(IntExtNode.unsplit b, IntExtNode.unsplit c) =
                       s(IntExtNode.unsplit u, IntExtNode.unsplit m') at hs'_eq
                rcases Sym2.eq_iff.mp hs'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · have hb : b = u := by injection h1
                  have hc : c = m' := by injection h2
                  rw [hb, hc] at hs'_in
                  exact hs'_in
                · have hb : b = m' := by injection h1
                  have hc : c = u := by injection h2
                  rw [hb, hc] at hs'_in
                  rwa [Sym2.eq_swap]
          refine ⟨Walk.cons m' (.bidir h_L_G) q', ?_, ?_, ?_, ?_⟩
          · change q'.length + 1 = p'.length + 1
            rw [hq'_len]
          · change IntExtNode.unsplit u :: (q'.vertices.map IntExtNode.unsplit)
                  = IntExtNode.unsplit u :: p'.vertices
            rw [hq'_vs]
          · intro hp_dir
            exact hp_dir.elim
          · intro i hPi
            match i, p', hPi, q', hq'_len, hq'_dir, hq'_bif with
            | 0, .nil _ _, _, .nil _ _, _, _, _ =>
                show True
                trivial
            | 0, .nil _ _, _, .cons _ _ _, hlen, _, _ =>
                simp [Walk.length] at hlen
            | 0, .cons _ _ _, _, .nil _ _, hlen, _, _ =>
                simp [Walk.length] at hlen
            | 0, .cons _ _ _, hDir, .cons _ _ _, _, hq'_dir, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hDir
                simp only [Walk.IsBifurcationWithSplit]
                exact hq'_dir hDir
            | k + 1, _, hPi, _, _, _, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hPi

private lemma all_unsplit_of_interior_W_image
    {G : CDMG Node} {W : Finset Node} {hW : W ⊆ G.J ∪ G.V}
    {x y : IntExtNode Node}
    (p : Walk (extendingCDMGsWith G W hW) x y)
    (hp_pos : p.length ≥ 1)
    {u v : Node} (hxu : x = IntExtNode.unsplit u) (hyv : y = IntExtNode.unsplit v)
    {W₂ : Finset Node}
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast,
                z ∈ W₂.image IntExtNode.unsplit) :
    ∀ z ∈ p.vertices, ∃ z' : Node, z = IntExtNode.unsplit z' := by
  intro z hz
  rw [Walk.vertices_eq_head_cons_tail p] at hz
  rcases List.mem_cons.mp hz with h_eq | h_in_tail
  · exact ⟨u, h_eq.trans hxu⟩
  · have h_tail_ne : p.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos p hp_pos
    have h_drop_or_last : z ∈ p.vertices.tail.dropLast ∨ z = y := by
      rw [← List.dropLast_append_getLast h_tail_ne] at h_in_tail
      rcases List.mem_append.mp h_in_tail with h_drop | h_last
      · exact Or.inl h_drop
      · refine Or.inr ?_
        rw [List.mem_singleton] at h_last
        rw [h_last, Walk.tail_getLast_of_pos p hp_pos]
    rcases h_drop_or_last with h_drop | h_last
    · have h_in_image := hp_inter z h_drop
      obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp h_in_image
      exact ⟨w, hw_eq.symm⟩
    · exact ⟨v, h_last.trans hyv⟩

-- ## Refactor replacements — Phase ii.C (Φ iff lemmas + transfer-edge handler).
--
-- Pii20 / Pii21 are pure plumbing over Phase ii.A's ascent and
-- Phase ii.B's descent; bodies port mechanically modulo upstream-name
-- retargets (`walk_ofExt_unsplit_full → walk_ofExt_unsplit_full`
-- etc.) and the consequent drop of the `edges` clause.  Pii22's
-- WalkStep destructuring shifts from the ordered-pair-plus-`Or` shape
-- to a `cases sStep with | forwardE / backwardE / bidir` split; only
-- the `.forwardE` branch carries content (`.backwardE` and `.bidir`
-- discharge from `hp_dir.elim` under the new `IsDirectedWalk`).

private lemma ext_marg_PhiE_iff_unsplit {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.J ∪ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) {u v : Node} :
    (extendingCDMGsWith G W₁ hW₁).MarginalizationΦE
        (W₂.image IntExtNode.unsplit)
        (IntExtNode.unsplit u) (IntExtNode.unsplit v) ↔
      G.MarginalizationΦE W₂ u v := by
  constructor
  · rintro ⟨p, hp_dir, hp_pos, hp_inter⟩
    have h_all := all_unsplit_of_interior_W_image (W := W₁) (hW := hW₁)
      p hp_pos (u := u) (v := v) rfl rfl (W₂ := W₂) hp_inter
    obtain ⟨q, hq_len, hq_vs, hq_dir, _⟩ :=
      walk_ofExt_unsplit_full hW₁ p h_all u v rfl rfl
    refine ⟨q, hq_dir hp_dir, ?_, ?_⟩
    · rw [hq_len]; exact hp_pos
    · intro x hx
      have hxL : IntExtNode.unsplit x ∈ p.vertices.tail.dropLast := by
        rw [← hq_vs, list_unsplit_tail_dropLast]
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      have h_in_image := hp_inter (IntExtNode.unsplit x) hxL
      obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp h_in_image
      have hwx : w = x := by injection hw_eq
      exact hwx ▸ hwW₂
  · rintro ⟨q, hq_dir, hq_pos, hq_inter⟩
    refine ⟨walk_toExt hW₁ q,
      walk_toExt_isDirectedWalk hW₁ q hq_dir, ?_, ?_⟩
    · rw [walk_toExt_length hW₁ q]; exact hq_pos
    · intro x hx
      rw [walk_toExt_vertices hW₁ q, list_unsplit_tail_dropLast] at hx
      obtain ⟨a, haIn, haEq⟩ := List.mem_map.mp hx
      rw [← haEq]
      exact Finset.mem_image.mpr ⟨a, hq_inter a haIn, rfl⟩

private lemma ext_marg_PhiL_iff_unsplit {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.J ∪ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) {u v : Node} :
    (extendingCDMGsWith G W₁ hW₁).MarginalizationΦL
        (W₂.image IntExtNode.unsplit)
        (IntExtNode.unsplit u) (IntExtNode.unsplit v) ↔
      G.MarginalizationΦL W₂ u v := by
  constructor
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · have hp_pos : p.length ≥ 1 :=
        Walk.length_pos_of_isBifurcation hp_bif
      have h_all := all_unsplit_of_interior_W_image (W := W₁) (hW := hW₁)
        p hp_pos (u := u) (v := v) rfl rfl (W₂ := W₂) hp_inter
      obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hp_bif
      obtain ⟨q, _, hq_vs, _, hq_bif⟩ :=
        walk_ofExt_unsplit_full hW₁ p h_all u v rfl rfl
      refine Or.inl ⟨q, ⟨?_, ?_, ?_, i, hq_bif i hi⟩, ?_⟩
      · intro heq; apply hne; rw [heq]
      · intro h
        apply hu_tail
        rw [← hq_vs, list_unsplit_tail]
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      · intro h
        apply hv_drop
        rw [← hq_vs, list_unsplit_dropLast]
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      · intro x hx
        have hx_in : IntExtNode.unsplit x ∈ p.vertices.tail.dropLast := by
          rw [← hq_vs, list_unsplit_tail_dropLast]
          exact List.mem_map.mpr ⟨x, hx, rfl⟩
        have h_in_image := hp_inter (IntExtNode.unsplit x) hx_in
        obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp h_in_image
        have hwx : w = x := by injection hw_eq
        exact hwx ▸ hwW₂
    · have hp_pos : p.length ≥ 1 :=
        Walk.length_pos_of_isBifurcation hp_bif
      have h_all := all_unsplit_of_interior_W_image (W := W₁) (hW := hW₁)
        p hp_pos (u := v) (v := u) rfl rfl (W₂ := W₂) hp_inter
      obtain ⟨hne, hv_tail, hu_drop, i, hi⟩ := hp_bif
      obtain ⟨q, _, hq_vs, _, hq_bif⟩ :=
        walk_ofExt_unsplit_full hW₁ p h_all v u rfl rfl
      refine Or.inr ⟨q, ⟨?_, ?_, ?_, i, hq_bif i hi⟩, ?_⟩
      · intro heq; apply hne; rw [heq]
      · intro h
        apply hv_tail
        rw [← hq_vs, list_unsplit_tail]
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      · intro h
        apply hu_drop
        rw [← hq_vs, list_unsplit_dropLast]
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      · intro x hx
        have hx_in : IntExtNode.unsplit x ∈ p.vertices.tail.dropLast := by
          rw [← hq_vs, list_unsplit_tail_dropLast]
          exact List.mem_map.mpr ⟨x, hx, rfl⟩
        have h_in_image := hp_inter (IntExtNode.unsplit x) hx_in
        obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp h_in_image
        have hwx : w = x := by injection hw_eq
        exact hwx ▸ hwW₂
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · refine Or.inl ⟨walk_toExt hW₁ p,
        walk_toExt_isBifurcation hW₁ p hp_bif, ?_⟩
      intro x hx
      rw [walk_toExt_vertices hW₁ p, list_unsplit_tail_dropLast] at hx
      obtain ⟨a, haIn, haEq⟩ := List.mem_map.mp hx
      rw [← haEq]
      exact Finset.mem_image.mpr ⟨a, hp_inter a haIn, rfl⟩
    · refine Or.inr ⟨walk_toExt hW₁ p,
        walk_toExt_isBifurcation hW₁ p hp_bif, ?_⟩
      intro x hx
      rw [walk_toExt_vertices hW₁ p, list_unsplit_tail_dropLast] at hx
      obtain ⟨a, haIn, haEq⟩ := List.mem_map.mp hx
      rw [← haEq]
      exact Finset.mem_image.mpr ⟨a, hp_inter a haIn, rfl⟩

-- Transfer-edge walk surgery.  Under refactor, the WalkStep
-- destructuring shifts from the ordered-pair-plus-`Or` shape to a
-- `cases sStep with | forwardE / backwardE / bidir`; only `.forwardE`
-- carries content (the `.backwardE` and `.bidir` branches discharge
-- from `hp_dir.elim` because `IsDirectedWalk` is `False` on
-- those constructors).
private lemma walk_intCopy_target_unsplit {G : CDMG Node}
    {W : Finset Node} {hW : W ⊆ G.J ∪ G.V} {W₂ : Finset Node} (hDisj : Disjoint W W₂)
    {w : Node} (hwWJ : w ∈ W \ G.J)
    {y : IntExtNode Node}
    (p : Walk (extendingCDMGsWith G W hW)
            (IntExtNode.intCopy w) y)
    (hp_dir : p.IsDirectedWalk)
    (hp_pos : p.length ≥ 1)
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast,
                  z ∈ W₂.image IntExtNode.unsplit) :
    y = IntExtNode.unsplit w := by
  cases p with
  | nil _ _ => simp [Walk.length] at hp_pos
  | @cons _ _ mid sStep p' =>
      cases sStep with
      | backwardE _ => exact hp_dir.elim
      | bidir _ => exact hp_dir.elim
      | forwardE h_E =>
          change (IntExtNode.intCopy w, mid) ∈
              G.E.image (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2)) ∪
                (W \ G.J).image (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w)) at h_E
          rcases Finset.mem_union.mp h_E with hLift | hFresh
          · obtain ⟨e', _, he'_eq⟩ := Finset.mem_image.mp hLift
            have hcontra : IntExtNode.unsplit e'.1 = IntExtNode.intCopy w :=
              congrArg Prod.fst he'_eq
            cases hcontra
          · obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hFresh
            have h1 : IntExtNode.intCopy w' = IntExtNode.intCopy w :=
              congrArg Prod.fst hw'_eq
            have h2 : IntExtNode.unsplit w' = mid :=
              congrArg Prod.snd hw'_eq
            have hww' : w' = w := by injection h1
            rw [hww'] at h2
            have hmid : mid = IntExtNode.unsplit w := h2.symm
            subst hmid
            cases p' with
            | nil _ _ => rfl
            | @cons _ _ mid2 sStep2 p2 =>
                have h_pv_ne : p2.vertices ≠ [] :=
                  Walk.vertices_ne_nil p2
                have h_w_inter : IntExtNode.unsplit w ∈
                    (Walk.cons (G := extendingCDMGsWith G W hW)
                      (IntExtNode.unsplit w) (.forwardE h_E)
                      (Walk.cons mid2 sStep2 p2)).vertices.tail.dropLast := by
                  change IntExtNode.unsplit w ∈ (IntExtNode.intCopy w
                    :: IntExtNode.unsplit w :: p2.vertices).tail.dropLast
                  rw [show (IntExtNode.intCopy w :: IntExtNode.unsplit w
                              :: p2.vertices : List _).tail
                          = IntExtNode.unsplit w :: p2.vertices from rfl]
                  rw [List.dropLast_cons_of_ne_nil h_pv_ne]
                  exact List.mem_cons_self
                have h_in_image := hp_inter (IntExtNode.unsplit w) h_w_inter
                obtain ⟨w''', hw'''W₂, hw'''_eq⟩ := Finset.mem_image.mp h_in_image
                have hww''' : w''' = w := by injection hw'''_eq
                rw [hww'''] at hw'''W₂
                exact absurd hw'''W₂ (Finset.disjoint_left.mp hDisj
                  (Finset.mem_sdiff.mp hwWJ).1)

-- ## Refactor replacements — Phase ii.D (field equality lemmas).
--
-- Pii23 (E-field) is structural-light: the E-side carrier shape is
-- unchanged (`Finset (Node × Node)` over `IntExtNode Node`), only
-- upstream-name retargets propagate plus the Pii20 Φ_E iff bridge.
-- Pii24 (L-field) is the Sym2-image dance: LHS is
-- `(filter_LHS).image (fun e => s(e.1, e.2))` while RHS is
-- `((filter_RHS).image (fun e => s(e.1, e.2))).image (Sym2.map .unsplit)`.
-- The proof applies `Finset.ext` + `Sym2.ind` to fix the witness pair,
-- then reduces both directions to ordered-pair-plus-iff (Pii21).

set_option maxHeartbeats 400000 in
private lemma ext_marg_E_field_eq {G : CDMG Node} (W₁ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    ((extendingCDMGsWith G W₁ hW₁).marginalize
        (W₂.image IntExtNode.unsplit)
        (image_unsplit_subset_extendingCDMGsWith_V hW₁ hW₂)).E
      = (extendingCDMGsWith (G.marginalize W₂ hW₂) W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)).E := by
  apply Finset.ext
  intro e
  change
    e ∈ (((G.J.image IntExtNode.unsplit ∪ (W₁ \ G.J).image IntExtNode.intCopy)
            ∪ (G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit))
          ×ˢ (G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit)).filter
        (fun e => (extendingCDMGsWith G W₁ hW₁).MarginalizationΦE
                    (W₂.image IntExtNode.unsplit) e.1 e.2)
    ↔ e ∈ (((G.J ∪ (G.V \ W₂)) ×ˢ (G.V \ W₂)).filter
              (fun e => G.MarginalizationΦE W₂ e.1 e.2)).image
            (fun e => (IntExtNode.unsplit e.1, IntExtNode.unsplit e.2))
        ∪ (W₁ \ G.J).image
            (fun w => (IntExtNode.intCopy w, IntExtNode.unsplit w))
  rw [image_unsplit_sdiff]
  rw [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, h2⟩, hPhi⟩
    obtain ⟨v, hvVW₂, hv_eq⟩ := Finset.mem_image.mp h2
    rcases Finset.mem_union.mp h1 with h1JI | h1V
    · rcases Finset.mem_union.mp h1JI with h1J | h1I
      · obtain ⟨u, huJ, hu_eq⟩ := Finset.mem_image.mp h1J
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_image.mpr ⟨(u, v), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_union_left _ huJ, hvVW₂⟩, ?_⟩
          rw [show e.1 = IntExtNode.unsplit u from hu_eq.symm,
              show e.2 = IntExtNode.unsplit v from hv_eq.symm] at hPhi
          exact (ext_marg_PhiE_iff_unsplit hW₁ hDisj).mp hPhi
        · exact Prod.ext hu_eq hv_eq
      · obtain ⟨w, hwWJ, hw_eq⟩ := Finset.mem_image.mp h1I
        refine Finset.mem_union_right _ ?_
        refine Finset.mem_image.mpr ⟨w, hwWJ, ?_⟩
        obtain ⟨ec1, ec2⟩ := e
        change IntExtNode.intCopy w = ec1 at hw_eq
        change IntExtNode.unsplit v = ec2 at hv_eq
        subst hw_eq
        obtain ⟨p, hp_dir, hp_pos, hp_inter⟩ := hPhi
        have hec2 : ec2 = IntExtNode.unsplit w :=
          walk_intCopy_target_unsplit (hW := hW₁) hDisj hwWJ p hp_dir hp_pos hp_inter
        subst hec2
        rfl
    · obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp h1V
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_image.mpr ⟨(u, v), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_union_right _ hu, hvVW₂⟩, ?_⟩
        rw [show e.1 = IntExtNode.unsplit u from hu_eq.symm,
            show e.2 = IntExtNode.unsplit v from hv_eq.symm] at hPhi
        exact (ext_marg_PhiE_iff_unsplit hW₁ hDisj).mp hPhi
      · exact Prod.ext hu_eq hv_eq
  · intro h_union
    rcases Finset.mem_union.mp h_union with h_lifted | h_fresh
    · obtain ⟨⟨u, v⟩, hUV_mem, hUV_eq⟩ := Finset.mem_image.mp h_lifted
      rw [Finset.mem_filter, Finset.mem_product] at hUV_mem
      obtain ⟨⟨hu_in, hv_in⟩, hPhi⟩ := hUV_mem
      have h1_eq : e.1 = IntExtNode.unsplit u :=
        congrArg Prod.fst hUV_eq.symm
      have h2_eq : e.2 = IntExtNode.unsplit v :=
        congrArg Prod.snd hUV_eq.symm
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rcases Finset.mem_union.mp hu_in with huJ | huVW₂
        · refine Finset.mem_union_left _ ?_
          refine Finset.mem_union_left _ ?_
          rw [h1_eq]
          exact Finset.mem_image.mpr ⟨u, huJ, rfl⟩
        · refine Finset.mem_union_right _ ?_
          rw [h1_eq]
          exact Finset.mem_image.mpr ⟨u, huVW₂, rfl⟩
      · rw [h2_eq]
        exact Finset.mem_image.mpr ⟨v, hv_in, rfl⟩
      · rw [h1_eq, h2_eq]
        exact (ext_marg_PhiE_iff_unsplit hW₁ hDisj).mpr hPhi
    · obtain ⟨w, hwWJ, hw_eq⟩ := Finset.mem_image.mp h_fresh
      have hwW₁ : w ∈ W₁ := (Finset.mem_sdiff.mp hwWJ).1
      have hwNJ : w ∉ G.J := (Finset.mem_sdiff.mp hwWJ).2
      have hwV : w ∈ G.V := by
        rcases Finset.mem_union.mp (hW₁ hwW₁) with hJ | hV
        · exact absurd hJ hwNJ
        · exact hV
      have hwNW₂ : w ∉ W₂ := Finset.disjoint_left.mp hDisj hwW₁
      have h1_eq : e.1 = IntExtNode.intCopy w :=
        congrArg Prod.fst hw_eq.symm
      have h2_eq : e.2 = IntExtNode.unsplit w :=
        congrArg Prod.snd hw_eq.symm
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h1_eq]
        refine Finset.mem_union_left _ ?_
        refine Finset.mem_union_right _ ?_
        exact Finset.mem_image.mpr ⟨w, hwWJ, rfl⟩
      · rw [h2_eq]
        exact Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hwV, hwNW₂⟩, rfl⟩
      · rw [h1_eq, h2_eq]
        have h_fresh_edge : (IntExtNode.intCopy w, IntExtNode.unsplit w)
            ∈ (extendingCDMGsWith G W₁ hW₁).E := by
          change _ ∈ G.E.image _ ∪ (W₁ \ G.J).image _
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwWJ, rfl⟩
        have h_unsplitw_in : IntExtNode.unsplit w ∈ extendingCDMGsWith G W₁ hW₁ := by
          change _ ∈ (extendingCDMGsWith G W₁ hW₁).J
                ∪ (extendingCDMGsWith G W₁ hW₁).V
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwV, rfl⟩
        refine ⟨Walk.cons (IntExtNode.unsplit w)
                  (.forwardE h_fresh_edge)
                  (Walk.nil (IntExtNode.unsplit w) h_unsplitw_in),
                ?_, by change 0 + 1 ≥ 1; omega, ?_⟩
        · show (Walk.nil (IntExtNode.unsplit w)
                  h_unsplitw_in).IsDirectedWalk
          trivial
        · intro x hx
          simp [Walk.vertices, List.tail] at hx

set_option maxHeartbeats 800000 in
private lemma ext_marg_L_field_eq {G : CDMG Node} (W₁ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    ((extendingCDMGsWith G W₁ hW₁).marginalize
        (W₂.image IntExtNode.unsplit)
        (image_unsplit_subset_extendingCDMGsWith_V hW₁ hW₂)).L
      = (extendingCDMGsWith (G.marginalize W₂ hW₂) W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)).L := by
  change
    ((((G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit)
        ×ˢ (G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit)).filter
        (fun e => e.1 ≠ e.2 ∧
          (extendingCDMGsWith G W₁ hW₁).MarginalizationΦL
            (W₂.image IntExtNode.unsplit) e.1 e.2)).image (fun e => s(e.1, e.2)))
      = ((((G.V \ W₂) ×ˢ (G.V \ W₂)).filter
            (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W₂ e.1 e.2)).image
              (fun e => s(e.1, e.2))).image (Sym2.map IntExtNode.unsplit)
  rw [image_unsplit_sdiff]
  apply Finset.ext
  refine Sym2.ind (fun a b => ?_)
  constructor
  · intro h_LHS
    obtain ⟨e, he_filter, he_eq⟩ := Finset.mem_image.mp h_LHS
    rw [Finset.mem_filter, Finset.mem_product] at he_filter
    obtain ⟨⟨h1, h2⟩, hNe, hPhi⟩ := he_filter
    obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp h1
    obtain ⟨v, hv, hv_eq⟩ := Finset.mem_image.mp h2
    have hu_ne_v : u ≠ v := by
      intro huv
      apply hNe
      exact hu_eq.symm.trans ((congrArg IntExtNode.unsplit huv).trans hv_eq)
    have hPhi_G : G.MarginalizationΦL W₂ u v := by
      rw [show e.1 = IntExtNode.unsplit u from hu_eq.symm,
          show e.2 = IntExtNode.unsplit v from hv_eq.symm] at hPhi
      exact (ext_marg_PhiL_iff_unsplit hW₁ hDisj).mp hPhi
    refine Finset.mem_image.mpr ⟨s(u, v), ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨(u, v), ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨?_, hu_ne_v, hPhi_G⟩
      exact Finset.mem_product.mpr ⟨hu, hv⟩
    · change s(IntExtNode.unsplit u, IntExtNode.unsplit v) = s(a, b)
      rw [show IntExtNode.unsplit u = e.1 from hu_eq,
          show IntExtNode.unsplit v = e.2 from hv_eq]
      exact he_eq
  · intro h_RHS
    obtain ⟨s', hs'_in, hs'_eq⟩ := Finset.mem_image.mp h_RHS
    obtain ⟨e', he'_filter, he'_eq⟩ := Finset.mem_image.mp hs'_in
    rw [Finset.mem_filter, Finset.mem_product] at he'_filter
    obtain ⟨⟨hu_in, hv_in⟩, hNe, hPhi⟩ := he'_filter
    rw [← he'_eq] at hs'_eq
    refine Finset.mem_image.mpr
      ⟨(IntExtNode.unsplit e'.1, IntExtNode.unsplit e'.2), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨e'.1, hu_in, rfl⟩
        · exact Finset.mem_image.mpr ⟨e'.2, hv_in, rfl⟩
      · intro heq; apply hNe; injection heq
      · exact (ext_marg_PhiL_iff_unsplit hW₁ hDisj).mpr hPhi
    · exact hs'_eq

-- ## Refactor replacements — Phase ii.E (main theorem, Part ii).
--
-- Two structural shifts from the original:
--   1. `CDMG` → `CDMG`: the structure drops from 9 fields to
--      8 (no `hL_symm`).  The local `cdmgExt` `have`-lemma's `rintro`
--      destructure shrinks to 8 anonymous slots.
--   2. `extendingCDMGsWith`, `marginalize` retarget to their
--      `refactor_*` twins (`extendingCDMGsWith` is in the
--      `CDMG` namespace and is referenced by function-style, not dot
--      notation — see Phase ii.A header rationale); the E / L field
--      equalities call the Phase ii.D twins.

-- claim_3_18 -- start statement
theorem marginalize_extendingCDMGsWith_comm (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (extendingCDMGsWith G W₁ hW₁).marginalize
        (W₂.image IntExtNode.unsplit)
        (image_unsplit_subset_extendingCDMGsWith_V hW₁ hW₂)
      = extendingCDMGsWith (G.marginalize W₂ hW₂) W₁
        (subset_carrier_of_marginalize hW₂ hW₁ hDisj)
-- claim_3_18 -- end statement
:= by
  have cdmgExt : ∀ {G₁ G₂ : CDMG (IntExtNode Node)},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨_, _, _, _, _, _, _, _⟩
           ⟨_, _, _, _, _, _, _, _⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL; rfl
  refine cdmgExt ?_ ?_ ?_ ?_
  · -- J: both sides reduce to G.J.image .unsplit ∪ (W₁ \ G.J).image .intCopy
    rfl
  · -- V: image-sdiff identity
    change G.V.image IntExtNode.unsplit \ W₂.image IntExtNode.unsplit
      = (G.V \ W₂).image IntExtNode.unsplit
    exact image_unsplit_sdiff
  · -- E: see `ext_marg_E_field_eq`.
    exact ext_marg_E_field_eq W₁ hW₁ W₂ hW₂ hDisj
  · -- L: see `ext_marg_L_field_eq`.
    exact ext_marg_L_field_eq W₁ hW₁ W₂ hW₂ hDisj

-- ## Refactor replacements — Phase iii.A (carrier helpers / sdiff /
-- constructor disjointness for node-splitting, Piii1-Piii15).
--
-- All fifteen helpers are mechanical name-retargets of the originals:
--   * `CDMG → CDMG`, `nodeSplittingOn → nodeSplittingOn`;
--   * `SplitNode → SplitNode`, `toCopy0/1 → toCopy0/1`.
-- The E-field carrier shape is unchanged (`Finset (Node × Node)`); the
-- L-field carrier shape changes from `Finset (Node × Node)` to
-- `Finset (Sym2 Node)`, which only affects Piii12
-- (`lifted_L_in_split_L_generic`): the underlying
-- `nodeSplittingOn.L` is now `G.L.image (Sym2.map (toCopy0 W₁))`,
-- so the membership witness is built via `Finset.mem_image.mpr ⟨s(u,v), hL, rfl⟩`
-- (the `Sym2.map f s(a,b) = s(f a, f b)` reduction is definitional under
-- `Sym2.mk` notation).

private lemma image_split_unsplit_sdiff {S T : Finset Node} :
    S.image SplitNode.unsplit \ T.image SplitNode.unsplit
      = (S \ T).image SplitNode.unsplit := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, hAS, rfl⟩, h_notT⟩
    refine ⟨a, ⟨hAS, ?_⟩, rfl⟩
    intro hAT
    exact h_notT ⟨a, hAT, rfl⟩
  · rintro ⟨a, ⟨hAS, hANotT⟩, rfl⟩
    refine ⟨⟨a, hAS, rfl⟩, ?_⟩
    rintro ⟨b, hBT, hEq⟩
    apply hANotT
    have : b = a := by injection hEq
    exact this ▸ hBT

private lemma unsplit_image_disjoint_copy0 {S T : Finset Node} :
    Disjoint (S.image SplitNode.unsplit) (T.image SplitNode.copy0) := by
  rw [Finset.disjoint_left]
  intro x hUns hC0
  obtain ⟨_, _, h1⟩ := Finset.mem_image.mp hUns
  obtain ⟨_, _, h2⟩ := Finset.mem_image.mp hC0
  rw [← h2] at h1
  cases h1

private lemma unsplit_image_disjoint_copy1 {S T : Finset Node} :
    Disjoint (S.image SplitNode.unsplit) (T.image SplitNode.copy1) := by
  rw [Finset.disjoint_left]
  intro x hUns hC1
  obtain ⟨_, _, h1⟩ := Finset.mem_image.mp hUns
  obtain ⟨_, _, h2⟩ := Finset.mem_image.mp hC1
  rw [← h2] at h1
  cases h1

private lemma mem_G_of_unsplit_mem_split {G : CDMG Node}
    {W : Finset Node} (hW : W ⊆ G.V) {v : Node}
    (hv : SplitNode.unsplit v ∈ G.nodeSplittingOn W hW) :
    v ∈ G := by
  change v ∈ G.J ∪ G.V
  change SplitNode.unsplit v ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W).image SplitNode.unsplit ∪ W.image SplitNode.copy0
      ∪ W.image SplitNode.copy1) at hv
  rcases Finset.mem_union.mp hv with hJ | hRest
  · obtain ⟨j, hjJ, hjEq⟩ := Finset.mem_image.mp hJ
    have hju : j = v := by injection hjEq
    subst hju
    exact Finset.mem_union_left _ hjJ
  · rcases Finset.mem_union.mp hRest with hV12 | h1
    · rcases Finset.mem_union.mp hV12 with hVuns | h0
      · obtain ⟨z, hzVW, hzEq⟩ := Finset.mem_image.mp hVuns
        have hzv : z = v := by injection hzEq
        subst hzv
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hzVW).1
      · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h0
        cases hEq
    · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h1
      cases hEq

private lemma toCopy0_unsplit_of_notW {W : Finset Node} {v : Node} (h : v ∉ W) :
    toCopy0 W v = SplitNode.unsplit v := by
  unfold toCopy0; rw [if_neg h]

private lemma toCopy1_unsplit_of_notW {W : Finset Node} {v : Node} (h : v ∉ W) :
    toCopy1 W v = SplitNode.unsplit v := by
  unfold toCopy1; rw [if_neg h]

private lemma lifted_edge_in_split_E {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) {u v : Node}
    (huv_inE : (u, v) ∈ G.E) (hv_notW : v ∉ W₁) :
    (toCopy1 W₁ u, SplitNode.unsplit v)
      ∈ (G.nodeSplittingOn W₁ hW₁).E := by
  change _ ∈ G.E.image _ ∪ _
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_image.mpr ⟨(u, v), huv_inE, ?_⟩
  simp [toCopy0_unsplit_of_notW hv_notW]

private lemma mem_split_of_mem_G_unsplit {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {v : Node} (hv : v ∈ G) (hv_notW₁ : v ∉ W₁) :
    SplitNode.unsplit v ∈ G.nodeSplittingOn W₁ hW₁ := by
  change _ ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1)
  change v ∈ G.J ∪ G.V at hv
  rcases Finset.mem_union.mp hv with hJ | hV
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hJ, rfl⟩)
  · refine Finset.mem_union_right _ ?_
    refine Finset.mem_union_left _ ?_
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hV, hv_notW₁⟩, rfl⟩

private lemma mem_split_of_mem_W₁_copy0 {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {w : Node} (hw : w ∈ W₁) :
    SplitNode.copy0 w ∈ G.nodeSplittingOn W₁ hW₁ := by
  change _ ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1)
  refine Finset.mem_union_right _ ?_
  refine Finset.mem_union_left _ ?_
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

private lemma mem_split_of_mem_W₁_copy1 {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {w : Node} (hw : w ∈ W₁) :
    SplitNode.copy1 w ∈ G.nodeSplittingOn W₁ hW₁ := by
  change _ ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1)
  refine Finset.mem_union_right _ ?_
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_image.mpr ⟨w, hw, rfl⟩

private lemma lifted_E_in_split_E_generic {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {u v : Node}
    (huv_inE : (u, v) ∈ G.E) :
    (toCopy1 W₁ u, toCopy0 W₁ v)
      ∈ (G.nodeSplittingOn W₁ hW₁).E := by
  change _ ∈ G.E.image _ ∪ _
  refine Finset.mem_union_left _ ?_
  exact Finset.mem_image.mpr ⟨(u, v), huv_inE, rfl⟩

-- KEY Sym2 reshape.  `nodeSplittingOn.L = G.L.image (Sym2.map
-- (toCopy0 W₁))`, so we lift `s(u, v) ∈ G.L` via
-- `Finset.mem_image.mpr ⟨s(u, v), huv_inL, rfl⟩`; the
-- `Sym2.map f s(a, b) = s(f a, f b)` reduction is definitional under
-- `s(·, ·)` notation.
private lemma lifted_L_in_split_L_generic {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {u v : Node}
    (huv_inL : s(u, v) ∈ G.L) :
    s(toCopy0 W₁ u, toCopy0 W₁ v)
      ∈ (G.nodeSplittingOn W₁ hW₁).L := by
  change _ ∈ G.L.image (Sym2.map (toCopy0 W₁))
  exact Finset.mem_image.mpr ⟨s(u, v), huv_inL, rfl⟩

private lemma unsplit_notW₁_of_unsplit_mem_split {G : CDMG Node}
    {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V} {v : Node}
    (hv : SplitNode.unsplit v ∈ G.nodeSplittingOn W₁ hW₁) :
    v ∈ G ∧ v ∉ W₁ := by
  change v ∈ G.J ∪ G.V ∧ _
  change SplitNode.unsplit v ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1) at hv
  rcases Finset.mem_union.mp hv with hJ | hRest
  · obtain ⟨j, hjJ, hjEq⟩ := Finset.mem_image.mp hJ
    have hjv : j = v := by injection hjEq
    subst hjv
    refine ⟨Finset.mem_union_left _ hjJ, ?_⟩
    intro hjW₁
    have hjV : j ∈ G.V := hW₁ hjW₁
    exact Finset.disjoint_left.mp G.hJV_disj hjJ hjV
  · rcases Finset.mem_union.mp hRest with hV12 | h1
    · rcases Finset.mem_union.mp hV12 with hVuns | h0
      · obtain ⟨z, hzVW, hzEq⟩ := Finset.mem_image.mp hVuns
        have hzv : z = v := by injection hzEq
        subst hzv
        obtain ⟨hzV, hzNW⟩ := Finset.mem_sdiff.mp hzVW
        exact ⟨Finset.mem_union_right _ hzV, hzNW⟩
      · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h0
        cases hEq
    · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h1
      cases hEq

private lemma mem_W₁_of_copy0_mem_split {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {w : Node}
    (hw : SplitNode.copy0 w ∈ G.nodeSplittingOn W₁ hW₁) : w ∈ W₁ := by
  change SplitNode.copy0 w ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1) at hw
  rcases Finset.mem_union.mp hw with hJ | hRest
  · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hJ; cases hEq
  · rcases Finset.mem_union.mp hRest with hV12 | h1
    · rcases Finset.mem_union.mp hV12 with hVuns | h0
      · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hVuns; cases hEq
      · obtain ⟨w', hw'W₁, hw'Eq⟩ := Finset.mem_image.mp h0
        have : w' = w := by injection hw'Eq
        exact this ▸ hw'W₁
    · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h1; cases hEq

private lemma mem_W₁_of_copy1_mem_split {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {w : Node}
    (hw : SplitNode.copy1 w ∈ G.nodeSplittingOn W₁ hW₁) : w ∈ W₁ := by
  change SplitNode.copy1 w ∈ G.J.image SplitNode.unsplit ∪
    ((G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
      ∪ W₁.image SplitNode.copy1) at hw
  rcases Finset.mem_union.mp hw with hJ | hRest
  · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hJ; cases hEq
  · rcases Finset.mem_union.mp hRest with hV12 | h1
    · rcases Finset.mem_union.mp hV12 with hVuns | h0
      · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp hVuns; cases hEq
      · obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h0; cases hEq
    · obtain ⟨w', hw'W₁, hw'Eq⟩ := Finset.mem_image.mp h1
      have : w' = w := by injection hw'Eq
      exact this ▸ hw'W₁

-- ## Refactor replacements — Phase iii.B (walk ascent G → split,
-- `.unsplit`-tagged, Piii16-Piii22).
--
-- Body shifts:
--   1. `WalkStep` destructure: the original's `rcases h with ⟨ha, hOr⟩ | ⟨ha, hE⟩`
--      becomes pattern-match on `s : WalkStep G u v` with the
--      three typed constructors `.forwardE / .backwardE / .bidir`.
--   2. Cons-cell pattern: `.cons _ a hStep p` (4-arg) becomes
--      `.cons _ s p` (3-arg).  The lifted-step builder
--      `walkStep_toSplit` returns a `WalkStep`
--      directly; no stored ordered pair `a` is threaded through.
--   3. L-membership for the `.bidir` branch reshapes:
--      `(u, v) ∈ G.L → (toCopy0 u, toCopy0 v) ∈ split.L` becomes
--      `s(u, v) ∈ G.L → s(.unsplit u, .unsplit v) ∈ split.L`
--      via `Sym2.map` and `toCopy0_unsplit_of_notW`.
--   4. `IsBifurcationWithSplit` has 10 pattern-match branches
--      (3 step tags × 3 tail/k shapes + nil); the port mirrors
--      `walk_toExt_isBifurcationWithSplit` structurally.

private def walkStep_toSplit {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {u v : Node} (hu_notW : u ∉ W₁) (hv_notW : v ∉ W₁) :
    WalkStep G u v →
      WalkStep (G.nodeSplittingOn W₁ hW₁)
        (SplitNode.unsplit u) (SplitNode.unsplit v)
  | .forwardE h_E => .forwardE (by
      change _ ∈ G.E.image _ ∪ _
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_image.mpr ⟨(u, v), h_E, ?_⟩
      show (toCopy1 W₁ u, toCopy0 W₁ v) = _
      rw [toCopy1_unsplit_of_notW hu_notW,
          toCopy0_unsplit_of_notW hv_notW])
  | .backwardE h_E => .backwardE (by
      change _ ∈ G.E.image _ ∪ _
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_image.mpr ⟨(v, u), h_E, ?_⟩
      show (toCopy1 W₁ v, toCopy0 W₁ u) = _
      rw [toCopy1_unsplit_of_notW hv_notW,
          toCopy0_unsplit_of_notW hu_notW])
  | .bidir h_L => .bidir (by
      change _ ∈ G.L.image (Sym2.map (toCopy0 W₁))
      refine Finset.mem_image.mpr ⟨s(u, v), h_L, ?_⟩
      show Sym2.map (toCopy0 W₁) s(u, v) = _
      change s(toCopy0 W₁ u, toCopy0 W₁ v) = _
      rw [toCopy0_unsplit_of_notW hu_notW,
          toCopy0_unsplit_of_notW hv_notW])

private def walk_toSplit_unsplit {G : CDMG Node} {W₁ : Finset Node}
    (hW₁ : W₁ ⊆ G.V) :
    ∀ {u v : Node} (p : Walk G u v),
      (∀ x ∈ p.vertices, x ∉ W₁) →
      Walk (G.nodeSplittingOn W₁ hW₁)
        (SplitNode.unsplit u) (SplitNode.unsplit v)
  | _, _, .nil v hv, h_all =>
      Walk.nil (SplitNode.unsplit v)
        (mem_split_of_mem_G_unsplit (hW₁ := hW₁) hv
          (h_all v (Walk.head_mem_vertices _)))
  | _, _, .cons v s p, h_all =>
      Walk.cons (SplitNode.unsplit v)
        (walkStep_toSplit (hW₁ := hW₁)
          (h_all _ List.mem_cons_self)
          (h_all v (List.mem_cons_of_mem _ (Walk.head_mem_vertices p)))
          s)
        (walk_toSplit_unsplit hW₁ p (fun x hx =>
          h_all x (List.mem_cons_of_mem _ hx)))

private lemma walk_toSplit_unsplit_length {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) :
    ∀ {u v : Node} (p : Walk G u v)
      (h_all : ∀ x ∈ p.vertices, x ∉ W₁),
      (walk_toSplit_unsplit hW₁ p h_all).length = p.length
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ _ p, _ => by
      change (walk_toSplit_unsplit hW₁ p _).length + 1
              = p.length + 1
      rw [walk_toSplit_unsplit_length hW₁ p]

private lemma walk_toSplit_unsplit_vertices {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) :
    ∀ {u v : Node} (p : Walk G u v)
      (h_all : ∀ x ∈ p.vertices, x ∉ W₁),
      (walk_toSplit_unsplit hW₁ p h_all).vertices
        = p.vertices.map SplitNode.unsplit
  | _, _, .nil _ _, _ => rfl
  | _, _, .cons _ _ p, _ => by
      change _ :: (walk_toSplit_unsplit hW₁ p _).vertices = _ :: _
      rw [walk_toSplit_unsplit_vertices hW₁ p]

private lemma walk_toSplit_unsplit_isDirectedWalk {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) :
    ∀ {u v : Node} (p : Walk G u v)
      (h_all : ∀ x ∈ p.vertices, x ∉ W₁),
      p.IsDirectedWalk →
        (walk_toSplit_unsplit hW₁ p h_all).IsDirectedWalk
  | _, _, .nil _ _, _, _ => trivial
  | _, _, .cons _ (.forwardE _) p, h_all, hDir => by
      have h_all_p : ∀ x ∈ p.vertices, x ∉ W₁ := fun x hx =>
        h_all x (List.mem_cons_of_mem _ hx)
      change (walk_toSplit_unsplit hW₁ p h_all_p).IsDirectedWalk
      exact walk_toSplit_unsplit_isDirectedWalk hW₁ p h_all_p hDir
  | _, _, .cons _ (.backwardE _) _, _, hDir => hDir.elim
  | _, _, .cons _ (.bidir _) _, _, hDir => hDir.elim

private lemma walk_toSplit_unsplit_isBifurcationWithSplit
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) :
    ∀ {u v : Node} (p : Walk G u v)
      (h_all : ∀ x ∈ p.vertices, x ∉ W₁) (i : ℕ),
      p.IsBifurcationWithSplit i →
        (walk_toSplit_unsplit hW₁ p h_all).IsBifurcationWithSplit i := by
  intro u v p
  induction p with
  | nil _ _ =>
      intro _ i hSpl
      simp only [Walk.IsBifurcationWithSplit] at hSpl
  | @cons u' w' vMid s p' ih =>
      intro h_all i hSpl
      cases hSplCheck : s with
      | forwardE h_E =>
          subst hSplCheck
          revert h_all
          match i, p', hSpl with
          | 0, .nil _ _, hSpl =>
              intro _
              simp only [Walk.IsBifurcationWithSplit] at hSpl
          | 0, .cons _ _ _, hSpl =>
              intro _
              simp only [Walk.IsBifurcationWithSplit] at hSpl
          | _ + 1, _, hSpl =>
              intro _
              simp only [Walk.IsBifurcationWithSplit] at hSpl
      | backwardE h_E =>
          subst hSplCheck
          revert h_all
          match i, p', hSpl, ih with
          | 0, .nil _ _, hSpl, _ =>
              intro _
              simp only [Walk.IsBifurcationWithSplit] at hSpl
          | 0, .cons vI sI pI, hDir, _ =>
              intro h_all
              simp only [Walk.IsBifurcationWithSplit] at hDir
              have h_all_p : ∀ x ∈ (Walk.cons (G := G) vI sI pI).vertices,
                  x ∉ W₁ := fun x hx => h_all x (List.mem_cons_of_mem _ hx)
              simp only [walk_toSplit_unsplit, walkStep_toSplit,
                Walk.IsBifurcationWithSplit]
              exact walk_toSplit_unsplit_isDirectedWalk hW₁ _ h_all_p hDir
          | k + 1, p'', hRec, ih =>
              intro h_all
              simp only [Walk.IsBifurcationWithSplit] at hRec
              have h_all_p : ∀ x ∈ p''.vertices, x ∉ W₁ := fun x hx =>
                h_all x (List.mem_cons_of_mem _ hx)
              simp only [walk_toSplit_unsplit, walkStep_toSplit,
                Walk.IsBifurcationWithSplit]
              exact ih h_all_p k hRec
      | bidir h_L =>
          subst hSplCheck
          revert h_all
          match i, p', hSpl with
          | 0, .nil _ _, _ =>
              intro _
              simp only [walk_toSplit_unsplit, walkStep_toSplit,
                Walk.IsBifurcationWithSplit]
          | 0, .cons vI sI pI, hDir =>
              intro h_all
              simp only [Walk.IsBifurcationWithSplit] at hDir
              have h_all_p : ∀ x ∈ (Walk.cons (G := G) vI sI pI).vertices,
                  x ∉ W₁ := fun x hx => h_all x (List.mem_cons_of_mem _ hx)
              simp only [walk_toSplit_unsplit, walkStep_toSplit,
                Walk.IsBifurcationWithSplit]
              exact walk_toSplit_unsplit_isDirectedWalk hW₁ _ h_all_p hDir
          | _ + 1, _, hSpl =>
              intro _
              simp only [Walk.IsBifurcationWithSplit] at hSpl

private lemma walk_toSplit_unsplit_isBifurcation {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {u v : Node} (p : Walk G u v)
    (h_all : ∀ x ∈ p.vertices, x ∉ W₁) (hp : p.IsBifurcation) :
    (walk_toSplit_unsplit hW₁ p h_all).IsBifurcation := by
  obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hp
  refine ⟨?_, ?_, ?_, i, walk_toSplit_unsplit_isBifurcationWithSplit hW₁ p h_all i hi⟩
  · intro heq
    apply hne
    have : SplitNode.unsplit u = SplitNode.unsplit v := heq
    injection this
  · rw [walk_toSplit_unsplit_vertices hW₁ p]
    intro h
    rw [show (p.vertices.map SplitNode.unsplit).tail
              = p.vertices.tail.map SplitNode.unsplit from
        by cases p.vertices with
        | nil => rfl
        | cons _ _ => rfl] at h
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h
    have : a = u := by injection ha_eq
    exact hu_tail (this ▸ ha_in)
  · rw [walk_toSplit_unsplit_vertices hW₁ p]
    intro h
    have hMap : ∀ (l : List Node),
        (l.map SplitNode.unsplit).dropLast
          = l.dropLast.map SplitNode.unsplit := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
          cases xs with
          | nil => rfl
          | cons y ys =>
              simp only [List.map_cons, List.dropLast_cons₂]
              change _ :: ((y :: ys).map _).dropLast
                = _ :: ((y :: ys).dropLast).map SplitNode.unsplit
              rw [ih]
    rw [hMap p.vertices] at h
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h
    have : a = v := by injection ha_eq
    exact hv_drop (this ▸ ha_in)

-- ## Refactor replacements — Phase iii.C (walk descent split → G,
-- `.unsplit`-pinned, Piii23-Piii33).
--
-- The descent goes through `walkStep_ofSplit_unsplit` (Piii25),
-- which is now a pattern-matching `def` that reads the channel directly
-- off the typed `WalkStep` constructor.  The `.bidir` branch is
-- the **Sym2 reshape**: `s' ∈ G.L` is recovered from
-- `Sym2.map (toCopy0 W₁) s' = s(.unsplit u, .unsplit v)`
-- via `Sym2.ind` + `Sym2.eq_iff` + `Sym2.eq_swap` (the two `(a, b) = (u, v)`
-- vs `(a, b) = (v, u)` orientations are handled symmetrically).

private lemma node_of_toCopy1_unsplit {W₁ : Finset Node} {z : Node} {w : Node}
    (h : toCopy1 W₁ z = SplitNode.unsplit w) : z = w := by
  unfold toCopy1 at h
  by_cases hIn : z ∈ W₁
  · rw [if_pos hIn] at h
    cases h
  · rw [if_neg hIn] at h
    injection h

private lemma node_of_toCopy0_unsplit {W₁ : Finset Node} {z : Node} {w : Node}
    (h : toCopy0 W₁ z = SplitNode.unsplit w) : z = w := by
  unfold toCopy0 at h
  by_cases hIn : z ∈ W₁
  · rw [if_pos hIn] at h
    cases h
  · rw [if_neg hIn] at h
    injection h

-- Walk-step descent split → G with both endpoints `.unsplit`-tagged.
-- Pattern-matching `def`; consumers can recover the constructor tag of
-- the result via `simp [walkStep_ofSplit_unsplit]`.
-- Heartbeats raised: the `change` in each branch unfolds
-- `nodeSplittingOn.E` / `.L` (a noncomputable structure over
-- the `SplitNode Node` carrier) and Lean's defEq pass is
-- expensive on that shape.
set_option maxHeartbeats 800000 in
private def walkStep_ofSplit_unsplit {G : CDMG Node}
    {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V} {u v : Node} :
    WalkStep (G.nodeSplittingOn W₁ hW₁)
      (SplitNode.unsplit u) (SplitNode.unsplit v) →
    WalkStep G u v
  | .forwardE h_E => .forwardE (by
      change (SplitNode.unsplit u, SplitNode.unsplit v) ∈
          G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
            W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
        at h_E
      rcases Finset.mem_union.mp h_E with hLift | hTrans
      · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
        have h1 : toCopy1 W₁ a'.1 = SplitNode.unsplit u :=
          congrArg Prod.fst ha'_eq
        have h2 : toCopy0 W₁ a'.2 = SplitNode.unsplit v :=
          congrArg Prod.snd ha'_eq
        have ha'1 : a'.1 = u := node_of_toCopy1_unsplit h1
        have ha'2 : a'.2 = v := node_of_toCopy0_unsplit h2
        have h_pair : a' = (u, v) := Prod.ext ha'1 ha'2
        rw [← h_pair]; exact ha'_in
      · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
        have : SplitNode.copy0 w = SplitNode.unsplit u :=
          congrArg Prod.fst hw_eq
        cases this)
  | .backwardE h_E => .backwardE (by
      change (SplitNode.unsplit v, SplitNode.unsplit u) ∈
          G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
            W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
        at h_E
      rcases Finset.mem_union.mp h_E with hLift | hTrans
      · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
        have h1 : toCopy1 W₁ a'.1 = SplitNode.unsplit v :=
          congrArg Prod.fst ha'_eq
        have h2 : toCopy0 W₁ a'.2 = SplitNode.unsplit u :=
          congrArg Prod.snd ha'_eq
        have ha'1 : a'.1 = v := node_of_toCopy1_unsplit h1
        have ha'2 : a'.2 = u := node_of_toCopy0_unsplit h2
        have h_pair : a' = (v, u) := Prod.ext ha'1 ha'2
        rw [← h_pair]; exact ha'_in
      · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
        have : SplitNode.copy0 w = SplitNode.unsplit v :=
          congrArg Prod.fst hw_eq
        cases this)
  | .bidir h_L => .bidir (by
      change s(SplitNode.unsplit u, SplitNode.unsplit v)
          ∈ G.L.image (Sym2.map (toCopy0 W₁)) at h_L
      obtain ⟨s', hs'_in, hs'_eq⟩ := Finset.mem_image.mp h_L
      induction s' using Sym2.ind with
      | _ b c =>
          change s(toCopy0 W₁ b, toCopy0 W₁ c) =
                 s(SplitNode.unsplit u, SplitNode.unsplit v) at hs'_eq
          rcases Sym2.eq_iff.mp hs'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hb : b = u := node_of_toCopy0_unsplit h1
            have hc : c = v := node_of_toCopy0_unsplit h2
            rw [hb, hc] at hs'_in
            exact hs'_in
          · have hb : b = v := node_of_toCopy0_unsplit h1
            have hc : c = u := node_of_toCopy0_unsplit h2
            rw [hb, hc] at hs'_in
            rwa [Sym2.eq_swap])

private lemma list_split_unsplit_tail (l : List Node) :
    (l.map SplitNode.unsplit).tail = l.tail.map SplitNode.unsplit := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

private lemma list_split_unsplit_dropLast :
    ∀ (l : List Node),
      (l.map SplitNode.unsplit).dropLast
        = l.dropLast.map SplitNode.unsplit
  | [] => rfl
  | _ :: [] => rfl
  | x :: y :: rest => by
      change SplitNode.unsplit x
          :: (((y :: rest).map SplitNode.unsplit).dropLast)
          = SplitNode.unsplit x
              :: ((y :: rest).dropLast.map SplitNode.unsplit)
      rw [list_split_unsplit_dropLast (y :: rest)]

private lemma list_split_unsplit_tail_dropLast (l : List Node) :
    (l.map SplitNode.unsplit).tail.dropLast
      = l.tail.dropLast.map SplitNode.unsplit := by
  rw [list_split_unsplit_tail, list_split_unsplit_dropLast]

private lemma pair_eq_of_split_unsplit_eq {a : Node × Node} {u v : Node}
    (h : (SplitNode.unsplit a.1, SplitNode.unsplit a.2)
        = (SplitNode.unsplit u, SplitNode.unsplit v)) :
    a = (u, v) := by
  have h1 : SplitNode.unsplit a.1 = SplitNode.unsplit u :=
    congrArg Prod.fst h
  have h2 : SplitNode.unsplit a.2 = SplitNode.unsplit v :=
    congrArg Prod.snd h
  have ha1 : a.1 = u := by injection h1
  have ha2 : a.2 = v := by injection h2
  exact Prod.ext ha1 ha2

-- Heartbeats raised: the `change` unfolds `nodeSplittingOn.E`
-- (a noncomputable structure field over `SplitNode Node`).
set_option maxHeartbeats 800000 in
private lemma a_in_G_E_of_lifted_in_split {G : CDMG Node}
    {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V} {a' : Node × Node}
    {a : SplitNode Node × SplitNode Node}
    (ha_eq : a = (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2))
    (ha_E : a ∈ (G.nodeSplittingOn W₁ hW₁).E) : a' ∈ G.E := by
  change a ∈ G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))
          ∪ W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
        at ha_E
  rcases Finset.mem_union.mp ha_E with hLift | hTrans
  · obtain ⟨e', he'E, he'_eq⟩ := Finset.mem_image.mp hLift
    rw [ha_eq] at he'_eq
    have h1 : toCopy1 W₁ e'.1 = SplitNode.unsplit a'.1 :=
      congrArg Prod.fst he'_eq
    have h2 : toCopy0 W₁ e'.2 = SplitNode.unsplit a'.2 :=
      congrArg Prod.snd he'_eq
    have he1 : e'.1 = a'.1 := node_of_toCopy1_unsplit h1
    have he2 : e'.2 = a'.2 := node_of_toCopy0_unsplit h2
    have heq : e' = a' := Prod.ext he1 he2
    rw [← heq]; exact he'E
  · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
    rw [ha_eq] at hw_eq
    have hcontra : SplitNode.copy0 w = SplitNode.unsplit a'.1 :=
      congrArg Prod.fst hw_eq
    cases hcontra

-- L-field shape changes from `Finset (Node × Node)` to `Finset (Sym2 Node)`.
-- The lift is `Sym2.map (toCopy0 W₁)`; we use `Sym2.ind` to
-- destructure the lifted edge into an ordered-pair representative,
-- then `Sym2.eq_iff` to align orientations.
-- Heartbeats raised: the `change` unfolds `nodeSplittingOn.L`
-- (a noncomputable structure field over `SplitNode Node`).
set_option maxHeartbeats 800000 in
private lemma a_in_G_L_of_lifted_in_split {G : CDMG Node}
    {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V} {a' : Node × Node}
    {a : SplitNode Node × SplitNode Node}
    (ha_eq : a = (SplitNode.unsplit a'.1, SplitNode.unsplit a'.2))
    (ha_L : s(a.1, a.2) ∈ (G.nodeSplittingOn W₁ hW₁).L) :
    s(a'.1, a'.2) ∈ G.L := by
  change s(a.1, a.2) ∈ G.L.image (Sym2.map (toCopy0 W₁)) at ha_L
  obtain ⟨s', hs'_in, hs'_eq⟩ := Finset.mem_image.mp ha_L
  rw [ha_eq] at hs'_eq
  induction s' using Sym2.ind with
  | _ b c =>
      change s(toCopy0 W₁ b, toCopy0 W₁ c) =
             s(SplitNode.unsplit a'.1, SplitNode.unsplit a'.2) at hs'_eq
      rcases Sym2.eq_iff.mp hs'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hb : b = a'.1 := node_of_toCopy0_unsplit h1
        have hc : c = a'.2 := node_of_toCopy0_unsplit h2
        rw [hb, hc] at hs'_in
        exact hs'_in
      · have hb : b = a'.2 := node_of_toCopy0_unsplit h1
        have hc : c = a'.1 := node_of_toCopy0_unsplit h2
        rw [hb, hc] at hs'_in
        rwa [Sym2.eq_swap]

-- Walk descent split → G with both endpoints `.unsplit`-tagged.  Under
-- refactor, the `Walk` type has no `edges` accessor (typed
-- `WalkStep` carries the edge info structurally), so the `edges` clause
-- is dropped.  Consumers (Piii45, downstream) only use length / vertices /
-- IsDirectedWalk / IsBifurcationWithSplit.
-- Heartbeats raised: nested `change` operations on `nodeSplittingOn.E`
-- / `.L` are expensive on the `SplitNode Node` carrier.
set_option maxHeartbeats 1600000 in
private lemma walk_ofSplit_unsplit_full {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) :
    ∀ {x y : SplitNode Node}
      (p : Walk (G.nodeSplittingOn W₁ hW₁) x y),
      (∀ z ∈ p.vertices, ∃ z' : Node, z = SplitNode.unsplit z') →
      ∀ (u v : Node), x = SplitNode.unsplit u →
                       y = SplitNode.unsplit v →
      ∃ q : Walk G u v, q.length = p.length ∧
        q.vertices.map SplitNode.unsplit = p.vertices ∧
        (p.IsDirectedWalk → q.IsDirectedWalk) ∧
        (∀ i, p.IsBifurcationWithSplit i →
          q.IsBifurcationWithSplit i) := by
  intro x y p
  induction p with
  | nil w hw =>
      intro _ u v hxu hyv
      have hu_eq_v : SplitNode.unsplit u
          = (SplitNode.unsplit v : SplitNode Node) := by
        rw [← hxu, hyv]
      have huv : u = v := by injection hu_eq_v
      subst huv
      subst hxu
      have hu_in_G : u ∈ G := (unsplit_notW₁_of_unsplit_mem_split hw).1
      refine ⟨Walk.nil u hu_in_G, rfl, rfl, fun _ => trivial, ?_⟩
      intro i h
      simp only [Walk.IsBifurcationWithSplit] at h
  | @cons x' y' mid sStep p' ih =>
      intro h_all u v hxu hyv
      subst hxu
      have hmid_in : mid ∈ (Walk.cons
              (G := G.nodeSplittingOn W₁ hW₁)
              mid sStep p').vertices := by
        change mid ∈ (SplitNode.unsplit u :: p'.vertices)
        exact List.mem_cons_of_mem _ (Walk.head_mem_vertices p')
      obtain ⟨m', hmid_eq⟩ := h_all mid hmid_in
      subst hmid_eq
      have h_all_p' : ∀ z ∈ p'.vertices,
          ∃ z' : Node, z = SplitNode.unsplit z' := by
        intro z hz
        exact h_all z (List.mem_cons_of_mem _ hz)
      obtain ⟨q', hq'_len, hq'_vs, hq'_dir, hq'_bif⟩ :=
        ih h_all_p' m' v rfl hyv
      have hStepG : WalkStep G u m' :=
        walkStep_ofSplit_unsplit (hW₁ := hW₁) sStep
      cases hCase : sStep with
      | forwardE h_E =>
          have h_E_G : (u, m') ∈ G.E := by
            change (SplitNode.unsplit u, SplitNode.unsplit m') ∈
                G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
                  W₁.image
                    (fun w => (SplitNode.copy0 w, SplitNode.copy1 w)) at h_E
            rcases Finset.mem_union.mp h_E with hLift | hTrans
            · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
              have h1 : toCopy1 W₁ a'.1 = SplitNode.unsplit u :=
                congrArg Prod.fst ha'_eq
              have h2 : toCopy0 W₁ a'.2 = SplitNode.unsplit m' :=
                congrArg Prod.snd ha'_eq
              have ha'1 : a'.1 = u := node_of_toCopy1_unsplit h1
              have ha'2 : a'.2 = m' := node_of_toCopy0_unsplit h2
              have h_pair : a' = (u, m') := Prod.ext ha'1 ha'2
              rw [← h_pair]; exact ha'_in
            · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
              have : SplitNode.copy0 w = SplitNode.unsplit u :=
                congrArg Prod.fst hw_eq
              cases this
          refine ⟨Walk.cons m' (.forwardE h_E_G) q', ?_, ?_, ?_, ?_⟩
          · change q'.length + 1 = p'.length + 1
            rw [hq'_len]
          · change SplitNode.unsplit u
                :: (q'.vertices.map SplitNode.unsplit)
                = SplitNode.unsplit u :: p'.vertices
            rw [hq'_vs]
          · intro hp_dir
            change q'.IsDirectedWalk
            subst hCase
            exact hq'_dir hp_dir
          · intro i hPi
            match i, p', hPi with
            | 0, .nil _ _, hPi =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
            | 0, .cons _ _ _, hPi =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
            | _ + 1, _, hPi =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
      | backwardE h_E =>
          have h_E_G : (m', u) ∈ G.E := by
            change (SplitNode.unsplit m', SplitNode.unsplit u) ∈
                G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
                  W₁.image
                    (fun w => (SplitNode.copy0 w, SplitNode.copy1 w)) at h_E
            rcases Finset.mem_union.mp h_E with hLift | hTrans
            · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
              have h1 : toCopy1 W₁ a'.1 = SplitNode.unsplit m' :=
                congrArg Prod.fst ha'_eq
              have h2 : toCopy0 W₁ a'.2 = SplitNode.unsplit u :=
                congrArg Prod.snd ha'_eq
              have ha'1 : a'.1 = m' := node_of_toCopy1_unsplit h1
              have ha'2 : a'.2 = u := node_of_toCopy0_unsplit h2
              have h_pair : a' = (m', u) := Prod.ext ha'1 ha'2
              rw [← h_pair]; exact ha'_in
            · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
              have : SplitNode.copy0 w = SplitNode.unsplit m' :=
                congrArg Prod.fst hw_eq
              cases this
          refine ⟨Walk.cons m' (.backwardE h_E_G) q', ?_, ?_, ?_, ?_⟩
          · change q'.length + 1 = p'.length + 1
            rw [hq'_len]
          · change SplitNode.unsplit u
                :: (q'.vertices.map SplitNode.unsplit)
                = SplitNode.unsplit u :: p'.vertices
            rw [hq'_vs]
          · intro hp_dir
            subst hCase
            exact hp_dir.elim
          · intro i hPi
            match i, p', hPi, q', hq'_len, hq'_dir, hq'_bif with
            | 0, .nil _ _, hPi, _, _, _, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
            | 0, .cons _ _ _, _, .nil _ _, hlen, _, _ =>
                simp [Walk.length] at hlen
            | 0, .cons _ _ _, hDir, .cons _ _ _, _, hq'_dir, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hDir
                simp only [Walk.IsBifurcationWithSplit]
                exact hq'_dir hDir
            | k + 1, _, hRec, _, _, _, hq'_bif =>
                simp only [Walk.IsBifurcationWithSplit] at hRec
                simp only [Walk.IsBifurcationWithSplit]
                exact hq'_bif k hRec
      | bidir h_L =>
          have h_L_G : (s(u, m') : Sym2 Node) ∈ G.L := by
            change s(SplitNode.unsplit u, SplitNode.unsplit m') ∈
                G.L.image (Sym2.map (toCopy0 W₁)) at h_L
            obtain ⟨s', hs'_in, hs'_eq⟩ := Finset.mem_image.mp h_L
            induction s' using Sym2.ind with
            | _ b c =>
                change s(toCopy0 W₁ b, toCopy0 W₁ c) =
                       s(SplitNode.unsplit u, SplitNode.unsplit m')
                  at hs'_eq
                rcases Sym2.eq_iff.mp hs'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · have hb : b = u := node_of_toCopy0_unsplit h1
                  have hc : c = m' := node_of_toCopy0_unsplit h2
                  rw [hb, hc] at hs'_in
                  exact hs'_in
                · have hb : b = m' := node_of_toCopy0_unsplit h1
                  have hc : c = u := node_of_toCopy0_unsplit h2
                  rw [hb, hc] at hs'_in
                  rwa [Sym2.eq_swap]
          refine ⟨Walk.cons m' (.bidir h_L_G) q', ?_, ?_, ?_, ?_⟩
          · change q'.length + 1 = p'.length + 1
            rw [hq'_len]
          · change SplitNode.unsplit u
                :: (q'.vertices.map SplitNode.unsplit)
                = SplitNode.unsplit u :: p'.vertices
            rw [hq'_vs]
          · intro hp_dir
            subst hCase
            exact hp_dir.elim
          · intro i hPi
            match i, p', hPi, q', hq'_len, hq'_dir, hq'_bif with
            | 0, .nil _ _, _, .nil _ _, _, _, _ =>
                show True
                trivial
            | 0, .nil _ _, _, .cons _ _ _, hlen, _, _ =>
                simp [Walk.length] at hlen
            | 0, .cons _ _ _, _, .nil _ _, hlen, _, _ =>
                simp [Walk.length] at hlen
            | 0, .cons _ _ _, hDir, .cons _ _ _, _, hq'_dir, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hDir
                simp only [Walk.IsBifurcationWithSplit]
                exact hq'_dir hDir
            | k + 1, _, hPi, _, _, _, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hPi

private lemma all_unsplit_of_interior_W_image_split
    {G : CDMG Node} {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V}
    {x y : SplitNode Node}
    (p : Walk (G.nodeSplittingOn W₁ hW₁) x y)
    (hp_pos : p.length ≥ 1)
    {u v : Node} (hxu : x = SplitNode.unsplit u)
    (hyv : y = SplitNode.unsplit v)
    {W₂ : Finset Node}
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast,
                z ∈ W₂.image SplitNode.unsplit) :
    ∀ z ∈ p.vertices, ∃ z' : Node, z = SplitNode.unsplit z' := by
  intro z hz
  rw [Walk.vertices_eq_head_cons_tail p] at hz
  rcases List.mem_cons.mp hz with h_eq | h_in_tail
  · exact ⟨u, h_eq.trans hxu⟩
  · have h_tail_ne : p.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos p hp_pos
    have h_drop_or_last : z ∈ p.vertices.tail.dropLast ∨ z = y := by
      rw [← List.dropLast_append_getLast h_tail_ne] at h_in_tail
      rcases List.mem_append.mp h_in_tail with h_drop | h_last
      · exact Or.inl h_drop
      · refine Or.inr ?_
        rw [List.mem_singleton] at h_last
        rw [h_last, Walk.tail_getLast_of_pos p hp_pos]
    rcases h_drop_or_last with h_drop | h_last
    · have h_in_image := hp_inter z h_drop
      obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp h_in_image
      exact ⟨w, hw_eq.symm⟩
    · exact ⟨v, h_last.trans hyv⟩

-- ## Refactor replacements — Phase iii.D (toCopy0/1 walk-surgery +
-- E-field equality, Piii34-Piii47).
--
-- This sub-phase ports the asymmetric `toCopy1`-source / `toCopy0`-target
-- machinery that handles the transfer edges `(.copy0 w, .copy1 w)` in the
-- node-splitting carrier.  Body shifts:
--   1. Cons-cell pattern: `Walk.cons _ a hStep _` (4-arg with stored
--      ordered pair `a` and `WalkStep G u a v` witness) becomes
--      `Walk.cons _ s _` (3-arg) with `s : WalkStep G u v`.
--   2. `Or.inl ⟨rfl, Or.inl h_E⟩` style walk-step witnesses (the original
--      WalkStep disjunction-of-disjuncts) become `.forwardE h_E`,
--      `.backwardE h_E`, or `.bidir h_L` directly.
--   3. The `obtain ⟨ha_eq, ha_E, hp'_dir⟩ := hp_dir` triple-destructure on
--      `IsDirectedWalk` collapses to a direct `hRec : p'.IsDirectedWalk`
--      after `cases sStep with | forwardE _ =>`.

private lemma mem_split_of_mem_G_toCopy0 {G : CDMG Node}
    {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V} {v : Node} (hv : v ∈ G) :
    toCopy0 W₁ v ∈ G.nodeSplittingOn W₁ hW₁ := by
  by_cases hvW : v ∈ W₁
  · unfold toCopy0; rw [if_pos hvW]
    exact mem_split_of_mem_W₁_copy0 (hW₁ := hW₁) hvW
  · rw [toCopy0_unsplit_of_notW hvW]
    exact mem_split_of_mem_G_unsplit (hW₁ := hW₁) hv hvW

private lemma toCopy0_inj_node {W₁ : Finset Node} {a b : Node}
    (h : toCopy0 W₁ a = toCopy0 W₁ b) : a = b := by
  unfold toCopy0 at h
  by_cases hWa : a ∈ W₁
  · by_cases hWb : b ∈ W₁
    · rw [if_pos hWa, if_pos hWb] at h; injection h
    · rw [if_pos hWa, if_neg hWb] at h; cases h
  · by_cases hWb : b ∈ W₁
    · rw [if_neg hWa, if_pos hWb] at h; cases h
    · rw [if_neg hWa, if_neg hWb] at h; injection h

private lemma mem_split_V_marg_of_mem_V_W₂_toCopy0 {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    {v : Node} (hv : v ∈ G.V \ W₂) :
    toCopy0 W₁ v ∈ (G.nodeSplittingOn W₁ hW₁).V
      \ W₂.image SplitNode.unsplit := by
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · obtain ⟨hvV, _⟩ := Finset.mem_sdiff.mp hv
    change toCopy0 W₁ v ∈
      (G.V \ W₁).image SplitNode.unsplit ∪ W₁.image SplitNode.copy0
        ∪ W₁.image SplitNode.copy1
    by_cases hvW : v ∈ W₁
    · unfold toCopy0; rw [if_pos hvW]
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_right _ ?_
      exact Finset.mem_image.mpr ⟨v, hvW, rfl⟩
    · rw [toCopy0_unsplit_of_notW hvW]
      refine Finset.mem_union_left _ ?_
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hvV, hvW⟩, rfl⟩
  · intro h
    obtain ⟨w, hw, hw_eq⟩ := Finset.mem_image.mp h
    obtain ⟨_, hv_notW₂⟩ := Finset.mem_sdiff.mp hv
    by_cases hvW : v ∈ W₁
    · unfold toCopy0 at hw_eq; rw [if_pos hvW] at hw_eq; cases hw_eq
    · rw [toCopy0_unsplit_of_notW hvW] at hw_eq
      have : w = v := by injection hw_eq
      exact hv_notW₂ (this ▸ hw)

private lemma toCopy0_ne_copy1 {W₁ : Finset Node} {v w : Node} :
    toCopy0 W₁ v ≠ SplitNode.copy1 w := by
  unfold toCopy0
  by_cases hvW : v ∈ W₁
  · rw [if_pos hvW]; intro h; cases h
  · rw [if_neg hvW]; intro h; cases h

private lemma exists_underlying_of_mem_split_V_marg_not_copy1
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂)
    (x : SplitNode Node)
    (hx : x ∈ (G.nodeSplittingOn W₁ hW₁).V
            \ W₂.image SplitNode.unsplit)
    (h_no_copy1 : ∀ w, x ≠ SplitNode.copy1 w) :
    ∃ v : Node, v ∈ G.V \ W₂ ∧ x = toCopy0 W₁ v := by
  obtain ⟨h_in_split_V, h_notW₂⟩ := Finset.mem_sdiff.mp hx
  change x ∈ (G.V \ W₁).image SplitNode.unsplit
              ∪ W₁.image SplitNode.copy0
            ∪ W₁.image SplitNode.copy1 at h_in_split_V
  rcases Finset.mem_union.mp h_in_split_V with h12 | h_c1
  · rcases Finset.mem_union.mp h12 with h_uns | h_c0
    · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp h_uns
      refine ⟨v, ?_, ?_⟩
      · obtain ⟨hvV, _hvNW₁⟩ := Finset.mem_sdiff.mp hv
        refine Finset.mem_sdiff.mpr ⟨hvV, ?_⟩
        intro hvW₂
        apply h_notW₂
        rw [← hveq]
        exact Finset.mem_image.mpr ⟨v, hvW₂, rfl⟩
      · rw [← hveq, toCopy0_unsplit_of_notW (Finset.mem_sdiff.mp hv).2]
    · obtain ⟨w, hwW₁, hweq⟩ := Finset.mem_image.mp h_c0
      refine ⟨w, ?_, ?_⟩
      · refine Finset.mem_sdiff.mpr ⟨hW₁ hwW₁, ?_⟩
        exact Finset.disjoint_left.mp hDisj hwW₁
      · rw [← hweq]
        unfold toCopy0; rw [if_pos hwW₁]
  · obtain ⟨w, _, hweq⟩ := Finset.mem_image.mp h_c1
    exfalso; exact h_no_copy1 w hweq.symm

set_option maxHeartbeats 800000 in
private lemma exists_lifted_dir_walk_to_split_endTarget
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk →
      u ∉ W₁ →
      (∀ x ∈ p.vertices.tail.dropLast, x ∈ W₂) →
      ∃ (s : Walk (G.nodeSplittingOn W₁ hW₁)
              (SplitNode.unsplit u) (toCopy0 W₁ v)),
        s.IsDirectedWalk ∧ s.length = p.length ∧
        s.vertices = p.vertices.map (toCopy0 W₁)
  | _, _, .nil w hw, _, hu_notW, _ => by
      have h_eq : toCopy0 W₁ w = SplitNode.unsplit w :=
        toCopy0_unsplit_of_notW hu_notW
      rw [h_eq]
      refine ⟨Walk.nil (SplitNode.unsplit w)
        (mem_split_of_mem_G_unsplit (hW₁ := hW₁) hw hu_notW),
        trivial, rfl, ?_⟩
      change [SplitNode.unsplit w] = [toCopy0 W₁ w]
      rw [h_eq]
  | u, _, .cons w sStep (.nil _ hw), hp_dir, hu_notW, _ => by
      cases sStep with
      | backwardE _ => exact hp_dir.elim
      | bidir _ => exact hp_dir.elim
      | forwardE h_E =>
          have h_lifted_E : (toCopy1 W₁ u, toCopy0 W₁ w) ∈
              (G.nodeSplittingOn W₁ hW₁).E :=
            lifted_E_in_split_E_generic h_E
          have h_u_lift : toCopy1 W₁ u = SplitNode.unsplit u :=
            toCopy1_unsplit_of_notW hu_notW
          rw [h_u_lift] at h_lifted_E
          have h_u_lift0 : toCopy0 W₁ u = SplitNode.unsplit u :=
            toCopy0_unsplit_of_notW hu_notW
          have hw_in_split : toCopy0 W₁ w
              ∈ G.nodeSplittingOn W₁ hW₁ :=
            mem_split_of_mem_G_toCopy0 (hW₁ := hW₁) hw
          refine ⟨Walk.cons (toCopy0 W₁ w)
            (.forwardE h_lifted_E)
            (Walk.nil (toCopy0 W₁ w) hw_in_split), ?_, rfl, ?_⟩
          · exact (trivial : True)
          · change SplitNode.unsplit u :: [toCopy0 W₁ w]
                  = toCopy0 W₁ u :: [toCopy0 W₁ w]
            rw [h_u_lift0]
  | u, v, .cons vMid sStep (.cons vMid' sStep' p''), hp_dir, hu_notW, h_inter => by
      cases sStep with
      | backwardE _ => exact hp_dir.elim
      | bidir _ => exact hp_dir.elim
      | forwardE h_E =>
          have hp'_dir : (Walk.cons (G := G) vMid' sStep' p'').IsDirectedWalk :=
            hp_dir
          have hvMid_inW₂ : vMid ∈ W₂ := by
            apply h_inter
            change vMid ∈ (vMid :: p''.vertices).dropLast
            have hne : (p''.vertices : List Node) ≠ [] :=
              Walk.vertices_ne_nil _
            rw [List.dropLast_cons_of_ne_nil hne]
            exact List.mem_cons_self
          have hvMid_notW : vMid ∉ W₁ :=
            Finset.disjoint_left.mp hDisj.symm hvMid_inW₂
          have h_lifted_E : (toCopy1 W₁ u, toCopy0 W₁ vMid) ∈
              (G.nodeSplittingOn W₁ hW₁).E :=
            lifted_E_in_split_E_generic h_E
          have h_u_lift : toCopy1 W₁ u = SplitNode.unsplit u :=
            toCopy1_unsplit_of_notW hu_notW
          have h_vMid_lift : toCopy0 W₁ vMid
              = SplitNode.unsplit vMid :=
            toCopy0_unsplit_of_notW hvMid_notW
          rw [h_u_lift, h_vMid_lift] at h_lifted_E
          have h_inter_p' :
              ∀ x ∈ (Walk.cons (G := G) vMid' sStep' p'').vertices.tail.dropLast,
                x ∈ W₂ := by
            intro x hx
            apply h_inter
            change x ∈ (vMid :: p''.vertices).dropLast
            have hne : (p''.vertices : List Node) ≠ [] :=
              Walk.vertices_ne_nil _
            rw [List.dropLast_cons_of_ne_nil hne]
            refine List.mem_cons_of_mem _ ?_
            change x ∈ p''.vertices.dropLast
            exact hx
          obtain ⟨s', hs'_dir, hs'_len, hs'_verts⟩ :=
            exists_lifted_dir_walk_to_split_endTarget hW₁ hDisj
              (Walk.cons vMid' sStep' p'') hp'_dir hvMid_notW h_inter_p'
          have h_u_lift0 : toCopy0 W₁ u = SplitNode.unsplit u :=
            toCopy0_unsplit_of_notW hu_notW
          refine ⟨Walk.cons (SplitNode.unsplit vMid)
            (.forwardE h_lifted_E) s', ?_, ?_, ?_⟩
          · exact hs'_dir
          · change s'.length + 1
                = (Walk.cons (G := G) vMid' sStep' p'').length + 1
            rw [hs'_len]
          · change SplitNode.unsplit u :: s'.vertices
                = (u :: vMid :: p''.vertices).map (toCopy0 W₁)
            rw [hs'_verts, ← h_u_lift0]
            rfl

-- Centerpiece bifurcation ascent.  Three sub-cases in the cons step
-- (matching `IsBifurcationWithSplit` shape):
--   * `i = 0, p' = nil`: single bidirected edge (`.bidir` step + `.nil` tail).
--   * `i = 0, p' = cons`: hinge + directed right-arm (uses Piii39).
--   * `i = k+1, p' anything`: left-arm reverse-E step + recurse via ih.
-- The original packs hinge information into `Or.inl ⟨ha_vu, ha_E⟩` (backward
-- E hinge) vs `Or.inl ⟨ha_uv, ha_L⟩` (bidirected hinge); the refactor reads
-- those directly off `sStep`'s constructor (`.backwardE h_E` vs `.bidir h_L`).
-- We case-split on the outer `sStep` first (so the `IsBifurcationWithSplit`
-- equational lemmas can fire), then on the inner walk shape.
set_option maxHeartbeats 1600000 in
private lemma exists_lifted_bifWithSplit_to_split
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {u v : Node} (p : Walk G u v) (i : ℕ),
      p.IsBifurcationWithSplit i →
      (∀ x ∈ p.vertices.tail.dropLast, x ∈ W₂) →
      ∃ (q : Walk (G.nodeSplittingOn W₁ hW₁)
              (toCopy0 W₁ u) (toCopy0 W₁ v)),
        q.IsBifurcationWithSplit i ∧ q.length = p.length ∧
        q.vertices = p.vertices.map (toCopy0 W₁)
  | _, _, .nil _ _, _, hi, _ => by
      simp only [Walk.IsBifurcationWithSplit] at hi
  | u, _, .cons w sStep (.nil _ hw), 0, hi, _ => by
      cases sStep with
      | forwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | backwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | bidir h_L =>
          have h_lifted_L : s(toCopy0 W₁ u, toCopy0 W₁ w) ∈
              (G.nodeSplittingOn W₁ hW₁).L :=
            lifted_L_in_split_L_generic h_L
          have hw_in_split : toCopy0 W₁ w
              ∈ G.nodeSplittingOn W₁ hW₁ :=
            mem_split_of_mem_G_toCopy0 (hW₁ := hW₁) hw
          refine ⟨Walk.cons (toCopy0 W₁ w)
            (.bidir h_lifted_L)
            (Walk.nil (toCopy0 W₁ w) hw_in_split), ?_, rfl, ?_⟩
          · show True
            trivial
          · rfl
  | u, _, .cons vMid sStep (.cons vMid' sStep' p''), 0, hi, h_inter => by
      have hvMid_inW₂ : vMid ∈ W₂ := by
        apply h_inter
        change vMid ∈ (vMid :: p''.vertices).dropLast
        have hne : (p''.vertices : List Node) ≠ [] :=
          Walk.vertices_ne_nil _
        rw [List.dropLast_cons_of_ne_nil hne]
        exact List.mem_cons_self
      have hvMid_notW : vMid ∉ W₁ :=
        Finset.disjoint_left.mp hDisj.symm hvMid_inW₂
      have h_vMid_lift : toCopy0 W₁ vMid = SplitNode.unsplit vMid :=
        toCopy0_unsplit_of_notW hvMid_notW
      have h_vMid_lift1 : toCopy1 W₁ vMid = SplitNode.unsplit vMid :=
        toCopy1_unsplit_of_notW hvMid_notW
      -- Case-split on outer sStep first, then inner sStep'.
      cases sStep with
      | forwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | backwardE h_E =>
          -- hi : (.cons _ (.backwardE _) (.cons _ sStep' p'')).IsBifurcationWithSplit 0
          --    = (.cons _ sStep' p'').IsDirectedWalk
          -- For this to hold, sStep' must be .forwardE.
          have hp'_dir :
              (Walk.cons (G := G) vMid' sStep' p'').IsDirectedWalk := hi
          have h_in_E_pair : (vMid, u) ∈ G.E := h_E
          have h_lifted_E :
              (toCopy1 W₁ vMid, toCopy0 W₁ u) ∈
                (G.nodeSplittingOn W₁ hW₁).E :=
            lifted_E_in_split_E_generic h_in_E_pair
          rw [h_vMid_lift1] at h_lifted_E
          cases sStep' with
          | backwardE _ => exact hp'_dir.elim
          | bidir _ => exact hp'_dir.elim
          | forwardE h_E' =>
              have h_in_E_pair' : (vMid, vMid') ∈ G.E := h_E'
              have h_lifted_E' :
                  (toCopy1 W₁ vMid, toCopy0 W₁ vMid') ∈
                    (G.nodeSplittingOn W₁ hW₁).E :=
                lifted_E_in_split_E_generic h_in_E_pair'
              rw [h_vMid_lift1] at h_lifted_E'
              -- Case-split on p'' (nil vs cons) via `cases`.
              cases p'' with
              | nil =>
                  rename_i v_target hw_pp
                  have hw_in_split : toCopy0 W₁ v_target
                      ∈ G.nodeSplittingOn W₁ hW₁ :=
                    mem_split_of_mem_G_toCopy0 (hW₁ := hW₁) hw_pp
                  refine ⟨Walk.cons (SplitNode.unsplit vMid)
                    (.backwardE h_lifted_E)
                    (Walk.cons (toCopy0 W₁ v_target)
                      (.forwardE h_lifted_E')
                      (Walk.nil (toCopy0 W₁ v_target) hw_in_split)),
                    ?_, rfl, ?_⟩
                  · show True; trivial
                  · change toCopy0 W₁ u
                          :: SplitNode.unsplit vMid :: [toCopy0 W₁ v_target]
                      = toCopy0 W₁ u
                          :: toCopy0 W₁ vMid :: [toCopy0 W₁ v_target]
                    rw [← h_vMid_lift]
              | cons vMid'' sStep'' p''' =>
                  have hvMid'_inW₂ : vMid' ∈ W₂ := by
                    apply h_inter
                    change vMid' ∈ (vMid :: vMid' :: p'''.vertices).dropLast
                    have hne1 : ((vMid' :: p'''.vertices) : List Node) ≠ [] := by simp
                    rw [List.dropLast_cons_of_ne_nil hne1]
                    refine List.mem_cons_of_mem _ ?_
                    have hne2 : (p'''.vertices : List Node) ≠ [] :=
                      Walk.vertices_ne_nil _
                    rw [List.dropLast_cons_of_ne_nil hne2]
                    exact List.mem_cons_self
                  have hvMid'_notW : vMid' ∉ W₁ :=
                    Finset.disjoint_left.mp hDisj.symm hvMid'_inW₂
                  have h_vMid'_lift : toCopy0 W₁ vMid'
                      = SplitNode.unsplit vMid' :=
                    toCopy0_unsplit_of_notW hvMid'_notW
                  rw [h_vMid'_lift] at h_lifted_E'
                  have hp''_dir :
                      (Walk.cons (G := G) vMid'' sStep'' p''').IsDirectedWalk := hp'_dir
                  have h_inter_p''_for_helper :
                      ∀ x ∈ (Walk.cons (G := G) vMid'' sStep'' p''').vertices.tail.dropLast,
                        x ∈ W₂ := by
                    intro x hx
                    apply h_inter
                    change x ∈ (vMid :: vMid' :: p'''.vertices).dropLast
                    have hne1 : ((vMid' :: p'''.vertices) : List Node) ≠ [] := by simp
                    rw [List.dropLast_cons_of_ne_nil hne1]
                    refine List.mem_cons_of_mem _ ?_
                    have hne2 : (p'''.vertices : List Node) ≠ [] :=
                      Walk.vertices_ne_nil _
                    rw [List.dropLast_cons_of_ne_nil hne2]
                    refine List.mem_cons_of_mem _ ?_
                    change x ∈ p'''.vertices.dropLast
                    exact hx
                  obtain ⟨t', ht'_dir, ht'_len, ht'_verts⟩ :=
                    exists_lifted_dir_walk_to_split_endTarget hW₁ hDisj
                      (Walk.cons vMid'' sStep'' p''') hp''_dir hvMid'_notW
                      h_inter_p''_for_helper
                  refine ⟨Walk.cons (SplitNode.unsplit vMid)
                    (.backwardE h_lifted_E)
                    (Walk.cons (SplitNode.unsplit vMid')
                      (.forwardE h_lifted_E') t'), ?_, ?_, ?_⟩
                  · show t'.IsDirectedWalk
                    exact ht'_dir
                  · show t'.length + 1 + 1
                        = (Walk.cons (G := G) vMid'' sStep'' p''').length + 1 + 1
                    rw [ht'_len]
                  · show toCopy0 W₁ u
                            :: SplitNode.unsplit vMid :: t'.vertices
                        = toCopy0 W₁ u
                            :: toCopy0 W₁ vMid
                              :: (Walk.cons (G := G) vMid'' sStep'' p''').vertices.map (toCopy0 W₁)
                    rw [ht'_verts, ← h_vMid_lift]
      | bidir h_L =>
          have hp'_dir :
              (Walk.cons (G := G) vMid' sStep' p'').IsDirectedWalk := hi
          have h_in_L_pair : s(u, vMid) ∈ G.L := h_L
          have h_lifted_L : s(toCopy0 W₁ u, toCopy0 W₁ vMid) ∈
              (G.nodeSplittingOn W₁ hW₁).L :=
            lifted_L_in_split_L_generic h_in_L_pair
          rw [h_vMid_lift] at h_lifted_L
          cases sStep' with
          | backwardE _ => exact hp'_dir.elim
          | bidir _ => exact hp'_dir.elim
          | forwardE h_E' =>
              have h_in_E_pair' : (vMid, vMid') ∈ G.E := h_E'
              have h_lifted_E' :
                  (toCopy1 W₁ vMid, toCopy0 W₁ vMid') ∈
                    (G.nodeSplittingOn W₁ hW₁).E :=
                lifted_E_in_split_E_generic h_in_E_pair'
              rw [h_vMid_lift1] at h_lifted_E'
              cases p'' with
              | nil =>
                  rename_i v_target hw_pp
                  have hw_in_split : toCopy0 W₁ v_target
                      ∈ G.nodeSplittingOn W₁ hW₁ :=
                    mem_split_of_mem_G_toCopy0 (hW₁ := hW₁) hw_pp
                  refine ⟨Walk.cons (SplitNode.unsplit vMid)
                    (.bidir h_lifted_L)
                    (Walk.cons (toCopy0 W₁ v_target)
                      (.forwardE h_lifted_E')
                      (Walk.nil (toCopy0 W₁ v_target) hw_in_split)),
                    ?_, rfl, ?_⟩
                  · show True; trivial
                  · change toCopy0 W₁ u
                          :: SplitNode.unsplit vMid :: [toCopy0 W₁ v_target]
                      = toCopy0 W₁ u
                          :: toCopy0 W₁ vMid :: [toCopy0 W₁ v_target]
                    rw [← h_vMid_lift]
              | cons vMid'' sStep'' p''' =>
                  have hvMid'_inW₂ : vMid' ∈ W₂ := by
                    apply h_inter
                    change vMid' ∈ (vMid :: vMid' :: p'''.vertices).dropLast
                    have hne1 : ((vMid' :: p'''.vertices) : List Node) ≠ [] := by simp
                    rw [List.dropLast_cons_of_ne_nil hne1]
                    refine List.mem_cons_of_mem _ ?_
                    have hne2 : (p'''.vertices : List Node) ≠ [] :=
                      Walk.vertices_ne_nil _
                    rw [List.dropLast_cons_of_ne_nil hne2]
                    exact List.mem_cons_self
                  have hvMid'_notW : vMid' ∉ W₁ :=
                    Finset.disjoint_left.mp hDisj.symm hvMid'_inW₂
                  have h_vMid'_lift : toCopy0 W₁ vMid'
                      = SplitNode.unsplit vMid' :=
                    toCopy0_unsplit_of_notW hvMid'_notW
                  rw [h_vMid'_lift] at h_lifted_E'
                  have hp''_dir :
                      (Walk.cons (G := G) vMid'' sStep'' p''').IsDirectedWalk := hp'_dir
                  have h_inter_p''_for_helper :
                      ∀ x ∈ (Walk.cons (G := G) vMid'' sStep'' p''').vertices.tail.dropLast,
                        x ∈ W₂ := by
                    intro x hx
                    apply h_inter
                    change x ∈ (vMid :: vMid' :: p'''.vertices).dropLast
                    have hne1 : ((vMid' :: p'''.vertices) : List Node) ≠ [] := by simp
                    rw [List.dropLast_cons_of_ne_nil hne1]
                    refine List.mem_cons_of_mem _ ?_
                    have hne2 : (p'''.vertices : List Node) ≠ [] :=
                      Walk.vertices_ne_nil _
                    rw [List.dropLast_cons_of_ne_nil hne2]
                    refine List.mem_cons_of_mem _ ?_
                    change x ∈ p'''.vertices.dropLast
                    exact hx
                  obtain ⟨t', ht'_dir, ht'_len, ht'_verts⟩ :=
                    exists_lifted_dir_walk_to_split_endTarget hW₁ hDisj
                      (Walk.cons vMid'' sStep'' p''') hp''_dir hvMid'_notW
                      h_inter_p''_for_helper
                  refine ⟨Walk.cons (SplitNode.unsplit vMid)
                    (.bidir h_lifted_L)
                    (Walk.cons (SplitNode.unsplit vMid')
                      (.forwardE h_lifted_E') t'), ?_, ?_, ?_⟩
                  · show t'.IsDirectedWalk
                    exact ht'_dir
                  · show t'.length + 1 + 1
                        = (Walk.cons (G := G) vMid'' sStep'' p''').length + 1 + 1
                    rw [ht'_len]
                  · show toCopy0 W₁ u
                            :: SplitNode.unsplit vMid :: t'.vertices
                        = toCopy0 W₁ u
                            :: toCopy0 W₁ vMid
                              :: (Walk.cons (G := G) vMid'' sStep'' p''').vertices.map (toCopy0 W₁)
                    rw [ht'_verts, ← h_vMid_lift]
  | u, _, .cons vMid sStep (.nil _ _), k + 1, hi, _ => by
      cases sStep with
      | forwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | backwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | bidir _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
  | u, _, .cons vMid sStep (.cons vMid' sStep' p''), k + 1, hi, h_inter => by
      have hvMid_inW₂ : vMid ∈ W₂ := by
        apply h_inter
        change vMid ∈ (vMid :: p''.vertices).dropLast
        have hne : (p''.vertices : List Node) ≠ [] :=
          Walk.vertices_ne_nil _
        rw [List.dropLast_cons_of_ne_nil hne]
        exact List.mem_cons_self
      have hvMid_notW : vMid ∉ W₁ :=
        Finset.disjoint_left.mp hDisj.symm hvMid_inW₂
      have h_vMid_lift : toCopy0 W₁ vMid = SplitNode.unsplit vMid :=
        toCopy0_unsplit_of_notW hvMid_notW
      have h_vMid_lift1 : toCopy1 W₁ vMid = SplitNode.unsplit vMid :=
        toCopy1_unsplit_of_notW hvMid_notW
      cases sStep with
      | forwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | bidir _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | backwardE h_E =>
          have h_in_E_pair : (vMid, u) ∈ G.E := h_E
          have h_lifted_E_raw : (toCopy1 W₁ vMid, toCopy0 W₁ u) ∈
              (G.nodeSplittingOn W₁ hW₁).E :=
            lifted_E_in_split_E_generic h_in_E_pair
          have h_lifted_E : (toCopy0 W₁ vMid, toCopy0 W₁ u) ∈
              (G.nodeSplittingOn W₁ hW₁).E := by
            rw [h_vMid_lift1, ← h_vMid_lift] at h_lifted_E_raw
            exact h_lifted_E_raw
          have hi_rec : (Walk.cons (G := G) vMid' sStep' p'').IsBifurcationWithSplit k := by
            simp only [Walk.IsBifurcationWithSplit] at hi
            exact hi
          have h_inter_p' :
              ∀ x ∈ (Walk.cons (G := G) vMid' sStep' p'').vertices.tail.dropLast,
                x ∈ W₂ := by
            intro x hx
            apply h_inter
            change x ∈ (vMid :: p''.vertices).dropLast
            have hne : (p''.vertices : List Node) ≠ [] :=
              Walk.vertices_ne_nil _
            rw [List.dropLast_cons_of_ne_nil hne]
            refine List.mem_cons_of_mem _ ?_
            change x ∈ p''.vertices.dropLast
            exact hx
          obtain ⟨s', hs'_split, hs'_len, hs'_verts⟩ :=
            exists_lifted_bifWithSplit_to_split hW₁ hDisj
              (Walk.cons vMid' sStep' p'') k hi_rec h_inter_p'
          refine ⟨Walk.cons (toCopy0 W₁ vMid)
            (.backwardE h_lifted_E) s', ?_, ?_, ?_⟩
          · simp only [Walk.IsBifurcationWithSplit]
            exact hs'_split
          · change s'.length + 1
                = (Walk.cons (G := G) vMid' sStep' p'').length + 1
            rw [hs'_len]
          · change toCopy0 W₁ u :: s'.vertices
                = toCopy0 W₁ u
                    :: (Walk.cons (G := G) vMid' sStep' p'').vertices.map (toCopy0 W₁)
            rw [hs'_verts]

private lemma exists_lifted_bif_to_split
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsBifurcation →
      (∀ x ∈ p.vertices.tail.dropLast, x ∈ W₂) →
      ∃ (q : Walk (G.nodeSplittingOn W₁ hW₁)
              (toCopy0 W₁ u) (toCopy0 W₁ v)),
        q.IsBifurcation ∧
        (∀ x ∈ q.vertices.tail.dropLast,
          x ∈ W₂.image SplitNode.unsplit) := by
  intro u v p hp_bif h_inter
  obtain ⟨hne, hu_tail, hv_drop, i, hi⟩ := hp_bif
  obtain ⟨q, hq_split, _hq_len, hq_verts⟩ :=
    exists_lifted_bifWithSplit_to_split hW₁ hDisj p i hi h_inter
  have h_tail_map : ∀ (l : List Node),
      (l.map (toCopy0 W₁)).tail = l.tail.map (toCopy0 W₁) := by
    intro l; cases l with
    | nil => rfl
    | cons _ _ => rfl
  have h_dropLast_map : ∀ (l : List Node),
      (l.map (toCopy0 W₁)).dropLast = l.dropLast.map (toCopy0 W₁) := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
        cases xs with
        | nil => rfl
        | cons y ys =>
            simp only [List.map_cons, List.dropLast_cons₂]
            change _ :: (((y :: ys).map (toCopy0 W₁)).dropLast)
                = _ :: ((y :: ys).dropLast.map (toCopy0 W₁))
            rw [ih]
  refine ⟨q, ⟨?_, ?_, ?_, i, hq_split⟩, ?_⟩
  · intro h_eq
    exact hne (toCopy0_inj_node h_eq)
  · intro h_mem
    rw [hq_verts, h_tail_map] at h_mem
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h_mem
    have : a = u := toCopy0_inj_node ha_eq
    exact hu_tail (this ▸ ha_in)
  · intro h_mem
    rw [hq_verts, h_dropLast_map] at h_mem
    obtain ⟨a, ha_in, ha_eq⟩ := List.mem_map.mp h_mem
    have : a = v := toCopy0_inj_node ha_eq
    exact hv_drop (this ▸ ha_in)
  · intro x hx
    have h_interior_map :
        q.vertices.tail.dropLast
          = p.vertices.tail.dropLast.map (toCopy0 W₁) := by
      rw [hq_verts, h_tail_map, h_dropLast_map]
    rw [h_interior_map] at hx
    obtain ⟨y, hy_in, hy_eq⟩ := List.mem_map.mp hx
    have hy_inW₂ : y ∈ W₂ := h_inter y hy_in
    have hy_notW₁ : y ∉ W₁ := Finset.disjoint_left.mp hDisj.symm hy_inW₂
    have h_y_lift : toCopy0 W₁ y = SplitNode.unsplit y :=
      toCopy0_unsplit_of_notW hy_notW₁
    rw [← hy_eq, h_y_lift]
    exact Finset.mem_image.mpr ⟨y, hy_inW₂, rfl⟩

-- The only outgoing edge from `.copy0 w` in `split.E` is either the
-- transfer edge or a lifted G-edge with `toCopy1 W₁ a = .copy0 w` —
-- but `toCopy1 W₁ a ∈ {.unsplit a, .copy1 a}`, never `.copy0`, so
-- the lifted-edge case is impossible.
set_option maxHeartbeats 800000 in
private lemma walk_copy0_target_copy1 {G : CDMG Node}
    {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V} {W₂ : Finset Node} (hDisj : Disjoint W₁ W₂)
    {w : Node} (hwW₁ : w ∈ W₁) {y : SplitNode Node}
    (p : Walk (G.nodeSplittingOn W₁ hW₁) (SplitNode.copy0 w) y)
    (hp_dir : p.IsDirectedWalk)
    (hp_pos : p.length ≥ 1)
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast,
      z ∈ W₂.image SplitNode.unsplit) :
    y = SplitNode.copy1 w := by
  cases p with
  | nil _ _ => simp [Walk.length] at hp_pos
  | @cons _ _ mid sStep p' =>
      cases sStep with
      | backwardE _ => exact hp_dir.elim
      | bidir _ => exact hp_dir.elim
      | forwardE h_E =>
          have hp'_dir : p'.IsDirectedWalk := hp_dir
          change (SplitNode.copy0 w, mid) ∈
              G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
                W₁.image
                  (fun w' => (SplitNode.copy0 w', SplitNode.copy1 w'))
            at h_E
          rcases Finset.mem_union.mp h_E with hLift | hTrans
          · obtain ⟨e', _, he'_eq⟩ := Finset.mem_image.mp hLift
            have hcontra : toCopy1 W₁ e'.1 = SplitNode.copy0 w :=
              congrArg Prod.fst he'_eq
            unfold toCopy1 at hcontra
            by_cases hW : e'.1 ∈ W₁
            · rw [if_pos hW] at hcontra; cases hcontra
            · rw [if_neg hW] at hcontra; cases hcontra
          · obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp hTrans
            have h1 : SplitNode.copy0 w' = SplitNode.copy0 w :=
              congrArg Prod.fst hw'_eq
            have h2 : SplitNode.copy1 w' = mid :=
              congrArg Prod.snd hw'_eq
            have hww' : w' = w := by injection h1
            rw [hww'] at h2
            have hmid : mid = SplitNode.copy1 w := h2.symm
            subst hmid
            cases p' with
            | nil _ _ => rfl
            | @cons _ _ mid2 sStep2 p2 =>
                have h_pv_ne : p2.vertices ≠ [] :=
                  Walk.vertices_ne_nil p2
                have h_w_inter : SplitNode.copy1 w ∈
                    (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                      (SplitNode.copy1 w) (.forwardE h_E)
                      (Walk.cons mid2 sStep2 p2)).vertices.tail.dropLast := by
                  change SplitNode.copy1 w ∈ (SplitNode.copy0 w
                    :: SplitNode.copy1 w :: p2.vertices).tail.dropLast
                  rw [show (SplitNode.copy0 w :: SplitNode.copy1 w
                              :: p2.vertices : List _).tail
                          = SplitNode.copy1 w :: p2.vertices from rfl]
                  rw [List.dropLast_cons_of_ne_nil h_pv_ne]
                  exact List.mem_cons_self
                have h_in_image := hp_inter (SplitNode.copy1 w) h_w_inter
                obtain ⟨_, _, hw''_eq⟩ := Finset.mem_image.mp h_in_image
                cases hw''_eq

set_option maxHeartbeats 800000 in
private lemma walk_G_lift_to_split
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {u v : Node} (q : Walk G u v),
      q.IsDirectedWalk →
      q.length ≥ 1 →
      (∀ z ∈ q.vertices.tail.dropLast, z ∈ W₂) →
      ∃ p : Walk (G.nodeSplittingOn W₁ hW₁)
              (toCopy1 W₁ u) (toCopy0 W₁ v),
        p.IsDirectedWalk ∧ p.length = q.length ∧
        (∀ x ∈ p.vertices.tail.dropLast,
          x ∈ W₂.image SplitNode.unsplit)
  | _, _, .nil _ _, _, hpos, _ => by simp [Walk.length] at hpos
  | u, _, .cons w sStep (.nil _ hw_in), hq_dir, _, _ => by
      cases sStep with
      | backwardE _ => exact hq_dir.elim
      | bidir _ => exact hq_dir.elim
      | forwardE h_E =>
          have h_uw_E : (u, w) ∈ G.E := h_E
          have h_lifted_E : (toCopy1 W₁ u, toCopy0 W₁ w) ∈
              (G.nodeSplittingOn W₁ hW₁).E :=
            lifted_E_in_split_E_generic h_uw_E
          have h_w_in_split : toCopy0 W₁ w ∈ G.nodeSplittingOn W₁ hW₁ :=
            mem_split_of_mem_G_toCopy0 (hW₁ := hW₁) hw_in
          refine ⟨Walk.cons (toCopy0 W₁ w) (.forwardE h_lifted_E)
            (Walk.nil (toCopy0 W₁ w) h_w_in_split),
            trivial, by change 1 = 0 + 1; omega, ?_⟩
          intro x hx
          simp [Walk.vertices, List.tail, List.dropLast] at hx
  | u, _, .cons w sStep (.cons w2 sStep2 q2), hq_dir, _, hq_inter => by
      cases sStep with
      | backwardE _ => exact hq_dir.elim
      | bidir _ => exact hq_dir.elim
      | forwardE h_E =>
          have h_uw_E : (u, w) ∈ G.E := h_E
          have h_lifted_E : (toCopy1 W₁ u, toCopy0 W₁ w) ∈
              (G.nodeSplittingOn W₁ hW₁).E :=
            lifted_E_in_split_E_generic h_uw_E
          have h_qv_ne : q2.vertices ≠ [] :=
            Walk.vertices_ne_nil q2
          have hw_inW₂ : w ∈ W₂ := by
            apply hq_inter
            change w ∈ (w :: q2.vertices).dropLast
            rw [List.dropLast_cons_of_ne_nil h_qv_ne]
            exact List.mem_cons_self
          have hw_notW₁ : w ∉ W₁ :=
            Finset.disjoint_left.mp hDisj.symm hw_inW₂
          have h_w_lift0 : toCopy0 W₁ w = SplitNode.unsplit w :=
            toCopy0_unsplit_of_notW hw_notW₁
          have h_w_lift1 : toCopy1 W₁ w = SplitNode.unsplit w :=
            toCopy1_unsplit_of_notW hw_notW₁
          have hq'_dir : (Walk.cons (G := G) w2 sStep2 q2).IsDirectedWalk :=
            hq_dir
          have hq'_inter_aux :
              ∀ z ∈ (Walk.cons (G := G) w2 sStep2 q2).vertices.tail.dropLast,
                z ∈ W₂ := by
            intro z hz
            apply hq_inter
            change z ∈ (w :: q2.vertices).dropLast
            rw [List.dropLast_cons_of_ne_nil h_qv_ne]
            refine List.mem_cons_of_mem _ ?_
            change z ∈ q2.vertices.dropLast
            exact hz
          have h_q'_pos :
              (Walk.cons (G := G) w2 sStep2 q2).length ≥ 1 := by
            change q2.length + 1 ≥ 1; omega
          obtain ⟨p', hp'_dir, hp'_len, hp'_inter⟩ :=
            walk_G_lift_to_split hW₁ hDisj
              (Walk.cons w2 sStep2 q2) hq'_dir h_q'_pos hq'_inter_aux
          have h_lifted_E' : (toCopy1 W₁ u, toCopy1 W₁ w) ∈
              (G.nodeSplittingOn W₁ hW₁).E := by
            rw [h_w_lift1, ← h_w_lift0]; exact h_lifted_E
          refine ⟨Walk.cons (toCopy1 W₁ w) (.forwardE h_lifted_E') p',
            hp'_dir, ?_, ?_⟩
          · change p'.length + 1
                = (Walk.cons (G := G) w2 sStep2 q2).length + 1
            rw [hp'_len]
          · intro x hx
            change x ∈ p'.vertices.dropLast at hx
            have h_p'_pos : p'.length ≥ 1 := by
              rw [hp'_len]; exact h_q'_pos
            have h_p'_tail_ne : p'.vertices.tail ≠ [] :=
              Walk.tail_vertices_ne_nil_of_pos p' h_p'_pos
            rw [Walk.vertices_eq_head_cons_tail p'] at hx
            rw [List.dropLast_cons_of_ne_nil h_p'_tail_ne] at hx
            rcases List.mem_cons.mp hx with hx_head | hx_tail
            · rw [hx_head]; rw [h_w_lift1]
              exact Finset.mem_image.mpr ⟨w, hw_inW₂, rfl⟩
            · exact hp'_inter x hx_tail

set_option maxHeartbeats 800000 in
private lemma walk_split_descend_to_G
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {x y : SplitNode Node}
      (p : Walk (G.nodeSplittingOn W₁ hW₁) x y),
      p.IsDirectedWalk →
      (∀ z ∈ p.vertices.tail.dropLast,
        z ∈ W₂.image SplitNode.unsplit) →
      ∀ {u v : Node}, x = toCopy1 W₁ u → y = toCopy0 W₁ v →
      ∃ q : Walk G u v, q.IsDirectedWalk ∧
        q.length = p.length ∧
        (∀ z ∈ q.vertices.tail.dropLast, z ∈ W₂)
  | _, _, .nil w hw, _, _, u, v, hxu, hyv => by
      have hCopy_eq : toCopy1 W₁ u = toCopy0 W₁ v := hxu.symm.trans hyv
      by_cases huW : u ∈ W₁
      · have h1 : toCopy1 W₁ u = SplitNode.copy1 u := by
          unfold toCopy1; rw [if_pos huW]
        rw [h1] at hCopy_eq
        unfold toCopy0 at hCopy_eq
        by_cases hvW : v ∈ W₁
        · rw [if_pos hvW] at hCopy_eq; cases hCopy_eq
        · rw [if_neg hvW] at hCopy_eq; cases hCopy_eq
      · have h1 : toCopy1 W₁ u = SplitNode.unsplit u :=
          toCopy1_unsplit_of_notW huW
        rw [h1] at hCopy_eq
        unfold toCopy0 at hCopy_eq
        by_cases hvW : v ∈ W₁
        · rw [if_pos hvW] at hCopy_eq; cases hCopy_eq
        · rw [if_neg hvW] at hCopy_eq
          have huv : u = v := by injection hCopy_eq
          subst huv
          have hu_G : u ∈ G := by
            have hu_in_split : SplitNode.unsplit u
                ∈ G.nodeSplittingOn W₁ hW₁ := by
              rw [← h1, ← hxu]; exact hw
            exact mem_G_of_unsplit_mem_split hW₁ hu_in_split
          refine ⟨Walk.nil u hu_G, trivial, rfl, ?_⟩
          intro x hx
          simp [Walk.vertices, List.tail, List.dropLast] at hx
  | x, _, .cons mid sStep (.nil _ hmid_in), hp_dir, _, u, v, hxu, hyv => by
      cases sStep with
      | backwardE _ => exact hp_dir.elim
      | bidir _ => exact hp_dir.elim
      | forwardE h_E =>
          change (x, mid) ∈
              G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
                W₁.image
                  (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
            at h_E
          rcases Finset.mem_union.mp h_E with hLift | hTrans
          · obtain ⟨e', he'_E, he'_eq⟩ := Finset.mem_image.mp hLift
            have h_e1 : toCopy1 W₁ e'.1 = x := congrArg Prod.fst he'_eq
            have h_e2 : toCopy0 W₁ e'.2 = mid := congrArg Prod.snd he'_eq
            rw [hxu] at h_e1
            have he'1 : e'.1 = u := by
              unfold toCopy1 at h_e1
              by_cases hW₁_e' : e'.1 ∈ W₁
              · by_cases hW₁_u : u ∈ W₁
                · rw [if_pos hW₁_e', if_pos hW₁_u] at h_e1; injection h_e1
                · rw [if_pos hW₁_e', if_neg hW₁_u] at h_e1; cases h_e1
              · by_cases hW₁_u : u ∈ W₁
                · rw [if_neg hW₁_e', if_pos hW₁_u] at h_e1; cases h_e1
                · rw [if_neg hW₁_e', if_neg hW₁_u] at h_e1; injection h_e1
            have h_e2v : toCopy0 W₁ e'.2 = toCopy0 W₁ v := by
              rw [h_e2]; exact hyv
            have he'2 : e'.2 = v := toCopy0_inj_node h_e2v
            have h_uv_E : (u, v) ∈ G.E := by
              have h_eq : (u, v) = e' := by
                ext
                · exact he'1.symm
                · exact he'2.symm
              rw [h_eq]; exact he'_E
            obtain ⟨_, hv_G⟩ := G.hE_subset h_uv_E
            refine ⟨Walk.cons v (.forwardE h_uv_E)
              (Walk.nil v (Finset.mem_union_right _ hv_G)),
              trivial, by change 1 = 0 + 1; omega, ?_⟩
            intro x hx
            simp [Walk.vertices, List.tail, List.dropLast] at hx
          · obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hTrans
            have hcontra : SplitNode.copy0 w' = x :=
              congrArg Prod.fst hw'_eq
            rw [hxu] at hcontra
            unfold toCopy1 at hcontra
            by_cases hW1 : u ∈ W₁
            · rw [if_pos hW1] at hcontra; cases hcontra
            · rw [if_neg hW1] at hcontra; cases hcontra
  | x, _, .cons mid sStep (.cons mid2 sStep2 p2), hp_dir, hp_inter, u, v, hxu, hyv => by
      cases sStep with
      | backwardE _ => exact hp_dir.elim
      | bidir _ => exact hp_dir.elim
      | forwardE h_E =>
          have hp'_dir : (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 sStep2 p2).IsDirectedWalk :=
            hp_dir
          change (x, mid) ∈
              G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
                W₁.image
                  (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
            at h_E
          rcases Finset.mem_union.mp h_E with hLift | hTrans
          · obtain ⟨e', he'_E, he'_eq⟩ := Finset.mem_image.mp hLift
            have h_e1 : toCopy1 W₁ e'.1 = x := congrArg Prod.fst he'_eq
            have h_e2 : toCopy0 W₁ e'.2 = mid := congrArg Prod.snd he'_eq
            rw [hxu] at h_e1
            have he'1 : e'.1 = u := by
              unfold toCopy1 at h_e1
              by_cases hW₁_e' : e'.1 ∈ W₁
              · by_cases hW₁_u : u ∈ W₁
                · rw [if_pos hW₁_e', if_pos hW₁_u] at h_e1; injection h_e1
                · rw [if_pos hW₁_e', if_neg hW₁_u] at h_e1; cases h_e1
              · by_cases hW₁_u : u ∈ W₁
                · rw [if_neg hW₁_e', if_pos hW₁_u] at h_e1; cases h_e1
                · rw [if_neg hW₁_e', if_neg hW₁_u] at h_e1; injection h_e1
            have h_pv_ne : p2.vertices ≠ [] :=
              Walk.vertices_ne_nil p2
            have hmid_inter : mid ∈ W₂.image SplitNode.unsplit := by
              apply hp_inter
              change mid ∈ (mid :: p2.vertices).dropLast
              rw [List.dropLast_cons_of_ne_nil h_pv_ne]
              exact List.mem_cons_self
            obtain ⟨z, hzW₂, hz_eq⟩ := Finset.mem_image.mp hmid_inter
            have hz_notW₁ : z ∉ W₁ :=
              Finset.disjoint_left.mp hDisj.symm hzW₂
            have h_z_lift : toCopy0 W₁ z = SplitNode.unsplit z :=
              toCopy0_unsplit_of_notW hz_notW₁
            have he'2_eq : toCopy0 W₁ e'.2 = toCopy0 W₁ z := by
              rw [h_e2, ← hz_eq, h_z_lift]
            have he'2 : e'.2 = z := toCopy0_inj_node he'2_eq
            have h_uz_E : (u, z) ∈ G.E := by
              have h_eq : (u, z) = e' := by
                ext
                · exact he'1.symm
                · exact he'2.symm
              rw [h_eq]; exact he'_E
            have h_z_lift1 : toCopy1 W₁ z = SplitNode.unsplit z :=
              toCopy1_unsplit_of_notW hz_notW₁
            have hp'_inter : ∀ x ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 sStep2 p2).vertices.tail.dropLast,
                x ∈ W₂.image SplitNode.unsplit := by
              intro x hx
              apply hp_inter
              change x ∈ (mid :: p2.vertices).dropLast
              rw [List.dropLast_cons_of_ne_nil h_pv_ne]
              refine List.mem_cons_of_mem _ ?_
              change x ∈ p2.vertices.dropLast
              exact hx
            obtain ⟨q', hq'_dir, hq'_len, hq'_inter⟩ :=
              walk_split_descend_to_G hW₁ hDisj
                (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 sStep2 p2)
                hp'_dir hp'_inter (hz_eq.symm.trans h_z_lift1.symm) hyv
            refine ⟨Walk.cons z (.forwardE h_uz_E) q', hq'_dir, ?_, ?_⟩
            · change q'.length + 1
                = (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 sStep2 p2).length + 1
              rw [hq'_len]
            · intro x hx
              change x ∈ q'.vertices.dropLast at hx
              have h_q'_pos : q'.length ≥ 1 := by
                rw [hq'_len]; change p2.length + 1 ≥ 1; omega
              have h_q'_tail_ne : q'.vertices.tail ≠ [] :=
                Walk.tail_vertices_ne_nil_of_pos q' h_q'_pos
              rw [Walk.vertices_eq_head_cons_tail q'] at hx
              rw [List.dropLast_cons_of_ne_nil h_q'_tail_ne] at hx
              rcases List.mem_cons.mp hx with hx_z | hx_tail
              · rw [hx_z]; exact hzW₂
              · exact hq'_inter x hx_tail
          · obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hTrans
            have hcontra : SplitNode.copy0 w' = x :=
              congrArg Prod.fst hw'_eq
            rw [hxu] at hcontra
            unfold toCopy1 at hcontra
            by_cases hW1 : u ∈ W₁
            · rw [if_pos hW1] at hcontra; cases hcontra
            · rw [if_neg hW1] at hcontra; cases hcontra

private lemma split_marg_PhiE_iff
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) {u v : Node} :
    (G.nodeSplittingOn W₁ hW₁).MarginalizationΦE
        (W₂.image SplitNode.unsplit)
        (toCopy1 W₁ u) (toCopy0 W₁ v) ↔
      G.MarginalizationΦE W₂ u v := by
  constructor
  · rintro ⟨p, hp_dir, hp_pos, hp_inter⟩
    obtain ⟨q, hq_dir, hq_len, hq_inter⟩ :=
      walk_split_descend_to_G hW₁ hDisj p hp_dir hp_inter rfl rfl
    refine ⟨q, hq_dir, ?_, hq_inter⟩
    rw [hq_len]; exact hp_pos
  · rintro ⟨q, hq_dir, hq_pos, hq_inter⟩
    obtain ⟨p, hp_dir, hp_len, hp_inter⟩ :=
      walk_G_lift_to_split hW₁ hDisj q hq_dir hq_pos hq_inter
    refine ⟨p, hp_dir, ?_, hp_inter⟩
    rw [hp_len]; exact hq_pos

set_option maxHeartbeats 800000 in
private lemma walk_target_copy1_source_copy0
    {G : CDMG Node} {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V} {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) :
    ∀ {x : SplitNode Node} {w : Node}, w ∈ W₁ →
      (p : Walk (G.nodeSplittingOn W₁ hW₁) x (SplitNode.copy1 w)) →
      p.IsDirectedWalk → p.length ≥ 1 →
      (∀ z ∈ p.vertices.tail.dropLast,
        z ∈ W₂.image SplitNode.unsplit) →
      x = SplitNode.copy0 w
  | _, _, _, .nil _ _, _, hp_pos, _ => by
      simp [Walk.length] at hp_pos
  | x, w, _, .cons _ sStep (.nil _ _), hp_dir, _, _ => by
      cases sStep with
      | backwardE _ => exact hp_dir.elim
      | bidir _ => exact hp_dir.elim
      | forwardE h_E =>
          change (x, SplitNode.copy1 w) ∈
              G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
                W₁.image
                  (fun w' => (SplitNode.copy0 w', SplitNode.copy1 w'))
            at h_E
          rcases Finset.mem_union.mp h_E with hLift | hTrans
          · obtain ⟨e', _, he'_eq⟩ := Finset.mem_image.mp hLift
            have h_e2 : toCopy0 W₁ e'.2 = SplitNode.copy1 w :=
              congrArg Prod.snd he'_eq
            exact absurd h_e2 toCopy0_ne_copy1
          · obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hTrans
            have h_e2 : SplitNode.copy1 w' = SplitNode.copy1 w :=
              congrArg Prod.snd hw'_eq
            have h_e1 : SplitNode.copy0 w' = x :=
              congrArg Prod.fst hw'_eq
            have : w' = w := by injection h_e2
            rw [this] at h_e1
            exact h_e1.symm
  | x, w, hwW₁, .cons mid sStep (.cons mid2 sStep2 p2), hp_dir, _, hp_inter => by
      cases sStep with
      | backwardE _ => exact hp_dir.elim
      | bidir _ => exact hp_dir.elim
      | forwardE h_E =>
          have hp'_dir : (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 sStep2 p2).IsDirectedWalk :=
            hp_dir
          have h_pv_ne : p2.vertices ≠ [] :=
            Walk.vertices_ne_nil p2
          have hmid_inter : mid ∈ W₂.image SplitNode.unsplit := by
            apply hp_inter
            change mid ∈ (mid :: p2.vertices).dropLast
            rw [List.dropLast_cons_of_ne_nil h_pv_ne]
            exact List.mem_cons_self
          obtain ⟨z, hzW₂, hz_eq⟩ := Finset.mem_image.mp hmid_inter
          have hz_notW₁ : z ∉ W₁ :=
            Finset.disjoint_left.mp hDisj.symm hzW₂
          change (x, mid) ∈
              G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
                W₁.image
                  (fun w' => (SplitNode.copy0 w', SplitNode.copy1 w'))
            at h_E
          rcases Finset.mem_union.mp h_E with hLift | hTrans
          · have h_p'_pos :
                (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 sStep2 p2).length ≥ 1 := by
              change p2.length + 1 ≥ 1; omega
            have hp'_inter :
                ∀ z' ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 sStep2 p2).vertices.tail.dropLast,
                  z' ∈ W₂.image SplitNode.unsplit := by
              intro z' hz'
              apply hp_inter
              change z' ∈ (mid :: p2.vertices).dropLast
              rw [List.dropLast_cons_of_ne_nil h_pv_ne]
              refine List.mem_cons_of_mem _ ?_
              change z' ∈ p2.vertices.dropLast
              exact hz'
            have h_rec : mid = SplitNode.copy0 w :=
              walk_target_copy1_source_copy0 hDisj hwW₁
                (Walk.cons (G := G.nodeSplittingOn W₁ hW₁) mid2 sStep2 p2)
                hp'_dir h_p'_pos hp'_inter
            rw [h_rec] at hz_eq
            cases hz_eq
          · obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hTrans
            have h_e2 : SplitNode.copy1 w' = mid :=
              congrArg Prod.snd hw'_eq
            rw [← hz_eq] at h_e2
            cases h_e2

-- E-field equality for Part (iii).  The body structurally mirrors the
-- original (E-field shape is unchanged by the refactor — still
-- `Finset (Node × Node)`); only upstream-name retargets and the
-- transfer-edge walk construction (single `.forwardE` step) shift.
set_option maxHeartbeats 1600000 in
private lemma split_marg_E_field_eq
    {G : CDMG Node} (W₁ : Finset Node) (hW₁ : W₁ ⊆ G.V)
    (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    ((G.nodeSplittingOn W₁ hW₁).marginalize
        (W₂.image SplitNode.unsplit)
        (image_unsplit_subset_nodeSplittingOn_V_of_disjoint
          hW₁ hW₂ hDisj.symm)).E
      = ((G.marginalize W₂ hW₂).nodeSplittingOn W₁
          (subset_sdiff_of_disjoint hW₁ hDisj)).E := by
  apply Finset.ext
  rintro ⟨e1, e2⟩
  change
    (e1, e2) ∈ ((G.J.image SplitNode.unsplit ∪
            ((G.V \ W₁).image SplitNode.unsplit
                ∪ W₁.image SplitNode.copy0
              ∪ W₁.image SplitNode.copy1) \ W₂.image SplitNode.unsplit)
          ×ˢ (((G.V \ W₁).image SplitNode.unsplit
                  ∪ W₁.image SplitNode.copy0
                ∪ W₁.image SplitNode.copy1) \ W₂.image SplitNode.unsplit)).filter
        (fun e => (G.nodeSplittingOn W₁ hW₁).MarginalizationΦE
                    (W₂.image SplitNode.unsplit) e.1 e.2)
    ↔ (e1, e2) ∈ (((G.J ∪ (G.V \ W₂)) ×ˢ (G.V \ W₂)).filter
              (fun e => G.MarginalizationΦE W₂ e.1 e.2)).image
            (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))
        ∪ W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
  rw [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, h2⟩, hPhi⟩
    obtain ⟨h2_in_V, h2_notW₂⟩ := Finset.mem_sdiff.mp h2
    rcases Finset.mem_union.mp h2_in_V with h2_uns_or_c0 | h2_c1
    · rcases Finset.mem_union.mp h2_uns_or_c0 with h2_uns | h2_c0
      · obtain ⟨v', hv'_VW₁, hv'_eq⟩ := Finset.mem_image.mp h2_uns
        obtain ⟨hv'_V, hv'_notW₁⟩ := Finset.mem_sdiff.mp hv'_VW₁
        have hv'_notW₂ : v' ∉ W₂ := by
          intro hv'W₂
          apply h2_notW₂; rw [← hv'_eq]
          exact Finset.mem_image.mpr ⟨v', hv'W₂, rfl⟩
        have hv'_lift : toCopy0 W₁ v' = SplitNode.unsplit v' :=
          toCopy0_unsplit_of_notW hv'_notW₁
        have h_e2_toCopy0 : e2 = toCopy0 W₁ v' := hv'_eq.symm.trans hv'_lift.symm
        rcases Finset.mem_union.mp h1 with h1_J | h1_V_marg
        · obtain ⟨j, hjJ, hj_eq⟩ := Finset.mem_image.mp h1_J
          have hj_notW₁ : j ∉ W₁ := by
            intro hjW₁
            exact Finset.disjoint_left.mp G.hJV_disj hjJ (hW₁ hjW₁)
          have hj_lift1 : toCopy1 W₁ j = SplitNode.unsplit j :=
            toCopy1_unsplit_of_notW hj_notW₁
          have h_e1_toCopy1 : e1 = toCopy1 W₁ j := hj_eq.symm.trans hj_lift1.symm
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨(j, v'), ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_union_left _ hjJ, Finset.mem_sdiff.mpr ⟨hv'_V, hv'_notW₂⟩⟩, ?_⟩
            rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
            exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
          · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
        · obtain ⟨h1_in_V, _⟩ := Finset.mem_sdiff.mp h1_V_marg
          rcases Finset.mem_union.mp h1_in_V with h1_uns_or_c0 | h1_c1
          · rcases Finset.mem_union.mp h1_uns_or_c0 with h1_uns | h1_c0
            · obtain ⟨u', hu'_VW₁, hu'_eq⟩ := Finset.mem_image.mp h1_uns
              obtain ⟨hu'_V, hu'_notW₁⟩ := Finset.mem_sdiff.mp hu'_VW₁
              have hu'_notW₂ : u' ∉ W₂ := by
                intro hu'W₂
                obtain ⟨_, h_notW₂⟩ := Finset.mem_sdiff.mp h1_V_marg
                apply h_notW₂; rw [← hu'_eq]
                exact Finset.mem_image.mpr ⟨u', hu'W₂, rfl⟩
              have hu'_lift1 : toCopy1 W₁ u' = SplitNode.unsplit u' :=
                toCopy1_unsplit_of_notW hu'_notW₁
              have h_e1_toCopy1 : e1 = toCopy1 W₁ u' :=
                hu'_eq.symm.trans hu'_lift1.symm
              refine Finset.mem_union_left _ ?_
              refine Finset.mem_image.mpr ⟨(u', v'), ?_, ?_⟩
              · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                  ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hu'_V, hu'_notW₂⟩),
                    Finset.mem_sdiff.mpr ⟨hv'_V, hv'_notW₂⟩⟩, ?_⟩
                rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
                exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
              · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
            · obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h1_c0
              exfalso
              obtain ⟨p, hp_dir, hp_pos, hp_inter⟩ := hPhi
              have hsrc_eq : SplitNode.copy0 w' = e1 := hw'_eq
              have h_tgt_eq : e2 = SplitNode.copy1 w' := by
                have := walk_copy0_target_copy1 (hW₁ := hW₁) hDisj hw'W₁
                  (hsrc_eq ▸ p)
                  (by cases hsrc_eq; exact hp_dir)
                  (by cases hsrc_eq; exact hp_pos)
                  (by cases hsrc_eq; exact hp_inter)
                exact this
              rw [h_tgt_eq] at hv'_eq
              cases hv'_eq
          · obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h1_c1
            have hw'_lift1 : toCopy1 W₁ w' = SplitNode.copy1 w' := by
              unfold toCopy1; rw [if_pos hw'W₁]
            have h_e1_toCopy1 : e1 = toCopy1 W₁ w' := hw'_eq.symm.trans hw'_lift1.symm
            have hw'_V : w' ∈ G.V := hW₁ hw'W₁
            have hw'_notW₂ : w' ∉ W₂ := Finset.disjoint_left.mp hDisj hw'W₁
            refine Finset.mem_union_left _ ?_
            refine Finset.mem_image.mpr ⟨(w', v'), ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hw'_V, hw'_notW₂⟩),
                  Finset.mem_sdiff.mpr ⟨hv'_V, hv'_notW₂⟩⟩, ?_⟩
              rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
              exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
            · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
      · obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h2_c0
        have hw'_lift0 : toCopy0 W₁ w' = SplitNode.copy0 w' := by
          unfold toCopy0; rw [if_pos hw'W₁]
        have h_e2_toCopy0 : e2 = toCopy0 W₁ w' := hw'_eq.symm.trans hw'_lift0.symm
        have hw'_V : w' ∈ G.V := hW₁ hw'W₁
        have hw'_notW₂ : w' ∉ W₂ := Finset.disjoint_left.mp hDisj hw'W₁
        rcases Finset.mem_union.mp h1 with h1_J | h1_V_marg
        · obtain ⟨j, hjJ, hj_eq⟩ := Finset.mem_image.mp h1_J
          have hj_notW₁ : j ∉ W₁ := by
            intro hjW₁
            exact Finset.disjoint_left.mp G.hJV_disj hjJ (hW₁ hjW₁)
          have hj_lift1 : toCopy1 W₁ j = SplitNode.unsplit j :=
            toCopy1_unsplit_of_notW hj_notW₁
          have h_e1_toCopy1 : e1 = toCopy1 W₁ j := hj_eq.symm.trans hj_lift1.symm
          refine Finset.mem_union_left _ ?_
          refine Finset.mem_image.mpr ⟨(j, w'), ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_union_left _ hjJ, Finset.mem_sdiff.mpr ⟨hw'_V, hw'_notW₂⟩⟩, ?_⟩
            rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
            exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
          · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
        · obtain ⟨h1_in_V, _⟩ := Finset.mem_sdiff.mp h1_V_marg
          rcases Finset.mem_union.mp h1_in_V with h1_uns_or_c0 | h1_c1
          · rcases Finset.mem_union.mp h1_uns_or_c0 with h1_uns | h1_c0
            · obtain ⟨u', hu'_VW₁, hu'_eq⟩ := Finset.mem_image.mp h1_uns
              obtain ⟨hu'_V, hu'_notW₁⟩ := Finset.mem_sdiff.mp hu'_VW₁
              have hu'_notW₂ : u' ∉ W₂ := by
                intro hu'W₂
                obtain ⟨_, h_notW₂⟩ := Finset.mem_sdiff.mp h1_V_marg
                apply h_notW₂; rw [← hu'_eq]
                exact Finset.mem_image.mpr ⟨u', hu'W₂, rfl⟩
              have hu'_lift1 : toCopy1 W₁ u' = SplitNode.unsplit u' :=
                toCopy1_unsplit_of_notW hu'_notW₁
              have h_e1_toCopy1 : e1 = toCopy1 W₁ u' :=
                hu'_eq.symm.trans hu'_lift1.symm
              refine Finset.mem_union_left _ ?_
              refine Finset.mem_image.mpr ⟨(u', w'), ?_, ?_⟩
              · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                  ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hu'_V, hu'_notW₂⟩),
                    Finset.mem_sdiff.mpr ⟨hw'_V, hw'_notW₂⟩⟩, ?_⟩
                rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
                exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
              · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
            · obtain ⟨w'', hw''W₁, hw''_eq⟩ := Finset.mem_image.mp h1_c0
              exfalso
              obtain ⟨p, hp_dir, hp_pos, hp_inter⟩ := hPhi
              have hsrc_eq : SplitNode.copy0 w'' = e1 := hw''_eq
              have h_tgt_eq : e2 = SplitNode.copy1 w'' := by
                have := walk_copy0_target_copy1 (hW₁ := hW₁) hDisj hw''W₁
                  (hsrc_eq ▸ p)
                  (by cases hsrc_eq; exact hp_dir)
                  (by cases hsrc_eq; exact hp_pos)
                  (by cases hsrc_eq; exact hp_inter)
                exact this
              rw [h_tgt_eq] at hw'_eq
              cases hw'_eq
          · obtain ⟨w'', hw''W₁, hw''_eq⟩ := Finset.mem_image.mp h1_c1
            have hw''_lift1 : toCopy1 W₁ w'' = SplitNode.copy1 w'' := by
              unfold toCopy1; rw [if_pos hw''W₁]
            have h_e1_toCopy1 : e1 = toCopy1 W₁ w'' :=
              hw''_eq.symm.trans hw''_lift1.symm
            have hw''_V : w'' ∈ G.V := hW₁ hw''W₁
            have hw''_notW₂ : w'' ∉ W₂ := Finset.disjoint_left.mp hDisj hw''W₁
            refine Finset.mem_union_left _ ?_
            refine Finset.mem_image.mpr ⟨(w'', w'), ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hw''_V, hw''_notW₂⟩),
                  Finset.mem_sdiff.mpr ⟨hw'_V, hw'_notW₂⟩⟩, ?_⟩
              rw [h_e1_toCopy1, h_e2_toCopy0] at hPhi
              exact (split_marg_PhiE_iff hW₁ hDisj).mp hPhi
            · exact Prod.ext h_e1_toCopy1.symm h_e2_toCopy0.symm
    · obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h2_c1
      obtain ⟨p, hp_dir, hp_pos, hp_inter⟩ := hPhi
      have h_tgt_eq : e2 = SplitNode.copy1 w' := hw'_eq.symm
      have h_src_eq : e1 = SplitNode.copy0 w' := by
        have := walk_target_copy1_source_copy0 (hW₁ := hW₁) hDisj hw'W₁
          (h_tgt_eq ▸ p)
          (by cases h_tgt_eq; exact hp_dir)
          (by cases h_tgt_eq; exact hp_pos)
          (by cases h_tgt_eq; exact hp_inter)
        exact this
      refine Finset.mem_union_right _ ?_
      refine Finset.mem_image.mpr ⟨w', hw'W₁, ?_⟩
      exact Prod.ext h_src_eq.symm h_tgt_eq.symm
  · intro h_union
    rcases Finset.mem_union.mp h_union with h_lifted | h_transfer
    · obtain ⟨⟨u, v⟩, h_uv_mem, h_uv_eq⟩ := Finset.mem_image.mp h_lifted
      rw [Finset.mem_filter, Finset.mem_product] at h_uv_mem
      obtain ⟨⟨hu_in, hv_in⟩, hPhi⟩ := h_uv_mem
      have h_e1 : e1 = toCopy1 W₁ u := congrArg Prod.fst h_uv_eq.symm
      have h_e2 : e2 = toCopy0 W₁ v := congrArg Prod.snd h_uv_eq.symm
      obtain ⟨hv_V, hv_notW₂⟩ := Finset.mem_sdiff.mp hv_in
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h_e1]
        by_cases hu_W₁ : u ∈ W₁
        · have hu_lift1 : toCopy1 W₁ u = SplitNode.copy1 u := by
            unfold toCopy1; rw [if_pos hu_W₁]
          rw [hu_lift1]
          have hu_notW₂ : u ∉ W₂ := Finset.disjoint_left.mp hDisj hu_W₁
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨u, hu_W₁, rfl⟩
          · intro h_in
            obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp h_in
            cases hw_eq
        · have hu_lift1 : toCopy1 W₁ u = SplitNode.unsplit u :=
            toCopy1_unsplit_of_notW hu_W₁
          rw [hu_lift1]
          rcases Finset.mem_union.mp hu_in with hu_J | hu_VW₂
          · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu_J, rfl⟩)
          · obtain ⟨hu_V, hu_notW₂⟩ := Finset.mem_sdiff.mp hu_VW₂
            refine Finset.mem_union_right _ ?_
            refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
            · refine Finset.mem_union_left _ ?_
              refine Finset.mem_union_left _ ?_
              exact Finset.mem_image.mpr
                ⟨u, Finset.mem_sdiff.mpr ⟨hu_V, hu_W₁⟩, rfl⟩
            · intro h_in
              obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp h_in
              have : w = u := by injection hw_eq
              exact hu_notW₂ (this ▸ hwW₂)
      · rw [h_e2]
        by_cases hv_W₁ : v ∈ W₁
        · have hv_lift0 : toCopy0 W₁ v = SplitNode.copy0 v := by
            unfold toCopy0; rw [if_pos hv_W₁]
          rw [hv_lift0]
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_left _ ?_
            refine Finset.mem_union_right _ ?_
            exact Finset.mem_image.mpr ⟨v, hv_W₁, rfl⟩
          · intro h_in
            obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp h_in
            cases hw_eq
        · have hv_lift0 : toCopy0 W₁ v = SplitNode.unsplit v :=
            toCopy0_unsplit_of_notW hv_W₁
          rw [hv_lift0]
          refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
          · refine Finset.mem_union_left _ ?_
            refine Finset.mem_union_left _ ?_
            exact Finset.mem_image.mpr
              ⟨v, Finset.mem_sdiff.mpr ⟨hv_V, hv_W₁⟩, rfl⟩
          · intro h_in
            obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp h_in
            have : w = v := by injection hw_eq
            exact hv_notW₂ (this ▸ hwW₂)
      · rw [h_e1, h_e2]
        exact (split_marg_PhiE_iff hW₁ hDisj).mpr hPhi
    · obtain ⟨w, hwW₁, hw_eq⟩ := Finset.mem_image.mp h_transfer
      have h_e1 : e1 = SplitNode.copy0 w := congrArg Prod.fst hw_eq.symm
      have h_e2 : e2 = SplitNode.copy1 w := congrArg Prod.snd hw_eq.symm
      have hw_V : w ∈ G.V := hW₁ hwW₁
      have hw_notW₂ : w ∉ W₂ := Finset.disjoint_left.mp hDisj hwW₁
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h_e1]
        refine Finset.mem_union_right _ ?_
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · refine Finset.mem_union_left _ ?_
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · intro h_in
          obtain ⟨_, _, hw_eq'⟩ := Finset.mem_image.mp h_in
          cases hw_eq'
      · rw [h_e2]
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        · intro h_in
          obtain ⟨_, _, hw_eq'⟩ := Finset.mem_image.mp h_in
          cases hw_eq'
      · rw [h_e1, h_e2]
        have h_transfer_E : (SplitNode.copy0 w, SplitNode.copy1 w) ∈
            (G.nodeSplittingOn W₁ hW₁).E := by
          change _ ∈ G.E.image _ ∪ W₁.image _
          refine Finset.mem_union_right _ ?_
          exact Finset.mem_image.mpr ⟨w, hwW₁, rfl⟩
        have h_tgt_in : SplitNode.copy1 w
            ∈ G.nodeSplittingOn W₁ hW₁ :=
          mem_split_of_mem_W₁_copy1 (hW₁ := hW₁) hwW₁
        refine ⟨Walk.cons (SplitNode.copy1 w) (.forwardE h_transfer_E)
          (Walk.nil (SplitNode.copy1 w) h_tgt_in),
          trivial, by change 1 ≥ 1; omega, ?_⟩
        intro x hx
        simp [Walk.vertices, List.tail, List.dropLast] at hx

-- ## Refactor replacements — Phase iii.E (L-field helpers, Piii48-Piii61).
--
-- Body shifts (these are the L-field analogues of the E-field
-- helpers in Phase iii.D):
--   1. `WalkStep` destructure changes from the disjunction
--      `⟨ha, hOr⟩ | ⟨ha, hE⟩` to a constructor case-split on
--      `.forwardE / .backwardE / .bidir`.  The `.cons _ a hStep p`
--      cons-cell pattern (4-arg) becomes `.cons _ s p` (3-arg).
--   2. L-shape changes from `Finset (Node × Node)` to
--      `Finset (Sym2 Node)`.  The `nodeSplittingOn.L` lift is now
--      `G.L.image (Sym2.map (toCopy0 W₁))`; descent reads
--      via `Finset.mem_image.mp` + `Sym2.ind` + `Sym2.eq_iff`.
--   3. `Piii59 / Piii60` (`not_bif_source_copy1` / `not_bif_target_copy1_aux`)
--      no longer destructure a stored ordered-pair `a` from a
--      `cons` cell; instead they case-split on the typed step
--      `sStep : WalkStep G u v` and inspect its
--      `.forwardE h_E` witness `h_E : (u, v) ∈ split.E`.

private lemma pair_eq_of_toCopy0_eq {W₁ : Finset Node}
    {a : Node × Node} {u v : Node}
    (h : (toCopy0 W₁ a.1, toCopy0 W₁ a.2)
        = (toCopy0 W₁ u, toCopy0 W₁ v)) :
    a = (u, v) := by
  have h1 : toCopy0 W₁ a.1 = toCopy0 W₁ u := congrArg Prod.fst h
  have h2 : toCopy0 W₁ a.2 = toCopy0 W₁ v := congrArg Prod.snd h
  exact Prod.ext (toCopy0_inj_node h1) (toCopy0_inj_node h2)

private lemma toCopy1_eq_toCopy0_imp_notW {W₁ : Finset Node} {u v : Node}
    (h : toCopy1 W₁ v = toCopy0 W₁ u) :
    u ∉ W₁ ∧ v ∉ W₁ ∧ u = v := by
  unfold toCopy1 toCopy0 at h
  by_cases hW_v : v ∈ W₁ <;> by_cases hW_u : u ∈ W₁
  · rw [if_pos hW_v, if_pos hW_u] at h; cases h
  · rw [if_pos hW_v, if_neg hW_u] at h; cases h
  · rw [if_neg hW_v, if_pos hW_u] at h; cases h
  · rw [if_neg hW_v, if_neg hW_u] at h
    refine ⟨hW_u, hW_v, ?_⟩
    have heq : SplitNode.unsplit v = SplitNode.unsplit u := h
    have hvu : v = u := by injection heq
    exact hvu.symm

-- E-edge descent through `toCopy0`-tagged endpoints (transfer edge ruled
-- out by the `.copy1` mismatch on the target slot).  Heartbeats raised
-- to handle the `change` against `nodeSplittingOn.E` defEq.
set_option maxHeartbeats 800000 in
private lemma a_in_G_E_of_toCopy0_lifted_in_split
    {G : CDMG Node} {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V}
    {a' : Node × Node}
    {a : SplitNode Node × SplitNode Node}
    (ha_eq : a = (toCopy0 W₁ a'.1, toCopy0 W₁ a'.2))
    (ha_E : a ∈ (G.nodeSplittingOn W₁ hW₁).E) : a' ∈ G.E := by
  change a ∈ G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2))
          ∪ W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
        at ha_E
  rcases Finset.mem_union.mp ha_E with hLift | hTrans
  · obtain ⟨e', he'E, he'_eq⟩ := Finset.mem_image.mp hLift
    rw [ha_eq] at he'_eq
    have h1 : toCopy1 W₁ e'.1 = toCopy0 W₁ a'.1 :=
      congrArg Prod.fst he'_eq
    have h2 : toCopy0 W₁ e'.2 = toCopy0 W₁ a'.2 :=
      congrArg Prod.snd he'_eq
    obtain ⟨_, _, he1⟩ := toCopy1_eq_toCopy0_imp_notW h1
    have he2 : e'.2 = a'.2 := toCopy0_inj_node h2
    have heq : e' = a' := Prod.ext he1.symm he2
    rw [← heq]; exact he'E
  · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
    rw [ha_eq] at hw_eq
    have hcontra : SplitNode.copy1 w = toCopy0 W₁ a'.2 :=
      congrArg Prod.snd hw_eq
    exact (toCopy0_ne_copy1 hcontra.symm).elim

-- L-edge descent through `toCopy0`-tagged endpoints.  L is
-- `Finset (Sym2 Node)`; the lift `G.L.image (Sym2.map (toCopy0 W₁))`
-- is destructured via `Sym2.ind` + `Sym2.eq_iff`.
set_option maxHeartbeats 800000 in
private lemma a_in_G_L_of_toCopy0_lifted_in_split
    {G : CDMG Node} {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V}
    {a' : Node × Node}
    {a : SplitNode Node × SplitNode Node}
    (ha_eq : a = (toCopy0 W₁ a'.1, toCopy0 W₁ a'.2))
    (ha_L : s(a.1, a.2) ∈ (G.nodeSplittingOn W₁ hW₁).L) :
    s(a'.1, a'.2) ∈ G.L := by
  change s(a.1, a.2) ∈ G.L.image (Sym2.map (toCopy0 W₁)) at ha_L
  obtain ⟨s', hs'_in, hs'_eq⟩ := Finset.mem_image.mp ha_L
  rw [ha_eq] at hs'_eq
  induction s' using Sym2.ind with
  | _ b c =>
      change s(toCopy0 W₁ b, toCopy0 W₁ c) =
             s(toCopy0 W₁ a'.1, toCopy0 W₁ a'.2) at hs'_eq
      rcases Sym2.eq_iff.mp hs'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hb : b = a'.1 := toCopy0_inj_node h1
        have hc : c = a'.2 := toCopy0_inj_node h2
        rw [hb, hc] at hs'_in
        exact hs'_in
      · have hb : b = a'.2 := toCopy0_inj_node h1
        have hc : c = a'.1 := toCopy0_inj_node h2
        rw [hb, hc] at hs'_in
        rwa [Sym2.eq_swap]

-- WalkStep descent: both endpoints `toCopy0`-tagged.  Returns a
-- typed `WalkStep G u v` constructed via the three
-- constructors of `WalkStep`.  Pattern-matching `def`;
-- consumers can recover the constructor tag of the result via
-- `simp [walkStep_ofSplit_toCopy0]`.
set_option maxHeartbeats 800000 in
private def walkStep_ofSplit_toCopy0 {G : CDMG Node}
    {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V} {u v : Node} :
    WalkStep (G.nodeSplittingOn W₁ hW₁)
      (toCopy0 W₁ u) (toCopy0 W₁ v) →
    WalkStep G u v
  | .forwardE h_E => .forwardE (by
      change (toCopy0 W₁ u, toCopy0 W₁ v) ∈
          G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
            W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
        at h_E
      rcases Finset.mem_union.mp h_E with hLift | hTrans
      · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
        have h1 : toCopy1 W₁ a'.1 = toCopy0 W₁ u :=
          congrArg Prod.fst ha'_eq
        have h2 : toCopy0 W₁ a'.2 = toCopy0 W₁ v :=
          congrArg Prod.snd ha'_eq
        obtain ⟨_, _, ha'1_eq⟩ := toCopy1_eq_toCopy0_imp_notW h1
        have ha'2 : a'.2 = v := toCopy0_inj_node h2
        have h_pair : a' = (u, v) := Prod.ext ha'1_eq.symm ha'2
        rw [← h_pair]; exact ha'_in
      · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
        have hcontra : SplitNode.copy1 w = toCopy0 W₁ v :=
          congrArg Prod.snd hw_eq
        exact (toCopy0_ne_copy1 hcontra.symm).elim)
  | .backwardE h_E => .backwardE (by
      change (toCopy0 W₁ v, toCopy0 W₁ u) ∈
          G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
            W₁.image (fun w => (SplitNode.copy0 w, SplitNode.copy1 w))
        at h_E
      rcases Finset.mem_union.mp h_E with hLift | hTrans
      · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
        have h1 : toCopy1 W₁ a'.1 = toCopy0 W₁ v :=
          congrArg Prod.fst ha'_eq
        have h2 : toCopy0 W₁ a'.2 = toCopy0 W₁ u :=
          congrArg Prod.snd ha'_eq
        obtain ⟨_, _, ha'1_eq⟩ := toCopy1_eq_toCopy0_imp_notW h1
        have ha'2 : a'.2 = u := toCopy0_inj_node h2
        have h_pair : a' = (v, u) := Prod.ext ha'1_eq.symm ha'2
        rw [← h_pair]; exact ha'_in
      · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
        have hcontra : SplitNode.copy1 w = toCopy0 W₁ u :=
          congrArg Prod.snd hw_eq
        exact (toCopy0_ne_copy1 hcontra.symm).elim)
  | .bidir h_L => .bidir (by
      change s(toCopy0 W₁ u, toCopy0 W₁ v)
          ∈ G.L.image (Sym2.map (toCopy0 W₁)) at h_L
      obtain ⟨s', hs'_in, hs'_eq⟩ := Finset.mem_image.mp h_L
      induction s' using Sym2.ind with
      | _ b c =>
          change s(toCopy0 W₁ b, toCopy0 W₁ c) =
                 s(toCopy0 W₁ u, toCopy0 W₁ v) at hs'_eq
          rcases Sym2.eq_iff.mp hs'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hb : b = u := toCopy0_inj_node h1
            have hc : c = v := toCopy0_inj_node h2
            rw [hb, hc] at hs'_in
            exact hs'_in
          · have hb : b = v := toCopy0_inj_node h1
            have hc : c = u := toCopy0_inj_node h2
            rw [hb, hc] at hs'_in
            rwa [Sym2.eq_swap])

private lemma mem_G_of_toCopy0_mem_split {G : CDMG Node}
    {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V} {v : Node}
    (h : toCopy0 W₁ v ∈ G.nodeSplittingOn W₁ hW₁) : v ∈ G := by
  by_cases hW : v ∈ W₁
  · exact Finset.mem_union_right _ (hW₁ hW)
  · rw [toCopy0_unsplit_of_notW hW] at h
    exact mem_G_of_unsplit_mem_split hW₁ h

private lemma list_toCopy0_tail {W₁ : Finset Node} (l : List Node) :
    (l.map (toCopy0 W₁)).tail = l.tail.map (toCopy0 W₁) := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

private lemma list_toCopy0_dropLast {W₁ : Finset Node} :
    ∀ (l : List Node),
      (l.map (toCopy0 W₁)).dropLast = l.dropLast.map (toCopy0 W₁)
  | [] => rfl
  | _ :: [] => rfl
  | x :: y :: rest => by
      change toCopy0 W₁ x
              :: (((y :: rest).map (toCopy0 W₁)).dropLast)
          = toCopy0 W₁ x
              :: ((y :: rest).dropLast.map (toCopy0 W₁))
      rw [list_toCopy0_dropLast (y :: rest)]

-- Walk descent split → G with all vertices `toCopy0`-tagged.
-- Generalises `walk_ofSplit_unsplit_full` to allow `.copy0`
-- tags (W₁-underlying).  Transfer edges are ruled out automatically
-- (their `.copy1` target conflicts with the `toCopy0` tag on the
-- target slot).  Heartbeats raised as in the `.unsplit` analogue
-- (`walk_ofSplit_unsplit_full`): nested `change` operations
-- on `nodeSplittingOn.E` / `.L` are expensive on the
-- `SplitNode Node` carrier.
set_option maxHeartbeats 1600000 in
private lemma walk_ofSplit_toCopy0_full {G : CDMG Node}
    {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) :
    ∀ {x y : SplitNode Node}
      (p : Walk (G.nodeSplittingOn W₁ hW₁) x y),
      (∀ z ∈ p.vertices, ∃ z' : Node, z = toCopy0 W₁ z') →
      ∀ (u v : Node), x = toCopy0 W₁ u →
                       y = toCopy0 W₁ v →
      ∃ q : Walk G u v, q.length = p.length ∧
        q.vertices.map (toCopy0 W₁) = p.vertices ∧
        (p.IsDirectedWalk → q.IsDirectedWalk) ∧
        (∀ i, p.IsBifurcationWithSplit i →
          q.IsBifurcationWithSplit i) := by
  intro x y p
  induction p with
  | nil w hw =>
      intro _ u v hxu hyv
      have hu_eq_v : toCopy0 W₁ u = toCopy0 W₁ v := hxu.symm.trans hyv
      have huv : u = v := toCopy0_inj_node hu_eq_v
      subst huv; subst hxu
      have hu_in_G : u ∈ G := mem_G_of_toCopy0_mem_split (hW₁ := hW₁) hw
      refine ⟨Walk.nil u hu_in_G, rfl, rfl, fun _ => trivial, ?_⟩
      intro i h
      simp only [Walk.IsBifurcationWithSplit] at h
  | @cons x' y' mid sStep p' ih =>
      intro h_all u v hxu hyv
      subst hxu
      have hmid_in : mid ∈ (Walk.cons
              (G := G.nodeSplittingOn W₁ hW₁)
              mid sStep p').vertices := by
        change mid ∈ (toCopy0 W₁ u :: p'.vertices)
        exact List.mem_cons_of_mem _ (Walk.head_mem_vertices p')
      obtain ⟨m', hmid_eq⟩ := h_all mid hmid_in
      subst hmid_eq
      have h_all_p' : ∀ z ∈ p'.vertices,
          ∃ z' : Node, z = toCopy0 W₁ z' := by
        intro z hz
        exact h_all z (List.mem_cons_of_mem _ hz)
      obtain ⟨q', hq'_len, hq'_vs, hq'_dir, hq'_bif⟩ :=
        ih h_all_p' m' v rfl hyv
      cases hCase : sStep with
      | forwardE h_E =>
          have h_E_G : (u, m') ∈ G.E := by
            change (toCopy0 W₁ u, toCopy0 W₁ m') ∈
                G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
                  W₁.image
                    (fun w => (SplitNode.copy0 w, SplitNode.copy1 w)) at h_E
            rcases Finset.mem_union.mp h_E with hLift | hTrans
            · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
              have h1 : toCopy1 W₁ a'.1 = toCopy0 W₁ u :=
                congrArg Prod.fst ha'_eq
              have h2 : toCopy0 W₁ a'.2 = toCopy0 W₁ m' :=
                congrArg Prod.snd ha'_eq
              obtain ⟨_, _, ha'1_eq⟩ := toCopy1_eq_toCopy0_imp_notW h1
              have ha'2 : a'.2 = m' := toCopy0_inj_node h2
              have h_pair : a' = (u, m') := Prod.ext ha'1_eq.symm ha'2
              rw [← h_pair]; exact ha'_in
            · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
              have hcontra : SplitNode.copy1 w = toCopy0 W₁ m' :=
                congrArg Prod.snd hw_eq
              exact (toCopy0_ne_copy1 hcontra.symm).elim
          refine ⟨Walk.cons m' (.forwardE h_E_G) q', ?_, ?_, ?_, ?_⟩
          · change q'.length + 1 = p'.length + 1
            rw [hq'_len]
          · change toCopy0 W₁ u
                :: (q'.vertices.map (toCopy0 W₁))
                = toCopy0 W₁ u :: p'.vertices
            rw [hq'_vs]
          · intro hp_dir
            change q'.IsDirectedWalk
            subst hCase
            exact hq'_dir hp_dir
          · intro i hPi
            match i, p', hPi with
            | 0, .nil _ _, hPi =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
            | 0, .cons _ _ _, hPi =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
            | _ + 1, _, hPi =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
      | backwardE h_E =>
          have h_E_G : (m', u) ∈ G.E := by
            change (toCopy0 W₁ m', toCopy0 W₁ u) ∈
                G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
                  W₁.image
                    (fun w => (SplitNode.copy0 w, SplitNode.copy1 w)) at h_E
            rcases Finset.mem_union.mp h_E with hLift | hTrans
            · obtain ⟨a', ha'_in, ha'_eq⟩ := Finset.mem_image.mp hLift
              have h1 : toCopy1 W₁ a'.1 = toCopy0 W₁ m' :=
                congrArg Prod.fst ha'_eq
              have h2 : toCopy0 W₁ a'.2 = toCopy0 W₁ u :=
                congrArg Prod.snd ha'_eq
              obtain ⟨_, _, ha'1_eq⟩ := toCopy1_eq_toCopy0_imp_notW h1
              have ha'2 : a'.2 = u := toCopy0_inj_node h2
              have h_pair : a' = (m', u) := Prod.ext ha'1_eq.symm ha'2
              rw [← h_pair]; exact ha'_in
            · obtain ⟨w, _, hw_eq⟩ := Finset.mem_image.mp hTrans
              have hcontra : SplitNode.copy1 w = toCopy0 W₁ u :=
                congrArg Prod.snd hw_eq
              exact (toCopy0_ne_copy1 hcontra.symm).elim
          refine ⟨Walk.cons m' (.backwardE h_E_G) q', ?_, ?_, ?_, ?_⟩
          · change q'.length + 1 = p'.length + 1
            rw [hq'_len]
          · change toCopy0 W₁ u
                :: (q'.vertices.map (toCopy0 W₁))
                = toCopy0 W₁ u :: p'.vertices
            rw [hq'_vs]
          · intro hp_dir
            subst hCase
            exact hp_dir.elim
          · intro i hPi
            match i, p', hPi, q', hq'_len, hq'_dir, hq'_bif with
            | 0, .nil _ _, hPi, _, _, _, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hPi
            | 0, .cons _ _ _, _, .nil _ _, hlen, _, _ =>
                simp [Walk.length] at hlen
            | 0, .cons _ _ _, hDir, .cons _ _ _, _, hq'_dir, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hDir
                simp only [Walk.IsBifurcationWithSplit]
                exact hq'_dir hDir
            | k + 1, _, hRec, _, _, _, hq'_bif =>
                simp only [Walk.IsBifurcationWithSplit] at hRec
                simp only [Walk.IsBifurcationWithSplit]
                exact hq'_bif k hRec
      | bidir h_L =>
          have h_L_G : (s(u, m') : Sym2 Node) ∈ G.L := by
            change s(toCopy0 W₁ u, toCopy0 W₁ m') ∈
                G.L.image (Sym2.map (toCopy0 W₁)) at h_L
            obtain ⟨s', hs'_in, hs'_eq⟩ := Finset.mem_image.mp h_L
            induction s' using Sym2.ind with
            | _ b c =>
                change s(toCopy0 W₁ b, toCopy0 W₁ c) =
                       s(toCopy0 W₁ u, toCopy0 W₁ m')
                  at hs'_eq
                rcases Sym2.eq_iff.mp hs'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · have hb : b = u := toCopy0_inj_node h1
                  have hc : c = m' := toCopy0_inj_node h2
                  rw [hb, hc] at hs'_in
                  exact hs'_in
                · have hb : b = m' := toCopy0_inj_node h1
                  have hc : c = u := toCopy0_inj_node h2
                  rw [hb, hc] at hs'_in
                  rwa [Sym2.eq_swap]
          refine ⟨Walk.cons m' (.bidir h_L_G) q', ?_, ?_, ?_, ?_⟩
          · change q'.length + 1 = p'.length + 1
            rw [hq'_len]
          · change toCopy0 W₁ u
                :: (q'.vertices.map (toCopy0 W₁))
                = toCopy0 W₁ u :: p'.vertices
            rw [hq'_vs]
          · intro hp_dir
            subst hCase
            exact hp_dir.elim
          · intro i hPi
            match i, p', hPi, q', hq'_len, hq'_dir, hq'_bif with
            | 0, .nil _ _, _, .nil _ _, _, _, _ =>
                show True
                trivial
            | 0, .nil _ _, _, .cons _ _ _, hlen, _, _ =>
                simp [Walk.length] at hlen
            | 0, .cons _ _ _, _, .nil _ _, hlen, _, _ =>
                simp [Walk.length] at hlen
            | 0, .cons _ _ _, hDir, .cons _ _ _, _, hq'_dir, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hDir
                simp only [Walk.IsBifurcationWithSplit]
                exact hq'_dir hDir
            | k + 1, _, hPi, _, _, _, _ =>
                simp only [Walk.IsBifurcationWithSplit] at hPi

private lemma all_toCopy0_of_interior_W_image_split
    {G : CDMG Node} {W₁ : Finset Node} {hW₁ : W₁ ⊆ G.V}
    {W₂ : Finset Node} (hDisj : Disjoint W₁ W₂)
    {x y : SplitNode Node}
    (p : Walk (G.nodeSplittingOn W₁ hW₁) x y)
    (hp_pos : p.length ≥ 1)
    {u v : Node} (hxu : x = toCopy0 W₁ u) (hyv : y = toCopy0 W₁ v)
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast,
                z ∈ W₂.image SplitNode.unsplit) :
    ∀ z ∈ p.vertices, ∃ z' : Node, z = toCopy0 W₁ z' := by
  intro z hz
  rw [Walk.vertices_eq_head_cons_tail p] at hz
  rcases List.mem_cons.mp hz with h_eq | h_in_tail
  · exact ⟨u, h_eq.trans hxu⟩
  · have h_tail_ne : p.vertices.tail ≠ [] :=
      Walk.tail_vertices_ne_nil_of_pos p hp_pos
    have h_drop_or_last : z ∈ p.vertices.tail.dropLast ∨ z = y := by
      rw [← List.dropLast_append_getLast h_tail_ne] at h_in_tail
      rcases List.mem_append.mp h_in_tail with h_drop | h_last
      · exact Or.inl h_drop
      · refine Or.inr ?_
        rw [List.mem_singleton] at h_last
        rw [h_last, Walk.tail_getLast_of_pos p hp_pos]
    rcases h_drop_or_last with h_drop | h_last
    · obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp (hp_inter z h_drop)
      have hw_notW : w ∉ W₁ := Finset.disjoint_left.mp hDisj.symm hwW₂
      exact ⟨w, hw_eq.symm.trans (toCopy0_unsplit_of_notW hw_notW).symm⟩
    · exact ⟨v, h_last.trans hyv⟩

-- Part (iii) Φ_L iff: bifurcation in split iff bifurcation in G.
-- Wrapper over `walk_ofSplit_toCopy0_full` (descent),
-- `exists_lifted_bif_to_split` (ascent),
-- and `all_toCopy0_of_interior_W_image_split` (interior tagging).
private lemma split_marg_PhiL_iff
    {G : CDMG Node} {W₁ : Finset Node} (hW₁ : W₁ ⊆ G.V) {W₂ : Finset Node}
    (hDisj : Disjoint W₁ W₂) {u v : Node} (huv : u ≠ v) :
    (G.nodeSplittingOn W₁ hW₁).MarginalizationΦL
        (W₂.image SplitNode.unsplit)
        (toCopy0 W₁ u) (toCopy0 W₁ v) ↔
      G.MarginalizationΦL W₂ u v := by
  constructor
  · rintro (⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩)
    · have hp_pos : p.length ≥ 1 :=
        Walk.length_pos_of_isBifurcation hp_bif
      have h_all := all_toCopy0_of_interior_W_image_split
        (hW₁ := hW₁) (hDisj := hDisj) p hp_pos rfl rfl hp_inter
      obtain ⟨_hne, hu_tail, hv_drop, i, hi⟩ := hp_bif
      obtain ⟨q, _hq_len, hq_vs, _, hq_bif⟩ :=
        walk_ofSplit_toCopy0_full hW₁ p h_all u v rfl rfl
      refine Or.inl ⟨q, ⟨huv, ?_, ?_, i, hq_bif i hi⟩, ?_⟩
      · intro h
        apply hu_tail
        have : p.vertices.tail
            = q.vertices.tail.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_tail]
        rw [this]
        exact List.mem_map.mpr ⟨u, h, rfl⟩
      · intro h
        apply hv_drop
        have : p.vertices.dropLast
            = q.vertices.dropLast.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_dropLast]
        rw [this]
        exact List.mem_map.mpr ⟨v, h, rfl⟩
      · intro x hx
        have : p.vertices.tail.dropLast
            = q.vertices.tail.dropLast.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_tail, list_toCopy0_dropLast]
        have hx_p : toCopy0 W₁ x ∈ p.vertices.tail.dropLast := by
          rw [this]
          exact List.mem_map.mpr ⟨x, hx, rfl⟩
        obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp (hp_inter _ hx_p)
        have hw_notW : w ∉ W₁ := Finset.disjoint_left.mp hDisj.symm hwW₂
        have hw_lift : toCopy0 W₁ w = SplitNode.unsplit w :=
          toCopy0_unsplit_of_notW hw_notW
        have heq : toCopy0 W₁ x = toCopy0 W₁ w :=
          hw_eq.symm.trans hw_lift.symm
        have hxw : x = w := toCopy0_inj_node heq
        exact hxw ▸ hwW₂
    · have hp_pos : p.length ≥ 1 :=
        Walk.length_pos_of_isBifurcation hp_bif
      have h_all := all_toCopy0_of_interior_W_image_split
        (hW₁ := hW₁) (hDisj := hDisj) p hp_pos (u := v) (v := u) rfl rfl hp_inter
      obtain ⟨_hne, hv_tail, hu_drop, i, hi⟩ := hp_bif
      obtain ⟨q, _hq_len, hq_vs, _, hq_bif⟩ :=
        walk_ofSplit_toCopy0_full hW₁ p h_all v u rfl rfl
      refine Or.inr ⟨q, ⟨huv.symm, ?_, ?_, i, hq_bif i hi⟩, ?_⟩
      · intro h
        apply hv_tail
        have : p.vertices.tail
            = q.vertices.tail.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_tail]
        rw [this]
        exact List.mem_map.mpr ⟨v, h, rfl⟩
      · intro h
        apply hu_drop
        have : p.vertices.dropLast
            = q.vertices.dropLast.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_dropLast]
        rw [this]
        exact List.mem_map.mpr ⟨u, h, rfl⟩
      · intro x hx
        have : p.vertices.tail.dropLast
            = q.vertices.tail.dropLast.map (toCopy0 W₁) := by
          rw [← hq_vs, list_toCopy0_tail, list_toCopy0_dropLast]
        have hx_p : toCopy0 W₁ x ∈ p.vertices.tail.dropLast := by
          rw [this]
          exact List.mem_map.mpr ⟨x, hx, rfl⟩
        obtain ⟨w, hwW₂, hw_eq⟩ := Finset.mem_image.mp (hp_inter _ hx_p)
        have hw_notW : w ∉ W₁ := Finset.disjoint_left.mp hDisj.symm hwW₂
        have hw_lift : toCopy0 W₁ w = SplitNode.unsplit w :=
          toCopy0_unsplit_of_notW hw_notW
        have heq : toCopy0 W₁ x = toCopy0 W₁ w :=
          hw_eq.symm.trans hw_lift.symm
        have hxw : x = w := toCopy0_inj_node heq
        exact hxw ▸ hwW₂
  · rintro (⟨q, hq_bif, hq_inter⟩ | ⟨q, hq_bif, hq_inter⟩)
    · obtain ⟨p, hp_bif, hp_inter⟩ :=
        exists_lifted_bif_to_split hW₁ hDisj q hq_bif hq_inter
      exact Or.inl ⟨p, hp_bif, hp_inter⟩
    · obtain ⟨p, hp_bif, hp_inter⟩ :=
        exists_lifted_bif_to_split hW₁ hDisj q hq_bif hq_inter
      exact Or.inr ⟨p, hp_bif, hp_inter⟩

-- W₁¹-exclusion (source side): no bifurcation walk in split with
-- source `.copy1 w` (w ∈ W₁) and interior in `W₂.image .unsplit`.
--
-- Body shifts from the original:
--   1. The outer `cases p` + `rcases hStep` two-step destructure
--      collapses to `cases p` + `cases sStep` (the typed WalkStep
--      constructor case-split).
--   2. `.forwardE _` outer: `IsBifurcationWithSplit` is False
--      at all `(i, p' shape)` combinations — simp closes immediately.
--   3. `.bidir h_L` outer: `s(.copy1 w, mid) ∈ G.L.image (Sym2.map (toCopy0 W₁))`
--      gives `toCopy0 _ = .copy1 w` via `Sym2.ind` +
--      `Sym2.eq_iff`, contradicting `toCopy0_ne_copy1`.
--   4. `.backwardE h_E` outer with transfer-edge witness yields
--      `mid = .copy0 w`; then for `p' = .cons`, `mid` sits in
--      `p.vertices.tail.dropLast` so `hp_inter` forces
--      `mid ∈ W₂.image .unsplit`, contradicted by `.copy0 ≠ .unsplit`.
-- Heartbeats raised: the `change` operations against
-- `nodeSplittingOn.E` / `.L` are expensive on the
-- `SplitNode Node` carrier (same reason as Piii32 / Piii56).
set_option maxHeartbeats 800000 in
private lemma not_bif_source_copy1
    {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {W₂ : Finset Node} (hDisj : Disjoint W₁ W₂)
    {w : Node} {y : SplitNode Node}
    (p : Walk (G.nodeSplittingOn W₁ hW₁)
            (SplitNode.copy1 w) y)
    (hp_bif : p.IsBifurcation)
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast,
                  z ∈ W₂.image SplitNode.unsplit) :
    False := by
  obtain ⟨_hne, _hu_tail, _hv_drop, i, hi⟩ := hp_bif
  cases p with
  | nil _ _ =>
      simp only [Walk.IsBifurcationWithSplit] at hi
  | @cons _ _ mid sStep p' =>
      cases sStep with
      | forwardE _ =>
          cases p' with
          | nil _ _ =>
              cases i with
              | zero =>
                  simp only [Walk.IsBifurcationWithSplit] at hi
              | succ k =>
                  simp only [Walk.IsBifurcationWithSplit] at hi
          | cons _ _ _ =>
              cases i with
              | zero =>
                  simp only [Walk.IsBifurcationWithSplit] at hi
              | succ k =>
                  simp only [Walk.IsBifurcationWithSplit] at hi
      | bidir h_L =>
          change s(SplitNode.copy1 w, mid) ∈
              G.L.image (Sym2.map (toCopy0 W₁)) at h_L
          obtain ⟨s', _, hs'_eq⟩ := Finset.mem_image.mp h_L
          induction s' using Sym2.ind with
          | _ b c =>
              change s(toCopy0 W₁ b, toCopy0 W₁ c) =
                     s(SplitNode.copy1 w, mid) at hs'_eq
              rcases Sym2.eq_iff.mp hs'_eq with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact toCopy0_ne_copy1 h1
              · exact toCopy0_ne_copy1 h2
      | backwardE h_E =>
          change (mid, SplitNode.copy1 w) ∈
              G.E.image (fun e => (toCopy1 W₁ e.1, toCopy0 W₁ e.2)) ∪
                W₁.image
                  (fun w' => (SplitNode.copy0 w', SplitNode.copy1 w'))
            at h_E
          rcases Finset.mem_union.mp h_E with hLift | hTrans
          · obtain ⟨e', _, he'_eq⟩ := Finset.mem_image.mp hLift
            have h_e2 : toCopy0 W₁ e'.2 = SplitNode.copy1 w :=
              congrArg Prod.snd he'_eq
            exact toCopy0_ne_copy1 h_e2
          · obtain ⟨w', _, hw'_eq⟩ := Finset.mem_image.mp hTrans
            have h2 : SplitNode.copy1 w' = SplitNode.copy1 w :=
              congrArg Prod.snd hw'_eq
            have h1 : SplitNode.copy0 w' = mid :=
              congrArg Prod.fst hw'_eq
            have hw'w : w' = w := by injection h2
            rw [hw'w] at h1
            have h_mid : mid = SplitNode.copy0 w := h1.symm
            cases p' with
            | nil _ _ =>
                cases i with
                | zero =>
                    simp only [Walk.IsBifurcationWithSplit] at hi
                | succ k =>
                    simp only [Walk.IsBifurcationWithSplit] at hi
            | @cons _ _ mid' sStep' p2 =>
                have h_pv_ne : p2.vertices ≠ [] :=
                  Walk.vertices_ne_nil p2
                have hmid_inter : mid ∈ W₂.image SplitNode.unsplit := by
                  apply hp_inter
                  change mid ∈ (mid :: p2.vertices).dropLast
                  rw [List.dropLast_cons_of_ne_nil h_pv_ne]
                  exact List.mem_cons_self
                rw [h_mid] at hmid_inter
                obtain ⟨_, _, hcontra⟩ := Finset.mem_image.mp hmid_inter
                cases hcontra

-- W₁¹-exclusion (target side, auxiliary on bifurcation index).
--
-- Pattern-matched recursive `lemma` mirroring the original.  Body
-- shifts: replace `.cons _ a _ p'` (4-arg) with `.cons _ sStep p'`
-- (3-arg), case-split on `sStep` instead of the
-- ordered-pair-plus-Prop disjunction `⟨ha, hOr⟩ | ⟨ha, hE⟩`.
-- The `.bidir h_L` single-edge case at i=0 with `.nil` tail gives
-- direct contradiction via `Sym2.ind` + `toCopy0_ne_copy1`.
-- The hinge-cum-directed-tail case at i=0 with `.cons` tail goes
-- through `walk_target_copy1_source_copy0` to force
-- `mid = .copy0 w`, then `hp_inter` gives the
-- `.copy0 ≠ .unsplit` contradiction.
private lemma not_bif_target_copy1_aux
    {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {W₂ : Finset Node} (hDisj : Disjoint W₁ W₂)
    {w : Node} (hwW₁ : w ∈ W₁) :
    ∀ {x : SplitNode Node}
      (p : Walk (G.nodeSplittingOn W₁ hW₁) x
              (SplitNode.copy1 w))
      (i : ℕ),
      p.IsBifurcationWithSplit i →
      (∀ z ∈ p.vertices.tail.dropLast,
          z ∈ W₂.image SplitNode.unsplit) →
      False
  | _, .nil _ _, _, hi, _ => by
      simp only [Walk.IsBifurcationWithSplit] at hi
  | _, .cons _ sStep (.nil _ _), 0, hi, _ => by
      cases sStep with
      | forwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | backwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | bidir h_L =>
          change s(_, SplitNode.copy1 w) ∈
              G.L.image (Sym2.map (toCopy0 W₁)) at h_L
          obtain ⟨s', _, hs'_eq⟩ := Finset.mem_image.mp h_L
          induction s' using Sym2.ind with
          | _ b c =>
              change s(toCopy0 W₁ b, toCopy0 W₁ c) =
                     s(_, SplitNode.copy1 w) at hs'_eq
              rcases Sym2.eq_iff.mp hs'_eq with ⟨_, h2⟩ | ⟨h1, _⟩
              · exact toCopy0_ne_copy1 h2
              · exact toCopy0_ne_copy1 h1
  | _, .cons _ sStep (.nil _ _), _ + 1, hi, _ => by
      cases sStep with
      | forwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | backwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | bidir _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
  | _, .cons mid sStep (.cons mid' sStep' p2), 0, hi, h_inter => by
      cases sStep with
      | forwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | backwardE _ =>
          have hp'_dir :
              (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                mid' sStep' p2).IsDirectedWalk := hi
          have hp'_pos :
              (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                mid' sStep' p2).length ≥ 1 := by
            change p2.length + 1 ≥ 1; omega
          have hp'_inter :
              ∀ z ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                  mid' sStep' p2).vertices.tail.dropLast,
                z ∈ W₂.image SplitNode.unsplit := by
            intro z hz
            apply h_inter
            change z ∈ (mid :: p2.vertices).dropLast
            have h_ne : p2.vertices ≠ [] :=
              Walk.vertices_ne_nil _
            rw [List.dropLast_cons_of_ne_nil h_ne]
            refine List.mem_cons_of_mem _ ?_
            change z ∈ p2.vertices.dropLast
            exact hz
          have h_src_eq : mid = SplitNode.copy0 w :=
            walk_target_copy1_source_copy0 (hW₁ := hW₁) hDisj hwW₁
              (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                mid' sStep' p2)
              hp'_dir hp'_pos hp'_inter
          have hmid_inter : mid ∈ W₂.image SplitNode.unsplit := by
            apply h_inter
            change mid ∈ (mid :: p2.vertices).dropLast
            have h_ne : p2.vertices ≠ [] :=
              Walk.vertices_ne_nil _
            rw [List.dropLast_cons_of_ne_nil h_ne]
            exact List.mem_cons_self
          rw [h_src_eq] at hmid_inter
          obtain ⟨_, _, hcontra⟩ := Finset.mem_image.mp hmid_inter
          cases hcontra
      | bidir _ =>
          have hp'_dir :
              (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                mid' sStep' p2).IsDirectedWalk := hi
          have hp'_pos :
              (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                mid' sStep' p2).length ≥ 1 := by
            change p2.length + 1 ≥ 1; omega
          have hp'_inter :
              ∀ z ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                  mid' sStep' p2).vertices.tail.dropLast,
                z ∈ W₂.image SplitNode.unsplit := by
            intro z hz
            apply h_inter
            change z ∈ (mid :: p2.vertices).dropLast
            have h_ne : p2.vertices ≠ [] :=
              Walk.vertices_ne_nil _
            rw [List.dropLast_cons_of_ne_nil h_ne]
            refine List.mem_cons_of_mem _ ?_
            change z ∈ p2.vertices.dropLast
            exact hz
          have h_src_eq : mid = SplitNode.copy0 w :=
            walk_target_copy1_source_copy0 (hW₁ := hW₁) hDisj hwW₁
              (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                mid' sStep' p2)
              hp'_dir hp'_pos hp'_inter
          have hmid_inter : mid ∈ W₂.image SplitNode.unsplit := by
            apply h_inter
            change mid ∈ (mid :: p2.vertices).dropLast
            have h_ne : p2.vertices ≠ [] :=
              Walk.vertices_ne_nil _
            rw [List.dropLast_cons_of_ne_nil h_ne]
            exact List.mem_cons_self
          rw [h_src_eq] at hmid_inter
          obtain ⟨_, _, hcontra⟩ := Finset.mem_image.mp hmid_inter
          cases hcontra
  | _, .cons mid sStep (.cons mid' sStep' p2), k + 1, hi, h_inter => by
      cases sStep with
      | forwardE _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | bidir _ =>
          simp only [Walk.IsBifurcationWithSplit] at hi
      | backwardE _ =>
          have hi_rec :
              (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                mid' sStep' p2).IsBifurcationWithSplit k := by
            simp only [Walk.IsBifurcationWithSplit] at hi
            exact hi
          have hp'_inter :
              ∀ z ∈ (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
                  mid' sStep' p2).vertices.tail.dropLast,
                z ∈ W₂.image SplitNode.unsplit := by
            intro z hz
            apply h_inter
            change z ∈ (mid :: p2.vertices).dropLast
            have h_ne : p2.vertices ≠ [] :=
              Walk.vertices_ne_nil _
            rw [List.dropLast_cons_of_ne_nil h_ne]
            refine List.mem_cons_of_mem _ ?_
            change z ∈ p2.vertices.dropLast
            exact hz
          exact not_bif_target_copy1_aux hDisj hwW₁
            (Walk.cons (G := G.nodeSplittingOn W₁ hW₁)
              mid' sStep' p2)
            k hi_rec hp'_inter

-- Wrapper over the recursive `not_bif_target_copy1_aux`.
-- Body identical to the original modulo the refactor_ prefix.
private lemma not_bif_target_copy1
    {G : CDMG Node} {W₁ : Finset Node}
    {hW₁ : W₁ ⊆ G.V} {W₂ : Finset Node} (hDisj : Disjoint W₁ W₂)
    {w : Node} (hwW₁ : w ∈ W₁) {x : SplitNode Node}
    (p : Walk (G.nodeSplittingOn W₁ hW₁) x
            (SplitNode.copy1 w))
    (hp_bif : p.IsBifurcation)
    (hp_inter : ∀ z ∈ p.vertices.tail.dropLast,
                  z ∈ W₂.image SplitNode.unsplit) :
    False := by
  obtain ⟨_, _, _, i, hi⟩ := hp_bif
  exact not_bif_target_copy1_aux hDisj hwW₁ p i hi hp_inter

-- ## Refactor replacements — Phase iii.F (L-field equality and main theorem).
--
-- Body shifts:
--   1. L-shape change: LHS is one `Finset.image (Sym2.mk)` layer
--      over an ordered-pair filter; RHS is TWO layers — inner
--      `Finset.image (Sym2.mk)` (from the marginalize-on-G's L)
--      and outer `Finset.image (Sym2.map (toCopy0 W₁))`
--      (from the nodeSplittingOn-on-(marg G)'s L lift).
--   2. The original Piii62 cast both sides to ordered-pair filter
--      equality.  Under refactor, we use `induction r using Sym2.ind`
--      to destructure a Sym2 element on each side and reduce to the
--      ordered-pair witness construction.

-- L-field equality for Part (iii).  LHS / RHS Sym2-image layers
-- differ structurally: LHS = `filter.image (Sym2.mk)`; RHS =
-- `filter.image (Sym2.mk).image (Sym2.map (toCopy0 W₁))`.
-- Strategy: destructure Sym2 element via `Sym2.ind`, peel image
-- layers via `Finset.mem_image.mp/mpr`, use `split_marg_PhiL_iff`
-- for the bidirectional ΦL conversion, `exists_underlying_of_mem_split_V_marg_not_copy1`
-- for the carrier descent, and `not_bif_source_copy1` /
-- `not_bif_target_copy1` for the W₁¹-exclusion (these gate
-- the existence of `u, v` with `e1' = toCopy0 u, e2' = toCopy0 v`).
-- Heartbeats raised: the `change` operations against the deep nested
-- structure equality on the V / W₂.image carrier and the marginalize
-- + nodeSplittingOn L composition is expensive on the
-- `SplitNode Node` carrier.
set_option maxHeartbeats 6400000 in
private lemma split_marg_L_field_eq
    {G : CDMG Node} (W₁ : Finset Node) (hW₁ : W₁ ⊆ G.V)
    (W₂ : Finset Node) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    ((G.nodeSplittingOn W₁ hW₁).marginalize
        (W₂.image SplitNode.unsplit)
        (image_unsplit_subset_nodeSplittingOn_V_of_disjoint hW₁ hW₂ hDisj.symm)).L
      = ((G.marginalize W₂ hW₂).nodeSplittingOn W₁
          (subset_sdiff_of_disjoint hW₁ hDisj)).L := by
  apply Finset.ext
  intro r
  change
    r ∈ (((((G.V \ W₁).image SplitNode.unsplit ∪
                W₁.image SplitNode.copy0
              ∪ W₁.image SplitNode.copy1)
              \ W₂.image SplitNode.unsplit) ×ˢ
          (((G.V \ W₁).image SplitNode.unsplit ∪
                W₁.image SplitNode.copy0
              ∪ W₁.image SplitNode.copy1)
              \ W₂.image SplitNode.unsplit)).filter
        (fun e => e.1 ≠ e.2 ∧
          (G.nodeSplittingOn W₁ hW₁).MarginalizationΦL
            (W₂.image SplitNode.unsplit) e.1 e.2)).image
        (fun e => s(e.1, e.2))
    ↔ r ∈ ((((G.V \ W₂) ×ˢ (G.V \ W₂)).filter
              (fun e => e.1 ≠ e.2 ∧ G.MarginalizationΦL W₂ e.1 e.2)).image
            (fun e => s(e.1, e.2))).image (Sym2.map (toCopy0 W₁))
  induction r using Sym2.ind with
  | _ e1 e2 =>
    constructor
    · intro h_lhs
      obtain ⟨⟨e1', e2'⟩, h_mem, h_eq⟩ := Finset.mem_image.mp h_lhs
      rw [Finset.mem_filter, Finset.mem_product] at h_mem
      obtain ⟨⟨h1, h2⟩, hNe, hPhi⟩ := h_mem
      change e1' ∈ _ at h1
      change e2' ∈ _ at h2
      change e1' ≠ e2' at hNe
      change (G.nodeSplittingOn W₁ hW₁).MarginalizationΦL
          (W₂.image SplitNode.unsplit) e1' e2' at hPhi
      -- W₁¹-exclusion for both endpoints.
      have h_e1'_not_copy1 : ∀ w, e1' ≠ SplitNode.copy1 w := by
        intro w hcopy_eq
        have hwW₁ : w ∈ W₁ := by
          rw [hcopy_eq] at h1
          obtain ⟨h_in_v, _⟩ := Finset.mem_sdiff.mp h1
          rcases Finset.mem_union.mp h_in_v with h12 | h_c1
          · rcases Finset.mem_union.mp h12 with h_uns | h_c0
            · obtain ⟨_, _, h_uns_eq⟩ := Finset.mem_image.mp h_uns
              cases h_uns_eq
            · obtain ⟨_, _, h_c0_eq⟩ := Finset.mem_image.mp h_c0
              cases h_c0_eq
          · obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h_c1
            have hw'w : w' = w := by injection hw'_eq
            exact hw'w ▸ hw'W₁
        rcases hPhi with ⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩
        · exact not_bif_source_copy1 (hW₁ := hW₁) hDisj (hcopy_eq ▸ p)
            (by cases hcopy_eq; exact hp_bif)
            (by cases hcopy_eq; exact hp_inter)
        · exact not_bif_target_copy1 (hW₁ := hW₁) hDisj hwW₁ (hcopy_eq ▸ p)
            (by cases hcopy_eq; exact hp_bif)
            (by cases hcopy_eq; exact hp_inter)
      have h_e2'_not_copy1 : ∀ w, e2' ≠ SplitNode.copy1 w := by
        intro w hcopy_eq
        have hwW₁ : w ∈ W₁ := by
          rw [hcopy_eq] at h2
          obtain ⟨h_in_v, _⟩ := Finset.mem_sdiff.mp h2
          rcases Finset.mem_union.mp h_in_v with h12 | h_c1
          · rcases Finset.mem_union.mp h12 with h_uns | h_c0
            · obtain ⟨_, _, h_uns_eq⟩ := Finset.mem_image.mp h_uns
              cases h_uns_eq
            · obtain ⟨_, _, h_c0_eq⟩ := Finset.mem_image.mp h_c0
              cases h_c0_eq
          · obtain ⟨w', hw'W₁, hw'_eq⟩ := Finset.mem_image.mp h_c1
            have hw'w : w' = w := by injection hw'_eq
            exact hw'w ▸ hw'W₁
        rcases hPhi with ⟨p, hp_bif, hp_inter⟩ | ⟨p, hp_bif, hp_inter⟩
        · exact not_bif_target_copy1 (hW₁ := hW₁) hDisj hwW₁ (hcopy_eq ▸ p)
            (by cases hcopy_eq; exact hp_bif)
            (by cases hcopy_eq; exact hp_inter)
        · exact not_bif_source_copy1 (hW₁ := hW₁) hDisj (hcopy_eq ▸ p)
            (by cases hcopy_eq; exact hp_bif)
            (by cases hcopy_eq; exact hp_inter)
      obtain ⟨u, hu, hu_eq⟩ :=
        exists_underlying_of_mem_split_V_marg_not_copy1
          hW₁ hDisj e1' h1 h_e1'_not_copy1
      obtain ⟨v, hv, hv_eq⟩ :=
        exists_underlying_of_mem_split_V_marg_not_copy1
          hW₁ hDisj e2' h2 h_e2'_not_copy1
      refine Finset.mem_image.mpr ⟨s(u, v), ?_, ?_⟩
      · refine Finset.mem_image.mpr ⟨(u, v), ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, ?_, ?_⟩
        · intro huv
          apply hNe
          change u = v at huv
          rw [hu_eq, hv_eq, huv]
        · have huv_ne : u ≠ v := by
            intro huv
            apply hNe
            rw [hu_eq, hv_eq, huv]
          rw [hu_eq, hv_eq] at hPhi
          exact (split_marg_PhiL_iff hW₁ hDisj huv_ne).mp hPhi
      · change s(toCopy0 W₁ u, toCopy0 W₁ v) = s(e1, e2)
        rw [← hu_eq, ← hv_eq]
        exact h_eq
    · intro h_rhs
      obtain ⟨r', hr'_mem, hr'_eq⟩ := Finset.mem_image.mp h_rhs
      obtain ⟨⟨u, v⟩, h_uv_mem, h_uv_eq⟩ := Finset.mem_image.mp hr'_mem
      rw [Finset.mem_filter, Finset.mem_product] at h_uv_mem
      obtain ⟨⟨hu_in, hv_in⟩, hNe, hPhi⟩ := h_uv_mem
      change u ∈ _ at hu_in
      change v ∈ _ at hv_in
      change u ≠ v at hNe
      change G.MarginalizationΦL W₂ u v at hPhi
      have hr'_eq' : s(toCopy0 W₁ u, toCopy0 W₁ v) = s(e1, e2) := by
        rw [← h_uv_eq] at hr'_eq
        exact hr'_eq
      refine Finset.mem_image.mpr
        ⟨(toCopy0 W₁ u, toCopy0 W₁ v), ?_, hr'_eq'⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
      · exact mem_split_V_marg_of_mem_V_W₂_toCopy0 hW₁ hu_in
      · exact mem_split_V_marg_of_mem_V_W₂_toCopy0 hW₁ hv_in
      · intro h_eq
        exact hNe (toCopy0_inj_node h_eq)
      · exact (split_marg_PhiL_iff hW₁ hDisj hNe).mpr hPhi

-- Main theorem (Part iii): marginalisation and node-splitting commute.
--
-- Two structural shifts from the original:
--   1. `CDMG` → `CDMG`: the structure drops from 9 fields
--      to 8 (no `hL_symm`, since Sym2 makes bidirected-edge symmetry
--      definitional).  The local `cdmgExt` `rintro` destructure
--      shrinks to 8 anonymous slots accordingly.
--   2. The four field equalities J / V / E / L route through the
--      refactor_* twins of the auxiliary lemmas
--      (`split_marg_E_field_eq`, `split_marg_L_field_eq`).
--      The V plumbing is unchanged modulo
--      `SplitNode → SplitNode`.
-- Heartbeats raised: the `cdmgExt`-driven decomposition descends into
-- the deeply-nested record literal of the (split.marg) and
-- (marg.split) `CDMG` values, which Lean spends time
-- reducing via WHNF on the `SplitNode Node` carrier.
set_option maxHeartbeats 6400000 in
-- claim_3_18 -- start statement
theorem marginalize_nodeSplittingOn_comm (G : CDMG Node)
    (W₁ W₂ : Finset Node) (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V)
    (hDisj : Disjoint W₁ W₂) :
    (G.nodeSplittingOn W₁ hW₁).marginalize
        (W₂.image SplitNode.unsplit)
        (image_unsplit_subset_nodeSplittingOn_V_of_disjoint hW₁ hW₂ hDisj.symm)
      = (G.marginalize W₂ hW₂).nodeSplittingOn W₁
        (subset_sdiff_of_disjoint hW₁ hDisj)
-- claim_3_18 -- end statement
:= by
  -- ## CDMG extensionality (8-field destructure; no `hL_symm`).
  have cdmgExt : ∀ {G₁ G₂ : CDMG (SplitNode Node)},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨_, _, _, _, _, _, _, _⟩
           ⟨_, _, _, _, _, _, _, _⟩ hJ hV hE hL
    obtain rfl := hJ; obtain rfl := hV; obtain rfl := hE; obtain rfl := hL; rfl
  refine cdmgExt ?_ ?_ ?_ ?_
  · -- J: marginalize and nodeSplittingOn both preserve
    -- G.J's image under SplitNode.unsplit.
    rfl
  · -- V: split.V \ W₂.unsplit = ((G.V \ W₂) \ W₁).image .unsplit ∪ W₁.image .copy0 ∪ W₁.image .copy1
    change ((G.V \ W₁).image SplitNode.unsplit ∪
              W₁.image SplitNode.copy0
              ∪ W₁.image SplitNode.copy1)
              \ (W₂.image SplitNode.unsplit)
        = ((G.V \ W₂) \ W₁).image SplitNode.unsplit
              ∪ W₁.image SplitNode.copy0
              ∪ W₁.image SplitNode.copy1
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨h_main, h_notW₂⟩
      rcases h_main with (h_uns_or_c0 | h_c1)
      · rcases h_uns_or_c0 with h_uns | h_c0
        · obtain ⟨v, ⟨hvV, hvNW₁⟩, rfl⟩ := h_uns
          refine Or.inl (Or.inl ⟨v, ⟨⟨hvV, ?_⟩, hvNW₁⟩, rfl⟩)
          intro hvW₂
          exact h_notW₂ ⟨v, hvW₂, rfl⟩
        · exact Or.inl (Or.inr h_c0)
      · exact Or.inr h_c1
    · rintro (h_uns_or_c0 | h_c1)
      · rcases h_uns_or_c0 with h_uns | h_c0
        · obtain ⟨v, ⟨⟨hvV, hvNW₂⟩, hvNW₁⟩, rfl⟩ := h_uns
          refine ⟨Or.inl (Or.inl ⟨v, ⟨hvV, hvNW₁⟩, rfl⟩), ?_⟩
          rintro ⟨w, hw, hEq⟩
          have : w = v := by injection hEq
          exact hvNW₂ (this ▸ hw)
        · obtain ⟨w, hw, rfl⟩ := h_c0
          refine ⟨Or.inl (Or.inr ⟨w, hw, rfl⟩), ?_⟩
          rintro ⟨v, _, hEq⟩
          cases hEq
      · obtain ⟨w, hw, rfl⟩ := h_c1
        refine ⟨Or.inr ⟨w, hw, rfl⟩, ?_⟩
        rintro ⟨v, _, hEq⟩
        cases hEq
  · -- E
    exact split_marg_E_field_eq W₁ hW₁ W₂ hW₂ hDisj
  · -- L
    exact split_marg_L_field_eq W₁ hW₁ W₂ hW₂ hDisj

end CDMG

end Causality
