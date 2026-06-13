import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_2.MarginalizationAK

namespace Causality

/-!
# Marginalizations commute (`claim_3_17`)

This file formalises the LN lemma `claim_3_17`
(`\label{marginalizations-commute}` in `graphs.tex`):

> Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ V` two disjoint
> subsets of output nodes.  Then
> `(G^{∖W₁})^{∖W₂} = (G^{∖W₂})^{∖W₁} = G^{∖(W₁ ∪ W₂)}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_17_statement_MarginalizationsCommute.tex`, verified equivalent
to the LN block.  `addition_to_the_LN` is empty for this row.  The
rewritten tex decomposes the LN's displayed triple equality into the
conjunction of two binary equalities:

* (a) `(G^{∖W₁})^{∖W₂} = G^{∖(W₁ ∪ W₂)}`,
* (b) `(G^{∖W₂})^{∖W₁} = G^{∖(W₁ ∪ W₂)}`.

Transitivity of equality recovers the LN's "swap symmetry" reading
`(G^{∖W₁})^{∖W₂} = (G^{∖W₂})^{∖W₁}` from (a) ∧ (b).

The disjointness hypothesis `W₁ ∩ W₂ = ∅` is load-bearing for the
*typing* of the iterated marginalisations: `def_3_14`
(`MarginalizationAK.lean`) requires its `W` argument to be a subset of
the input CDMG's output-node set `V`, and the inner marginalisation
`G.marginalize W₁ hW₁` has output-node set `G.V \ W₁`; the outer
marginalisation by `W₂` is therefore well-typed iff
`W₂ ⊆ G.V \ W₁`, which follows from `W₂ ⊆ G.V` plus
`Disjoint W₁ W₂`.  Symmetric for the mirror.  The joint
marginalisation needs only `W₁ ∪ W₂ ⊆ G.V`, immediate from `hW₁`
and `hW₂` via `Finset.union_subset` (disjointness is *not* needed on
the joint side).

The body is filled in by `prove_claim_in_lean` (Manager B), following
the to-be-written tex proof at
`tex/claim_3_17_proof_MarginalizationsCommute.tex`.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`) and `def_3_14` (`MarginalizationAK.lean`).
--   Both fixtures are load-bearing for this row's statement because
--   the signature references `CDMG Node` and `G.marginalize`
--   (`def_3_14`), each of which depends on `[DecidableEq Node]` through
--   the `Finset`-backed membership and filter operations on `G.V`,
--   `G.E`, `G.L`, and the marginalised `G.V \ W` carrier.  Stronger
--   instances (`Fintype`, `LinearOrder`) are not needed at the
--   statement level and are deferred to the proof body's use sites.
-- claim_3_17 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_17 --- end helper

-- ## Helper — disjoint-subset transport into the marginalised carrier
--
-- The main theorem signature evaluates `(G.marginalize W₁ hW₁).marginalize
-- W₂ ?_`, which per `def_3_14`'s signature (`MarginalizationAK.lean`)
-- requires
-- `?_ : W₂ ⊆ (G.marginalize W₁ hW₁).V`,
-- and `(G.marginalize W₁ hW₁).V` reduces definitionally to `G.V \ W₁`
-- (item ii of `def_3_14`).  The rewritten tex's "Well-typedness of the
-- iterated and joint marginalizations" paragraph derives this from the
-- two hypotheses `W₂ ⊆ G.V` and `Disjoint W₁ W₂` via the standard
-- set identity "`A ⊆ B \ C ↔ A ⊆ B ∧ A ∩ C = ∅`".  We expose the
-- transport as a stand-alone helper lemma so the theorem signature
-- stays free of inline term-mode plumbing.
--
-- ## Design choice
--
-- *Wrapped with `--- start helper` so the rendered statement on the
--   website is self-contained.*  The main theorem signature consumes
--   this lemma twice — once for the inner-`hW` of the
--   `W₁`-then-`W₂` composition (with `S = W₂`, `T = W₁`), once for the
--   inner-`hW` of the `W₂`-then-`W₁` composition (with `S = W₁`,
--   `T = W₂`).  Without the helper, both inner subset-arguments would
--   inline a `Finset.subset_sdiff.mpr ⟨…, …⟩` term, bloating the
--   rendered theorem and forcing a reader to know the lemma's iff
--   shape.  Mirrors the helper pattern in the sibling
--   `HardInterventionsCommute.lean` (`claim_3_4`).
--
-- *Phrased as `S ⊆ G.V → Disjoint T S → S ⊆ G.V \ T`, the form the
--   call site consumes directly.*  Equivalent reformulations
--   considered and rejected:
--   * A bare `Finset.subset_sdiff` rewrite (`S ⊆ G.V \ T ↔ S ⊆ G.V ∧
--     Disjoint S T`) was rejected because it would force every call
--     site to apply `.mpr` and rearrange the conjunction's
--     disjointness orientation.
--   * A version pinned to a specific `(G : CDMG Node)` was rejected
--     because the lemma is purely about `Finset` set-difference; the
--     `G.V` instantiation happens at the call site.
--
-- *Implicit `S`, `T`; explicit `hS`, `hDisj`.*  At the call sites
--   `subset_sdiff_of_disjoint hW₂ hDisj.symm` and
--   `subset_sdiff_of_disjoint hW₁ hDisj`, the implicit `S` and `T`
--   are synthesised from the goal and the calls read left-to-right
--   as "the carrier-subset hypothesis is `hS`; the disjointness
--   witness is `hDisj`/`hDisj.symm`".
--
-- *Note on `Disjoint` orientation.*  `Finset.subset_sdiff` packages
--   the disjointness as `Disjoint S T` (the *transported* set vs the
--   *removed* set).  For the `W₁`-then-`W₂` composition we have
--   `hDisj : Disjoint W₁ W₂` and need `Disjoint W₂ W₁`, so the call
--   site passes `hDisj.symm`.  For the swapped composition we need
--   `Disjoint W₁ W₂` directly, so the call site passes `hDisj`.
--
-- *Hypothesis shape `Disjoint S T`, not `S ∩ T = ∅`.*  The two are
--   semantically equivalent on `Finset Node`
--   (`Finset.disjoint_iff_inter_eq_empty`), but `Finset.subset_sdiff`
--   is phrased natively against the `Disjoint` typeclass — taking
--   the literal-`∩ = ∅` form here would force every call site to
--   thread an `Iff.mp` / `Iff.mpr` rewrite through the equivalence.
--   `Disjoint` is also the chapter-3-wide canonical shape
--   (`def_3_1`'s `hJV_disj`, `def_3_14`'s `marginalize_hJV_disj`,
--   and the analogous disjointness binder on the main theorem
--   below), so the helper's API parses uniformly with its
--   surroundings.  Semantic content is identical to the LN's literal
--   "$W_1 \cap W_2 = \emptyset$".
--
-- *Term-mode one-liner `Finset.subset_sdiff.mpr ⟨hS, hDisj⟩`, not a
--   tactic proof.*  The conclusion `S ⊆ U \ T` is a direct
--   restatement of the mathlib iff
--   `Finset.subset_sdiff : S ⊆ U \ T ↔ S ⊆ U ∧ Disjoint S T`; a
--   `by`-block (`by rw [Finset.subset_sdiff]; exact ⟨hS, hDisj⟩`)
--   would add tactic-state noise for zero readability gain, would
--   inflate the rendered helper on the website, and would obscure
--   that the helper is *literally* one direction of a named mathlib
--   iff (so a maintainer can pattern-match it on sight).
--
-- *`private`.*  Localises the lemma to this file.  Future rows that
--   compose marginalisations (or any operator producing a `V \ W`
--   carrier) should re-introduce the same helper at their use site
--   rather than reach across files; if a chapter-wide reuse pattern
--   emerges, the helper can be promoted in a later refactor.
-- claim_3_17 --- start helper
private lemma subset_sdiff_of_disjoint {S T : Finset Node}
    {U : Finset Node} (hS : S ⊆ U) (hDisj : Disjoint S T) :
    S ⊆ U \ T
-- claim_3_17 --- end helper
:= Finset.subset_sdiff.mpr ⟨hS, hDisj⟩

-- ref: claim_3_17
-- For any CDMG `G : CDMG Node`, any two subsets `W₁, W₂ ⊆ G.V` with
-- `Disjoint W₁ W₂`, the LN's triple equality
--   `(G^{∖W₁})^{∖W₂} = (G^{∖W₂})^{∖W₁} = G^{∖(W₁ ∪ W₂)}`
-- decomposes into two binary CDMG equalities:
--   (a) `(G.marginalize W₁ hW₁).marginalize W₂ … =
--         G.marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)`,
--   (b) `(G.marginalize W₂ hW₂).marginalize W₁ … =
--         G.marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)`.
-- Transitivity of equality then recovers the LN's "swap symmetry"
-- `(G.marginalize W₁ hW₁).marginalize W₂ … =
--  (G.marginalize W₂ hW₂).marginalize W₁ …` from (a) ∧ (b).
/-
LN tex (rewritten canonical statement for `claim_3_17`, in essence):

  Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ V` with
  `W₁ ∩ W₂ = ∅`.  Then
    (a) `(G^{∖W₁})^{∖W₂} = G^{∖(W₁ ∪ W₂)}`,
    (b) `(G^{∖W₂})^{∖W₁} = G^{∖(W₁ ∪ W₂)}`.

LN block (verbatim, for backup):

  Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ V` two disjoint
  subsets of output nodes.  Then we have:
    `(G^{∖W₁})^{∖W₂} = (G^{∖W₂})^{∖W₁} = G^{∖(W₁ ∪ W₂)}`.
-/
-- ## Design choice
--
-- *One theorem returning a conjunction (Option A from the worker
--   prompt), not two separate top-level theorems.*  The LN's
--   `\begin{Lem}` block is one lemma joining three CDMGs in a triple
--   equality `A = B = C`; the rewritten canonical statement file
--   explicitly decomposes this into the conjunction of two binary
--   equalities (a) `A = C` and (b) `B = C`.  Lean has no native
--   triple-equality syntax, so a single theorem returning
--   `(a) ∧ (b)` is the literal Lean rendering, mirroring the
--   rewrite's decomposition.  Consumers reach `.1` for (a) and `.2`
--   for (b); the LN's "swap symmetry" reading
--   `(G.marginalize W₁ hW₁).marginalize W₂ … =
--    (G.marginalize W₂ hW₂).marginalize W₁ …` is recovered as
--   `.1.trans .2.symm` (so no separate `A = B` sub-claim is needed —
--   transitivity of `=` does it for free, as the rewrite's closing
--   remark licenses).  Splitting into two named theorems was
--   rejected because it would (i) duplicate the antecedents `hW₁`,
--   `hW₂`, `hDisj` at the theorem-head level, and (ii) diverge from
--   the rewrite's single-lemma packaging.  Matches the sibling
--   pattern in `HardInterventionsCommute.lean` (`claim_3_4`), which
--   also packages its two sub-claims as a single theorem returning
--   a conjunction.
--
-- *Conjunction order (a) ∧ (b), matching the rewrite and the LN
--   reading order.*  The rewrite's `enumerate[label=(\alph*)]` block
--   lists (a) `W₁`-then-`W₂` first, (b) `W₂`-then-`W₁` second; we
--   preserve that order in the Lean conjunction so the natural `.1`
--   / `.2` projections line up with the (a) / (b) labels of the
--   rewrite.
--
-- *Right-hand side `G.marginalize (W₁ ∪ W₂) (Finset.union_subset
--   hW₁ hW₂)`, with the union-subset proof term inlined.*  The proof
--   term `Finset.union_subset hW₁ hW₂ : W₁ ∪ W₂ ⊆ G.V` is a mathlib
--   one-liner not worth a named helper; both sub-claims share the
--   same right-hand side and the same proof term, so the conjunction
--   reads with literal `=`-symmetry between (a) and (b).  Note the
--   *joint* marginalisation does not consume `hDisj` — the LN-tex's
--   "Well-typedness" paragraph flagged that disjointness is needed
--   only for the iterated forms.
--
-- *Inner-`hW` for the nested marginalisations via
--   `subset_sdiff_of_disjoint`.*  The outer `.marginalize W₂` (in
--   (a)) and `.marginalize W₁` (in (b)) need a subset proof against
--   the carrier `(G.marginalize Wᵢ hWᵢ).V = G.V \ Wᵢ` of the
--   inner-marginalised CDMG, not against `G.V`.  The helper lemma
--   `subset_sdiff_of_disjoint` transports the hypothesis across the
--   carrier identity that the rewritten tex's "Well-typedness"
--   paragraph proves verbatim.  Inlining a `by`-block in the type
--   was rejected because it would (i) bloat the rendered statement
--   on the website, and (ii) duplicate the carrier-matching
--   reasoning at every use site.
--
-- *Three independent theorem hypotheses `hW₁ : W₁ ⊆ G.V`, `hW₂ : W₂
--   ⊆ G.V`, `hDisj : Disjoint W₁ W₂`, NOT two derived-subset proofs
--   (e.g. `hW₁ : W₁ ⊆ G.V` and `hW₂' : W₂ ⊆ G.V \ W₁`) baked into
--   the binders.*  The LN's premise block lists three independent
--   facts ("$W_1 \ins V$", "$W_2 \ins V$", "$W_1 \cap W_2 =
--   \emptyset$"), and the rewritten tex's "Well-typedness" paragraph
--   factors the typing precondition for the inner-`W₂` argument
--   exactly into the conjunction of `W₂ ⊆ G.V` and disjointness.
--   Baking the derived subset `W₂ ⊆ G.V \ W₁` into the binder would
--   (i) conflate the LN's clean premise list with an internal
--   calculation about `marginalize`'s domain, (ii) force every call
--   site to discharge the less-natural fact `W₂ ⊆ G.V \ W₁`
--   (downstream consumers will almost always have `W₂ ⊆ G.V` plus
--   disjointness, not the conjoined sdiff-subset on a plate), and
--   (iii) break the LN-level symmetry between the `W₁`-then-`W₂`
--   and `W₂`-then-`W₁` readings — one binder would carry
--   `W₂ ⊆ G.V \ W₁`, the other would need `W₁ ⊆ G.V \ W₂`, doubling
--   the derived plumbing.  The derived subset proofs are instead
--   supplied *at the marginalisation call sites inside the
--   signature* via `subset_sdiff_of_disjoint hW₂ hDisj.symm` and
--   `subset_sdiff_of_disjoint hW₁ hDisj`, keeping the theorem-head
--   binder list isomorphic to the LN's premise list.
--
-- *`Disjoint W₁ W₂`, not `W₁ ∩ W₂ = ∅`.*  The two are equivalent on
--   `Finset Node` (`Finset.disjoint_iff_inter_eq_empty`).  We pick
--   the `Disjoint`-typeclass form because (i) mathlib's
--   `Finset.subset_sdiff` is phrased against `Disjoint`, so the
--   helper lemma `subset_sdiff_of_disjoint` consumes it directly
--   without a wrapper rewrite, and (ii) `Disjoint` is the canonical
--   shape used everywhere in chapter 3 (`def_3_1`'s `hJV_disj`,
--   `def_3_14`'s `marginalize_hJV_disj`, the sibling
--   `claim_3_8`/`claim_3_11` disjoint-intervention rows).  The
--   semantic content is identical to the LN's literal "$W_1 \cap
--   W_2 = \emptyset$".
--
-- *CDMG equality (`=`) is read field-wise.*  Equality of two `CDMG`s
--   unfolds via the `structure` injectivity from `def_3_1` to the
--   conjunction of equalities on the four data fields `J`, `V`, `E`,
--   `L` (the five propositional fields of `def_3_1` are
--   propositional and Lean's proof irrelevance discharges them
--   automatically).  We do not bake the field-wise unpacking into
--   the *statement*; it is deferred to the proof per the rewritten
--   tex's closing remark "the conjunctive unpacking into the four
--   field-by-field equalities is deferred to the proof".
--
-- *`W₁` / `W₂` and `hW₁` / `hW₂` quantified at the theorem head,
--   matching `marginalize`'s binder convention.*  `def_3_14`
--   (`MarginalizationAK.lean`) takes `(W : Finset Node) (hW : W ⊆
--   G.V)` as explicit arguments; we reuse the same shape so call
--   sites `G.marginalize Wᵢ hWᵢ` parse identically here and at every
--   downstream consumer.  The binder shape
--   `(G : CDMG Node) (W₁ W₂ : Finset Node) (hW₁ hW₂ : … ⊆ G.V)
--    (hDisj : Disjoint W₁ W₂)` is a direct echo of `def_3_14`'s
--   signature with `W` / `hW` replicated for the two marginalisation
--   sets plus the disjointness rider that makes the iterated forms
--   well-typed.
--
-- *Degenerate cases admitted.*  All three quantifiers are read
--   universally; the (vacuously disjoint) degenerate cases
--   `W₁ = W₂ = ∅`, `W₁ = ∅` alone, and `W₂ = ∅` alone are all
--   admitted by this signature.  In each case the triple equality
--   collapses (e.g.\ `W₁ = W₂ = ∅` reduces to `G = G = G`); the
--   theorem remains true and the signature does not pre-emptively
--   exclude them.
-- claim_3_17 -- start statement
theorem marginalize_comm (G : CDMG Node) (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.V) (hW₂ : W₂ ⊆ G.V) (hDisj : Disjoint W₁ W₂) :
    (G.marginalize W₁ hW₁).marginalize W₂
        (subset_sdiff_of_disjoint hW₂ hDisj.symm)
      = G.marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)
    ∧
    (G.marginalize W₂ hW₂).marginalize W₁
        (subset_sdiff_of_disjoint hW₁ hDisj)
      = G.marginalize (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)
-- claim_3_17 -- end statement
:= sorry

end CDMG

end Causality
