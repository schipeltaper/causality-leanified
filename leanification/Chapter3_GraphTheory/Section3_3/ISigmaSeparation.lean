import Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks

namespace Causality

/-!
# i-σ-separation (`def_3_18`)

This file formalises `def_3_18` (`\label{def:sigma_separation}`), the
fifth definition of Section 3.3 of the lecture notes.  Given a CDMG
`G = (J, V, E, L)` and subsets `A, B, C ⊆ J ∪ V` (not necessarily
disjoint, nor disjoint from `J`, nor non-empty), the row introduces:

* `G.IsISigmaSeparated A B C` — `A \isPerp_G B \given C`: every walk
  `π : Walk G u v` (per `def_3_4` item i.) with `u ∈ A` and
  `v ∈ J ∪ B` is `C`-σ-blocked in the sense of `def_3_17`
  (`SigmaBlockedWalks.lean`).  The asymmetric inclusion of `J` on the
  right is the LN's deliberate, non-standard choice (LN footnote): it
  is what makes the implied separoid rules for `id` / `iσ`-separation
  match those of Markov-kernel conditional independence.
* `G.IsNotISigmaSeparated A B C` — `A \nisPerp_G B \given C`: the
  negation, definitionally `¬ G.IsISigmaSeparated A B C`.
* `G.IsISigmaSeparatedEmpty A B` — `A \isPerp_G B`: the unconditional
  (`C = ∅`) shorthand of `G.IsISigmaSeparated A B ∅`.
* `G.IsSigmaSeparated A B C` — `A \sPerp_G B \given C`: the LN's
  `J = ∅` notation alias of `G.IsISigmaSeparated A B C`.
* `G.IsNotSigmaSeparated A B C` — `A \nsPerp_G B \given C`: the
  `J = ∅` notation alias of `G.IsNotISigmaSeparated A B C`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/def_3_18_ISigmaSeparation.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:sigma_separation}`) augmented with one operator
clarification:

* `[sigma_symmetry_claim_invokes_unstated_reversal_invariance]` — the
  trailing LN remark on `σ`-separation symmetry is recorded as
  background only.  The symmetry claim itself is the dedicated
  separate claim row `claim_3_22`
  (`SigmaSeparationSymmetric`); no Lean obligation is derived from
  the embedded `claimmark` within this definition.

## Design pillars

1. **`Set Node`-valued node-subset arguments `A B C`.**  Matches the
   conditioning-set carrier of `def_3_17`'s `IsSigmaBlockedGiven`
   (which already takes `C : Set Node`) and the family-set carriers
   of `def_3_5` (`Pa`, `Anc`, etc.).  No `A, B, C ⊆ J ∪ V` hypothesis
   is enforced at the def site: out-of-graph nodes contribute
   vacuously (there are no walks with such endpoints in `G`), and
   downstream consumers that need the subset constraint can add it
   at the use site.  Matches the LN's "not necessarily disjoint, nor
   disjoint from `J`, nor non-empty" permissiveness.

2. **Walk quantifier with `{u v : Node}` implicit, `(π : Walk G u v)`
   explicit.**  Mirrors `def_3_16`'s `IsBlockableNonCollider`
   `{u v : Node} (p : Walk G u v) (k : ℕ)` binder shape: endpoints
   are inferred from the walk's type and never need to be named at
   the call site.  Length-zero walks (`Walk.nil`) are in scope by
   construction — the per-position predicate `IsSigmaBlockedGiven`
   handles them via its existential over collider / blockable
   non-collider positions, which is empty on a length-zero walk
   (hence such walks are σ-open, NOT σ-blocked, when reachable from
   `A` into `J ∪ B`).

3. **Asymmetric endpoint constraint `v ∈ (G.J : Set Node) ∪ B`.**
   The right endpoint of the walk lives in `J ∪ B`, not in `B`.
   This is the LN's deliberate non-standard inclusion of `J`,
   flagged in footnote `fn:why-J`.  As a direct consequence the
   marginal case `B = ∅` is *not* vacuous when `J ≠ ∅`:
   `G.IsISigmaSeparated A ∅ C` asserts every walk from `A` into the
   input nodes `J` is `C`-σ-blocked.  The coercion
   `(G.J : Set Node)` lifts `G.J : Finset Node` to the carrier of
   `B`, matching the pattern used in `def_3_5`'s `NonDesc`.

4. **Negation as a definitionally-equal `def`, not a fresh
   existential.**  `IsNotISigmaSeparated` unfolds to
   `¬ IsISigmaSeparated` — the LN's `\nisPerp` is purely a
   notation for the negation of `\isPerp`, not a new concept.  The
   tex spec's "equivalently, ∃ walk … not C-σ-blocked"
   reformulation is the classical De Morgan dual of the negated
   universal, not a parallel definition.  Keeping the negation
   definitional avoids a redundant existential encoding.

5. **`abbrev` for the unconditional `C = ∅` shorthand; `def` with
   explicit `hJ : G.J = ∅` for the `J = ∅` renames.**  Item 3 of
   the LN is a pure notation alias `A \isPerp_G B :=
   A \isPerp_G B \given ∅` — encoded as `abbrev` so
   `IsISigmaSeparatedEmpty A B` reduces to
   `IsISigmaSeparated A B ∅` at every elaboration site without an
   `unfold` step.  Item 4 renames the predicate under `J = ∅`;
   encoded as `def` with explicit `(hJ : G.J = ∅)` premise so the
   σ-vs-iσ-name distinction stays visible at the call site (an
   `abbrev` would unfold eagerly and erase `hJ` from goal displays
   at unrelated tactic steps).
-/

end Causality

namespace Causality

namespace CDMG

-- def_3_18 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_18 --- end helper


-- ref: def_3_18 (item 1).
--
-- `G.IsISigmaSeparated A B C hA hB hC` encodes the LN's
-- `A \isPerp_G B \given C`: every walk `π : Walk G u v` with `u ∈ A`
-- and `v ∈ J ∪ B` is `C`-σ-blocked in the sense of `def_3_17`'s
-- `IsSigmaBlockedGiven`.
--
-- ## Design choice — IsISigmaSeparated
--
-- *Asymmetric `J`-inclusion on the right.*  The right-endpoint
--   constraint `v ∈ (G.J : Set Node) ∪ B` (rather than the symmetric
--   `v ∈ B` reading standard in the d-separation literature) is the
--   LN's deliberate non-standard choice flagged in footnote
--   `fn:why-J` of `graphs.tex \label{def:sigma_separation}`.  With
--   `J` included on the right, the implied (asymmetric) separoid
--   rules for `id`/`iσ`-separation match the corresponding rules for
--   conditional independence under Markov kernels — directly
--   payload-bearing for the separoid axiom "J-Inverted Right
--   Decomposition" used in `scms4.tex`.  Corollary
--   (`empty_b_non_vacuous_when_j_nonempty`):
--   `G.IsISigmaSeparated A ∅ C hA hB hC` is NOT vacuous when
--   `G.J ≠ ∅` — it asserts every walk from `A` to the input nodes
--   `J` is `C`-σ-blocked.  Only at `J = ∅` (the σ-rename of item 4
--   below, gated by `(hJ : G.J = ∅)`) does the right-endpoint
--   constraint collapse to `v ∈ B` and recover the usual "separation
--   from the empty set is vacuous" reading.
--
-- *Flat `∀`-over-walks shape, NOT a quotient by reversal-classes.*
--   An alternative shape was considered and rejected: replace the
--   universal over walks with one over reversal-equivalence-classes
--   under the involution flagged by the operator-authored addition
--   `[sigma_symmetry_claim_invokes_unstated_reversal_invariance]`.
--   Three independent reasons rule it out:
--   (a) The addition is BACKGROUND for the standalone σ-symmetry
--   claim `claim_3_22` (`SigmaSeparationSymmetric`) and does NOT
--   motivate a structural re-encoding here — `claim_3_22`'s proof
--   transports across the involution given a flat `∀`-walk shape.
--   (b) Every downstream `A ⊥^iσ B | C` consumer (chapter 4+
--   Markov-property, do-calculus, iSCM identification, plus the
--   σ-independence model / causal-relations / minimal-separating-
--   sets infrastructure) pattern-matches on this def's flat
--   `∀`-over-walks shape directly.  A quotient re-encoding would
--   force every consumer to dispatch through a quotient lift
--   (`Quot.mk` / `Quot.lift`) at each invocation, scrambling the
--   1-to-1 LN-to-Lean correspondence the canonical tex commits to.
--   (c) The asymmetric `J`-inclusion above would be *lost* under
--   reversal-class collapse, because walk reversal swaps endpoints
--   but `J` is not symmetric in `(u, v)`.
--
-- *Downstream consumers.*  Immediate downstream consumers are items
--   2-5 below (the negation `IsNotISigmaSeparated`, the unconditional
--   `C = ∅` abbrev `IsISigmaSeparatedEmpty`, the `J = ∅` σ-name
--   aliases `IsSigmaSeparated` and `IsNotSigmaSeparated`), each
--   forwarding to this predicate.  The driving downstream consumer
--   is `claim_3_22` `SigmaSeparationSymmetric`
--   (`SigmaSeparationSymmetric.lean`).  Further downstream
--   (chapter 4+), every Markov-property / do-calculus / iSCM
--   identification result that mentions `A ⊥^iσ B | C` pattern-
--   matches on this def's universal-over-walks shape with the
--   asymmetric `J ∪ B` right-endpoint reading.
--
-- *Operator-authored addition
--   `[sigma_symmetry_claim_invokes_unstated_reversal_invariance]`.*
--   The LN-faithful reading of σ-separation-symmetry — walk
--   reversal is an involution on the set of walks, and σ-blocking
--   conditions on internal nodes are stated in a manner invariant
--   under reversal — is treated as BACKGROUND at this row.  The
--   symmetry claim itself is `claim_3_22`
--   (`SigmaSeparationSymmetric`); no Lean obligation is derived
--   here from the embedded `claimmark`.  `claim_3_22`'s eventual
--   Lean proof draws on the structural reversal invariance of
--   `Walk` and `IsSigmaBlockedGiven` directly.
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def IsISigmaSeparated (G : CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  ∀ {u v : Node} (π : Walk G u v),
      u ∈ A → v ∈ (G.J : Set Node) ∪ B → π.IsSigmaBlockedGiven C hC
-- def_3_18 -- end statement


-- ref: def_3_18 (item 2).
--
-- `G.IsNotISigmaSeparated A B C hA hB hC` encodes the LN's
-- `A \nisPerp_G B \given C`: the definitional negation of
-- `G.IsISigmaSeparated A B C`.  Equivalently (by classical
-- De Morgan, not by Lean reduction): there exists a walk
-- `π : Walk G u v` with `u ∈ A`, `v ∈ J ∪ B`, and
-- `¬ π.IsSigmaBlockedGiven C hC`.
--
-- ## Design choice — IsNotISigmaSeparated
--
-- *Definitional negation, not a positive existential.*  The LN's
--   `\nisPerp` is purely notation for the negation of `\isPerp`,
--   not a new concept.  Keeping the negation definitional preserves
--   the link with item 1 and avoids a classical bridging lemma at
--   every interconversion site.  The tex spec's "equivalently, ∃
--   walk … not C-σ-blocked" reformulation is the classical De Morgan
--   dual of the negated universal, not a parallel definition.
--
-- *Downstream consumers.*  The immediate downstream consumer is
--   item 5's `IsNotSigmaSeparated`, which renames this predicate
--   under `J = ∅`.  Future consumers include any claim that
--   pattern-matches on `A \nisPerp_G B \given C` (chapter 4+ Markov
--   properties, do-calculus).
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def IsNotISigmaSeparated (G : CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  ¬ G.IsISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement


-- ref: def_3_18 (item 3).
--
-- `G.IsISigmaSeparatedEmpty A B hA hB` encodes the LN's
-- unconditional shorthand `A \isPerp_G B := A \isPerp_G B \given ∅`.
-- Unfolds eagerly (via `abbrev`) to
-- `G.IsISigmaSeparated A B ∅ hA hB (Set.empty_subset _)`.
--
-- ## Design choice — IsISigmaSeparatedEmpty
--
-- *`abbrev` over `def`.*  The LN spells `A \isPerp_G B` as pure
--   notation for `A \isPerp_G B \given ∅`, not a new concept.
--   `abbrev`'s eager-unfolding semantics means every consumer
--   pattern-matches on item 1's flat `∀`-over-walks shape directly,
--   with no wrapper dispatch.
--
-- *Two-binder signature.*  No `hC` — discharged automatically via
--   `Set.empty_subset _` at the abbrev site.  Matches the LN's
--   `A \isPerp_G B` surface syntax.
--
-- *Empty-`B` non-vacuous when `J ≠ ∅`
--   (`empty_b_non_vacuous_when_j_nonempty`).*  Unfolding via this
--   `abbrev` yields `G.IsISigmaSeparated A ∅ ∅ hA hB
--   (Set.empty_subset _)`, which asserts every walk from `A` to
--   `G.J ∪ ∅ = G.J` is `∅`-σ-blocked — a genuine condition.
--   Downstream Markov-property results in chapter 4+ pattern-match
--   on this through the abbrev's transparent surface.
-- def_3_18 -- start statement
abbrev IsISigmaSeparatedEmpty (G : CDMG Node) (A B : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.IsISigmaSeparated A B ∅ hA hB (Set.empty_subset _)
-- def_3_18 -- end statement


-- ref: def_3_18 (item 4).
--
-- `G.IsSigmaSeparated hJ A B C hA hB hC` encodes the LN's
-- `A \sPerp_G B \given C`: the `J = ∅` notation alias of
-- `G.IsISigmaSeparated A B C`.  The underlying predicate is
-- identical — the `J = ∅` specialisation is a property of the
-- consumer's CDMG, not a logical condition on the body.  Under
-- `J = ∅` the right-endpoint constraint `v ∈ J ∪ B` reduces to
-- `v ∈ B`, so `A \sPerp_G B \given C` reads as "every walk from `A`
-- to `B` is `C`-σ-blocked" in the standard literature sense.
--
-- ## Design choice — IsSigmaSeparated
--
-- *`def` over `abbrev`.*  Keeps the σ-vs-iσ name distinction visible
--   in goal displays at call sites; an `abbrev` would unfold eagerly
--   and erase the σ-name and `hJ` from goal displays at unrelated
--   tactic steps.
--
-- *Two-layer separation: body forwards to iσ; `hJ` is consumer's
--   responsibility.*  The body forwards directly to
--   `G.IsISigmaSeparated A B C hA hB hC` — a single-line wrapper.
--   Item 1's asymmetric `J ∪ B` right-endpoint reading is encoded
--   once in the underlying iσ def; the σ-rename layer adds NO new
--   endpoint-membership re-statement.  The `(hJ : G.J = ∅)` premise
--   is a property of the consumer's CDMG, not a logical condition
--   on the body.  `IsSigmaSeparated hJ A B C hA hB hC` reduces by
--   `simp only [IsSigmaSeparated, IsISigmaSeparated]` to the
--   universal-over-walks statement with `v ∈ (G.J : Set Node) ∪ B`;
--   the `hJ` evidence is available in scope for the consumer to
--   rewrite the union to `v ∈ B` when they need the literature-
--   standard form.  An alternative encoding — a stand-alone
--   σ-separation `def` with `v ∈ B` hard-coded, or a `DMG`-typeclass
--   instance argument replacing `hJ` — would either duplicate item
--   1's body or introduce a `DMG` typeclass dependency `def_3_18`
--   does not otherwise need.
--
-- *Downstream consumers.*  The driving downstream consumer is
--   `claim_3_22` `SigmaSeparationSymmetric` (stated purely in
--   σ-separation language for `J = ∅`): the symmetry proof closes
--   by walk reversal acting on the σ-blocked existential.  Other
--   consumers include chapter 4+ Markov-property results that
--   state the no-input special case in σ-language before lifting
--   to the general iσ form.
--
-- *Operator-authored addition
--   `[sigma_symmetry_claim_invokes_unstated_reversal_invariance]`.*
--   The LN-faithful reading of the symmetry justification — walk
--   reversal is an involution on the set of walks and σ-blocking
--   conditions on internal nodes are stated invariantly under
--   reversal — is treated as BACKGROUND at this row.  No
--   σ-symmetry-level code in this file performs the proof;
--   `claim_3_22`'s eventual Lean proof draws on these structural
--   properties of `Walk` and `IsSigmaBlockedGiven` directly.
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def IsSigmaSeparated (G : CDMG Node) (hJ : G.J = ∅) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.IsISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement


-- ref: def_3_18 (item 4, negation).
--
-- `G.IsNotSigmaSeparated hJ A B C hA hB hC` encodes the LN's
-- `A \nsPerp_G B \given C`: the `J = ∅` notation alias of
-- `G.IsNotISigmaSeparated A B C`.
--
-- ## Design choice — IsNotSigmaSeparated
--
-- *Mirror with `IsSigmaSeparated`.*  The pair (`IsSigmaSeparated`,
--   `IsNotSigmaSeparated`) under `J = ∅` matches the LN's
--   (`\sPerp`, `\nsPerp`) notation pair.  Downstream case splits in
--   claim statements alternate between the two names with the same
--   `hJ` evidence at both, so the signatures mirror each other.
--
-- *Explicit `hJ` premise, signature-mirror only.*  The negation's
--   truth-value follows from item 2's truth-value (which has no
--   `hJ`), so this row's `hJ` is kept purely for σ/¬σ-name-pairing
--   symmetry with item 4.
--
-- *`def` over `abbrev`.*  Same rationale as item 4: preserve the
--   σ-name distinction in goal displays at call sites.  An
--   alternative encoding as a positive existential `∃ walk, …`
--   (literature-standard σ-non-separation form) would break the
--   definitional link with item 4 via item 2 via item 1, forcing
--   every σ-vs-¬σ case split through a classical De Morgan bridging
--   lemma.
--
-- *Downstream consumers.*  Pairs with item 4's `IsSigmaSeparated`
--   in σ-vs-¬σ case splits — claim statements and proof case splits
--   in chapter 3+ alternate between the two names.
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def IsNotSigmaSeparated (G : CDMG Node) (hJ : G.J = ∅) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.IsNotISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement

end CDMG

end Causality
