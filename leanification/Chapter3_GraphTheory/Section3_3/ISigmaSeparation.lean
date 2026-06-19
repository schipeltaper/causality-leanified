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

namespace CDMG

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Matches
--   the chapter convention set by every prior file in Section 3.3
--   (`CollidersAndNon.lean`, `BlockableAndUnblockable.lean`,
--   `SigmaBlockedWalks.lean`, `AcyclicNonCollidersBlockable.lean`).
--   Without the `variable` the wrapped predicate signatures below
--   have free type variables and fail to type-check.
--
-- *Three-dash `--- start helper` / `--- end helper` markers, not
--   two-dash `-- start statement`.*  Lean 4's `variable` auto-binding
--   folds these implicit binders into every declaration below — they
--   are load-bearing infrastructure, not throwaway local sugar.
-- def_3_18 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_18 --- end helper

-- ref: def_3_18 (item 1)
--
-- `G.IsISigmaSeparated A B C` iff every walk `π : Walk G u v` with
-- `u ∈ A` and `v ∈ J ∪ B` is `C`-σ-blocked in the sense of
-- `def_3_17`.  This is the LN's `A \isPerp_G B \given C`.
/-
LN tex (item 1 of `def_3_18`, rewritten canonical statement):

  A is i-σ-separated from B given C in G, in symbols
    A ⫫ⁱˢ_G B | C,
  iff for every integer n ≥ 0 and every walk
    π = (v_0, a_0, v_1, …, v_{n-1}, a_{n-1}, v_n)
  in G (def_3_4 item i.) with v_0 ∈ A and v_n ∈ J ∪ B, the walk π is
  C-σ-blocked in the sense of def_3_17.

  The right-hand inclusion of J is the deliberate, non-standard LN
  choice (footnote fn:why-J): it makes the implied separoid rules
  for iσ-separation match those for conditional independence under
  Markov kernels.  Length-zero walks are in scope.
-/
-- ## Design choice
--
-- *`(A B C : Set Node)` as explicit `def` parameters, in that
--   order.*  Mirrors the LN's binder order "A, B, C ⊆ J ∪ V" and
--   matches the `def_3_5` family-set convention.  The conditioning
--   set `C` last keeps the unconditional shorthand
--   `IsISigmaSeparated A B ∅` syntactically lightweight.
--
-- *`Set Node` (not `Finset Node`) for `A`, `B`, `C`.*  The LN's
--   "$A, B, C \ins J \cup V$, not necessarily disjoint, not
--   necessarily non-empty" reading places no finiteness obligation
--   on the three sets and explicitly admits `∅`; `Set Node` is the
--   matching carrier.  `Set Node` also (a) inherits the boolean
--   algebra (`∪`, `∩`, `\`, `∅`) needed to spell `J ∪ B` and
--   `C = ∅` directly, (b) interoperates with `G.AncSet : Set Node →
--   Set Node` (used inside `IsSigmaBlockedGiven`) without any extra
--   coercion, and (c) matches def_3_17's `IsSigmaBlockedGiven`,
--   which already takes `C : Set Node`.  A `Finset Node` shape was
--   considered and rejected: it would force every consumer to
--   supply a `Finset` even in proofs that only need set algebra,
--   would not interoperate with `G.AncSet` directly, and would not
--   reflect the LN's "not necessarily non-empty" / arbitrary-subset
--   permissiveness.  Consumers that happen to have a
--   `s : Finset Node` can always pass `(↑s : Set Node)`.
--
-- *Walk-first universal `∀ {u v} (π : Walk G u v), u ∈ A → … → …`,
--   not membership-first.*  The walk is the primary subject of the
--   universal; the endpoint memberships are properties of the
--   walk's endpoints.  This reads as "for every walk π with
--   v_0 ∈ A and v_n ∈ J ∪ B, π is C-σ-blocked", word-for-word with
--   the LN.  An alternative form
--     `∀ {u} ∈ A, ∀ {v} ∈ J ∪ B, ∀ (π : Walk G u v), …`
--   was considered: equivalent but pushes membership ahead of the
--   walk and reads as "for every starting and ending node, for
--   every walk between them" — one extra layer of nesting at the
--   call site.
--
-- *Endpoint constraint `v ∈ (G.J : Set Node) ∪ B`, NOT
--   `((G.J ∪ B) : Set Node)` and NOT `v ∈ G.J ∨ v ∈ B`.*  `G.J`
--   has type `Finset Node` (from `CDMG.J : Finset Node`) and `B`
--   has type `Set Node`; the Finset-level union `G.J ∪ B` is
--   ill-typed (no `HAdd`/`Union` instance between `Finset Node`
--   and `Set Node`), so the only well-typed move is to coerce
--   `G.J` to `Set Node` first and then take the set-union with
--   `B`.  This differs from `def_3_5`'s `NonDesc`, which forms
--   `((G.J ∪ G.V : Finset Node) : Set Node)` because *both* sides
--   of the inner union are `Finset Node` — that Finset-level
--   union is well-typed there and produces a single `Finset`
--   coerced once.  Here `B` is already a `Set`, so we coerce the
--   `Finset` side and union at the `Set` level.  The set-union
--   form additionally lifts every `Set`-algebra lemma
--   (`Set.mem_union`, `Set.union_empty`, `Set.empty_union`,
--   `Set.union_comm`) directly to walks of `IsISigmaSeparated`.
--   Spelling the constraint as `v ∈ G.J ∨ v ∈ B` would be
--   definitionally equivalent (via `Set.mem_union`) but lose the
--   `J ∪ B`-as-a-set reading that the LN's notation expects.
--
-- *Asymmetric inclusion of `J` on the right is deliberate, not a
--   typo.*  The LN explicitly flags this in footnote
--   `fn:why-J`: including `J` on the right side of the walk
--   endpoint makes the implied (asymmetric) separoid rules for
--   `id`-/`iσ`-separation match the rules for conditional
--   independence under Markov kernels.  This is load-bearing for
--   chapter 4+ (Markov properties / CBNs), where the Lean
--   formalisation will need to pattern-match on exactly this
--   shape.  Future readers tempted to "fix" the asymmetry — e.g.
--   by symmetrising to `(G.J : Set Node) ∪ B ∪ A` on the right,
--   or by dropping `J` to recover the usual literature
--   convention — should not.  Direct consequence: the marginal
--   case `B = ∅` is *not* vacuous when `G.J ≠ ∅`.  The wording-
--   check subtlety `empty_b_non_vacuous_when_j_nonempty` records
--   this; the canonical tex's "Asymmetric inclusion of $J$ on the
--   right" paragraph pins down the precise statement
--   (`A ⫫ⁱˢ_G ∅ | C` asserts every walk from `A` into `J` is
--   `C`-σ-blocked).
--
-- *Walks of every length, including the trivial (length-zero)
--   walk, are in scope.*  Lean's `∀ (π : Walk G u v)` ranges over
--   both `Walk.nil` (n = 0) and `Walk.cons` (n ≥ 1) constructors.
--   When `u = v` and there exists `a ∈ A ∩ (J ∪ B)`, the trivial
--   walk `Walk.nil a _ : Walk G a a` is admitted by the
--   quantifier.  Whether such a walk is `C`-σ-blocked is determined
--   by `def_3_17`'s `IsSigmaBlockedGiven` at the length-zero case
--   (the existential over collider / blockable non-collider
--   positions on `Walk.nil` is empty, hence the length-zero walk is
--   *not* `C`-σ-blocked — `IsSigmaBlockedGiven` is `False` on
--   `Walk.nil`).  This is the formalizer's downstream observation
--   recorded in the canonical tex paragraph "Range of the walk
--   quantifier"; it is *not* a fresh hypothesis here, and the
--   length-zero range is *not* a vacuous edge of the definition
--   when `A ∩ (J ∪ B) ≠ ∅`.  The wording-check subtlety
--   `overlap_with_j_or_target_creates_self_walks` records the
--   downstream surprise: e.g. `G.IsISigmaSeparated A A C`
--   degenerates to a condition that every `a ∈ A` has its trivial
--   self-walk `Walk.nil a _` not be `C`-σ-blocked, which since
--   `IsSigmaBlockedGiven` on `Walk.nil` is `False` cannot hold
--   for any non-empty `A`; consumers reaching for "separation of
--   `A` from itself = True" should be aware.
--
-- *`Walk.IsSigmaBlockedGiven` reused verbatim from `def_3_17`
--   (`SigmaBlockedWalks.lean`).*  The LN's "π is σ-blocked by C"
--   is exactly that predicate.  Dot-notation
--   `π.IsSigmaBlockedGiven C` reads as the LN does, and is the
--   unit this whole definition quantifies over.  Encoding the
--   blocking condition inline (via the existential disjunction of
--   `def_3_17`) was rejected: it would duplicate the
--   `SigmaBlockedWalks.lean` body and break the per-row LN-grep
--   correspondence.  Downstream proofs that need the unfolded
--   existential disjunction can `unfold IsSigmaBlockedGiven` at
--   the use site.

-- ## Design choice — subset premises on `A`, `B`, `C`
--
-- *Three explicit subset hypotheses
--   `(hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V)
--   (hC : C ⊆ ↑G.J ∪ ↑G.V)` on the predicate itself, not on
--   downstream theorem sites and not bundled.*  The LN writes
--   "$A, B, C \ins J \cup V$" once at the head of the separation
--   block — three named, per-set premises mirror that exactly and
--   close the silent-admission leak the predicate would otherwise
--   exhibit (a caller could pass arbitrary `Set Node` including
--   nodes that don't exist in `G`, and the predicate would be
--   well-typed under a meaning the LN never assigned it).
--   Pinning the constraint on the def — not on theorem sites — is
--   the only encoding that closes that leak at the source.
--
-- *Separate named hypotheses, not a bundled
--   `A ∪ B ∪ C ⊆ ↑G.J ∪ ↑G.V` union or an `∧`-conjunction.*
--   Matches the chapter convention from Section 3.2
--   (`HardInterventionsCommute`, `DisjointHardInterventionsSwig`,
--   `AddingInterventionNodes`), each of which carries separate
--   named `(hW₁ : …) (hW₂ : …)` binders rather than `∧`-bundled
--   side conditions.  A bundled form would force every downstream
--   proof to `.1`/`.2.1`/`.2.2`-project the conjunction at the use
--   site and lose the per-set readability the LN's prose relies on.
--
-- *Asymmetric `J` inclusion on the right
--   (`v ∈ (G.J : Set Node) ∪ B`).*  LN footnote `fn:why-J` is
--   the load-bearing justification: it makes the implied
--   (asymmetric) separoid rules for `id`-/`iσ`-separation match
--   those for Markov-kernel conditional independence (chapter 4+).
--   This is intentional, not a typo for a future reader to
--   "symmetrise".  The subset hypotheses tighten the predicate's
--   *domain*, not the walk universal's reach into `G.J`; the
--   wording-check subtlety `empty_b_non_vacuous_when_j_nonempty`
--   still applies (`B = ∅` stays non-vacuous when `G.J ≠ ∅`
--   under the restricted domain).
--
-- *Subset premises live only on the signature; body is the
--   walk universal alone.*  The body remains
--   `∀ {u v} (π : Walk G u v), u ∈ A → v ∈ J ∪ B →
--   π.IsSigmaBlockedGiven C`.  `hA`, `hB`, `hC` restrict the
--   domain of definition (which `(A, B, C)` triples the predicate
--   admits), not the semantics of the walk universal.
-- `hA`, `hB`, `hC` are bound on the signature for LN-faithfulness
-- ("$A, B, C \ins J \cup V$") and to close the silent-admission leak
-- documented in the design-choice block above, but the body is the
-- walk-universal over `G`'s own structure and does not consume them
-- (out-of-graph nodes contribute vacuously to the walk universal).
-- The `set_option` matches the chapter convention (`HardInterventionOn`,
-- `NodeSplittingOn`, `NodeSplittingHard`, `AddingInterventionNodes`,
-- `MarginalizationAndIntervention`) for LN-faithful binders that are
-- load-bearing on the *signature* but inert in the body.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsISigmaSeparated
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def IsISigmaSeparated (G : CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  ∀ {u v : Node} (π : Walk G u v),
      u ∈ A → v ∈ (G.J : Set Node) ∪ B → π.IsSigmaBlockedGiven C
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsISigmaSeparated

-- ref: def_3_18 (item 2)
--
-- `G.IsNotISigmaSeparated A B C` is the LN's `A \nisPerp_G B \given
-- C`: the definitional negation of `G.IsISigmaSeparated A B C`.
-- Equivalently (by classical De Morgan, not by Lean reduction):
-- there exists a walk `π : Walk G u v` with `u ∈ A`, `v ∈ J ∪ B`,
-- and `¬ π.IsSigmaBlockedGiven C`.
--
-- ## Design choice
--
-- *Named `def` for the negation, rather than asking downstream
--   sites to spell `¬ G.IsISigmaSeparated A B C`.*  LN item 2
--   introduces `\nisPerp` as named notation for the negation of
--   `\isPerp`; mirroring that with a named Lean `def` keeps
--   downstream statement / claim sites grep-aligned with the LN
--   prose (every LN reference to `A \nisPerp_G B \given C`
--   corresponds to a literal `G.IsNotISigmaSeparated A B C` in
--   Lean).  Without this alias, every downstream invocation would
--   have to inline `¬ G.IsISigmaSeparated A B C`, breaking the
--   one-to-one LN-to-Lean correspondence and forcing readers to
--   reconstruct the LN's named relation from a Lean negation.
--
-- *Definitionally equal to the negation, not a parallel
--   existential.*  Encoding it as `¬ IsISigmaSeparated` keeps the
--   two predicates definitionally linked: `G.IsNotISigmaSeparated
--   A B C` unfolds to `¬ G.IsISigmaSeparated A B C` by `rfl`, so
--   `unfold IsNotISigmaSeparated` and `simp only
--   [IsNotISigmaSeparated]` collapse it to the negation form at
--   any proof site.  Downstream proofs that switch between the
--   two never have to invoke a separate equivalence lemma.  The
--   tex spec's "equivalently, ∃ walk …" reformulation is the
--   classical De Morgan dual of the negated universal —
--   derivable as a one-line lemma when needed, not a parallel
--   definition.  An alternative "positive existential" shape
--   (`∃ {u v} (π : Walk G u v), u ∈ A ∧ v ∈ J ∪ B ∧
--   ¬ π.IsSigmaBlockedGiven C`) was considered: equivalent
--   classically, but it would break the definitional link with
--   `IsISigmaSeparated` and require a classical bridging lemma
--   at every interconversion site.

-- ## Design choice
--
-- *Pure named negation, carrying the same three subset premises
--   as `IsISigmaSeparated`.*  LN item 2 introduces `\nisPerp` as
--   named notation for the negation of `\isPerp` — a named
--   convenience predicate, not a new concept.  Mirroring the
--   subset hypotheses on the underlying iσ predicate keeps the
--   two predicates' call-site signatures aligned (every use of
--   `IsNotISigmaSeparated` already has the data to discharge
--   `IsISigmaSeparated`'s premises), and the body forwards to
--   `¬ IsISigmaSeparated` definitionally — no parallel
--   existential, no bridging lemma.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsNotISigmaSeparated
-- def_3_18 -- start statement
def IsNotISigmaSeparated (G : CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  ¬ G.IsISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsNotISigmaSeparated

-- ref: def_3_18 (item 3)
--
-- `G.IsISigmaSeparatedEmpty A B` is the LN's unconditional shorthand
-- `A \isPerp_G B := A \isPerp_G B \given ∅`.  Unfolds to
-- `G.IsISigmaSeparated A B ∅`.
--
-- ## Design choice
--
-- *`abbrev`, not `def`.*  LN item 3 is pure notation — the
--   symbol `A \isPerp_G B` is *defined to mean* `A \isPerp_G B
--   \given ∅`, not a new concept.  `abbrev` is fully transparent
--   to elaboration: Lean reduces `G.IsISigmaSeparatedEmpty A B`
--   to `G.IsISigmaSeparated A B ∅` at every use site without an
--   `unfold` step, so any lemma that targets the underlying
--   predicate fires automatically on the shorthand and vice
--   versa.  Encoding as `def` would create an opaque alias and
--   force every consumer interchanging the two to invoke
--   `unfold` / `simp only [IsISigmaSeparatedEmpty]` — a wholly
--   gratuitous obstacle given the LN's "is defined as" reading.
--   Same trade-off as the other notation-shorthand sites in
--   chapter 3.
--
-- *No separate negation alias for the C = ∅ case.*  The LN does
--   not introduce a separate symbol for "not unconditionally
--   iσ-separated" — that gap is intentional.  Downstream sites
--   needing this combination spell it as
--   `¬ G.IsISigmaSeparatedEmpty A B` or
--   `G.IsNotISigmaSeparated A B ∅`; the `abbrev`'s transparency
--   makes both interchangeable.

-- ## Design choice — derived predicate for the `C = ∅` case
--
-- *Named derived predicate for the unconditional case
--   `(A B : Set Node) (hA hB)`, not the iσ predicate always
--   carrying a vacuous third subset proof.*  LN item 3 *defines*
--   `A \isPerp_G B` as the special case
--   `A \isPerp_G B \given ∅`; mirroring that with a dedicated
--   `IsISigmaSeparatedEmpty` gives consumers a clean name for the
--   marginal case without making them supply a vacuous third
--   subset proof.  The body forwards to
--   `IsISigmaSeparated A B ∅` and discharges
--   `hC : ∅ ⊆ ↑G.J ∪ ↑G.V` automatically via
--   `Set.empty_subset _`, so the user never has to write the
--   empty-subset proof at the call site.
--
-- *Two subset hypotheses `(hA hB)`, not three.*  The third slot
--   would be a constant `Set.empty_subset _` — making it implicit
--   in the alias keeps the call-site signature minimal and
--   reflects the LN's notation `A \isPerp_G B` (no `C` argument
--   appears).
--
-- *`abbrev`, not `def`.*  Pure notational alias — Lean reduces
--   `G.IsISigmaSeparatedEmpty A B hA hB` to
--   `G.IsISigmaSeparated A B ∅ hA hB (Set.empty_subset _)` at
--   every use site without an explicit `unfold`, so every lemma
--   about the underlying iσ predicate fires automatically on the
--   shorthand and vice versa.  No `hJ` is involved here, so the
--   `def` encoding the σ-aliases below use does not apply.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsISigmaSeparatedEmpty
-- def_3_18 -- start statement
abbrev IsISigmaSeparatedEmpty (G : CDMG Node) (A B : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.IsISigmaSeparated A B ∅ hA hB (Set.empty_subset _)
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsISigmaSeparatedEmpty

-- ref: def_3_18 (item 4)
--
-- `G.IsSigmaSeparated A B C` is the LN's `A \sPerp_G B \given C`:
-- the `J = ∅` notation alias of `G.IsISigmaSeparated A B C`.  The
-- alias keeps the underlying predicate identical — the `J = ∅`
-- specialisation is a property of the consumer's CDMG (a "fact about
-- `G`"), not a logical condition on the predicate.  Under `J = ∅`
-- the right-endpoint constraint `v ∈ J ∪ B` reduces to `v ∈ B`.
--
-- ## Design choice
--
-- *Separate named alias rather than asking downstream consumers
--   to write `IsISigmaSeparated` with `G.J = ∅`.*  LN item 4
--   *renames* the predicate (drops the leading "$i$") for the
--   special case `J = ∅`; the same mathematical object acquires
--   a new name when the input-node set is empty.  Mirroring that
--   with a named Lean alias keeps the LN's terminology
--   available at every downstream call site (most prominently
--   `claim_3_22` `SigmaSeparationSymmetric`, which is stated and
--   proved purely in σ-separation language under `J = ∅`; and
--   chapter 4+'s Markov-property results, which the LN states in
--   σ-separation form for the no-input special case before
--   lifting to the general iσ form).  Without the alias every
--   such consumer would have to spell "the special case of
--   iσ-separation where `J = ∅`", scrambling the LN-to-Lean
--   correspondence on the LN's most-used graphical-separation
--   predicate.
--
-- *No symmetry claim here.*  The LN's embedded `claimmark` for
--   σ-separation symmetry (`claim_3_22`) is intentionally excluded
--   from this row, per the rewritten canonical tex's "Treatment of
--   the trailing LN remark" paragraph and the operator addition
--   `[sigma_symmetry_claim_invokes_unstated_reversal_invariance]`.
--   The symmetry statement and proof live in
--   `claim_3_22_statement_SigmaSeparationSymmetric.tex` /
--   `claim_3_22_proof_SigmaSeparationSymmetric.tex` and its Lean
--   counterpart.  The wording-check subtlety
--   `symmetry_claim_walks_between_wording_imprecise` records the
--   specific gap (LN says "the set of walks between A and B is
--   the same regardless of direction"; the precise content is
--   that walk-reversal is an involution and σ-blocking is
--   invariant under it) — that gap is to be addressed inside
--   `claim_3_22`'s proof, not here.

-- ## Design choice — `J = ∅` hypothesis
--
-- *Explicit `(hJ : G.J = ∅)` premise on the predicate, not a
--   separate `DMG` subtype or typeclass.*  LN item 4 defines
--   `A \sPerp_G B \given C := A \isPerp_G B \given C` *for the
--   special case `J = ∅`* — a notational renaming under the
--   assumption, not a new type.  Taking the equation `G.J = ∅`
--   directly as a hypothesis matches the LN reading word-for-word
--   and keeps the declaration lightweight (no new typeclass, no
--   structure projection at every use site).  Downstream
--   consumers (e.g. `claim_3_22` σ-separation symmetry) can
--   discharge `hJ` directly from their own hypotheses.
--
-- *`def IsDMG (G : CDMG Node) : Prop := G.J = ∅` already exists
--   in `Section3_1/CDMGTypes.lean` (`def_3_7`)* — a downstream
--   consumer who prefers the named property can write
--   `(hDMG : G.IsDMG)` and unfold to `G.J = ∅`.  But this
--   predicate takes the bare equation to stay self-contained
--   relative to the CDMG-property hierarchy and to avoid making
--   def_3_18 transitively depend on def_3_7 (which it otherwise
--   does not need).
--
-- *Same three subset hypotheses as the underlying iσ predicate.*
--   The LN's "$A, B, C \ins J \cup V$" applies under both names;
--   the renaming under `J = ∅` does not loosen the LN's domain of
--   definition.  Body forwards `(A, B, C, hA, hB, hC)` unchanged
--   to `IsISigmaSeparated`.
--
-- *`def`, not `abbrev`.*  With `hJ` as a dependent hypothesis,
--   `abbrev`'s aggressive reducibility becomes a footgun: Lean
--   would unfold the alias eagerly and the `hJ` evidence would
--   disappear from goal displays at unrelated tactic steps.
--   `def` keeps the alias opaque-by-default and preserves the
--   σ-vs-iσ symbolic distinction at every use site.
-- `hJ : G.J = ∅` is bound on the signature for LN-faithfulness ("for
-- the special case $J = \emptyset$") and to keep the σ-/iσ-name
-- distinction visible at the call site, but the body forwards
-- `(A, B, C, hA, hB, hC)` unchanged to `IsISigmaSeparated` —
-- the `J = ∅` precondition is a consumer-side fact about the CDMG,
-- not a logical condition baked into the body.  Same `set_option`
-- convention as `HardInterventionOn` / `NodeSplittingOn` /
-- `NodeSplittingHard` / `AddingInterventionNodes` /
-- `MarginalizationAndIntervention`.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsSigmaSeparated
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def IsSigmaSeparated (G : CDMG Node) (hJ : G.J = ∅) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.IsISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsSigmaSeparated

-- ref: def_3_18 (item 4, negation)
--
-- `G.IsNotSigmaSeparated A B C` is the LN's `A \nsPerp_G B \given C`:
-- the `J = ∅` notation alias of `G.IsNotISigmaSeparated A B C`.
--
-- ## Design choice
--
-- *Mirror of `IsSigmaSeparated`, in the negation direction.*
--   LN item 4 renames `\nisPerp` to `\nsPerp` under `J = ∅` in
--   the same breath that it renames `\isPerp` to `\sPerp`; the
--   pair is introduced as a unit and downstream sites use the
--   pair as a unit (`A \sPerp_G B \given C` and
--   `A \nsPerp_G B \given C` appear side-by-side in claim
--   statements and proof case-splits).  Including the negated
--   alias keeps that pairing intact in Lean.
--
-- *No new content beyond `IsNotISigmaSeparated ∘ rename`.*  In
--   particular this alias does *not* re-introduce the "positive
--   existential" formulation of the negation — the existential
--   reformulation, when needed, remains the standalone classical
--   De Morgan lemma noted in `IsNotISigmaSeparated`'s design
--   block and is shared across both `iσ` and `σ` names.

-- ## Design choice
--
-- *Negation of `IsSigmaSeparated`, carrying the same `(hJ : G.J =
--   ∅)` and three subset premises.*  LN item 4 introduces
--   `\nsPerp` alongside `\sPerp` as the paired negated notation
--   under `J = ∅` — a named convenience predicate, not a new
--   concept; the σ and ¬σ names are introduced and used as a unit
--   (claim statements and proof case-splits alternate between the
--   two), so the predicate signatures stay aligned.  Body
--   forwards to `IsNotISigmaSeparated`.  Same `def` (not
--   `abbrev`) encoding as `IsSigmaSeparated` for the same
--   `hJ`-dependency reason.
-- `hJ : G.J = ∅` is bound on the signature for LN-faithfulness and
-- σ-/iσ-name pairing with `IsSigmaSeparated`, but the body
-- forwards `(A, B, C, hA, hB, hC)` unchanged to
-- `IsNotISigmaSeparated`.  Same `set_option` exemption as
-- `IsSigmaSeparated` above, for the same reason.
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsNotSigmaSeparated
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def IsNotSigmaSeparated (G : CDMG Node) (hJ : G.J = ∅) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.IsNotISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsNotSigmaSeparated

end CDMG

end Causality

namespace Causality

namespace refactor_CDMG

-- ## Design choice — refactor section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same chapter
--   convention used by the original `CDMG` namespace above and by every
--   other `refactor_CDMG`-opening file in the chapter (see
--   `SigmaBlockedWalks.lean:346-348`, `BlockableAndUnblockable.lean`,
--   `CollidersAndNon.lean`, `Section3_1/Walks.lean`,
--   `Section3_1/CDMG.lean`).  The refactor does not alter the carrier-
--   type discipline — only (a) `def_3_1`'s `L`-field shape
--   (`Finset (Sym2 Node)` with `hL_irrefl : ∀ ⦃s⦄, s ∈ L → ¬ s.IsDiag`),
--   (b) `def_3_4`'s per-step walk-edge data (typed `refactor_WalkStep`
--   with three constructors `.forwardE / .backwardE / .bidir`) and the
--   `cons`-cell of `refactor_Walk`, and (c) `def_3_17`'s
--   `refactor_IsSigmaBlockedGiven` added an explicit
--   `hC : C ⊆ ↑G.J ∪ ↑G.V` premise on the signature (per its refactor
--   design block at `SigmaBlockedWalks.lean:709-716`).  Binders below
--   are byte-identical to the original `CDMG`-namespace `variable`
--   line at the top of this file.
--
-- *Three-dash `--- start helper` / `--- end helper`, not two-dash
--   `-- start statement`.*  Lean 4's `variable` auto-binding folds these
--   implicit binders into every refactored declaration below exactly as
--   it does for the originals.  Matches the helper-flavour tagging used
--   by every prior refactor section in this chapter.
-- def_3_18 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_18 --- end helper

-- ref: def_3_18 (item 1) — refactor
--
-- `G.refactor_IsISigmaSeparated A B C hA hB hC` iff every walk
-- `π : refactor_Walk G u v` with `u ∈ A` and `v ∈ J ∪ B` is
-- `C`-σ-blocked in the sense of `def_3_17`'s
-- `refactor_IsSigmaBlockedGiven`.  This is the LN's
-- `A \isPerp_G B \given C` ported against the typed-WalkStep refactor.
--
-- This is the kernel of the σ-separation framework: items 2-5 of
-- def_3_18 (negation, unconditional `C = ∅` shorthand, and the J=∅
-- σ-name aliases) all forward to this predicate, and every downstream
-- chapter (CBNs in ch 4, do-calculus in ch 5, iSCMs in ch 8–10,
-- causal discovery in ch 11+) pattern-matches on the
-- `A ⊥^iσ B | C` notation that ultimately destructures via this def.
--
-- *Upstream-retarget deltas for this REPLACEMENT (self-contained
-- record).*  Three mechanical retargets propagate into the body
-- relative to the pre-refactor encoding:
-- - `CDMG Node` → `refactor_CDMG Node` (root `def_3_1`,
--   `Section3_1/CDMG.lean`): the carrier change is
--   `L : Finset (Sym2 Node)` with
--   `hL_irrefl : ∀ ⦃s⦄, s ∈ L → ¬ s.IsDiag`, replacing the original
--   `L : Finset (Node × Node)` paired with `hL_symm`.  `J` and `V`
--   stay as `Finset Node` and `E` stays as `Finset (Node × Node)`.
-- - `Walk G u v` → `refactor_Walk G u v` (root `def_3_4`,
--   `Section3_1/Walks.lean`): the typed `refactor_WalkStep` with
--   three constructors `.forwardE` / `.backwardE` / `.bidir`
--   replaces the untyped `(Node × Node)` + `Prop`-level `WalkStep`
--   classifier.  A `.bidir` step carries an
--   `h : s(u,v) ∈ G.L` witness in the `Sym2 Node` swap-quotient,
--   so the channel is intrinsic to the constructor tag rather than
--   reconstructed from the stored pair.
-- - `π.IsSigmaBlockedGiven C` → `π.refactor_IsSigmaBlockedGiven C hC`
--   (`def_3_17`'s refactor; `SigmaBlockedWalks.lean:720`): the new
--   `hC : C ⊆ ↑G.J ∪ ↑G.V` premise was added to the σ-blocking
--   signature by `def_3_17`'s refactor (per its design block at
--   `SigmaBlockedWalks.lean:709-716`), so this def now threads `hC`
--   through to the forward call.  We do NOT introduce `hC` here;
--   we merely propagate it.
--
-- ## Design pillars (LN-faithful, encoding-orthogonal)
--
-- *`(A B C : Set Node)` as explicit `def` parameters in that order.*
--   Mirrors the LN's binder order "A, B, C ⊆ J ∪ V" and matches the
--   `def_3_5` family-set convention.  The conditioning set `C` last
--   keeps the unconditional shorthand
--   `refactor_IsISigmaSeparated A B ∅` syntactically lightweight
--   (and enables the `refactor_IsISigmaSeparatedEmpty` `abbrev` below
--   to take only `(A B)` rather than `(A B C)`).
--
-- *`Set Node` (not `Finset Node`) for `A`, `B`, `C`.*  The LN's
--   "$A, B, C \ins J \cup V$, not necessarily disjoint, not
--   necessarily non-empty" reading places no finiteness obligation on
--   the three sets and explicitly admits `∅`; `Set Node` is the
--   matching carrier.  `Set Node` also (a) inherits the boolean
--   algebra (`∪`, `∩`, `\`, `∅`) needed to spell `J ∪ B` and `C = ∅`
--   directly, (b) interoperates with `G.refactor_AncSet : Set Node →
--   Set Node` (used inside `refactor_IsSigmaBlockedGiven`) without
--   any extra coercion, and (c) matches `def_3_17`'s
--   `refactor_IsSigmaBlockedGiven`, which already takes
--   `C : Set Node`.  A `Finset Node` shape was considered and
--   rejected: it would force every consumer to supply a `Finset`
--   even in proofs that only need set algebra, would not
--   interoperate with `refactor_AncSet` directly, and would not
--   reflect the LN's "not necessarily non-empty" / arbitrary-subset
--   permissiveness.  Consumers that happen to have a
--   `s : Finset Node` can always pass `(↑s : Set Node)`.
--
-- *Walk-first universal `∀ {u v} (π : refactor_Walk G u v), u ∈ A →
--   v ∈ J ∪ B → …`, not membership-first and not a positive
--   existential.*  The walk is the primary subject of the universal;
--   the endpoint memberships are properties of the walk's endpoints.
--   This reads as "for every walk π with v_0 ∈ A and v_n ∈ J ∪ B,
--   π is C-σ-blocked", word-for-word with the LN.  An alternative
--   membership-first form
--     `∀ {u} ∈ A, ∀ {v} ∈ J ∪ B, ∀ (π : refactor_Walk G u v), …`
--   was considered: equivalent but pushes membership ahead of the
--   walk and reads as "for every starting and ending node, for every
--   walk between them" — one extra layer of nesting at the call
--   site.  A positive existential reformulation
--     `∃ {u v} (π : refactor_Walk G u v), u ∈ A ∧ v ∈ J ∪ B ∧
--       ¬ π.refactor_IsSigmaBlockedGiven C hC`
--   gives the LN's `\nisPerp` — but as a separate predicate
--   (`refactor_IsNotISigmaSeparated` below), NOT as the encoding of
--   `\isPerp` itself.
--
-- *`{u v : Node}` implicit endpoints.*  Mirrors `def_3_16`'s
--   `refactor_IsBlockableNonCollider {u v : Node}
--   (p : refactor_Walk G u v) (k : ℕ)` binder shape: endpoints are
--   inferred from the walk's type and never need to be named at the
--   call site.  Explicit endpoints would force every caller to spell
--   `IsISigmaSeparated.{u := …, v := …} π …`, breaking the LN's
--   "for every walk π" reading at every use.
--
-- *Endpoint constraint `v ∈ (G.J : Set Node) ∪ B`, NOT
--   `((G.J ∪ B) : Set Node)` and NOT `v ∈ G.J ∨ v ∈ B`.*  `G.J` has
--   type `Finset Node` (`refactor_CDMG.J : Finset Node` — `def_3_1`'s
--   refactor did NOT change the J/V carrier-type discipline; only
--   `L`'s carrier changed) and `B` has type `Set Node`; the
--   Finset-level union `G.J ∪ B` is ill-typed (no instance between
--   `Finset Node` and `Set Node`), so the only well-typed move is to
--   coerce `G.J` to `Set Node` first and then take the set-union
--   with `B`.  This differs from `def_3_5`'s `refactor_NonDesc`,
--   which forms `((G.J ∪ G.V : Finset Node) : Set Node)` because
--   *both* sides of the inner union are `Finset Node` — that
--   Finset-level union is well-typed there and produces a single
--   `Finset` coerced once.  Here `B` is already a `Set`, so we
--   coerce the `Finset` side and union at the `Set` level.  The
--   set-union form additionally lifts every `Set`-algebra lemma
--   (`Set.mem_union`, `Set.union_empty`, `Set.empty_union`,
--   `Set.union_comm`) directly to walks of
--   `refactor_IsISigmaSeparated`.  Spelling the constraint as
--   `v ∈ G.J ∨ v ∈ B` would be definitionally equivalent (via
--   `Set.mem_union`) but lose the `J ∪ B`-as-a-set reading that the
--   LN's notation expects.
--
-- *Asymmetric inclusion of `J` on the right is deliberate, not a
--   typo.*  The LN explicitly flags this in footnote `fn:why-J`:
--   including `J` on the right side of the walk endpoint makes the
--   implied (asymmetric) separoid rules for `id`-/`iσ`-separation
--   match the rules for conditional independence under Markov
--   kernels.  This is load-bearing for chapter 4+ (Markov properties
--   / CBNs), where the Lean formalisation will need to pattern-match
--   on exactly this shape.  Future readers tempted to "fix" the
--   asymmetry — e.g. by symmetrising to `(G.J : Set Node) ∪ B ∪ A`
--   on the right, or by dropping `J` to recover the usual literature
--   convention — should not.
--
-- *Wording-check subtlety `empty_b_non_vacuous_when_j_nonempty`
--   (surfaced by the working-phase LN-critic for `def_3_18`).*
--   Direct consequence of the asymmetric J inclusion above: the
--   marginal case `B = ∅` is *not* vacuous when `G.J ≠ ∅`.
--   `G.refactor_IsISigmaSeparated A ∅ C hA hB hC` literally asserts
--   that every walk in `G` from a node in `A` to a node in `J` is
--   `C`-σ-blocked — a genuine condition, NOT the usual separoid
--   "$A \isPerp \emptyset | C$ is vacuous" reading.  Only when
--   `G.J = ∅` (i.e., we're in `refactor_IsSigmaSeparated`'s J=∅
--   territory) does the usual vacuity reading apply.  Downstream
--   consumers reaching for vacuity should first discharge `G.J = ∅`.
--   The canonical tex spec's "Asymmetric inclusion of $J$ on the
--   right" paragraph pins down the precise statement.
--
-- *Walks of every length, including the trivial (length-zero) walk,
--   are in scope.*  Lean's `∀ (π : refactor_Walk G u v)` ranges over
--   both `refactor_Walk.nil` (n = 0) and `refactor_Walk.cons` (n ≥ 1)
--   constructors.  When `u = v` and there exists
--   `a ∈ A ∩ (J ∪ B)`, the trivial walk `refactor_Walk.nil a _ :
--   refactor_Walk G a a` is admitted by the quantifier.  Whether
--   such a walk is `C`-σ-blocked is determined by `def_3_17`'s
--   `refactor_IsSigmaBlockedGiven` at the length-zero case: the
--   existential over collider / blockable non-collider positions on
--   `nil` is empty, hence the length-zero walk is *not*
--   `C`-σ-blocked — `refactor_IsSigmaBlockedGiven` is `False` on
--   `refactor_Walk.nil`.  The canonical tex's "Range of the walk
--   quantifier" paragraph records this; it is the formalizer's
--   downstream observation, not a fresh hypothesis on this def.
--
-- *Wording-check subtlety
--   `overlap_with_j_or_target_creates_self_walks` (surfaced by the
--   working-phase LN-critic for `def_3_18`).*  The LN explicitly
--   admits `A, B, C` not necessarily disjoint; combined with the
--   asymmetric J inclusion, when `A ∩ (J ∪ B) ≠ ∅` (in particular
--   `A ∩ G.J ≠ ∅`, `A ∩ B ≠ ∅`, or `A = B`) the trivial self-walks
--   at the overlap nodes become part of the walk-universal's scope.
--   Consequence: e.g. `G.refactor_IsISigmaSeparated A A C` degenerates
--   to a condition that every `a ∈ A` has its trivial self-walk
--   `refactor_Walk.nil a _` be `C`-σ-blocked — and since
--   `refactor_IsSigmaBlockedGiven` on `nil` is `False`, this cannot
--   hold for any non-empty `A`.  Consumers reaching for "separation
--   of `A` from itself = True" by separoid intuition should be aware
--   this is structurally false here.  Downstream lemmas that need
--   the disjoint-subsets case must add the disjointness hypothesis
--   at the use site — the def admits the overlap case by LN design.
--
-- *`refactor_Walk.refactor_IsSigmaBlockedGiven` reused verbatim from
--   `def_3_17` (`SigmaBlockedWalks.lean`).*  The LN's "π is σ-blocked
--   by C" is exactly that predicate.  Dot-notation
--   `π.refactor_IsSigmaBlockedGiven C hC` reads as the LN does, and
--   is the unit this whole definition quantifies over.  Encoding the
--   blocking condition inline (via the existential disjunction of
--   `def_3_17`) was rejected: it would duplicate the
--   `SigmaBlockedWalks.lean` body and break the per-row LN-grep
--   correspondence.  Downstream proofs that need the unfolded
--   existential disjunction can `unfold refactor_IsSigmaBlockedGiven`
--   at the use site.
--
-- *Three explicit subset hypotheses
--   `(hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V)
--   (hC : C ⊆ ↑G.J ∪ ↑G.V)` on the predicate itself.*  The LN writes
--   "$A, B, C \ins J \cup V$" once at the head of the separation
--   block — three named, per-set premises mirror that exactly and
--   close the silent-admission leak the predicate would otherwise
--   exhibit (a caller could pass arbitrary `Set Node` including
--   nodes that don't exist in `G`, and the predicate would be
--   well-typed under a meaning the LN never assigned it).  Pinning
--   the constraint on the def — not on theorem sites — is the only
--   encoding that closes that leak at the source.  Separate named
--   hypotheses (not a bundled `A ∪ B ∪ C ⊆ ↑G.J ∪ ↑G.V` or an
--   `∧`-conjunction) match the chapter convention from Section 3.2
--   (`HardInterventionsCommute`, `DisjointHardInterventionsSwig`,
--   `AddingInterventionNodes`) and avoid `.1`/`.2`-projecting at
--   every downstream proof site.  `hC` is the only one consumed by
--   the body (passed to `π.refactor_IsSigmaBlockedGiven`); `hA` and
--   `hB` restrict the *domain* of definition rather than the body's
--   semantics — out-of-graph nodes contribute vacuously to the walk
--   universal anyway (no walks have such endpoints in `G`), but
--   `hA`/`hB` close the silent-admission leak at the type-signature
--   level.  The `set_option linter.unusedVariables false in` prefix
--   is needed because `hA` and `hB` are LN-faithful but body-inert
--   (same chapter convention as `HardInterventionOn`,
--   `NodeSplittingOn`, `NodeSplittingHard`, `AddingInterventionNodes`,
--   `MarginalizationAndIntervention`).
--
-- ## Refactor-specific rationale
--
-- *Why the refactor needs to touch this predicate.*  Mechanically
--   only, not semantically.  Three upstream symbols (`CDMG`, `Walk`,
--   `IsSigmaBlockedGiven`) have all themselves been refactored, plus
--   `IsSigmaBlockedGiven` now takes an explicit
--   `hC : C ⊆ ↑G.J ∪ ↑G.V` premise (per `def_3_17`'s refactor design
--   block), so the def must be re-stated using the refactored
--   upstreams.  The universal-over-walks `Prop`-level shape, the
--   LN-correspondence to "for every walk π" scope, the asymmetric
--   J-inclusion on the right endpoint, and every design pillar
--   above carry through verbatim.
--
-- *Constructor-choice invariance and walk-reversal channel
--   preservation inherited via upstream encoding.*  The refactor's
--   load-bearing payoff at this layer is structural symmetry.  Under
--   the pre-refactor ordered-pair-plus-`hL_symm` encoding, the same
--   LN walk could fall on different sides of the LN's `\isPerp` /
--   `\nisPerp` boundary on writing-mirror CDMGs (vertex pairs that
--   simultaneously support a directed `E`-edge and a bidirected
--   `L`-edge, admitted by `def_3_1`'s
--   `[edge_set_disjointness_under_specified]` addition) — because
--   the per-walk-position predicates `IsCollider` /
--   `IsBlockableNonCollider` that `IsSigmaBlockedGiven` ranges over
--   read the channel off the walker-chosen ordered-pair
--   representation.  Under the typed-WalkStep + `Sym2 Node`
--   refactor the channel is carried by the WalkStep constructor tag
--   and a `.bidir` step's `s(u,v) ∈ G.L` witness lives in the swap-
--   quotient `Sym2 Node`, so the per-position classifiers are
--   constructor-choice invariant and reversal-invariant
--   (definitional `s(u,v) = s(v,u)` — no `hL_symm` invocation).
--   These properties propagate to `refactor_IsSigmaBlockedGiven`
--   (per its design block at `SigmaBlockedWalks.lean:600-716`) and
--   from there to *this* predicate's `Prop`-level value on writing-
--   mirror walks.  No σ-separation-level code in this file performs
--   the fix; the upstream encoding does, and the refactor inherits
--   structurally.
--
-- *Downstream consumers of this REPLACEMENT.*  The immediate
--   downstream consumers in this row's namespace are items 2-5 below
--   (negation, unconditional-`C=∅` abbrev, and the J=∅ σ-name
--   aliases), which all forward to this predicate without re-
--   deriving.  The *driving* future consumer (not in the current
--   refactor table but flagged in `def_3_1`'s and `def_3_17`'s
--   refactor design blocks as the motivation for the `Sym2 Node`
--   encoding of `L`) is the LN's `claim_3_22`
--   `SigmaSeparationSymmetric`: under `J = ∅`,
--   `G.refactor_IsSigmaSeparated A B C ↔
--   G.refactor_IsSigmaSeparated B A C`.  Under the refactor the
--   symmetry argument closes by construction: walk reversal is an
--   involution on `refactor_Walk G u v ↔ refactor_Walk G v u` that
--   preserves the typed-WalkStep channel of every step (the `.bidir`
--   reversal is the definitional `Sym2` swap-equality; the
--   `.forwardE` / `.backwardE` reversal flips the constructor tag
--   without consulting any orientation field), so a walk witness on
--   one side of the symmetry maps to a walk witness on the other
--   side and the universal-over-walks quantification of *this*
--   predicate transports verbatim.  Further downstream (chapter 4+)
--   every Markov-property / do-calculus / iSCM identification result
--   that mentions `A ⊥^σ B | C` pattern-matches on exactly this
--   def's universal-over-walks shape, with the asymmetric J
--   inclusion baked into the separoid-rule infrastructure.  This is
--   the load-bearing payoff of the refactor at this row — and the
--   reason the refactor was triggered.
--
-- *Why NOT re-thinking the def shape under the refactor.*  The
--   typed-WalkStep + `Sym2 Node` encoding change is orthogonal to
--   `refactor_IsISigmaSeparated`'s `Prop`-level shape (universal over
--   walks with endpoint-membership premises).  The encoding change
--   *strengthens* the per-walk predicate `refactor_IsSigmaBlockedGiven`
--   that this def quantifies over — it is now constructor-choice
--   invariant and reversal-friendly — but does not motivate a
--   re-design at the σ-separation layer.  Re-designing σ-separation
--   here (e.g. as an existential over reversal-pair equivalence
--   classes of walks, or as a structural recursion on the typed-
--   WalkStep walk type) was rejected: (a) the LN's universal-over-
--   walks shape is the right reading for downstream witness
--   extraction (every consumer pulls a specific blocking witness from
--   a specific walk); (b) collapsing to reversal classes would lose
--   the asymmetric-J reading of the right-endpoint constraint (the
--   LN intends a one-way universal from `A` into `J ∪ B`, not a
--   class-level quantifier); (c) the mechanical port preserves the
--   LN-grep one-to-one correspondence at the def site.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsISigmaSeparated (was: refactor_IsISigmaSeparated)
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def refactor_IsISigmaSeparated (G : refactor_CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  ∀ {u v : Node} (π : refactor_Walk G u v),
      u ∈ A → v ∈ (G.J : Set Node) ∪ B → π.refactor_IsSigmaBlockedGiven C hC
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsISigmaSeparated

-- ref: def_3_18 (item 2) — refactor
--
-- `G.refactor_IsNotISigmaSeparated A B C hA hB hC` is the LN's
-- `A \nisPerp_G B \given C` ported against the typed-WalkStep
-- refactor: the definitional negation of
-- `G.refactor_IsISigmaSeparated A B C`.  Equivalently (by classical
-- De Morgan, not by Lean reduction): there exists a walk
-- `π : refactor_Walk G u v` with `u ∈ A`, `v ∈ J ∪ B`, and
-- `¬ π.refactor_IsSigmaBlockedGiven C hC`.
--
-- *Upstream-retarget deltas for this REPLACEMENT (self-contained
-- record).*  Two mechanical retargets relative to the pre-refactor
-- encoding:
-- - `CDMG Node` → `refactor_CDMG Node` (root `def_3_1`);
-- - `G.IsISigmaSeparated` → `G.refactor_IsISigmaSeparated` (item 1
--   above, ported in this same refactor section).
-- The named-negation alias shape, the definitional-equality
-- encoding, and the three subset premises are preserved verbatim.
--
-- ## Design pillars (LN-faithful, encoding-orthogonal)
--
-- *Named `def` for the negation, rather than asking downstream
--   sites to spell `¬ G.refactor_IsISigmaSeparated A B C hA hB hC`.*
--   LN item 2 introduces `\nisPerp` as named notation for the
--   negation of `\isPerp`; mirroring that with a named Lean `def`
--   keeps downstream statement / claim sites grep-aligned with the
--   LN prose (every LN reference to `A \nisPerp_G B \given C`
--   corresponds to a literal `G.refactor_IsNotISigmaSeparated A B C
--   hA hB hC` in Lean).  Without this alias, every downstream
--   invocation would have to inline `¬ G.refactor_IsISigmaSeparated
--   …`, breaking the one-to-one LN-to-Lean correspondence and
--   forcing readers to reconstruct the LN's named relation from a
--   Lean negation.
--
-- *Definitionally equal to the negation, not a parallel positive
--   existential.*  Encoding it as `¬ refactor_IsISigmaSeparated`
--   keeps the two predicates definitionally linked:
--   `G.refactor_IsNotISigmaSeparated A B C hA hB hC` unfolds to
--   `¬ G.refactor_IsISigmaSeparated A B C hA hB hC` by `rfl`, so
--   `unfold refactor_IsNotISigmaSeparated` and `simp only
--   [refactor_IsNotISigmaSeparated]` collapse it to the negation
--   form at any proof site.  Downstream proofs that switch between
--   the two never have to invoke a separate equivalence lemma.  The
--   canonical tex's "equivalently, ∃ walk …" reformulation is the
--   classical De Morgan dual of the negated universal — derivable
--   as a one-line lemma when needed, not a parallel definition.
--   An alternative "positive existential" shape
--     `∃ {u v} (π : refactor_Walk G u v), u ∈ A ∧ v ∈ J ∪ B ∧
--       ¬ π.refactor_IsSigmaBlockedGiven C hC`
--   was considered: equivalent classically, but it would break the
--   definitional link with `refactor_IsISigmaSeparated` and require
--   a classical bridging lemma at every interconversion site.
--
-- *Same three subset premises `(hA hB hC)` as the underlying iσ
--   predicate.*  LN item 2 introduces `\nisPerp` as named notation
--   for the negation of `\isPerp` — a named convenience predicate,
--   not a new concept.  Mirroring the subset hypotheses on the
--   underlying iσ predicate keeps the two predicates' call-site
--   signatures aligned (every use of `refactor_IsNotISigmaSeparated`
--   already has the data to discharge `refactor_IsISigmaSeparated`'s
--   premises), and the body forwards to
--   `¬ refactor_IsISigmaSeparated` definitionally — no parallel
--   existential, no bridging lemma.  Same `set_option
--   linter.unusedVariables false in` exemption applies (`hA` and
--   `hB` are LN-faithful binders that flow into the iσ predicate as
--   arguments but are not pattern-matched here).
--
-- ## Refactor-specific rationale
--
-- *Why the refactor needs to touch this predicate.*  Mechanically
--   only, not semantically.  Two upstream retargets (the type
--   `refactor_CDMG Node` and the predicate
--   `refactor_IsISigmaSeparated` it negates).  The LN-correspondence
--   to `\nisPerp` as named notation for the negation of `\isPerp`,
--   the definitional-equality link with the iσ predicate, and the
--   matching subset hypotheses are all unchanged.  The design pillars
--   above carry through verbatim.
--
-- *Constructor-choice invariance and reversal symmetry inherited
--   via `refactor_IsISigmaSeparated`.*  Negation of an invariant
--   predicate is itself invariant: if
--   `G.refactor_IsISigmaSeparated A B C ↔
--   G.refactor_IsISigmaSeparated B A C` under `J = ∅` (the
--   σ-symmetry payoff per the σ predicate's design block above),
--   then their negations are equivalent too.  No standalone
--   σ-symmetry argument for `\nsPerp` is needed in this file or
--   downstream.
--
-- *Downstream consumers of this REPLACEMENT.*  The immediate
--   downstream consumer is item 5's `refactor_IsNotSigmaSeparated`,
--   which renames this predicate under `J = ∅`.  Future consumers
--   include any claim that pattern-matches on
--   `A \nisPerp_G B \given C` (chapter 4+ Markov properties,
--   do-calculus, etc.).
--
-- *Why NOT re-thinking the def shape.*  Same rationale as
--   `refactor_IsISigmaSeparated`: encoding change orthogonal to
--   the named-negation shape.  The "positive existential"
--   reformulation noted in the design pillars above was considered
--   and rejected for the same definitional-link reason.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsNotISigmaSeparated (was: refactor_IsNotISigmaSeparated)
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def refactor_IsNotISigmaSeparated (G : refactor_CDMG Node) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  ¬ G.refactor_IsISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsNotISigmaSeparated

-- ref: def_3_18 (item 3) — refactor
--
-- `G.refactor_IsISigmaSeparatedEmpty A B hA hB` is the LN's
-- unconditional shorthand `A \isPerp_G B := A \isPerp_G B \given ∅`
-- ported against the typed-WalkStep refactor.  Unfolds to
-- `G.refactor_IsISigmaSeparated A B ∅ hA hB (Set.empty_subset _)`.
--
-- *Upstream-retarget deltas for this REPLACEMENT (self-contained
-- record).*  Two mechanical retargets relative to the pre-refactor
-- encoding:
-- - `CDMG Node` → `refactor_CDMG Node` (root `def_3_1`);
-- - `G.IsISigmaSeparated` → `G.refactor_IsISigmaSeparated` (item 1
--   above, ported in this same refactor section).
-- The `abbrev` encoding (not `def`), the two-binder signature
-- (`hA hB`, not three), the empty third subset proof
-- (`Set.empty_subset _`), and the LN-correspondence to the
-- unconditional notation are preserved verbatim.
--
-- ## Design pillars (LN-faithful, encoding-orthogonal)
--
-- *Named derived predicate for the unconditional `C = ∅` case
--   `(A B : Set Node) (hA hB)`, not the iσ predicate always carrying
--   a vacuous third subset proof.*  LN item 3 *defines*
--   `A \isPerp_G B` as the special case `A \isPerp_G B \given ∅`;
--   mirroring that with a dedicated `refactor_IsISigmaSeparatedEmpty`
--   gives consumers a clean name for the marginal case without
--   making them supply a vacuous third subset proof.  The body
--   forwards to `refactor_IsISigmaSeparated A B ∅` and discharges
--   `hC : ∅ ⊆ ↑G.J ∪ ↑G.V` automatically via `Set.empty_subset _`,
--   so the user never has to write the empty-subset proof at the
--   call site.
--
-- *Two subset hypotheses `(hA hB)`, not three.*  The third slot
--   would be a constant `Set.empty_subset _` — making it implicit in
--   the alias keeps the call-site signature minimal and reflects the
--   LN's notation `A \isPerp_G B` (no `C` argument appears).
--
-- *`abbrev`, not `def`.*  LN item 3 is pure notation — the symbol
--   `A \isPerp_G B` is *defined to mean* `A \isPerp_G B \given ∅`,
--   not a new concept.  `abbrev` is fully transparent to elaboration:
--   Lean reduces `G.refactor_IsISigmaSeparatedEmpty A B hA hB` to
--   `G.refactor_IsISigmaSeparated A B ∅ hA hB (Set.empty_subset _)`
--   at every use site without an `unfold` step, so any lemma that
--   targets the underlying iσ predicate fires automatically on the
--   shorthand and vice versa.  Encoding as `def` would create an
--   opaque alias and force every consumer interchanging the two to
--   invoke `unfold` / `simp only [refactor_IsISigmaSeparatedEmpty]`
--   — a wholly gratuitous obstacle given the LN's "is defined as"
--   reading.  No `hJ` is involved here, so the `def` encoding the
--   σ-aliases below use does not apply.
--
-- *No separate negation alias for the `C = ∅` case.*  The LN does
--   not introduce a separate symbol for "not unconditionally
--   iσ-separated" — that gap is intentional.  Downstream sites
--   needing this combination spell it as
--   `¬ G.refactor_IsISigmaSeparatedEmpty A B hA hB` or
--   `G.refactor_IsNotISigmaSeparated A B ∅ hA hB (Set.empty_subset _)`;
--   the `abbrev`'s transparency makes both interchangeable.
--
-- ## Refactor-specific rationale
--
-- *Why the refactor needs to touch this abbrev.*  Mechanically only,
--   not semantically.  Two upstream retargets (the type
--   `refactor_CDMG Node` and the predicate
--   `refactor_IsISigmaSeparated` the body forwards to).  The
--   LN-correspondence to "is defined as" notation, the `abbrev`
--   transparency, and the two-binder signature reflecting the LN's
--   `A \isPerp_G B` notation are all unchanged.  The design pillars
--   above carry through verbatim.
--
-- *Constructor-choice invariance and reversal symmetry inherited
--   from `refactor_IsISigmaSeparated`.*  As an `abbrev` that unfolds
--   eagerly to the iσ predicate, every property of the iσ predicate
--   transports to this shorthand without restatement.  In
--   particular the σ-symmetry argument for `claim_3_22` applies to
--   the unconditional case as well (the LN's `A \sPerp_G B` and
--   `A \sPerp_G B \given ∅` are interchangeable under `J = ∅`).
--
-- *Downstream consumers of this REPLACEMENT.*  Any LN statement
--   spelled `A \isPerp_G B` (no conditioning set).  Includes the
--   LN's Markov-property results in chapter 4+ that quantify over
--   marginal independences.
--
-- *Why NOT re-thinking the abbrev shape.*  The encoding change is
--   orthogonal to the LN's pure-notation semantics — no re-design
--   opportunity at this layer.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsISigmaSeparatedEmpty (was: refactor_IsISigmaSeparatedEmpty)
-- def_3_18 -- start statement
abbrev refactor_IsISigmaSeparatedEmpty (G : refactor_CDMG Node) (A B : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.refactor_IsISigmaSeparated A B ∅ hA hB (Set.empty_subset _)
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsISigmaSeparatedEmpty

-- ref: def_3_18 (item 4) — refactor
--
-- `G.refactor_IsSigmaSeparated hJ A B C hA hB hC` is the LN's
-- `A \sPerp_G B \given C` ported against the typed-WalkStep
-- refactor: the `J = ∅` notation alias of
-- `G.refactor_IsISigmaSeparated A B C`.  The alias keeps the
-- underlying predicate identical — the `J = ∅` specialisation is a
-- property of the consumer's CDMG (a "fact about `G`"), not a
-- logical condition on the predicate.  Under `J = ∅` the right-
-- endpoint constraint `v ∈ J ∪ B` reduces to `v ∈ B`, so
-- `A \sPerp_G B \given C` reads as "every walk from `A` to `B` is
-- `C`-σ-blocked" in the standard literature sense.
--
-- *Upstream-retarget deltas for this REPLACEMENT (self-contained
-- record).*  Two mechanical retargets relative to the pre-refactor
-- encoding:
-- - `CDMG Node` → `refactor_CDMG Node` (root `def_3_1`);
-- - `G.IsISigmaSeparated` → `G.refactor_IsISigmaSeparated` (item 1
--   above, ported in this same refactor section).
-- The explicit `(hJ : G.J = ∅)` premise, the σ-vs-iσ name
-- distinction, the three subset hypotheses (`hA hB hC`), the `def`
-- (not `abbrev`) encoding, and the LN-correspondence to "the
-- special case of iσ-separation where `J = ∅`" are preserved
-- verbatim.  `refactor_CDMG.J` is still `Finset Node` (per `def_3_1`'s
-- refactor — the J/V carrier-type discipline did not change; only
-- `L`'s carrier moved to `Finset (Sym2 Node)`), so `G.J = ∅` is
-- well-typed and semantically equivalent to its pre-refactor
-- counterpart.
--
-- ## Design pillars (LN-faithful, encoding-orthogonal)
--
-- *Separate named alias rather than asking downstream consumers to
--   write `refactor_IsISigmaSeparated` with `G.J = ∅`.*  LN item 4
--   *renames* the predicate (drops the leading "$i$") for the
--   special case `J = ∅`; the same mathematical object acquires a
--   new name when the input-node set is empty.  Mirroring that with
--   a named Lean alias keeps the LN's terminology available at every
--   downstream call site (most prominently `claim_3_22`
--   `SigmaSeparationSymmetric`, which is stated and proved purely
--   in σ-separation language under `J = ∅`; and chapter 4+'s
--   Markov-property results, which the LN states in σ-separation
--   form for the no-input special case before lifting to the
--   general iσ form).  Without the alias every such consumer would
--   have to spell "the special case of iσ-separation where `J = ∅`",
--   scrambling the LN-to-Lean correspondence on the LN's most-used
--   graphical-separation predicate.
--
-- *Explicit `(hJ : G.J = ∅)` premise on the predicate, not a
--   separate `DMG` subtype or typeclass.*  LN item 4 defines
--   `A \sPerp_G B \given C := A \isPerp_G B \given C` *for the
--   special case `J = ∅`* — a notational renaming under the
--   assumption, not a new type.  Taking the equation `G.J = ∅`
--   directly as a hypothesis matches the LN reading word-for-word
--   and keeps the declaration lightweight (no new typeclass, no
--   structure projection at every use site).  Downstream consumers
--   (e.g. `claim_3_22` σ-separation symmetry) can discharge `hJ`
--   directly from their own hypotheses.  A `def IsDMG (G :
--   refactor_CDMG Node) : Prop := G.J = ∅` exists in
--   `Section3_1/CDMGTypes.lean` (`def_3_7`) for consumers preferring
--   the named property — but this predicate takes the bare equation
--   to stay self-contained relative to the CDMG-property hierarchy
--   and to avoid making `def_3_18` transitively depend on `def_3_7`
--   (which it otherwise does not need).
--
-- *Same three subset hypotheses as the underlying iσ predicate.*
--   The LN's "$A, B, C \ins J \cup V$" applies under both names;
--   the renaming under `J = ∅` does not loosen the LN's domain of
--   definition.  Body forwards `(A, B, C, hA, hB, hC)` unchanged
--   to `refactor_IsISigmaSeparated`.  Same `set_option
--   linter.unusedVariables false in` exemption (`hJ`, `hA`, `hB`
--   are LN-faithful binders inert in the body; only `hC` is
--   consumed through the iσ call).
--
-- *`def`, not `abbrev`.*  With `hJ` as a dependent hypothesis,
--   `abbrev`'s aggressive reducibility becomes a footgun: Lean
--   would unfold the alias eagerly and the `hJ` evidence would
--   disappear from goal displays at unrelated tactic steps.  `def`
--   keeps the alias opaque-by-default and preserves the σ-vs-iσ
--   symbolic distinction at every use site.  This is the opposite
--   of `refactor_IsISigmaSeparatedEmpty` (item 3 above), which
--   uses `abbrev` precisely *because* it has no `hJ`-dependent
--   evidence to preserve.
--
-- *No symmetry claim here.*  The LN's embedded `claimmark` for
--   σ-separation symmetry (`claim_3_22`) is intentionally excluded
--   from this row, per the canonical tex's "Treatment of the
--   trailing LN remark" paragraph and the row's authoritative
--   addition `[sigma_symmetry_claim_invokes_unstated_reversal_invariance]`.
--   The symmetry statement and proof live in
--   `claim_3_22_statement_SigmaSeparationSymmetric.tex` /
--   `claim_3_22_proof_SigmaSeparationSymmetric.tex` and its Lean
--   counterpart — NOT in this def.
--
-- *Wording-check subtlety
--   `symmetry_claim_walks_between_wording_imprecise` (surfaced by
--   the working-phase LN-critic for `def_3_18`).*  The LN justifies
--   σ-separation symmetry by saying "the set of walks between A
--   and B is the same regardless of direction".  Read literally,
--   this is imprecise: walks in a CDMG are directed sequences of
--   vertices and edges, so the *set* of walks from `A` to `B` is
--   NOT literally equal to the *set* of walks from `B` to `A`.  What
--   is true is that walk *reversal* induces a bijection (in fact, an
--   involution) between these two sets, and the σ-blocking property
--   is invariant under that bijection (because the collider /
--   non-collider role of each internal vertex is preserved by
--   reversal).  Under the typed-`WalkStep` + `Sym2 Node` refactor
--   both halves hold *structurally*: walk reversal flips
--   `.forwardE` ↔ `.backwardE` and leaves `.bidir` fixed (modulo the
--   definitional `Sym2` swap-equality `s(u,v) = s(v,u)`); and the
--   per-position classifiers `refactor_IsCollider` /
--   `refactor_IsBlockableNonCollider` read the channel off the
--   constructor tag, so they are preserved under reversal without
--   any `hL_symm` invocation.  This is the missing reversal-bijection
--   step that the LN's prose elides; `claim_3_22`'s proof discharges
--   it directly via the typed-WalkStep encoding.
--
-- *Addition `[sigma_symmetry_claim_invokes_unstated_reversal_invariance]`
--   (operator-authored, treated as part of the LN).*  In a CDMG, a
--   walk is a sequence of incident edges without regard to edge
--   orientation; consequently, every walk from `A` to `B` is, read
--   in reverse, a walk from `B` to `A`, and this reversal is an
--   involution on the set of walks.  The symmetry of σ-separation
--   (when `J = ∅`) is to be understood as resting on this walk-
--   reversal involution together with the fact that the σ-blocking
--   conditions on internal nodes are stated in a manner invariant
--   under reversal.  Under the refactor both ingredients are
--   structural properties of `refactor_Walk`: (i) the involution is
--   the obvious walk reversal that swaps endpoints and reverses the
--   `cons`-cell sequence, with channel preserved by the typed-
--   `WalkStep` constructor tagging; (ii) the σ-blocking invariance
--   is inherited from `refactor_IsSigmaBlockedGiven`'s constructor-
--   choice / reversal-friendly per-position classifiers (per
--   `SigmaBlockedWalks.lean:600-716`).  No σ-symmetry-level code
--   in this file performs the proof; `claim_3_22`'s Lean proof
--   draws on these structural properties through `refactor_Walk`
--   and `refactor_IsSigmaBlockedGiven` directly.
--
-- ## Refactor-specific rationale
--
-- *Why the refactor needs to touch this rename.*  Mechanically only,
--   not semantically.  Two upstream retargets (the type
--   `refactor_CDMG Node` and the predicate
--   `refactor_IsISigmaSeparated` the body forwards to).  The
--   LN-correspondence to `\sPerp` as renamed notation for `\isPerp`
--   under `J = ∅`, the explicit `hJ` premise that keeps the σ-name
--   visible at the call site, and the forward-to-iσ body are all
--   unchanged.  The design pillars above carry through verbatim.
--
-- *Constructor-choice invariance and reversal symmetry inherited
--   from `refactor_IsISigmaSeparated`.*  As a `def` that forwards
--   to the iσ predicate, every property of the iσ predicate
--   transports to this alias — in particular the σ-symmetry payoff
--   for `claim_3_22` (which is *stated* purely in σ-language under
--   `J = ∅`).  Under the refactor `claim_3_22` closes by
--   construction because walk reversal preserves the
--   `refactor_IsSigmaBlockedGiven` witness on every typed-WalkStep
--   walk (see "Addition" bullet above for the structural reasoning);
--   that argument plugs in directly through this alias's forward-
--   to-iσ body.
--
-- *Downstream consumers of this REPLACEMENT.*  The driving
--   downstream consumer is `claim_3_22`
--   `SigmaSeparationSymmetric` (stated *purely* in σ-separation
--   language for `J = ∅`).  Other consumers include chapter 4+
--   Markov-property results that state the no-input special case in
--   σ-language before lifting to the general iσ form.  The
--   `Sym2`-typed `L` encoding from `def_3_1`'s refactor is what
--   makes `claim_3_22` close cleanly on writing-mirror CDMGs — this
--   alias is the named entry point that downstream consumers use to
--   invoke the σ-symmetry result.
--
-- *Why NOT re-thinking the alias shape.*  The encoding change is
--   orthogonal to the rename semantics.  The refactor doesn't
--   suggest a new way to encode "the no-input special case" (e.g.
--   as a separate DMG type rather than an iσ alias on a J=∅ CDMG);
--   the LN's renaming-under-`hJ` reading is the right semantics
--   under the refactor too.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsSigmaSeparated (was: refactor_IsSigmaSeparated)
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def refactor_IsSigmaSeparated (G : refactor_CDMG Node) (hJ : G.J = ∅) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.refactor_IsISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsSigmaSeparated

-- ref: def_3_18 (item 4, negation) — refactor
--
-- `G.refactor_IsNotSigmaSeparated hJ A B C hA hB hC` is the LN's
-- `A \nsPerp_G B \given C` ported against the typed-WalkStep
-- refactor: the `J = ∅` notation alias of
-- `G.refactor_IsNotISigmaSeparated A B C`.
--
-- *Upstream-retarget deltas for this REPLACEMENT (self-contained
-- record).*  Two mechanical retargets relative to the pre-refactor
-- encoding:
-- - `CDMG Node` → `refactor_CDMG Node` (root `def_3_1`);
-- - `G.IsNotISigmaSeparated` → `G.refactor_IsNotISigmaSeparated`
--   (item 2 above, ported in this same refactor section).
-- The mirror with `refactor_IsSigmaSeparated` (paired σ-/¬σ-notation
-- under `J = ∅`), the explicit `hJ` premise, the three subset
-- hypotheses, and the `def` (not `abbrev`) encoding are preserved
-- verbatim.
--
-- ## Design pillars (LN-faithful, encoding-orthogonal)
--
-- *Mirror of `refactor_IsSigmaSeparated`, in the negation
--   direction.*  LN item 4 renames `\nisPerp` to `\nsPerp` under
--   `J = ∅` in the same breath that it renames `\isPerp` to
--   `\sPerp`; the pair is introduced as a unit and downstream sites
--   use the pair as a unit (`A \sPerp_G B \given C` and
--   `A \nsPerp_G B \given C` appear side-by-side in claim
--   statements and proof case-splits).  Including the negated alias
--   keeps that pairing intact in Lean — without it, σ-vs-¬σ case
--   analyses would have to mix `refactor_IsSigmaSeparated` with raw
--   `¬ refactor_IsSigmaSeparated` invocations, breaking the LN's
--   notational symmetry.
--
-- *No new content beyond `refactor_IsNotISigmaSeparated ∘ rename`.*
--   In particular this alias does *not* re-introduce the "positive
--   existential" formulation of the negation — the existential
--   reformulation, when needed, remains the standalone classical
--   De Morgan lemma noted in `refactor_IsNotISigmaSeparated`'s
--   design block above, and is shared across both `iσ` and `σ`
--   names.
--
-- *Same `(hJ : G.J = ∅)` premise as `refactor_IsSigmaSeparated`.*
--   Same encoding rationale as the σ predicate above: bare equation,
--   not a `DMG` typeclass; LN-faithful word-for-word; downstream
--   consumers discharge it from their own hypotheses.  Body forwards
--   `(A, B, C, hA, hB, hC)` unchanged to
--   `refactor_IsNotISigmaSeparated` — the negation alias does *not*
--   need to use the `J = ∅` fact (the negation's truth-value is
--   determined by the iσ predicate's), but `hJ` stays on the
--   signature for LN-faithfulness and σ-/¬σ-name pairing
--   symmetry.  Same `set_option linter.unusedVariables false in`
--   exemption (`hJ`, `hA`, `hB` are LN-faithful binders inert in
--   the body).
--
-- *`def`, not `abbrev`.*  Same `hJ`-dependent-evidence reason as
--   `refactor_IsSigmaSeparated`: `abbrev` would eagerly unfold and
--   the `hJ` evidence would disappear from goal displays at
--   unrelated tactic steps; `def` keeps the σ-vs-iσ symbolic
--   distinction visible.
--
-- ## Refactor-specific rationale
--
-- *Why the refactor needs to touch this rename.*  Mechanically only,
--   not semantically.  Two upstream retargets (the type
--   `refactor_CDMG Node` and the predicate
--   `refactor_IsNotISigmaSeparated`).  The LN-correspondence to
--   `\nsPerp` as renamed notation for `\nisPerp` under `J = ∅`, the
--   pairing-as-a-unit with `refactor_IsSigmaSeparated`, and the
--   forward-to-non-iσ body are all unchanged.  The design pillars
--   above carry through verbatim.
--
-- *Constructor-choice invariance and reversal symmetry inherited
--   via the iσ negation.*  Same propagation as
--   `refactor_IsNotISigmaSeparated`: negation of an invariant
--   predicate is itself invariant, so any σ-symmetry argument for
--   `\sPerp` transports to `\nsPerp` for free.  Under the refactor's
--   structural reversal-invariance (per
--   `refactor_IsSigmaSeparated`'s "Addition" bullet above), the
--   transport closes by construction.
--
-- *Downstream consumers of this REPLACEMENT.*  Pairs with item 4's
--   `refactor_IsSigmaSeparated` in σ-vs-¬σ case splits — claim
--   statements and proof case splits in chapter 3+ alternate
--   between the two names.
--
-- *Why NOT re-thinking the alias shape.*  Same rationale as item 4:
--   encoding change orthogonal to rename semantics.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsNotSigmaSeparated (was: refactor_IsNotSigmaSeparated)
set_option linter.unusedVariables false in
-- def_3_18 -- start statement
def refactor_IsNotSigmaSeparated (G : refactor_CDMG Node) (hJ : G.J = ∅) (A B C : Set Node)
    (hA : A ⊆ ↑G.J ∪ ↑G.V) (hB : B ⊆ ↑G.J ∪ ↑G.V) (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  G.refactor_IsNotISigmaSeparated A B C hA hB hC
-- def_3_18 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsNotSigmaSeparated

end refactor_CDMG

end Causality
