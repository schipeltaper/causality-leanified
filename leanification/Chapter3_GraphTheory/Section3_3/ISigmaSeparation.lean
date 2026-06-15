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

5. **`abbrev` for the unconditional `C = ∅` and `J = ∅`
   specialisations, not new `def`s.**  Items 3 and 4 of the LN are
   *notation aliases*: `A \isPerp_G B := A \isPerp_G B \given ∅`
   and `A \sPerp_G B \given C := A \isPerp_G B \given C`.  `abbrev`
   is transparent — `IsSigmaSeparated` reduces to
   `IsISigmaSeparated` at every elaboration site without an
   `unfold` step.  No `J = ∅` hypothesis is added to
   `IsSigmaSeparated`: the LN treats this as a renaming under the
   assumption (a property of the consumer's CDMG), not a logical
   condition on the predicate.
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
-- *No `A ⊆ J ∪ V` / `B ⊆ J ∪ V` / `C ⊆ J ∪ V` hypotheses at the
--   def site.*  The LN allows the three sets to be arbitrary
--   subsets of `J ∪ V`, but doesn't require it at the predicate
--   level — out-of-graph nodes contribute vacuously to the walk
--   universal (no walk in `G` has an out-of-graph endpoint).
--   Matches the analogous "no subset hypothesis" convention from
--   `def_3_17`'s `IsSigmaBlockedGiven` (also takes `C : Set Node`
--   with no constraint).
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
-- def_3_18 -- start statement
def IsISigmaSeparated (G : CDMG Node) (A B C : Set Node) : Prop :=
  ∀ {u v : Node} (π : Walk G u v),
      u ∈ A → v ∈ (G.J : Set Node) ∪ B → π.IsSigmaBlockedGiven C
-- def_3_18 -- end statement

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
-- def_3_18 --- start helper
def IsNotISigmaSeparated (G : CDMG Node) (A B C : Set Node) : Prop :=
  ¬ G.IsISigmaSeparated A B C
-- def_3_18 --- end helper

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
-- def_3_18 --- start helper
abbrev IsISigmaSeparatedEmpty (G : CDMG Node) (A B : Set Node) : Prop :=
  G.IsISigmaSeparated A B ∅
-- def_3_18 --- end helper

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
-- *`abbrev`, not a `J = ∅`-conditional `def`.*  The LN writes
--   "when `J = ∅`, … is also called …" — the renaming is in force
--   under the assumption, but the predicate itself is unchanged.
--   Adding `(hJ : G.J = ∅)` as a hypothesis would over-fire:
--   `IsSigmaSeparated` would then need to take the proof at every
--   call site, even though the LN's "we write …" introduces no
--   such proof obligation.  The `J = ∅` precondition is a
--   *call-site* fact about the consumer's CDMG (e.g. `claim_3_22`
--   hands it in as an explicit hypothesis), not a logical
--   condition baked into the predicate.  Same `abbrev`
--   transparency rationale as `IsISigmaSeparatedEmpty`: Lean
--   reduces `G.IsSigmaSeparated A B C` to
--   `G.IsISigmaSeparated A B C` at every use site, so every
--   lemma about either form fires on the other.
--
-- *Why an `abbrev` is the right choice over notation /
--   `local notation`.*  A `notation` macro would also be
--   transparent but would not survive cross-file boundaries
--   without re-declaration; an `abbrev` is namespaced under
--   `CDMG` and inherits the chapter-wide `Causality` /
--   `CDMG`-namespace open conventions, so downstream sites in
--   later chapters can write `G.IsSigmaSeparated A B C` without
--   special imports.
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
-- def_3_18 --- start helper
abbrev IsSigmaSeparated (G : CDMG Node) (A B C : Set Node) : Prop :=
  G.IsISigmaSeparated A B C
-- def_3_18 --- end helper

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
-- *`abbrev` for the same reasons as `IsSigmaSeparated`.*  Pure
--   notational renaming under a `J = ∅` precondition that is a
--   *consumer-side* fact about the CDMG.  Transparent unfolding
--   means a proof that establishes
--   `G.IsNotSigmaSeparated A B C` immediately discharges any
--   goal `G.IsNotISigmaSeparated A B C` (and vice versa), without
--   a bridging lemma.  The `J = ∅`-conditional `def` shape was
--   rejected for the same over-fire reason as `IsSigmaSeparated`:
--   the LN's renaming is *under* the assumption, not
--   *conditional on* a Lean-tracked proof of it.
--
-- *No new content beyond `IsNotISigmaSeparated ∘ rename`.*  In
--   particular this alias does *not* re-introduce the "positive
--   existential" formulation of the negation — the existential
--   reformulation, when needed, remains the standalone classical
--   De Morgan lemma noted in `IsNotISigmaSeparated`'s design
--   block and is shared across both `iσ` and `σ` names.
-- def_3_18 --- start helper
abbrev IsNotSigmaSeparated (G : CDMG Node) (A B C : Set Node) : Prop :=
  G.IsNotISigmaSeparated A B C
-- def_3_18 --- end helper

end CDMG

end Causality
