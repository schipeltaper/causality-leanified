import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_2.HardInterventionOn

namespace Causality

/-!
# Hard interventions commute (`claim_3_4`)

This file formalises the LN lemma `claim_3_4`
(`\label{hard-interventions-commute}` in `graphs.tex`):

> Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ J ∪ V`.  Then
> `(G_{do(W₁)})_{do(W₂)} = (G_{do(W₂)})_{do(W₁)} = G_{do(W₁ ∪ W₂)}`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_2/tex/`
`claim_3_4_statement_HardInterventionsCommute.tex`, verified equivalent
to the LN block.  The rewritten tex decomposes the LN's displayed
triple equality into the conjunction of two binary equalities:

* (a) `(G_{do(W₁)})_{do(W₂)} = G_{do(W₁ ∪ W₂)}`,
* (b) `(G_{do(W₂)})_{do(W₁)} = G_{do(W₁ ∪ W₂)}`.

Transitivity of equality recovers the LN's "swap symmetry" reading
`(G_{do(W₁)})_{do(W₂)} = (G_{do(W₂)})_{do(W₁)}` from (a) ∧ (b).

The body is filled in by `prove_claim_in_lean` (Manager B), following
the to-be-written tex proof at
`tex/claim_3_4_proof_HardInterventionsCommute.tex`.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  Both fixtures are load-bearing for this
--   row's statement because the signature references `CDMG Node` and
--   `G.hardInterventionOn` (`def_3_10`), each of which depends on
--   `[DecidableEq Node]` through the `Finset`-backed membership and
--   filter operations on `G.J ∪ G.V` and `G.E` / `G.L`.  Stronger
--   instances (`Fintype`, `LinearOrder`) are not needed at the
--   statement level and are deferred to the proof body's use sites.
-- claim_3_4 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_4 --- end helper

-- ## Helper — carrier-subset transport for nested hard interventions
--
-- The main theorem signature evaluates `(G.hardInterventionOn W₁
-- hW₁).hardInterventionOn W₂ ?_`, which per `def_3_10`'s signature
-- (`HardInterventionOn.lean`) requires
-- `?_ : W₂ ⊆ (G.hardInterventionOn W₁ hW₁).J ∪
--             (G.hardInterventionOn W₁ hW₁).V`.
-- The rewritten tex's "Carrier matching for the iterated hard
-- interventions" paragraph proves this from the `Finset` equality
-- `(G.J ∪ W₁) ∪ (G.V \ W₁) = G.J ∪ G.V`, which holds because
-- `W₁ ⊆ G.J ∪ G.V`.  We expose the transport as a stand-alone helper
-- lemma so the theorem signature stays free of inline `by`-blocks.
--
-- ## Design choice
--
-- *Wrapped with `--- start helper` so the rendered statement on the
--   website is self-contained.*  The main theorem signature uses this
--   lemma as the proof term for the inner-`hW` argument of the nested
--   `hardInterventionOn`; without it, the theorem type does not
--   elaborate.  The website builder is told to pull this helper out
--   alongside the rendered statement so a reader does not see a bare
--   reference to an undefined symbol.
--
-- *Phrased as a subset-transport (`S ⊆ G.J ∪ G.V → S ⊆ …`), not as a
--   set-equality (`(G.hardInterventionOn W hW).J ∪ … = G.J ∪ G.V`).*
--   The transport form is what the statement consumes directly; a
--   separate equality lemma would be one step further from the call
--   site and would force a `Finset.Subset.trans` rewrite at every
--   use site.
--
-- *Implicit `G`, `W`, `S`; explicit `hW`, `hS`.*  Mirrors
--   `hardInterventionOn`'s binder convention.  At the call site
--   `subset_carrier_of_hardInterventionOn hW₁ hW₂`, the implicit
--   arguments are synthesised from the goal, and the call reads
--   left-to-right as "the inner hard intervention is on `W₁` via
--   `hW₁`; the transported set is `W₂` via `hW₂`".
--
-- *`private`.*  Localises the lemma to this file.  Future rows that
--   compose hard interventions (e.g.\ ch.\ 5 do-calculus,
--   disjoint-intervention commutativity rows `claim_3_8` /
--   `claim_3_11`) should re-introduce the same helper at their use
--   site rather than reach across files.  If a chapter-wide reuse
--   pattern emerges, the helper can be promoted to a top-level lemma
--   in a later refactor.

-- ref: claim_3_4
-- For any CDMG `G : CDMG Node` and any two subsets `W₁, W₂ ⊆ G.J ∪
-- G.V`, the LN's triple equality
--   `(G_{do(W₁)})_{do(W₂)} = (G_{do(W₂)})_{do(W₁)} = G_{do(W₁ ∪ W₂)}`
-- decomposes into two binary CDMG equalities:
--   (a) `(G.hardInterventionOn W₁ hW₁).hardInterventionOn W₂ … =
--         G.hardInterventionOn (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)`,
--   (b) `(G.hardInterventionOn W₂ hW₂).hardInterventionOn W₁ … =
--         G.hardInterventionOn (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)`.
-- Transitivity of equality then recovers the LN's "swap symmetry"
-- `(G.hardInterventionOn W₁ hW₁).hardInterventionOn W₂ … =
-- (G.hardInterventionOn W₂ hW₂).hardInterventionOn W₁ …` from (a) ∧ (b).
/-
LN tex (rewritten canonical statement for `claim_3_4`, in essence):

  Let `G = (J, V, E, L)` be a CDMG and `W₁, W₂ ⊆ J ∪ V`.  Then
    (a) `(G_{do(W₁)})_{do(W₂)} = G_{do(W₁ ∪ W₂)}`,
    (b) `(G_{do(W₂)})_{do(W₁)} = G_{do(W₁ ∪ W₂)}`.

LN block (verbatim, for backup):

  Let `G := (J, V, E, L)` be a CDMG and `W_1, W_2 ⊆ J ∪ V` two
  subsets of nodes from `G`.  Then we have:
    `(G_{do(W_1)})_{do(W_2)} = (G_{do(W_2)})_{do(W_1)} = G_{do(W_1 ∪ W_2)}`.
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
--   `(G.hardInterventionOn W₁ hW₁).hardInterventionOn W₂ … =
--   (G.hardInterventionOn W₂ hW₂).hardInterventionOn W₁ …` is
--   recovered as `.1.trans .2.symm` (so no separate `A = B`
--   sub-claim is needed — transitivity of `=` does it for free, as
--   the rewrite's closing remark licenses).  Splitting into two
--   named theorems was rejected because it would (i) duplicate the
--   antecedents `hW₁`, `hW₂` at the theorem-head level, and (ii)
--   diverge from the rewrite's single-lemma packaging.  This matches
--   the sibling pattern in `claim_3_3` (`AcyclicPreservedUnderDo`),
--   which also packages its two sub-claims as a single theorem
--   returning a conjunction.
--
-- *Conjunction order (a) ∧ (b), matching the rewrite and the LN
--   reading order.*  The rewrite's `enumerate[label=(\alph*)]` block
--   lists (a) `W₁`-then-`W₂` first, (b) `W₂`-then-`W₁` second; we
--   preserve that order in the Lean conjunction so the natural `.1` /
--   `.2` projections line up with the (a) / (b) labels of the
--   rewrite.
--
-- *Right-hand side `G.hardInterventionOn (W₁ ∪ W₂) (Finset.union_subset
--   hW₁ hW₂)`, with the union-subset proof term inlined.*  The proof
--   term `Finset.union_subset hW₁ hW₂ : W₁ ∪ W₂ ⊆ G.J ∪ G.V` is a
--   mathlib one-liner not worth a named helper; both sub-claims share
--   the same right-hand side and the same proof term, so the
--   conjunction reads with literal `=`-symmetry between (a) and (b).
--
-- *Inner-`hW` for the nested intervention via
--   `subset_carrier_of_hardInterventionOn`.*  The outer
--   `.hardInterventionOn W₂` (in (a)) and `.hardInterventionOn W₁`
--   (in (b)) need a subset proof against the carrier of the
--   inner-intervened CDMG, not against `G.J ∪ G.V`.  The helper lemma
--   `subset_carrier_of_hardInterventionOn` transports the assumption
--   across the carrier-equality that the rewritten tex's
--   "Carrier matching for the iterated hard interventions" paragraph
--   proves verbatim.  Inlining a `by`-block in the type was rejected
--   because it would (i) bloat the rendered statement on the website,
--   and (ii) duplicate the carrier-matching reasoning at every use
--   site.
--
-- *CDMG equality (`=`) is read field-wise.*  Equality of two `CDMG`s
--   unfolds via the `structure` injectivity from `def_3_1` to the
--   conjunction of equalities on the four data fields `J`, `V`, `E`,
--   `L` (the five proof-fields are propositional and Lean's proof
--   irrelevance discharges them automatically).  We do not bake the
--   field-wise unpacking into the *statement*; it is deferred to the
--   proof per the rewritten tex's closing remark "the conjunctive
--   unpacking into the four field-by-field equalities is deferred to
--   the proof".
--
-- *`W₁` / `W₂` and `hW₁` / `hW₂` quantified at the theorem head,
--   matching `hardInterventionOn`'s binder convention.*  `def_3_10`
--   (`HardInterventionOn.lean`) takes `(W : Finset Node) (hW : W ⊆
--   G.J ∪ G.V)` as explicit arguments; we reuse the same shape so
--   call sites `G.hardInterventionOn Wᵢ hWᵢ` parse identically here
--   and at every downstream consumer.  The binder shape
--   `(G : CDMG Node) (W₁ W₂ : Finset Node) (hW₁ hW₂ : … ⊆ G.J ∪ G.V)`
--   is a direct echo of `def_3_10`'s signature with `W` / `hW`
--   replicated for the two intervention sets.
--
-- *No disjointness hypothesis: not `W₁ ∩ W₂ = ∅`, not `Wᵢ ∩ G.J = ∅`,
--   not any overlap restriction.*  The LN block in `graphs.tex`
--   (`\label{hard-interventions-commute}`) reads "two subsets of
--   nodes from `G`" with no disjointness rider, and the rewritten
--   canonical statement file makes this explicit ("no disjointness
--   between `W₁` and `W₂` is assumed, and overlap with `J` is
--   permitted, as per `def_3_10`'s precondition").  This is what
--   makes the lemma a *free composition* result on the hard-
--   intervention operation: `hardInterventionOn` commutes with
--   itself unconditionally, and the union expression `W₁ ∪ W₂` on
--   the right-hand side is the correct join with or without
--   overlap.  Contrast with the sibling row `claim_3_8`
--   (`DisjointHardInterventions`, `tex/claim_3_8_statement_…`), whose
--   Lean statement *will* carry an explicit `Disjoint W₁ W₂`
--   hypothesis because it mixes hard intervention with node-
--   splitting (where disjointness is genuinely load-bearing for the
--   split operation's well-typedness).  Adding a disjointness
--   binder here would strictly weaken the statement: every
--   downstream consumer (do-calculus reductions in ch.\ 5, the
--   iterated-intervention algebra of ch.\ 8+) can compose hard
--   interventions without first having to discharge a side
--   condition.  The `W ∩ J ≠ ∅` design-choice bullet in
--   `HardInterventionOn.lean` (`def_3_10`) already documents why
--   intervening on a node that is already in `J` is admissible at
--   the operation level; this row inherits that freedom and never
--   re-introduces it as a hypothesis.

end CDMG

namespace CDMG

-- ## Design choice — statement context (refactor twin)
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1`'s refactor twin `CDMG` (`CDMG.lean`).  Both
--   fixtures are load-bearing for this row's statement because the
--   signature references `CDMG Node` and
--   `G.hardInterventionOn` (`def_3_10`'s refactor twin in
--   `HardInterventionOn.lean`), each of which depends on
--   `[DecidableEq Node]` through the `Finset`-backed membership and
--   filter operations on `G.J ∪ G.V` and `G.E` / `G.L` (the latter is
--   now `Finset (Sym2 Node)`; `Sym2 Node`'s `DecidableEq` is derived
--   from `[DecidableEq Node]` by Mathlib).  Stronger instances
--   (`Fintype`, `LinearOrder`) are not needed at the statement level
--   and are deferred to the proof body's use sites.
-- claim_3_4 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_4 --- end helper

-- ## Local decidability instance for the L-filter predicate.
--
-- Private local copy of the `hardInterventionOn_decidable_bAll`
-- instance declared in `HardInterventionOn.lean`.  That instance is
-- declared `private` at the def-site (the design block on the
-- `hardInterventionOn` def explains why), so it does not
-- propagate to this file by `import`.  We supply our own identical
-- copy here so the `change` step in the L-branch of the main theorem
-- below — which writes the L-component of the iterated intervention
-- as `G.L.filter (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W)` — elaborates
-- without `DecidablePred` synthesis failure.  The implementation is
-- the same `Sym2.recOnSubsingleton` + `Sym2.ball` reduction used at
-- the def-site: every `s : Sym2 Node` is `s(a, b)` for some `a, b`;
-- `Sym2.ball` reduces `∀ v ∈ s(a, b), v ∉ W` to `a ∉ W ∧ b ∉ W`;
-- conjunction of decidable propositions is decidable.
set_option linter.style.longLine false in
private instance hardInterventionsCommute_decidable_bAll
    (W : Finset Node) :
    DecidablePred (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W) := fun s =>
  s.recOnSubsingleton fun _ _ => decidable_of_iff' _ Sym2.ball

-- ## Helper — carrier-subset transport for nested hard interventions
--   (refactor twin)
--
-- The main theorem signature evaluates
-- `(G.hardInterventionOn W₁ hW₁).hardInterventionOn W₂ ?_`,
-- which per `def_3_10`'s refactor twin signature requires
-- `?_ : W₂ ⊆ (G.hardInterventionOn W₁ hW₁).J ∪
--             (G.hardInterventionOn W₁ hW₁).V`.
-- This twin exposes the transport as a stand-alone helper lemma so the
-- theorem signature stays free of inline `by`-blocks.
--
-- *Mathematical content unchanged from the original.*  The proof is
-- pure set algebra on `Finset Node` over the `J/V/W` partition; `L`
-- is never touched, so the `Sym2`-encoded L of `CDMG` is
-- structurally invisible to this helper.  The body is identical to
-- the original `subset_carrier_of_hardInterventionOn`; only the
-- `CDMG` / `hardInterventionOn` upstream references are renamed to
-- their `refactor_` twins.
--
-- *Wrapped with `--- start helper` so the rendered statement on the
--   website is self-contained.*  Same reasoning as the original.
set_option linter.style.longLine false in
-- claim_3_4 --- start helper
private lemma subset_carrier_of_hardInterventionOn
    {G : CDMG Node} {W : Finset Node} (hW : W ⊆ G.J ∪ G.V)
    {S : Finset Node} (hS : S ⊆ G.J ∪ G.V) :
    S ⊆ (G.hardInterventionOn W hW).J ∪
          (G.hardInterventionOn W hW).V
-- claim_3_4 --- end helper
:= by
  intro v hv
  change v ∈ (G.J ∪ W) ∪ (G.V \ W)
  rcases Finset.mem_union.mp (hS hv) with hJ | hV
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hJ)
  · by_cases hW' : v ∈ W
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hW')
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hV, hW'⟩)

-- ref: claim_3_4 — refactor twin
-- For any CDMG `G : CDMG Node` and any two subsets
-- `W₁, W₂ ⊆ G.J ∪ G.V`, the LN's triple equality
--   `(G_{do(W₁)})_{do(W₂)} = (G_{do(W₂)})_{do(W₁)} = G_{do(W₁ ∪ W₂)}`
-- decomposes into two binary CDMG equalities (analogous to the
-- original `hardInterventionsCommute`).
--
-- The port is **mechanical**: triple CDMG equality decomposes
-- componentwise on the four data fields `J, V, E, L`, and only the
-- L branches change shape under the refactor.  The J / V / E
-- branches read byte-for-byte identically to the original (pure set
-- algebra on `Finset Node` and `Finset (Node × Node)`, both
-- untouched by `cdmg_typed_edges`); the L branches swap
-- `(Node × Node)`-style filter predicates for their `Sym2`-quotient
-- counterparts and pick up one extra local `DecidablePred` instance
-- (rationale below).  The remainder of this comment block records
-- *why* the new shape works structurally, so a future reader does
-- not have to re-derive the encoding choice.
--
-- ## Design choice (refactor twin)
--
-- *Structural port of the original `hardInterventionsCommute`*
-- onto
--   the `cdmg_typed_edges` refactor's new upstream types (DEPENDENT
--   row; root `def_3_1`).  The mathematical design — single theorem
--   returning a conjunction (a) ∧ (b), no disjointness hypothesis on
--   `W₁, W₂`, overlap with `J` permitted, right-hand side
--   `G.hardInterventionOn (W₁ ∪ W₂)`, inner-`hW` for the
--   nested intervention via `subset_carrier_of_hardInterventionOn`,
--   componentwise CDMG equality unpacked in the proof — is
--   **unchanged**.  See the original block above for the full
--   rationale; the resolutions of the LN wording-check (which
--   returned `NO_SUBTLETIES`) carry over verbatim.
--
-- *Mathematical content unchanged (TL;DR).*  The twin proves the same
--   theorem and runs the same argument as the original; the refactor
--   only swaps the upstream `CDMG` / `hardInterventionOn` shapes the
--   proof consumes.  J / V / E branches are byte-for-byte identical
--   (pure set algebra on `Finset Node` / `Finset (Node × Node)`,
--   untouched by the refactor).  Only the L branches change shape, as
--   the next bullet explains.
--
-- *The `hard_intervention_l_symmetrized_removal` deviation registered
--   against the *pre-refactor* encoding of `def_3_10` is structurally
--   resolved at the `def_3_10` row itself.*  Under the post-refactor
--   `Sym2` encoding of `CDMG.L`, the LN's item iv. set-builder
--   `L \sm \{ (v_1, v_2) \in L \mid v_2 \in W \}` reads literally:
--   there is no ordered "second component" on a `Sym2 Node` value to
--   test, so the only sensible filter is "any endpoint of the
--   unordered pair lies in `W`", which is what
--   `fun s => ∀ v ∈ s, v ∉ W` (kept-condition) expresses.  No
--   symmetrisation step is required — `s(v, w) = s(w, v)` is
--   definitional, so the LN-literal one-sided reading is already
--   symmetric by construction.  Consequently, the L branches of this
--   proof do *not* contain a "Remark on the Lean encoding of L"
--   bridging paragraph; the tex twin
--   `tex/refactor_claim_3_4_proof_HardInterventionsCommute.tex`
--   replaces that paragraph with a short note documenting the
--   structural resolution.
--
-- *Upstream-type shifts (and only those).*  The Lean translation work
--   is *mechanical* — each substitution maps one identifier:
--   - `CDMG Node                          → CDMG Node`
--   - `G.hardInterventionOn W hW          → G.hardInterventionOn W hW`
--   - `subset_carrier_of_hardInterventionOn → subset_carrier_of_hardInterventionOn`
--   - `cdmgExt` inline helper destructures 8 `CDMG` fields
--     (`J, V, hJV_disj, E, hE_subset, L, hL_subset, hL_irrefl`), not
--     the original 9 (the pre-refactor `hL_symm` field is gone — swap-
--     symmetry is definitional on `Sym2`).
--   - L-branch predicate
--     `fun e : Node × Node => e.1 ∉ W ∧ e.2 ∉ W` (ordered pair,
--      two-sided)
--     → `fun s : Sym2 Node => ∀ v ∈ s, v ∉ W` (Sym2 quotient, bounded
--        forall over endpoints).
--   - L-branch predicate equivalence
--     `(e.1 ∉ W₁ ∧ e.2 ∉ W₁) ∧ (e.1 ∉ W₂ ∧ e.2 ∉ W₂)
--        ↔ e.1 ∉ W₁ ∪ W₂ ∧ e.2 ∉ W₁ ∪ W₂`
--     (closed by `simp [Finset.mem_union, not_or]; tauto`)
--     → `(∀ v ∈ s, v ∉ W₁) ∧ (∀ v ∈ s, v ∉ W₂)
--          ↔ ∀ v ∈ s, v ∉ W₁ ∪ W₂`
--     (closed by `simp [Finset.mem_union, not_or, forall_and]` or an
--      explicit `constructor`-split if the simp set differs).
--
-- *Proof skeleton — `Finset.filter_filter` + `Finset.filter_congr`,
--   with one `Finset.union_comm` for sub-claim (b).*  All four
--   componentwise equalities run the same composition idiom: the
--   nested intervention writes a `filter`-after-`filter` on the
--   corresponding data field, which collapses to a single `filter`
--   via `Finset.filter_filter`; the resulting predicate is then
--   rewritten against the appropriate pointwise predicate
--   equivalence via `Finset.filter_congr`.  Branch by branch: J
--   collapses via `Finset.union_assoc` directly (no `filter`); V
--   collapses via the `sdiff_sdiff_left` identity
--   `(A \ B) \ C = A \ (B ∪ C)` (also no `filter`); E and L go
--   through `Finset.filter_filter`+`filter_congr` over the pointwise
--   equivalence `(p₁ x ∧ p₂ x) ↔ p₁₂ x` (cashed out via
--   `Finset.mem_union, not_or` for E, and the `forall_and`-
--   distributed `Sym2`-quotient analogue for L, per the predicate-
--   equivalence sub-bullet above).  Sub-claim (b)'s right-hand side
--   carries an extra `Finset.union_comm W₁ W₂` rewrite so the
--   `W₂ ∪ W₁` produced by re-running (a)'s argument at the swapped
--   pair matches the statement's syntactic `W₁ ∪ W₂` — this is the
--   tex's "by symmetry" closing step made literal at the Lean level.
--
-- *Local `private instance hardInterventionsCommute_decidable_bAll`
--   (declared above this comment block).*  See its own design
--   comment for the full body-level rationale; the design-level
--   point worth surfacing in the main theorem's block is that the
--   matching instance at the `def_3_10`-twin site
--   (`HardInterventionOn.lean`,
--   `hardInterventionOn_decidable_bAll`) is declared
--   `private`, so it does *not* propagate to this file by `import`.
--   The `change` step in the L branch of the main theorem below
--   writes the L-component filter syntax explicitly (`G.L.filter
--   (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W)`), which forces
--   `DecidablePred` synthesis at *this* file's elaboration scope —
--   absent a local witness, the `change` fails.  We replicate the
--   instance locally — same body, same `private` qualifier — rather
--   than promote the def-site instance to a public one.  Private-
--   to-private duplication is the cheapest fix on the spectrum
--   (export the def-site instance / promote to public file-scope
--   `instance` / inline `classical` at the `change`-site);
--   exporting would impose the `Sym2.ball`-via-`recOnSubsingleton`
--   reduction on every importer of `HardInterventionOn`, and inline
--   `classical` would tank kernel performance of the surrounding
--   `rw`+`refine` chain.
--
-- *What this refactor does NOT touch.*  The LN statement of
--   `claim_3_4` is unchanged by the refactor — the
--   `cdmg_typed_edges` rewrite happens at `def_3_1`'s typing layer,
--   not at this row's statement layer — so no rewritten statement
--   twin is required; only the proof body is twinned (at
--   `tex/refactor_claim_3_4_proof_HardInterventionsCommute.tex`).
--   `addition_to_the_LN` for this row is empty (`""` in
--   `refactor_data.json`), so no new operator-style clarifications
--   are introduced by the refactor.  The two implicit LN readings
--   already documented on the wrapped `REFACTOR-BLOCK-ORIGINAL`
--   block above — no disjointness between `W₁` and `W₂` is assumed,
--   and overlap with `J` is permitted (per `def_3_10`'s
--   precondition) — carry through verbatim, and every other top-
--   level design choice from the original (single-theorem-returning-
--   a-conjunction packaging, conjunction order (a) ∧ (b),
--   `Finset.union_subset` for the RHS subset proof,
--   `subset_carrier_of_hardInterventionOn`-style inner-`hW`,
--   explicit binders matching `hardInterventionOn`'s shape) is
--   reproduced in the twin without modification — read the ORIGINAL
--   block above for the full rationale on each.
set_option linter.style.longLine false in
-- claim_3_4 -- start statement
theorem hardInterventionsCommute (G : CDMG Node)
    (W₁ W₂ : Finset Node)
    (hW₁ : W₁ ⊆ G.J ∪ G.V) (hW₂ : W₂ ⊆ G.J ∪ G.V) :
    (G.hardInterventionOn W₁ hW₁).hardInterventionOn W₂
        (subset_carrier_of_hardInterventionOn hW₁ hW₂)
      = G.hardInterventionOn (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)
    ∧
    (G.hardInterventionOn W₂ hW₂).hardInterventionOn W₁
        (subset_carrier_of_hardInterventionOn hW₂ hW₁)
      = G.hardInterventionOn (W₁ ∪ W₂) (Finset.union_subset hW₁ hW₂)
-- claim_3_4 -- end statement
:= by
  -- Inline `CDMG` extensionality (used twice below): two
  -- `CDMG`s are equal if their four data fields (`J`, `V`,
  -- `E`, `L`) agree.  The four propositional fields of `def_3_1`'s
  -- refactor twin (`hJV_disj`, `hE_subset`, `hL_subset`,
  -- `hL_irrefl`) have types determined by the data fields, so once
  -- the data fields are equated their types coincide and proof
  -- irrelevance forces the witnesses equal.  Eight-field
  -- destructuring (the pre-refactor `hL_symm` field is gone — swap-
  -- symmetry is definitional on `Sym2`).
  have cdmgExt : ∀ {G₁ G₂ : CDMG Node},
      G₁.J = G₂.J → G₁.V = G₂.V → G₁.E = G₂.E → G₁.L = G₂.L → G₁ = G₂ := by
    rintro ⟨J₁, V₁, hJV₁, E₁, hE₁, L₁, hL₁, hLi₁⟩
           ⟨J₂, V₂, hJV₂, E₂, hE₂, L₂, hL₂, hLi₂⟩ hJ hV hE hL
    obtain rfl := hJ
    obtain rfl := hV
    obtain rfl := hE
    obtain rfl := hL
    rfl
  refine ⟨?_, ?_⟩
  · -- (a) `(G_{do(W₁)})_{do(W₂)} = G_{do(W₁ ∪ W₂)}`.
    -- Verify the four data-field equalities in turn, each of which is the
    -- componentwise check spelled out in the proof tex.
    refine cdmgExt ?_ ?_ ?_ ?_
    · -- J: `(G.J ∪ W₁) ∪ W₂ = G.J ∪ (W₁ ∪ W₂)` — associativity of `∪`.
      exact Finset.union_assoc G.J W₁ W₂
    · -- V: `(G.V \ W₁) \ W₂ = G.V \ (W₁ ∪ W₂)` — the LN identity
      -- `(A \ B) \ C = A \ (B ∪ C)` for set difference.
      exact sdiff_sdiff_left
    · -- E: the nested filter on `e.2 ∉ W₁` then `e.2 ∉ W₂` collapses to
      -- a single filter on `e.2 ∉ W₁ ∪ W₂` via `not_or` ↔ membership in
      -- a union.  Unchanged from the original (E's ordered-pair typing
      -- is untouched by the refactor).
      change (G.E.filter (fun e : Node × Node => e.2 ∉ W₁)).filter
            (fun e : Node × Node => e.2 ∉ W₂)
        = G.E.filter (fun e : Node × Node => e.2 ∉ W₁ ∪ W₂)
      rw [Finset.filter_filter]
      refine Finset.filter_congr (fun e _ => ?_)
      rw [Finset.mem_union, not_or]
    · -- L: filter `∀ v ∈ s, v ∉ W₁` then `∀ v ∈ s, v ∉ W₂` collapses to
      --    filter `∀ v ∈ s, v ∉ W₁ ∪ W₂`.  Predicate equivalence
      --    `(∀ v ∈ s, v ∉ W₁) ∧ (∀ v ∈ s, v ∉ W₂) ↔ ∀ v ∈ s, v ∉ W₁ ∪ W₂`
      --    closes via `forall_and` (split conjunction inside the bounded
      --    forall) plus the `Finset.mem_union, not_or` step the directed
      --    edge branch above also uses.  No symmetrisation needed — the
      --    `Sym2` typing is structurally orientation-free.
      change (G.L.filter (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₁)).filter
            (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₂)
        = G.L.filter (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₁ ∪ W₂)
      rw [Finset.filter_filter]
      refine Finset.filter_congr (fun s _ => ?_)
      constructor
      · rintro ⟨h1, h2⟩ v hv
        simp only [Finset.mem_union, not_or]
        exact ⟨h1 v hv, h2 v hv⟩
      · intro h
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · exact (by simpa [Finset.mem_union, not_or] using h v hv : v ∉ W₁ ∧ v ∉ W₂).1
        · exact (by simpa [Finset.mem_union, not_or] using h v hv : v ∉ W₁ ∧ v ∉ W₂).2
  · -- (b) `(G_{do(W₂)})_{do(W₁)} = G_{do(W₁ ∪ W₂)}`.
    -- Same four-field check with `W₁ ↔ W₂` swapped in the LHS, plus one
    -- `Finset.union_comm` on the right-hand side to rewrite
    -- `W₂ ∪ W₁` into `W₁ ∪ W₂` (the tex's "by symmetry" closing step).
    refine cdmgExt ?_ ?_ ?_ ?_
    · -- J: `(G.J ∪ W₂) ∪ W₁ = G.J ∪ (W₁ ∪ W₂)`.
      change G.J ∪ W₂ ∪ W₁ = G.J ∪ (W₁ ∪ W₂)
      rw [Finset.union_assoc, Finset.union_comm W₂ W₁]
    · -- V: `(G.V \ W₂) \ W₁ = G.V \ (W₁ ∪ W₂)`.  Use `Finset.union_comm`
      -- on the right-hand side first so the `sdiff_sdiff_left` shape
      -- `a \ (b ⊔ c)` unifies with `G.V \ (W₂ ∪ W₁)` by definitional
      -- equality of `⊔` and `∪` on `Finset`.
      change (G.V \ W₂) \ W₁ = G.V \ (W₁ ∪ W₂)
      rw [Finset.union_comm W₁ W₂]
      exact sdiff_sdiff_left
    · -- E: nested filter `(e.2 ∉ W₂) ∧ (e.2 ∉ W₁)` collapses to
      -- `e.2 ∉ W₁ ∪ W₂`.
      change (G.E.filter (fun e : Node × Node => e.2 ∉ W₂)).filter
            (fun e : Node × Node => e.2 ∉ W₁)
        = G.E.filter (fun e : Node × Node => e.2 ∉ W₁ ∪ W₂)
      rw [Finset.filter_filter]
      refine Finset.filter_congr (fun e _ => ?_)
      simp only [Finset.mem_union, not_or]
      tauto
    · -- L: same pattern as (a)'s L-branch with `W₁ ↔ W₂` swap.
      change (G.L.filter (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₂)).filter
            (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₁)
        = G.L.filter (fun s : Sym2 Node => ∀ v ∈ s, v ∉ W₁ ∪ W₂)
      rw [Finset.filter_filter]
      refine Finset.filter_congr (fun s _ => ?_)
      constructor
      · rintro ⟨h2, h1⟩ v hv
        simp only [Finset.mem_union, not_or]
        exact ⟨h1 v hv, h2 v hv⟩
      · intro h
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · exact (by simpa [Finset.mem_union, not_or] using h v hv : v ∉ W₁ ∧ v ∉ W₂).2
        · exact (by simpa [Finset.mem_union, not_or] using h v hv : v ∉ W₁ ∧ v ∉ W₂).1

end CDMG

end Causality
