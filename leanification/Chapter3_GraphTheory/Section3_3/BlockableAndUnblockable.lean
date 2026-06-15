import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.EdgeRelations
import Chapter3_GraphTheory.Section3_1.Walks
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_3.CollidersAndNon

namespace Causality

/-!
# Blockable and unblockable non-colliders on walks (`def_3_16`)

This file formalises `def_3_16` (`\label{def:unblockable_noncollider}`),
the second definition of Section 3.3 of the lecture notes.  Given a
walk `π = (v_0, a_0, v_1, …, a_{n-1}, v_n)` in a CDMG `G` and a
non-collider position `k` on `π` (per `def_3_15`), the position is
further classified as either an **unblockable** or a **blockable**
non-collider depending on whether every *outgoing walk-edge of `v_k`*
on `π` lands back inside the strongly connected component `G.Sc vk`.

* `Walk.IsBlockableNonCollider p k` — `p.IsNonCollider k` AND (`k`
  is at an end-position (`k = 0` or `k = p.length`) OR some
  walk-incident edge `a_i` (`i ∈ {k - 1, k}`) is an *outgoing*
  walk-edge of `v_k` (a directed edge with `v_k` as its tail) whose
  other walk-endpoint along `π` lies *outside* `G.Sc vk`).  Spelled
  out per the canonical tex as a disjunction with two end-position
  disjuncts and one disjunct per walk-incident index (backward
  writing `(vk, vkm1) ∈ E` for `i = k - 1`, forward writing
  `(vk, vkp1) ∈ E` for `i = k`).
* `Walk.IsUnblockableNonCollider p k` — `p.IsNonCollider k` AND not
  `p.IsBlockableNonCollider k`.  Unfolding the negation, this is
  equivalent to: non-collider AND interior (`k ≠ 0 ∧ k ≠ p.length`)
  AND every outgoing walk-edge of `v_k` along `π` lands in `G.Sc vk`
  — the LN's two-implication unblockable characterisation.  We
  encode the derived (negation) form so that mutual exclusivity on
  the non-collider sub-class becomes definitional.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/def_3_16_BlockableAndUnblockable.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:unblockable_noncollider}`).  The canonical tex's
`addition_to_the_LN` is empty — the rewrite resolves the LN-wording
ambiguities (existential-shorthand vs walk-edge reading; self-loop
overlap of the literal pattern matches; the "outgoing arrow" reading
of the blockable elaboration) by adopting the *walk-edge-based*
reading as canonical, mirroring `def_3_15`.

## Design pillars

1. **Walk-edge reading, not existential-shorthand reading.**  Each
   implication of clause (iii) conditions on `p.edges[k - 1]? = some
   (vk, vkm1)` / `p.edges[k]? = some (vk, vkp1)` — i.e.\ the *walk's*
   specific incident edges with `v_k` as tail — and adds the explicit
   `(vk, vkm1) ∈ G.E` / `(vk, vkp1) ∈ G.E` membership to mirror the
   LN's `\in E` notation.  An auxiliary directed edge `(vk, w) ∈ G.E`
   of `G` that does *not* appear as `a_{k - 1}` or `a_k` on `π` is
   irrelevant to the classification of `k` on `π`.  The canonical tex
   commits to this resolution in its "Reconciliation" paragraph; it
   is the resolution of the LN-critic's
   `pattern_shorthands_existential_in_g_not_walk_specific` and
   `blockable_clause_says_arrow_not_outgoing_edge` subtleties.

2. **Slot-keyed disjuncts, one per walk-incident index — not a
   quantified `∃ i ∈ I_π(k)`.**  The canonical tex spells the
   blockable disjunction's interior-position cases as two `∃`
   disjuncts, one for `i = k - 1` (backward writing) and one for
   `i = k` (forward writing).  Two independent disjuncts are cleaner
   in Lean than a quantification over a 0-or-1-element index set and
   compose better with the Option-membership lookups on `p.edges`.

3. **Asymmetric encoding: `Blockable` carries the positive
   characterisation (LN's disjunctive elaboration form),
   `Unblockable = NonCollider ∧ ¬ Blockable`.**  Mirrors
   `CollidersAndNon.lean`'s `IsCollider` / `IsNonCollider` asymmetry.
   Mutual exclusivity on the non-collider sub-class is *definitional*
   — one is literally the negation of the other on the
   `IsNonCollider` fragment — so the LN's "every non-collider position
   is exactly one of unblockable or blockable" reduces by unfolding,
   not by an external theorem.  Reading off the LN's disjunctive form
   for blockable as the primary def exposes the positive witness of a
   blocking walk-edge directly — exactly what downstream walk-reversal
   proofs (claim_3_22 onward) need to manipulate.  Encoding the LN's
   universal-implication form for unblockable as the primary def was
   rejected: it would duplicate the blockable case-split with negated
   polarities and would owe an external proof of mutual exclusivity
   that the negation encoding gives for free.

4. **Interior bound `1 ≤ k ∧ k + 1 ≤ p.length` carried via the
   `1 ≤ k` guard plus the Option-membership `p.vertices[k + 1]? =
   some vkp1`.**  Matches `IsCollider`'s `1 ≤ k ∧ ∃ vk a₁ a₂, …`
   shape, where the upper bound is implicit through the lookups.
   The explicit `1 ≤ k` is required because Lean's ℕ subtraction is
   truncated (without it, at `k = 0` the lookup `p.vertices[k - 1]?`
   would mis-target `p.vertices[0]? = some v_0`); the upper bound
   `k + 1 ≤ p.length` is recoverable from the vertex Option-membership.

5. **`G.Sc` reused from `FamilyRelationships.lean` (`def_3_5`,
   item vii).**  The strongly connected component
   `Sc^G(v) := Anc^G(v) ∩ Desc^G(v)` is already a `Set Node`-valued
   operator; set-membership `vkm1 ∈ G.Sc vk` reads off cleanly.  The
   trivial-walk witness from `def_3_5` makes `vk ∈ G.Sc vk` an
   automatic identity, which is what makes the self-loop case
   `a_{k - 1} = (vk, vk)` automatically satisfy the unblockable
   condition (canonical tex's "Treatment of directed self-loops"
   paragraph, inheriting `def_3_15`'s walk-edge resolution).

6. **`p.IsNonCollider k` reused from `CollidersAndNon.lean`
   (`def_3_15`).**  Clause (i) of both unblockable and blockable is
   literally the `def_3_15` non-collider classifier; reusing it
   keeps the LN's "non-collider precondition" visible at the type
   level rather than re-spelling the arrowhead-count negation here.

The substantive per-declaration design rationale lives in the
comment block immediately above each `-- def_3_16 -- start statement`
marker.
-/

namespace CDMG

-- ## Design choice — section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Matches the
--   chapter convention set by `CDMG.lean`, `CDMGNotation.lean`,
--   `EdgeRelations.lean`, `Walks.lean`, `FamilyRelationships.lean`,
--   `CollidersAndNon.lean`.  Fixing `Node` to a concrete carrier
--   here would force renumbering at every downstream consumer that
--   rewrites the vertex set.
--
-- *Three-dash `--- start helper` / `--- end helper`, not two-dash
--   `-- start statement`.*  Lean 4's `variable` auto-binding folds
--   these implicit binders into every declaration below — they are
--   load-bearing infrastructure, not throwaway local sugar.  Matches
--   the wrapping convention used by every prior file in this chapter
--   on the identical `variable` line.
-- def_3_16 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_16 --- end helper

namespace Walk

-- ## Design choice — Walk-namespace statement context
--
-- *Namespace-level `variable {G : CDMG Node}`.*  Both
--   `IsUnblockableNonCollider` and `IsBlockableNonCollider` take a
--   walk `p : Walk G u v` (and reach into `G` for `G.Sc` and
--   `G.E`).  Without the namespace-wide `variable`, every signature
--   would carry an explicit `{G : CDMG Node}` binder; the
--   auto-binding keeps the signatures readable and matches the LN's
--   once-at-the-top "Let $G = (J, V, E, L)$ be a CDMG" quantifier.
--   `{G}` is implicit because downstream consumers reach into `G`
--   via dot-notation on the walk
--   (`p.IsUnblockableNonCollider k`).
-- def_3_16 --- start helper
variable {G : CDMG Node}
-- def_3_16 --- end helper



-- ref: def_3_16 (paragraph "Blockable non-collider on π")
--
-- `p.IsBlockableNonCollider k` iff position `k` on the walk
-- `p` is a non-collider on `p` (per `def_3_15`) AND it is either at
-- an end-position (`k = 0` or `k = p.length`) or there is some
-- outgoing walk-edge of `v_k` on `π` whose other walk-endpoint along
-- `π` lies outside `G.Sc vk`.  This encodes the LN's "blockable
-- disjunction" elaboration (canonical tex's spelled-out disjunction
-- form) one-for-one:
--
--   k = 0  ∨  k = p.length
--   ∨  (a_{k - 1} = (v_k, v_{k - 1}) ∈ E  ∧  v_{k - 1} ∉ Sc^G(v_k))
--   ∨  (a_k     = (v_k, v_{k + 1}) ∈ E  ∧  v_{k + 1} ∉ Sc^G(v_k)).
--
-- ## Design choice
--
-- *Primary positive disjunction.*  The LN's "blockable" elaboration
--   is itself a disjunction (end-position OR some outgoing walk-edge
--   to a node not in the strongly connected component), so taking
--   *blockable* as the primary predicate reads off the LN
--   one-for-one and `IsUnblockableNonCollider` becomes a derived
--   predicate via negation on the non-collider sub-class.  Downstream
--   walk-reversal proofs (claim_3_22 onward) reduce to preservation
--   of this positive predicate — a cleaner case-split structure than
--   a universally-quantified-implication form, because the witness of
--   a blocking walk-edge is exposed directly rather than through a
--   double negation.  Mutual exclusivity of the two classifications
--   on the non-collider sub-class is definitional.
--
-- *Walk-edge reading, not existential-shorthand reading.*  Each
--   interior-position disjunct uses the walk's specific edge lookup
--   `p.edges[k - 1]? = some (vk, vkm1)` (resp.
--   `p.edges[k]? = some (vk, vkp1)`) as one of its conjuncts — NOT
--   a generic existence claim about edges in `G`.  The canonical
--   tex's "Reconciliation" paragraph and its trailing "outgoing
--   arrow" reconciliation explicitly reject the existential reading
--   of the LN's `v_k \tuh v_{k\pm 1}` shorthand: a non-walk
--   directed edge `(vk, w) ∈ G.E` of `G` that does not appear as
--   `a_{k - 1}` or `a_k` on `π` is irrelevant to the classification
--   of `k` on `π`.  This resolves the LN-critic's
--   `pattern_shorthands_existential_in_g_not_walk_specific` and
--   `blockable_clause_says_arrow_not_outgoing_edge` subtleties (and
--   inherits the resolution of `self_loop_pattern_overlap_inherited`
--   via the canonical tex's "Treatment of directed self-loops"
--   paragraph).
--
-- *Slot-keyed disjunction (`i = k - 1` and `i = k` as explicit
--   disjuncts), not slot-agnostic `∃ i ∈ {k - 1, k}`.*  The two
--   outgoing-walk-edge cases are spelled out as two explicit
--   disjuncts — one for the `i = k - 1` slot (backward writing
--   `a_{k - 1} = (v_k, v_{k - 1}) ∈ E`, guarded by `1 ≤ k`) and one
--   for the `i = k` slot (forward writing `a_k =
--   (v_k, v_{k + 1}) ∈ E`) — rather than as a single quantification
--   `∃ i ∈ {k - 1, k}, …`.  Three reasons: (a) the slot-keyed form
--   matches the LN's "blockable disjunction" verbatim — the
--   canonical tex's "Blockable non-collider on π" paragraph spells
--   out exactly the same two `∧`-conjuncts, one per slot; (b)
--   `Walk.vertices` / `Walk.edges` are already slot-indexed
--   (`p.vertices[k - 1]?`, `p.vertices[k]?`, `p.edges[k - 1]?`,
--   `p.edges[k]?` are distinct lookups), so the slot-keyed form
--   avoids an extra `∃ i` layer over the Option-membership lookups
--   that would have to be case-split into `i = k - 1` / `i = k` at
--   the first use anyway; (c) `IsCollider`
--   (`CollidersAndNon.lean`, `def_3_15`) commits the chapter to the
--   slot-keyed `1 ≤ k ∧ ∃ vk a₁ a₂, …` idiom, which the present
--   predicate mirrors slot-by-slot.  The unifying `∃ i ∈ {k - 1, k}`
--   abstraction would be elegant but inconsistent with the
--   chapter's existing conventions.
--
-- *Outgoing walk-edge condition is `E`-only, not `E ∪ L`.*  Each
--   non-trivial disjunct requires `(vk, vkm1) ∈ G.E` (resp.
--   `(vk, vkp1) ∈ G.E`): a directed edge whose tail is `v_k`.
--   Bidirected `L`-edges are **not** counted as contributing outgoing
--   arrowheads from `v_k`.  Three independent LN witnesses pin this
--   down: (1) the LN's blockable elaboration says "at least one
--   outgoing arrow `v_k \tuh v_{k \pm 1}`", and `\tuh` per def_3_2
--   item~2 unfolds strictly to `(v_k, v_{k \pm 1}) ∈ E` — directed
--   `E`-edges only, never `L`; (2) def_3_3's definition of "out of
--   `v_1`" explicitly excludes `L`-edges; (3) the canonical tex's
--   "Reconciliation" paragraph commits to the `E`-only reading
--   explicitly ("Bidirected edges (`a_i ∈ L`) ... are excluded from
--   this predicate").
--
-- *End-position disjuncts `k = 0 ∨ k = p.length`.*  The LN's
--   blockable elaboration places end-positions in the blockable
--   class explicitly (canonical tex's "Reconciliation" item
--   "end-position": "the source-block elaboration assigns
--   end-positions to the blockable category via the `k \in \{0, n\}`
--   disjunct").  We encode that placement as the first two disjuncts
--   of the disjunction.  Both end-positions automatically satisfy
--   the `p.IsNonCollider k` conjunct (at `k = 0`, `IsCollider`'s
--   `1 ≤ k` guard fails so `¬IsCollider 0` holds and `0 ≤ p.length`
--   is automatic; at `k = p.length`, the missing edge lookup
--   `p.edges[k]? = none` forces `¬IsCollider p.length` and
--   `p.length ≤ p.length` is automatic), so at both end-positions
--   `IsBlockableNonCollider` reduces to `True ∧ True =
--   True`, matching the LN.
--
-- *`p.IsNonCollider k` conjunct is load-bearing, not cosmetic.*
--   Without it the predicate would over-fire on collider positions:
--   an interior collider `k` might happen to admit a walk-edge
--   `p.edges[k]? = some (vk, vkp1)` with `(vk, vkp1) ∈ G.E` and
--   `vkp1 ∉ G.Sc vk` (the existence of such walks is not blocked by
--   the `IsCollider` predicate at all), and would then be
--   mis-classified as blockable.  The LN restricts "blockable" to
--   the non-collider sub-class — they are a classification *of
--   non-colliders*, not of all walk positions — and the
--   `p.IsNonCollider k` conjunct is the predicate-level encoding of
--   that restriction.
--
-- *No `Decidable` instance, `Prop`-only.*  Matches the chapter
--   convention for walk-position predicates (`IsCollider`,
--   `IsNonCollider`, `IsDirectedWalk`, ...).  A `Bool` form would
--   require deciding `(vk, vkm1) ∈ G.E` and `vkm1 ∈ G.Sc vk` at every
--   elaboration site, adding infrastructure with no payoff for
--   downstream `σ`-separation rows (`def_3_17`+).
--
-- def_3_16 -- start statement
def IsBlockableNonCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  p.IsNonCollider k ∧
  ( k = 0 ∨ k = p.length ∨
    (1 ≤ k ∧ ∃ (vkm1 vk : Node),
        p.vertices[k - 1]? = some vkm1 ∧
        p.vertices[k]? = some vk ∧
        p.edges[k - 1]? = some (vk, vkm1) ∧
        (vk, vkm1) ∈ G.E ∧
        vkm1 ∉ G.Sc vk) ∨
    (∃ (vk vkp1 : Node),
        p.vertices[k]? = some vk ∧
        p.vertices[k + 1]? = some vkp1 ∧
        p.edges[k]? = some (vk, vkp1) ∧
        (vk, vkp1) ∈ G.E ∧
        vkp1 ∉ G.Sc vk) )
-- def_3_16 -- end statement

-- ref: def_3_16 (paragraph "Unblockable non-collider on π")
--
-- `p.IsUnblockableNonCollider k` iff position `k` on the
-- walk `p` is a non-collider on `p` (per `def_3_15`) AND it is NOT a
-- blockable non-collider on `p`.  Unfolding the negation of
-- `IsBlockableNonCollider`'s disjunction recovers the LN's
-- two-implication unblockable characterisation: `k` is interior
-- (`k ≠ 0 ∧ k ≠ p.length`, equivalently `1 ≤ k ≤ p.length - 1` on
-- the in-range fragment) and every outgoing walk-edge of `v_k` on
-- `π` lands in `G.Sc vk`.
--
-- ## Design choice
--
-- *Encoded as `p.IsNonCollider k ∧ ¬ p.IsBlockableNonCollider
--   k`.*  The LN's "unblockable" classifier is the *non-blockable*
--   sub-class of non-collider positions; the canonical tex's
--   "Unblockable non-collider on π" paragraph spells out exactly this
--   characterisation.  Encoding the conjunction directly makes the
--   LN's mutual exclusivity ("every non-collider position is exactly
--   one of unblockable or blockable") definitional: for any `k`
--   satisfying `p.IsNonCollider k`, exactly one of
--   `IsBlockableNonCollider k` and `IsUnblockableNonCollider k`
--   holds, by unfolding.  Both predicates are definitionally
--   interlocked on the `IsNonCollider` sub-class.
--
-- *`p.IsNonCollider k` conjunct is load-bearing, not cosmetic.*
--   Without it the predicate would over-fire on collider positions:
--   any collider `k` automatically satisfies
--   `¬ IsBlockableNonCollider k` (because
--   `IsBlockableNonCollider` carries `IsNonCollider` as its
--   first conjunct, so colliders fail it), so dropping the
--   `IsNonCollider` conjunct here would mis-classify every collider
--   as unblockable.  The LN restricts both "unblockable" and
--   "blockable" to the non-collider sub-class — they are mutually
--   exclusive classifications *of non-colliders*, not of all walk
--   positions — and the `p.IsNonCollider k` conjunct is the
--   predicate-level encoding of that restriction.
--
-- *Why the derived predicate has the LN's intended meaning.*  By
--   unfolding `IsBlockableNonCollider`, the negation
--   distributes over the disjunction and gives: `k ≠ 0 ∧ k ≠
--   p.length` (negation of the end-position disjuncts — the LN's
--   "interior" clause (ii)) ∧ negation of each `∃`-disjunct ∧
--   `p.IsNonCollider k` (positive conjunct preserved by the
--   conjunction here).  Negating each `∃`-disjunct gives a universal
--   implication: "for every choice of `vk` and `vk±1` such that the
--   walk lookups match, `(vk, vk±1) ∈ G.E → vk±1 ∈ G.Sc vk`" — the
--   exact two implications of LN clause (iii).  So derivedness
--   preserves the LN's unblockable characterisation case-by-case.
--
-- *Dot-notation `p.IsBlockableNonCollider k`.*
--   `IsBlockableNonCollider` is declared in the same
--   `namespace Walk` and takes `p : Walk G u v` as its first
--   explicit positional argument, so the dot-notation resolves to
--   `Walk.IsBlockableNonCollider p k` — same idiom used by
--   `p.IsNonCollider k`, `p.IsCollider k`, and
--   `p.IsBlockableNonCollider k` directly above.
--
-- *No `Decidable` instance, `Prop`-only.*  Same rationale as
--   `IsBlockableNonCollider` above.  Downstream consumers
--   (`def_3_17` σ-blocked walks) take `IsUnblockableNonCollider` as
--   a hypothesis-style `Prop` predicate; matching that shape keeps
--   the type contract clean.
-- def_3_16 -- start statement
def IsUnblockableNonCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  p.IsNonCollider k ∧ ¬ p.IsBlockableNonCollider k
-- def_3_16 -- end statement

end Walk

end CDMG

end Causality
