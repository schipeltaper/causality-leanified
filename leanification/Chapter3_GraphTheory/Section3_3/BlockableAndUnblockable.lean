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
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsBlockableNonCollider
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
-- REFACTOR-BLOCK-ORIGINAL-END: IsBlockableNonCollider

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
-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsUnblockableNonCollider
-- def_3_16 -- start statement
def IsUnblockableNonCollider {u v : Node} (p : Walk G u v) (k : ℕ) : Prop :=
  p.IsNonCollider k ∧ ¬ p.IsBlockableNonCollider k
-- def_3_16 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsUnblockableNonCollider

end Walk

end CDMG

end Causality

namespace Causality

namespace refactor_CDMG

-- ## Design choice — refactor section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same chapter
--   convention used by the original `CDMG` namespace above and by every
--   other `refactor_CDMG`-opening file in the chapter
--   (`CollidersAndNon.lean`'s refactor section, `Walks.lean:1201-1203`,
--   `CDMG.lean`, `CDMGNotation.lean`, `EdgeRelations.lean`).  The
--   refactor does not alter the carrier-type discipline — only (a)
--   `def_3_1`'s `L`-field shape (`Finset (Sym2 Node)` with
--   `hL_irrefl : ∀ ⦃s⦄, s ∈ L → ¬ s.IsDiag`) and (b) `def_3_4`'s
--   per-step walk-edge data (typed `refactor_WalkStep` with three
--   constructors `.forwardE / .backwardE / .bidir`) and the `cons`-cell
--   of `refactor_Walk` — so the binders below are byte-identical to the
--   original `CDMG`-namespace variable line at the top of this file.
--
-- *Three-dash `--- start helper` / `--- end helper`, not two-dash
--   `-- start statement`.*  Lean 4's `variable` auto-binding folds these
--   implicit binders into every refactored declaration below exactly as
--   it does for the originals.  The three-dash flavour tags this as
--   helper-level wrapping, consistent with how the original `variable`
--   line at the top of this file and the `refactor_CDMG` section-wide
--   `variable` at `CollidersAndNon.lean`'s refactor section are tagged.
--   The Phase 7 cleanup script's whole-word rename
--   (`refactor_<Name>` → `<Name>`) leaves the `def_3_16` marker text
--   inside this block untouched (the marker is a documentation comment,
--   not a declaration name).
-- def_3_16 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_16 --- end helper

namespace refactor_Walk

-- ## Design choice — refactor_Walk-namespace statement context
--
-- *Why a namespace-level `variable {G : refactor_CDMG Node}`.*  Both
--   `refactor_IsBlockableNonCollider` and `refactor_IsUnblockableNonCollider`
--   (and their helpers `refactor_HasBlockingLeftSlot` /
--   `refactor_HasBlockingRightSlot`) recurse over / take a walk
--   `p : refactor_Walk G u v` and reach into `G` for `G.refactor_Sc`.
--   Without the namespace-wide `variable`, every signature would carry
--   an explicit `{G : refactor_CDMG Node}` binder; the auto-binding
--   keeps the signatures readable and matches the LN's "Let
--   $G = (J, V, E, L)$ be a CDMG" once-at-the-top quantifier.  Mirrors
--   the original `namespace Walk` opening earlier in this file and the
--   refactor `namespace refactor_Walk` opening at
--   `CollidersAndNon.lean`'s refactor section byte-for-byte modulo the
--   `CDMG → refactor_CDMG` type retarget.  `{G}` is implicit because
--   downstream consumers reach into `G` via dot-notation on the walk
--   (`p.refactor_IsBlockableNonCollider k`).
--
-- *Three-dash helper marker, not two-dash statement marker.*  Same
--   rationale as the original (Walk-namespace block above) and as the
--   refactor section's section-wide `variable` immediately above: this
--   `{G}` binder is load-bearing infrastructure that the tex/Lean
--   reconciliation tooling and the Phase 7 cleanup script must recognise
--   as helper-flavour.
-- def_3_16 --- start helper
variable {G : refactor_CDMG Node}
-- def_3_16 --- end helper

-- ref: def_3_16 (helper, "outgoing E-walk-edge at the (k-1)-slot
-- pointing outside Sc^G(v_k)") — refactor
--
-- `p.refactor_HasBlockingLeftSlot k` iff the slot `i = k - 1` on the
-- walk `p` (i.e. the step that ENDS at outer position `k`) is an
-- *outgoing E-walk-edge of v_k* — a `.backwardE` WalkStep whose stored
-- E-membership witness `(v_k, v_{k-1}) ∈ G.E` makes v_k the tail —
-- AND whose other walk-endpoint v_{k-1} lies *outside* the strongly
-- connected component `G.refactor_Sc v_k`.  Walks the cons chain to
-- the cons-cell where outer position `k` sits at the tail's head, then
-- reads the outer cons-cell's WalkStep — which is exactly the slot
-- `i = k - 1` step `s_{k-1} : refactor_WalkStep G v_{k-1} v_k`.
--
-- ## Design choice — refactor_HasBlockingLeftSlot
--
-- *Why a net-new helper at all (no original counterpart).*  The
--   original `Walk.IsBlockableNonCollider` (ORIGINAL block above)
--   spelled the slot-`(k-1)` "outgoing E-walk-edge of v_k with other
--   endpoint outside Sc^G(v_k)" conjunct via the Option-membership
--   `p.edges[k - 1]? = some (vk, vkm1) ∧ (vk, vkm1) ∈ G.E ∧
--   vkm1 ∉ G.Sc vk`.  Under the typed-WalkStep refactor (a)
--   `p.edges` does NOT exist — the original's `Walk.edges` block has
--   been intentionally dropped under the refactor (see
--   `Walks.lean:1631-1685`'s "Why no `refactor_edges`" block), so any
--   port that goes through `p.edges`-style indexing is non-buildable;
--   and (b) the channel/direction information that the original read
--   off the ordered pair `(vk, vkm1) ∈ G.E` is now carried by the
--   WalkStep's constructor tag (channel: `.forwardE` / `.backwardE` /
--   `.bidir`) and its type indices (source/target endpoints).  Per-slot
--   inspection must therefore go through structural constructor
--   pattern-match on `refactor_Walk`'s cons cells — exactly the
--   recursion pattern used by `refactor_IsCollider`
--   (`CollidersAndNon.lean`'s refactor section) and by
--   `refactor_IsBifurcationWithSplit` / `refactor_IsColliderRest` /
--   `refactor_intoEnd` / `refactor_outOfEnd` in `Walks.lean`.  The
--   helper's "blocking at the left slot of outer position k" framing
--   matches the canonical tex's "Blockable non-collider on π"
--   paragraph's first `∃`-disjunct verbatim, one conjunct per slot,
--   one helper per slot — paired with `refactor_HasBlockingRightSlot`
--   immediately below for the slot-`k` mirror.
--
-- *Constructor-tag-only / no writing-mirror union.*  At the slot-of-
--   interest branch, the helper fires ONLY on the `.backwardE _`
--   constructor and rejects `.forwardE _` / `.bidir _` outright — a
--   different convention than the writing-mirror union used by
--   `refactor_IsInto` in `CollidersAndNon.lean`.  The contrast is
--   load-bearing.  The LN's `\tuh` shorthand (def_3_2 item~2) unfolds
--   STRICTLY to `(v_k, v_{k\pm 1}) ∈ E` — E-channel only, never `L` —
--   so the canonical tex's "outgoing walk-edge of v_k at position k"
--   predicate `a_i ∈ E ∧ e_1 = v_k` (paragraph "Walk-incident indices
--   and outgoing walk-edges at a position") is by construction
--   single-channel.  The slot-`(k-1)` step `s_{k-1} : refactor_WalkStep
--   G v_{k-1} v_k` has v_k as its target index; among the three
--   constructor tags only `.backwardE _` (encoding `(v_k, v_{k-1}) ∈
--   G.E` — i.e. with v_k as the underlying directed edge's TAIL)
--   matches the LN's "outgoing E-walk-edge of v_k".  `.forwardE _`
--   would encode `(v_{k-1}, v_k) ∈ G.E` (v_k as the directed edge's
--   target, i.e. an INCOMING E-walk-edge of v_k — wrong direction for
--   the LN's `\tuh`); `.bidir _` would encode `s(v_{k-1}, v_k) ∈ G.L`
--   (an L-edge, which has arrowheads at BOTH endpoints but is not a
--   directed E-edge from v_k's perspective — also wrong channel for
--   the LN's `\tuh`).  Same convention used by `refactor_outOfStart`
--   (Walks.lean: `.forwardE → True`, `.backwardE → False`,
--   `.bidir → False`) and `refactor_outOfEnd` (Walks.lean:
--   `.backwardE → True`, `.forwardE → False`, `.bidir → False`) — both
--   precedent for "outgoing E-edge" being E-channel-only at the typed-
--   WalkStep level.  Contrast with `refactor_IsInto`
--   (`CollidersAndNon.lean`): there the LN's underlying primitive
--   `def_3_3` item~ii ("edge into a node") is itself a UNION over E and
--   L channels, so the writing-mirror disjunct restores constructor-
--   choice invariance on writing-mirror walks; here the LN's primitive
--   `\tuh` is E-only by definition, so no union semantics is needed
--   (and adding one would diverge from the LN's "outgoing walk-edge"
--   reading by silently broadening the slot-of-interest predicate to
--   include L-channel steps).  The original was ALSO constructor-
--   choice-dependent at writing-mirror walks (the walker's `p.edges`
--   storage choice determined whether the disjunct fired — if the
--   walker stored `a_{k-1} = (v_k, v_{k-1})` to land in E, the
--   original's predicate fired; if the walker stored a different
--   ordered-pair representation, even of the same underlying walk
--   position, the original's predicate did not fire); the refactor
--   preserves that dependence via the constructor-tag reading.  The
--   resolution this helper inherits from `def_3_15`'s canonical-tex
--   "Reconciliation with the source-block pattern writings" paragraph
--   — adopting the walk-edge-based reading as canonical — applies
--   word-for-word to the slot-`(k-1)` outgoing-walk-edge predicate.
--
-- *Wording-check subtleties this helper inherits.*  Three subtleties
--   were registered on this row's solving — `pattern_shorthands_
--   existential_in_g_not_walk_specific`,
--   `self_loop_pattern_overlap_inherited`, and
--   `blockable_clause_says_arrow_not_outgoing_edge`.  This helper's
--   resolution preserves each: (1) by reading slot `i = k - 1` off the
--   walk's specific WalkStep `s_{k-1}` via the cons-cell pattern (not
--   off an existence claim about edges in G) we resolve subtlety~1;
--   (2) the self-loop overlap is resolved via the helper's
--   node-equality-free check on the SC component — see the "Self-loop
--   semantics" bullet below; (3) the "outgoing arrow" reading of the
--   blockable elaboration is encoded by gating on the `.backwardE`
--   constructor (i.e. the WALK's specific edge at slot `i = k - 1`),
--   not by querying for an existence claim about E-membership in G
--   independent of the walk — resolving subtlety~3.
--
-- *Index arithmetic justification.*  The OUTER walk has cons-cells
--   (head-step `s_0` peeled off, then tail walk).  Outer slot `i = k -
--   1` (the step that ENDS at outer position `k`) corresponds to
--   *tail* slot `i = k - 2` (the step that ends at tail position
--   `k - 1`), because the tail walk's position-0 is the outer's
--   position-1.  Hence at outer `k + 2`, the recursive call asks the
--   tail for slot `i = (k + 2) - 2 = k`, i.e. for
--   `tail.refactor_HasBlockingLeftSlot (k + 1)` (which the tail then
--   reads as its own slot `i = (k + 1) - 1 = k`).  The dedicated
--   `(.cons _ _ _, 0)` branch and the `(.cons _ _ _, 1)` branch handle
--   outer positions 0 and 1 at the outer level — see the "1 ≤ k guard
--   collapses into the structural pattern" bullet below for the
--   rationale on those branches.
--
-- *The `1 ≤ k` guard from the original collapses into the structural
--   pattern.*  The original's "slot `i = k - 1` is only admissible
--   when `1 ≤ k`" guard (canonical tex paragraph "Walk-incident
--   indices and outgoing walk-edges at a position") is encoded
--   structurally via the `(.cons _ _ _, 0) → False` branch: at outer
--   position `k = 0` the slot `i = -1` does not exist, so the
--   predicate is `False` by structural pattern.  No explicit `1 ≤ k`
--   conjunct is needed in the predicate body.
--
-- *Out-of-range `k > p.refactor_length`.*  At positions beyond the
--   walk's length, the recursion descends through cons-cells with
--   index decrementing from `k + 2` to `k + 1` and eventually hits
--   `.nil _ _, _` (the trivial-walk base case), which returns
--   `False`.  Out-of-range positions therefore return `False` without
--   an explicit bound check, exactly as the original did via the
--   `p.edges[k - 1]? = none` Option-membership failure.  Additionally,
--   the surrounding `refactor_IsBlockableNonCollider` conjunct
--   `p.refactor_IsNonCollider k` requires `k ≤ p.refactor_length` (see
--   `CollidersAndNon.lean`'s `refactor_IsNonCollider` design block),
--   so the predicate is False on out-of-range positions either way.
--
-- *Why `.bidir _` returns False at the slot-of-interest branches even
--   though L-edges are bidirected.*  An L-edge `s(v_{k-1}, v_k) ∈ G.L`
--   is BIDIRECTED — by def_3_3 item~ii it places arrowheads at BOTH
--   endpoints — so a reader might expect it to count as an "outgoing
--   arrow from v_k" too (since it has an arrowhead at v_{k-1}, on
--   v_k's side an arrowhead is also present).  But the LN's `\tuh`
--   shorthand (def_3_2 item~2) is strictly E-membership; an L-edge
--   does NOT count as an outgoing E-arrow even though it has a
--   tail-side arrowhead.  This is the canonical tex's resolution
--   in its "Reconciliation" paragraph ("Bidirected edges
--   (`a_i ∈ L`) ... are excluded from this predicate") and `def_3_3`'s
--   definition of "out of v_1" (E-only).  Same convention used by
--   `refactor_outOfStart` and `refactor_outOfEnd` (Walks.lean) which
--   also return False on `.bidir _` — both precedent for "outgoing
--   E-edge" being E-channel-only.
--
-- *Self-loop semantics: a self-loop at slot k-1 never makes a
--   non-collider blockable via the left slot.*  A directed self-loop
--   `(v, v) ∈ G.E` at slot `i = k - 1` with `v_{k-1} = v_k = v` is
--   encoded as `s_{k-1} = .backwardE h` (or `.forwardE h`) with
--   `h : (v, v) ∈ G.E` and type `refactor_WalkStep G v v` (source
--   index `u = v`, target index `v_{outer} = v`).  At a position where
--   v_k = v, the slot-(k-1) `.backwardE _ : refactor_WalkStep G v v`
--   branch evaluates `u ∉ G.refactor_Sc v` to `v ∉ G.refactor_Sc v`
--   (since the cons-cell's source index `u` and target index `v` are
--   both bound to the self-loop's vertex `v`).  But `v ∈ G.refactor_Sc
--   v` ALWAYS holds — every vertex is trivially in its own SC
--   component by `def_3_5`'s trivial-walk witness (see
--   `FamilyRelationships.lean`'s `refactor_Anc` / `refactor_Desc` /
--   `refactor_Sc` design blocks for the unconditional self-membership
--   via `refactor_Walk.nil v hv`).  Hence `v ∉ G.refactor_Sc v` is
--   `False`, and the slot-`(k-1)` self-loop case returns `False` —
--   meaning a self-loop at slot `k - 1` never makes a non-collider
--   blockable via the left slot.  Matches the canonical tex's
--   "Treatment of directed self-loops" resolution byte-for-byte: "a
--   self-loop alone never disqualifies an interior position from
--   being unblockable".  No special-casing is needed in the helper
--   itself; the `refactor_Sc` self-membership absorbs the self-loop
--   convention through the SC-component test.  (Mirror behaviour on
--   the right-slot side; see `refactor_HasBlockingRightSlot` below.)
--
-- *Why the cons-cell middle-vertex binder `v` (not a wildcard) at the
--   slot-of-interest branch.*  The body of the slot-`(k-1)` branch
--   needs the cons-cell's target vertex `v` (= v_k of the walk, the
--   slot-(k-1) step's TARGET index) to query `G.refactor_Sc v`.  Pattern
--   position `v` on the `.cons v step tail` is `refactor_Walk.cons`'s
--   first explicit constructor argument — the `(v : Node)` slot of
--   `cons {u w : Node} (v : Node) (s : refactor_WalkStep G u v) (p :
--   refactor_Walk G v w)`.  Binding the cons-cell's middle vertex
--   reads exactly v_k, which is what the original's
--   `p.vertices[k]? = some vk` lookup yielded.  Implicit binders
--   `{u}` are also bound by the pattern (as `u`) because the
--   `.backwardE _ : refactor_WalkStep G u v` carries the target `v`
--   and we need `u` to test against `G.refactor_Sc v` (the binding
--   `u` is the walk's v_{k-1}).
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: HasBlockingLeftSlot (was: refactor_HasBlockingLeftSlot)
-- def_3_16 --- start helper
def refactor_HasBlockingLeftSlot : ∀ {u v : Node}, refactor_Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | _, _, .cons _ _ _, 0 => False
  | u, _, .cons v (.backwardE _) _, 1 => u ∉ G.refactor_Sc v
  | _, _, .cons _ (.forwardE _) _, 1 => False
  | _, _, .cons _ (.bidir _) _, 1 => False
  | _, _, .cons _ _ p, k + 2 => p.refactor_HasBlockingLeftSlot (k + 1)
-- def_3_16 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: HasBlockingLeftSlot

-- ref: def_3_16 (helper, "outgoing E-walk-edge at the k-slot
-- pointing outside Sc^G(v_k)") — refactor
--
-- `p.refactor_HasBlockingRightSlot k` iff the slot `i = k` on the walk
-- `p` (i.e. the step that STARTS at outer position `k`) is an
-- *outgoing E-walk-edge of v_k* — a `.forwardE` WalkStep whose stored
-- E-membership witness `(v_k, v_{k+1}) ∈ G.E` makes v_k the tail —
-- AND whose other walk-endpoint v_{k+1} lies *outside* the strongly
-- connected component `G.refactor_Sc v_k`.  Walks the cons chain to
-- the cons-cell where outer position `k` sits at the head, then reads
-- THAT cons-cell's WalkStep — which is exactly the slot `i = k` step
-- `s_k : refactor_WalkStep G v_k v_{k+1}`.
--
-- ## Design choice — refactor_HasBlockingRightSlot
--
-- *Mirror of `refactor_HasBlockingLeftSlot` on the slot-`k` side.*
--   Same recursion shape, same constructor-tag-only / no-writing-
--   mirror-union convention, same self-loop semantics absorbed via the
--   `refactor_Sc` self-membership.  See the
--   `refactor_HasBlockingLeftSlot` design block above for the full
--   justification of (a) why a net-new helper exists rather than a
--   port that goes through a `p.edges` lookup (the original's `p.edges`
--   has no refactor counterpart — see `Walks.lean:1631-1685`'s "Why no
--   `refactor_edges`" block); (b) the constructor-tag-only convention
--   matching `refactor_outOfStart` / `refactor_outOfEnd`; (c) inheritance
--   of the three LN-critic subtleties
--   (`pattern_shorthands_existential_in_g_not_walk_specific`,
--   `self_loop_pattern_overlap_inherited`,
--   `blockable_clause_says_arrow_not_outgoing_edge`) via the same
--   walk-edge-based reading.  The only semantic difference between
--   this helper and the left-slot one is the choice of constructor:
--   here the slot-of-interest is the HEAD step `s_k`, so the
--   "outgoing E-walk-edge of v_k" condition fires on `.forwardE _`
--   (encoding `(v_k, v_{k+1}) ∈ G.E` with v_k as tail), where the
--   left-slot version fired on `.backwardE _` (encoding `(v_k,
--   v_{k-1}) ∈ G.E` with v_k as tail, but seen from the *target* side
--   of `s_{k-1}`).
--
-- *Why the slot-of-interest binds `.forwardE _` (not `.backwardE _`).*
--   At outer position `k`, the step `s_k : refactor_WalkStep G v_k
--   v_{k+1}` has v_k as its source index and v_{k+1} as its target
--   index.  Among the three constructor tags, only `.forwardE _`
--   (encoding `(v_k, v_{k+1}) ∈ G.E` — i.e. with v_k as the underlying
--   directed edge's TAIL, running v_k → v_{k+1}) matches the LN's
--   "outgoing E-walk-edge of v_k at slot i = k".  `.backwardE _` would
--   encode `(v_{k+1}, v_k) ∈ G.E` (v_k as the directed edge's target,
--   i.e. an INCOMING E-walk-edge of v_k — wrong direction for `\tuh`);
--   `.bidir _` would encode `s(v_k, v_{k+1}) ∈ G.L` (L-channel —
--   wrong channel for `\tuh`).  Same E-only constructor-tag reading
--   as `refactor_outOfStart` (Walks.lean: `.forwardE → True`,
--   `.backwardE → False`, `.bidir → False`).
--
-- *Index arithmetic justification.*  Outer slot `i = k` (the step
--   that STARTS at outer position `k`) corresponds to TAIL slot
--   `i = k - 1` (the step that starts at tail position `k - 1`),
--   because the tail walk's position-0 is the outer's position-1.
--   Hence at outer `k + 1`, the recursive call asks the tail for slot
--   `i = (k + 1) - 1 = k`, i.e. for `tail.refactor_HasBlockingRightSlot
--   k` (which the tail then reads as its own slot `i = k`).  The
--   dedicated `(.cons _ (.forwardE _) _, 0)` / `(.cons _ (.backwardE
--   _) _, 0)` / `(.cons _ (.bidir _) _, 0)` branches handle outer
--   position `k = 0` at the outer level — no recursion needed at the
--   slot-of-interest position because the slot `i = 0` lives at the
--   head cons-cell directly.
--
-- *Out-of-range `k ≥ p.refactor_length`.*  At position `k =
--   p.refactor_length`, the slot `i = k = p.refactor_length` is
--   beyond the walk's edges (the last edge is at slot `i =
--   p.refactor_length - 1`).  The recursion descends through cons-
--   cells with index decrementing from `k + 1` to `k` and eventually
--   reaches `.nil _ _, _` (the trivial-walk base case), which returns
--   `False`.  Out-of-range positions therefore return `False` without
--   an explicit bound check, exactly as the original did via the
--   `p.edges[k]? = none` Option-membership failure.  Additionally,
--   the surrounding `refactor_IsBlockableNonCollider` conjunct
--   `p.refactor_IsNonCollider k` requires `k ≤ p.refactor_length`,
--   so the predicate is False on out-of-range positions either way.
--
-- *Why `.bidir _` returns False at the slot-of-interest branch even
--   though L-edges are bidirected.*  Same rationale as the
--   `refactor_HasBlockingLeftSlot` left-slot block.  An L-edge
--   `s(v_k, v_{k+1}) ∈ G.L` places arrowheads at both endpoints, but
--   the LN's `\tuh` shorthand (def_3_2 item~2) unfolds to E-membership
--   strictly; an L-edge does NOT count as an outgoing E-arrow even
--   though it has a tail-side arrowhead.  Canonical tex
--   "Reconciliation" paragraph: "Bidirected edges (`a_i ∈ L`) ... are
--   excluded from this predicate".  `def_3_3`'s "out of v_1" is also
--   E-only.  Same constructor-tag convention as `refactor_outOfStart`
--   (`.bidir → False`) and `refactor_outOfEnd` (`.bidir → False`).
--
-- *Self-loop semantics: a self-loop at slot k never makes a
--   non-collider blockable via the right slot.*  A directed self-loop
--   `(v, v) ∈ G.E` at slot `i = k` with `v_k = v_{k+1} = v` is encoded
--   as `s_k = .forwardE h` with `h : (v, v) ∈ G.E` and type
--   `refactor_WalkStep G v v` (both source and target indices bound
--   to the self-loop's vertex `v`).  At the slot-`k` branch, the
--   helper's binding pattern `.cons v (.forwardE _) _, 0` binds the
--   cons-cell's middle vertex `v` (the walk's v_{k+1}) and the
--   implicit source `u` (the walk's v_k); both are the loop vertex.
--   The check `v ∉ G.refactor_Sc u` becomes `v ∉ G.refactor_Sc v`,
--   which is `False` (every vertex is trivially in its own SC
--   component — see the analogous bullet on
--   `refactor_HasBlockingLeftSlot`).  Hence the slot-`k` self-loop case
--   returns `False` — meaning a self-loop at slot `k` never makes a
--   non-collider blockable via the right slot.  Matches the canonical
--   tex's "Treatment of directed self-loops" resolution byte-for-byte:
--   "a self-loop alone never disqualifies an interior position from
--   being unblockable".
--
-- *Why the cons-cell binders `v` and the implicit `u` (not wildcards)
--   at the slot-of-interest branch.*  The body of the slot-`k` branch
--   needs the cons-cell's target vertex `v` (= v_{k+1} of the walk,
--   the slot-k step's TARGET index, "the other walk-endpoint of v_k")
--   AND the cons-cell's source vertex `u` (= v_k of the walk, the
--   slot-k step's SOURCE index) to query `G.refactor_Sc u` and test
--   `v ∉ G.refactor_Sc u`.  Pattern positions `u` (implicit) and `v`
--   (explicit) on the `.cons v step tail` bind exactly the walk's v_k
--   and v_{k+1}.  The original's `p.vertices[k]? = some vk ∧
--   p.vertices[k + 1]? = some vkp1` is replaced by these structural
--   pattern bindings — same information, sourced from the cons-cell's
--   type indices instead of from a vertex-list Option lookup.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: HasBlockingRightSlot (was: refactor_HasBlockingRightSlot)
-- def_3_16 --- start helper
def refactor_HasBlockingRightSlot : ∀ {u v : Node}, refactor_Walk G u v → ℕ → Prop
  | _, _, .nil _ _, _ => False
  | u, _, .cons v (.forwardE _) _, 0 => v ∉ G.refactor_Sc u
  | _, _, .cons _ (.backwardE _) _, 0 => False
  | _, _, .cons _ (.bidir _) _, 0 => False
  | _, _, .cons _ _ p, k + 1 => p.refactor_HasBlockingRightSlot k
-- def_3_16 --- end helper
-- REFACTOR-BLOCK-REPLACEMENT-END: HasBlockingRightSlot

-- ref: def_3_16 (paragraph "Blockable non-collider on π") — refactor
--
-- `p.refactor_IsBlockableNonCollider k` iff position `k` on the walk
-- `p` is a non-collider on `p` (per `def_3_15`) AND it is either at
-- an end-position (`k = 0` or `k = p.refactor_length`) or there is
-- some outgoing walk-edge of v_k on π whose other walk-endpoint along
-- π lies outside `G.refactor_Sc v_k`.  Mechanically retargets the
-- original `Walk.IsBlockableNonCollider` (ORIGINAL block above)
-- against the typed-WalkStep / Sym2 refactor: the slot-(k-1) and
-- slot-k existential conjuncts of the original become the helpers
-- `refactor_HasBlockingLeftSlot` and `refactor_HasBlockingRightSlot`
-- (defined above), one for each slot of interest.  Encodes the LN's
-- "blockable disjunction" elaboration (canonical tex's spelled-out
-- disjunction form) one-for-one as a clean four-disjunct mirror.
--
-- ## Design choice — refactor_IsBlockableNonCollider
--
-- *Why no internal recursion at this level.*  The recursion lives
--   inside the two helpers (`refactor_HasBlockingLeftSlot` /
--   `refactor_HasBlockingRightSlot`), each of which descends the
--   cons-chain to the slot of interest and queries the WalkStep
--   constructor.  At this level the def is a flat four-disjunct
--   mirroring the canonical tex's "Blockable non-collider on π"
--   paragraph word-for-word: `k = 0` / `k = p.refactor_length` /
--   `HasBlockingLeftSlot k` / `HasBlockingRightSlot k`.  This is a
--   different shape from the original
--   `Walk.IsBlockableNonCollider` (which embedded the Option-
--   membership lookups inline at the same level as the end-position
--   disjuncts), but the LN-correspondence is unchanged: the four
--   disjuncts of this def are exactly the four disjuncts of the
--   canonical tex's spelled-out blockable disjunction.
--
-- *Mirror four-disjunct shape preserved from the canonical tex.*
--   The canonical tex spells the blockable disjunction as `k ∈
--   {0, n} ∨ (a_{k-1} = (v_k, v_{k-1}) ∈ E ∧ v_{k-1} ∉ Sc^G(v_k)) ∨
--   (a_k = (v_k, v_{k+1}) ∈ E ∧ v_{k+1} ∉ Sc^G(v_k))`, with the
--   trailing parenthetical "(the latter two disjuncts implicitly
--   requiring k ≥ 1 resp. k ≤ n − 1, and being vacuously false outside
--   that range)".  We mirror this verbatim: end-position disjuncts
--   `k = 0` / `k = p.refactor_length` are spelled separately
--   (following the canonical tex's `k ∈ {0, n}` split), and the
--   slot-`(k-1)` / slot-`k` predicates are encapsulated into the
--   helpers above (each of which is structurally `False` at the
--   out-of-range positions, mirroring the canonical tex's
--   parenthetical).
--
-- *Mutual exclusivity with `refactor_IsUnblockableNonCollider` is
--   definitional on the non-collider sub-class.*  See the
--   `refactor_IsUnblockableNonCollider` design block immediately
--   below for the full discussion; in short,
--   `refactor_IsUnblockableNonCollider p k := p.refactor_IsNonCollider
--   k ∧ ¬ p.refactor_IsBlockableNonCollider k`, so for any `k`
--   satisfying `p.refactor_IsNonCollider k` exactly one of the two
--   holds, by unfolding.  Mirrors the original's
--   `IsBlockableNonCollider` / `IsUnblockableNonCollider` asymmetry.
--
-- *End-position disjuncts `k = 0` / `k = p.refactor_length` are
--   spelled separately.*  Mirrors the canonical tex's "(latter two
--   disjuncts implicitly requiring k ≥ 1 resp. k ≤ n − 1, and being
--   vacuously false outside that range)" reading — the LN puts end-
--   positions in the blockable class explicitly (canonical tex's
--   "Reconciliation" item "end-position": "the source-block
--   elaboration assigns end-positions to the blockable category via
--   the `k ∈ {0, n}` disjunct").  At both end-positions
--   `refactor_IsBlockableNonCollider` reduces to `IsNonCollider ∧
--   True = IsNonCollider`, and `refactor_IsNonCollider` is `True` at
--   both end-positions (`refactor_IsCollider` is `False` at `k = 0`
--   via the `(.cons _ _ _, 0) → False` branch and at `k =
--   p.refactor_length` via the recursion bottoming out at a `.nil` or
--   `.cons _ _ (.nil _ _)` tail — see `CollidersAndNon.lean`'s
--   `refactor_IsCollider` design block).
--
-- *The `refactor_IsNonCollider k` conjunct is load-bearing, not
--   cosmetic.*  Without it the predicate would over-fire on collider
--   positions: an interior collider `k` might happen to admit a
--   `.forwardE _` step at slot `i = k` (encoding some `(v_k, v_{k+1})
--   ∈ G.E`) with `v_{k+1} ∉ G.refactor_Sc v_k`, and would then be
--   mis-classified as blockable.  The LN restricts "blockable" to the
--   non-collider sub-class — they are a classification *of non-
--   colliders*, not of all walk positions — and the
--   `refactor_IsNonCollider k` conjunct is the predicate-level
--   encoding of that restriction.  Same rationale as the original
--   (ORIGINAL block above's design notes).
--
-- *No `Decidable` instance, `Prop`-only.*  Same chapter convention as
--   the original.  Matches `refactor_IsCollider` /
--   `refactor_IsNonCollider` (`CollidersAndNon.lean`'s refactor
--   section), the typed-WalkStep walk-class predicates in
--   `Walks.lean`'s refactor section, and the original's `Prop`-only
--   shape.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsBlockableNonCollider (was: refactor_IsBlockableNonCollider)
-- def_3_16 -- start statement
def refactor_IsBlockableNonCollider {u v : Node} (p : refactor_Walk G u v) (k : ℕ) : Prop :=
  p.refactor_IsNonCollider k ∧
  ( k = 0 ∨ k = p.refactor_length ∨
    p.refactor_HasBlockingLeftSlot k ∨
    p.refactor_HasBlockingRightSlot k )
-- def_3_16 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsBlockableNonCollider

-- ref: def_3_16 (paragraph "Unblockable non-collider on π") — refactor
--
-- `p.refactor_IsUnblockableNonCollider k` iff position `k` on the walk
-- `p` is a non-collider on `p` (per `def_3_15`) AND it is NOT a
-- blockable non-collider on `p`.  Unfolding the negation of
-- `refactor_IsBlockableNonCollider`'s disjunction recovers the LN's
-- two-implication unblockable characterisation: `k` is interior
-- (`k ≠ 0 ∧ k ≠ p.refactor_length`) and every outgoing walk-edge of
-- v_k on π lands in `G.refactor_Sc v_k`.  Body identical to the
-- original `Walk.IsUnblockableNonCollider` (ORIGINAL block above)
-- modulo the mechanical retargets `IsNonCollider →
-- refactor_IsNonCollider`, `IsBlockableNonCollider →
-- refactor_IsBlockableNonCollider`.
--
-- ## Design choice — refactor_IsUnblockableNonCollider
--
-- *Asymmetric encoding: negation of blockable + non-collider
--   conjunct.*  Mirrors the original `IsUnblockableNonCollider`
--   design (ORIGINAL block above's design notes): the LN's
--   "unblockable" classifier is the *non-blockable* sub-class of
--   non-collider positions; the canonical tex's "Unblockable non-
--   collider on π" paragraph spells out exactly this characterisation
--   ("k is a non-collider on π ... and k is not an unblockable non-
--   collider on π"... [sic, the canonical tex's wording — read as
--   "blockable iff non-collider AND not unblockable" / "unblockable
--   iff non-collider AND not blockable", definitionally interlocked]).
--   Encoding the conjunction directly makes the LN's mutual
--   exclusivity ("every non-collider position is exactly one of
--   unblockable or blockable") definitional: for any `k` satisfying
--   `p.refactor_IsNonCollider k`, exactly one of
--   `refactor_IsBlockableNonCollider k` and
--   `refactor_IsUnblockableNonCollider k` holds, by unfolding.  Both
--   predicates are definitionally interlocked on the
--   `refactor_IsNonCollider` sub-class.
--
-- *Why the original's "primary positive disjunction" rationale
--   carries through unchanged.*  The original (ORIGINAL block above)
--   adopted the LN's "blockable" elaboration as the PRIMARY positive
--   disjunction and `IsUnblockableNonCollider` as the derived
--   predicate via negation, with the rationale that downstream walk-
--   reversal proofs (claim_3_22 onward) reduce to preservation of the
--   positive predicate.  The refactor preserves this design pillar
--   verbatim: `refactor_IsBlockableNonCollider` is still the primary
--   positive disjunction (four disjuncts: two end-position +
--   `HasBlockingLeftSlot` + `HasBlockingRightSlot`), and
--   `refactor_IsUnblockableNonCollider` is still the derived
--   predicate via negation.  Only the helper-level surface retargets
--   (the original's Option-membership lookups become the
--   `HasBlocking*Slot` recursive helpers); the asymmetric encoding
--   and its downstream consequences are unchanged.
--
-- *Mutual exclusivity on the non-collider sub-class is definitional.*
--   `refactor_IsUnblockableNonCollider p k` literally unfolds to
--   `p.refactor_IsNonCollider k ∧ ¬ p.refactor_IsBlockableNonCollider
--   k`, so for any `k` satisfying `p.refactor_IsNonCollider k` the
--   statement `p.refactor_IsUnblockableNonCollider k ↔
--   ¬ p.refactor_IsBlockableNonCollider k` reduces by definitional
--   unfolding alone — no external theorem needed.  The original's
--   symmetry property (ORIGINAL block above's design notes) is
--   preserved verbatim through the mechanical retarget.
--
-- *The `refactor_IsNonCollider k` conjunct is load-bearing (same
--   rationale as on `refactor_IsBlockableNonCollider`).*  Without it
--   the predicate would over-fire on collider positions: any
--   collider `k` automatically satisfies `¬
--   refactor_IsBlockableNonCollider k` (because
--   `refactor_IsBlockableNonCollider` carries
--   `refactor_IsNonCollider` as its first conjunct, so colliders fail
--   it), so dropping the `refactor_IsNonCollider` conjunct here would
--   mis-classify every collider as unblockable.  The LN restricts
--   both "unblockable" and "blockable" to the non-collider sub-class
--   — they are mutually exclusive classifications *of non-colliders*,
--   not of all walk positions — and the `refactor_IsNonCollider k`
--   conjunct is the predicate-level encoding of that restriction.
--
-- *Why the LN's intended meaning survives the negation.*  By
--   unfolding `refactor_IsBlockableNonCollider`, the negation
--   distributes over the four-disjunct disjunction and gives: `k ≠ 0
--   ∧ k ≠ p.refactor_length` (negation of the end-position disjuncts
--   — the LN's "interior" clause (ii)) ∧ `¬ HasBlockingLeftSlot k` ∧
--   `¬ HasBlockingRightSlot k` ∧ `refactor_IsNonCollider k` (positive
--   conjunct preserved by the conjunction here).  Negating each
--   helper gives a universal implication on the corresponding slot:
--   `¬ HasBlockingLeftSlot k` says "if slot `i = k - 1` is a
--   `.backwardE _` (encoding `(v_k, v_{k-1}) ∈ G.E`), then `v_{k-1}
--   ∈ G.refactor_Sc v_k`"; similarly for `¬ HasBlockingRightSlot k`
--   on slot `i = k`.  Together these recover the exact two
--   implications of LN clause (iii) of the unblockable definition.
--   So derivedness preserves the LN's unblockable characterisation
--   case-by-case.
--
-- *Dot-notation `p.refactor_IsBlockableNonCollider k`.*
--   `refactor_IsBlockableNonCollider` is declared in the same
--   `namespace refactor_Walk` and takes `p : refactor_Walk G u v` as
--   its first explicit positional argument, so the dot-notation
--   resolves to `refactor_Walk.refactor_IsBlockableNonCollider p k`
--   — same idiom used by `p.refactor_IsNonCollider k`,
--   `p.refactor_IsCollider k`.
--
-- *No `Decidable` instance, `Prop`-only.*  Same rationale as
--   `refactor_IsBlockableNonCollider` above and the original
--   `IsUnblockableNonCollider`.
-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsUnblockableNonCollider (was: refactor_IsUnblockableNonCollider)
-- def_3_16 -- start statement
def refactor_IsUnblockableNonCollider {u v : Node} (p : refactor_Walk G u v) (k : ℕ) : Prop :=
  p.refactor_IsNonCollider k ∧ ¬ p.refactor_IsBlockableNonCollider k
-- def_3_16 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsUnblockableNonCollider

end refactor_Walk

end refactor_CDMG

end Causality
