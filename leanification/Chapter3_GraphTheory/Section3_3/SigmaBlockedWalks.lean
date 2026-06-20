import Chapter3_GraphTheory.Section3_1.CDMG
import Chapter3_GraphTheory.Section3_1.CDMGNotation
import Chapter3_GraphTheory.Section3_1.EdgeRelations
import Chapter3_GraphTheory.Section3_1.Walks
import Chapter3_GraphTheory.Section3_1.FamilyRelationships
import Chapter3_GraphTheory.Section3_3.CollidersAndNon
import Chapter3_GraphTheory.Section3_3.BlockableAndUnblockable

namespace Causality

/-!
# σ-blocked and σ-open walks (`def_3_17`)

This file formalises `def_3_17` (`\label{def:sigma_blocking}`), the
third definition of Section 3.3 of the lecture notes.  Given a CDMG
`G = (J, V, E, L)`, a subset of nodes `C ⊆ J ∪ V`, and a walk
`π = (v_0, a_0, v_1, …, a_{n-1}, v_n)` in `G`, the walk `π` is
classified as either `C-σ-open` or `C-σ-blocked`:

* `Walk.IsSigmaOpenGiven p C` — every collider position `k` on `p` has
  `v_k ∈ Anc^G(C)`, AND every blockable non-collider position `k` on
  `p` has `v_k ∉ C`.
* `Walk.IsSigmaBlockedGiven p C` — there exists a collider position
  `k` on `p` with `v_k ∉ Anc^G(C)`, OR there exists a blockable
  non-collider position `k` on `p` with `v_k ∈ C`.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_3/tex/def_3_17_SigmaBlockedWalks.tex`,
verified equivalent to the LN block (`graphs.tex`,
`\label{def:sigma_blocking}`) augmented with one operator
clarification:

* `[claim_type_mismatch_vertex_vs_walk]` — the trailing LN remark
  ("unblockable non-colliders are always `C-σ-open`") is informal
  commentary, not part of the definition proper.  It applies the
  walk-level predicate `C-σ-open` to *vertices* (specifically to
  unblockable non-collider occurrences on a walk), which is a type
  mismatch with the just-stated definition (which only classifies
  *walks* as σ-open or σ-blocked).  No Lean obligation is derived
  from it here; any walk-level reformulation of its underlying
  content is handled separately as the dedicated claim row
  `claim_3_21`.

## Design pillars

1. **Walk-level `Prop` predicates `(p : Walk G u v) (C : Set Node)`.**
   The LN classifies *walks* as σ-open / σ-blocked relative to a
   conditioning set; matching that shape directly via
   `Walk.IsSigmaOpenGiven` / `Walk.IsSigmaBlockedGiven` reads as the
   LN does, and dot-notation `p.IsSigmaOpenGiven C` mirrors the LN's
   "π is C-σ-open" prose.  No vertex-level σ-open predicate is
   introduced — the addition `[claim_type_mismatch_vertex_vs_walk]`
   explicitly excludes that direction from this row's formalisation.

2. **Per-position quantification via the existing `IsCollider` and
   `IsBlockableNonCollider` predicates.**  Collider and blockable
   non-collider positions are *already* classified by `def_3_15`
   (`CollidersAndNon.lean`) and `def_3_16`
   (`BlockableAndUnblockable.lean`); reusing those predicates verbatim
   keeps the LN's "for every collider on π" / "for every blockable
   non-collider on π" scope visible at the type level rather than
   re-spelling the arrowhead-count / outgoing-walk-edge case-splits.

3. **`G.AncSet` reused from `FamilyRelationships.lean` (`def_3_5`,
   item iv set form).**  The LN's `Anc^G(C)` for `C ⊆ J ∪ V` is the
   indexed-union ancestor set `⋃_{c ∈ C} Anc^G(c)`, which
   `CDMG.AncSet : CDMG Node → Set Node → Set Node` already encodes.
   Out-of-graph `c ∈ C` contribute `G.Anc c = ∅` (via the `w ∈ G`
   guard inside `Anc`), so no `C ⊆ J ∪ V` hypothesis is needed at
   the def site.

4. **Vertex lookup via `p.vertices[k]? = some vk`, mirroring the
   `IsCollider` / `IsUnblockableNonCollider` idiom.**  The LN writes
   `v_k` for the vertex at position `k` on the walk; in Lean this
   reads off `p.vertices` as an `Option Node` lookup.  Pinning down
   `vk` with a `p.vertices[k]? = some vk` hypothesis lets the
   membership claim `vk ∈ G.AncSet C` (resp. `vk ∈ C`) be stated
   directly on the witness.  Out-of-range `k > p.length` make the
   lookup `none`, so the universal antecedents in `IsSigmaOpenGiven`
   become vacuous and the existential witnesses in
   `IsSigmaBlockedGiven` cannot be formed — matching the LN's
   scoping to `{0, …, n}` without an explicit upper-bound hypothesis.

5. **Unblockable non-colliders are silently outside both
   quantifications.**  Clause (i) ranges over collider positions;
   clause (ii) ranges over *blockable* non-collider positions.
   Unblockable non-collider positions are therefore not constrained
   by either clause — they are "vacuously open" in the walk-level
   sense.  The addition `[claim_type_mismatch_vertex_vs_walk]`
   excludes any per-vertex extension of "σ-open" to unblockable
   positions from this row's formalisation; the closest walk-level
   reformulation of the trailing LN remark lives in `claim_3_21`.

6. **Positive existential disjunction for `IsSigmaBlockedGiven`, NOT
   `¬ IsSigmaOpenGiven`.**  The rewritten canonical tex notes that
   the two classifiers are De Morgan duals and "by construction
   mutually exclusive and jointly exhaustive over walks in `G`".  We
   nonetheless encode `IsSigmaBlockedGiven` *directly* in the
   positive existential form: (a) it mirrors the LN's literal
   `∃ … \notin Anc^G(C) ∨ ∃ … \in C` writing; (b) downstream proofs
   that construct a blocking witness can directly form the
   `Or.inl ⟨k, vk, …⟩` / `Or.inr ⟨k, vk, …⟩` term; (c) the
   equivalence `¬ p.IsSigmaOpenGiven C ↔ p.IsSigmaBlockedGiven C` is
   a standalone (classical) De Morgan lemma to be proved when a
   downstream row needs it — not a definitional reduction the
   def-shape forces.  Encoding `IsSigmaBlockedGiven` as
   `¬ IsSigmaOpenGiven` was considered: it would make the negation
   definitional but would force downstream witness-construction
   proofs to wade through a double-negation push, inverting the
   readability win.
-/

end Causality

namespace Causality

namespace CDMG

-- ## Design choice — refactor section-wide statement context
--
-- *Polymorphic `Node : Type*` with `[DecidableEq Node]`.*  Same chapter
--   convention used by the original `CDMG` namespace above and by every
--   other `CDMG`-opening file in the chapter
--   (`BlockableAndUnblockable.lean:402-404`,
--   `CollidersAndNon.lean:320-322`, `Walks.lean:1201-1203`,
--   `CDMG.lean`, `CDMGNotation.lean`, `EdgeRelations.lean`,
--   `FamilyRelationships.lean`).  The refactor does not alter the
--   carrier-type discipline — only (a) `def_3_1`'s `L`-field shape
--   (`Finset (Sym2 Node)` with `hL_irrefl : ∀ ⦃s⦄, s ∈ L → ¬ s.IsDiag`)
--   and (b) `def_3_4`'s per-step walk-edge data (typed
--   `WalkStep` with three constructors
--   `.forwardE / .backwardE / .bidir`) and the `cons`-cell of
--   `Walk` — so the binders below are byte-identical to the
--   original `CDMG`-namespace variable line at the top of this file.
--
-- *Three-dash `--- start helper` / `--- end helper`, not two-dash
--   `-- start statement`.*  Lean 4's `variable` auto-binding folds these
--   implicit binders into every refactored declaration below exactly as
--   it does for the originals.  Matches the helper-flavour tagging used
--   by every prior refactor section in this chapter.
-- def_3_17 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- def_3_17 --- end helper

namespace Walk

-- ## Design choice — Walk-namespace statement context
--
-- *Why a namespace-level `variable {G : CDMG Node}`.*  Both
--   `IsSigmaOpenGiven` and `IsSigmaBlockedGiven` take
--   a walk `p : Walk G u v` and reach into `G` for
--   `G.AncSet`.  Without the namespace-wide `variable`, every
--   signature would carry an explicit `{G : CDMG Node}` binder;
--   the auto-binding keeps the signatures readable and matches the LN's
--   once-at-the-top "Let $G = (J, V, E, L)$ be a CDMG" quantifier.
--   Mirrors the original `namespace Walk` opening earlier in this file
--   and the refactor `namespace Walk` opening at
--   `BlockableAndUnblockable.lean:406-434` and
--   `CollidersAndNon.lean:557-583` byte-for-byte modulo the
--   `CDMG → CDMG` type retarget.  `{G}` is implicit because
--   downstream consumers reach into `G` via dot-notation on the walk
--   (`p.IsSigmaOpenGiven C`).
-- def_3_17 --- start helper
variable {G : CDMG Node}
-- def_3_17 --- end helper

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsSigmaOpenGiven
-- ref: def_3_17 (paragraph "C-σ-open walk") — refactor
--
-- `p.IsSigmaOpenGiven C` iff the walk `p` is `C-σ-open` in
-- the LN's sense, expressed against the typed-WalkStep refactor:
--   (i)   for every position `k` on `p` and every vertex `vk` with
--         `p.vertices[k]? = some vk`, if
--         `p.IsCollider k` then `vk ∈ G.AncSet C`;
--   (ii)  for every position `k` on `p` and every vertex `vk` with
--         `p.vertices[k]? = some vk`, if
--         `p.IsBlockableNonCollider k` then `vk ∉ C`.
--
-- Body identical to the original `Walk.IsSigmaOpenGiven` (ORIGINAL
-- block above) modulo mechanical upstream retargets:
-- - `Walk G u v` → `Walk G u v` (typed-WalkStep walk);
-- - `p.vertices` → `p.vertices`
--   (`Walks.lean:1688`);
-- - `p.IsCollider` → `p.IsCollider`
--   (`CollidersAndNon.lean:839`);
-- - `p.IsBlockableNonCollider` → `p.IsBlockableNonCollider`
--   (`BlockableAndUnblockable.lean:865`);
-- - `G.AncSet` → `G.AncSet`
--   (`FamilyRelationships.lean:810`).
-- The two-clause structure, the per-position universal quantification
-- via `p.vertices[k]? = some vk`, the asymmetric treatment of
-- blockable vs unblockable non-colliders (clause (ii) ranges over
-- blockable ONLY), and the `AncSet` quantification are all
-- preserved verbatim — only the names change.
--
-- ## Design choice — IsSigmaOpenGiven
--
-- *Why the refactor needs to touch this predicate.*  Mechanically only,
--   not semantically.  The body references five upstream symbols that
--   have all themselves been refactored (typed `Walk`,
--   `vertices`, `IsCollider`,
--   `IsBlockableNonCollider`, `AncSet`), so the def
--   needs to be re-stated using the refactored upstreams.  The
--   `Prop`-level conjunction of two universals, the
--   `p.vertices[k]? = some vk` Option-membership lookup
--   convention, the LN-correspondence to the canonical tex's "for every
--   collider on π" / "for every blockable non-collider on π" scope —
--   all unchanged.  The original's design pillars (ORIGINAL block above)
--   carry through verbatim; the heavy design rationale lives in the
--   ORIGINAL block's comment.
--
-- *What the typed-WalkStep + `Sym2 Node` upstream refactor buys σ-open
--   classification.*  The refactor's load-bearing payoff at *this*
--   level is constructor-choice invariance on writing-mirror walks.
--   Under the original ordered-pair encoding, the walker chose per
--   step an `a : Node × Node` representation; on a writing-mirror
--   step (a vertex pair `{v, w}` that simultaneously sits in `G.E`
--   and `G.L`, admitted by `def_3_1`'s
--   `[edge_set_disjointness_under_specified]` addition — channels are
--   type-disjoint carriers but not graph-theoretically exclusive at
--   the vertex-pair level) the same underlying walk position could be
--   stored as either an E-step or an L-step, and the original
--   `IsCollider` / `IsBlockableNonCollider` read the channel off the
--   stored pair via `G.into` / `G.outOf` union-membership.  The per-
--   position classification was therefore sensitive to the walker's
--   storage choice, which pulled through to σ-open classification
--   *here* — the same LN walk could fall on different sides of clauses
--   (i) / (ii) depending on writing-mirror typification.  Under the
--   refactor the channel is carried by the WalkStep constructor tag
--   and writing-mirror coincidence is resolved via node-equality on
--   the type indices (see `CollidersAndNon.lean`'s `IsInto`
--   design block and `BlockableAndUnblockable.lean`'s slot-helper
--   design blocks).  Consequence at *this* level:
--   `IsSigmaOpenGiven` inherits constructor-choice invariance
--   along the forgetful map `Walk G u v → LN walk in G` "for
--   free", purely from the upstream encoding change — no new code in
--   *this* file performs the writing-mirror fix; the upstream
--   predicates `IsCollider` and
--   `IsBlockableNonCollider` do, and σ-open just quantifies
--   over them.
--
-- *Walk-reversal channel preservation inherited from `L : Finset
--   (Sym2 Node)`.*  Under the refactor, a `.bidir` step stores an
--   L-membership witness `s(u, v) ∈ G.L` whose carrier is the
--   quotient `Sym2 Node = (Node × Node) / swap` rather than an ordered
--   pair plus a `hL_symm` symmetry implication (see `def_3_1`'s
--   refactor design block, "Walk reversal preserves channel" bullet).
--   Walk reversal therefore preserves the `.bidir` channel by
--   *definitional* swap-equality `s(u, v) = s(v, u)`; no orientation
--   swap on the stored witness is needed, and a position that was
--   classified collider / blockable non-collider pre-reversal
--   classifies identically post-reversal.  Under the ordered-pair-
--   plus-symmetry alternative on writing-mirror CDMGs, reversing an
--   L-step storing `(u, v)` could land the swapped `(v, u)` in `G.E`
--   coincidentally and silently reclassify the reversed step's
--   contribution to σ-open.  Consequence for *this* file:
--   `IsSigmaOpenGiven` is reversal-symmetric on
--   `Walk` by *upstream* construction — no σ-open-level code
--   spells out reversal — which is the structural precondition for
--   the eventual σ-separation-symmetry result (the *driving*
--   downstream consumer of this refactor's encoding choice per
--   `leanification/refactors/refactor_cdmg_typed_edges.md` and
--   `def_3_1`'s refactor design block).
--
-- *Downstream consumers of this REPLACEMENT.*  The immediate
--   refactor-table consumer is `def_3_18` (`ISigmaSeparation`), which
--   lifts `IsSigmaBlockedGiven` to a `σ`-separation relation
--   on disjoint subsets of `J ∪ V` and inherits σ-open's two-clause
--   shape via its negated existential.  Future downstream consumers
--   that this REPLACEMENT's shape is chosen to support (not in the
--   current refactor table but flagged in `def_3_1`'s refactor design
--   block as the *driving* motivation): the LN's future `claim_3_21`
--   (the trailing-remark reformulation about unblockable non-colliders
--   being σ-open, excluded from *this* row per
--   `[claim_type_mismatch_vertex_vs_walk]` and deferred to its own
--   claim row), and `claim_3_22` (σ-separation symmetry).  The
--   constructor-choice invariance and walk-reversal channel-
--   preservation properties inherited from the upstream encoding are
--   precisely the structural ingredients that the σ-symmetry
--   downstream consumer pattern-matches on.
--
-- *Why NOT re-thinking the σ-open def shape under the refactor.*  The
--   typed-WalkStep encoding change is orthogonal to
--   `IsSigmaOpenGiven`'s `Prop`-level shape (conjunction of two
--   universals indexed by walk position, ranging over collider and
--   blockable non-collider positions respectively).  The encoding
--   change *strengthens* the per-position predicates this def ranges
--   over — they are now constructor-choice invariant and reversal-
--   friendly — but does not motivate a re-design at the walk-level
--   σ-open layer.  Re-designing σ-open here (e.g. by structural
--   recursion on `Walk`'s `cons` cells, mirroring
--   `IsCollider`'s pattern-match shape) was rejected: (a)
--   the LN's two-universal shape is already the right reading for
--   both proof-direction discharges and downstream witness extraction;
--   (b) a recursive `cons`-pattern encoding would force σ-open into
--   `Bool` decidability shape, losing the `Prop`-level conjunction
--   structure that the De Morgan duality with
--   `IsSigmaBlockedGiven` is stated against; (c) the
--   mechanical port preserves the LN-grep one-to-one correspondence
--   at the def site, matching the priority shared with the original
--   (ORIGINAL block above).
--
-- *Asymmetric quantification preserved: clause (ii) ranges over
--   blockable non-colliders ONLY.*  The original (ORIGINAL block above)
--   pins this asymmetry as a load-bearing design pillar (per the
--   addition `[claim_type_mismatch_vertex_vs_walk]`'s exclusion of any
--   per-vertex extension of σ-open to unblockable positions).  Both
--   upstream predicates `IsCollider` and
--   `IsBlockableNonCollider` preserve the same shape as their
--   originals (per their respective design blocks at
--   `CollidersAndNon.lean` and `BlockableAndUnblockable.lean`), so the
--   asymmetry survives the port verbatim.  Encoding clause (ii) as
--   `p.IsNonCollider k → vk ∉ C` would over-fire on unblockable
--   non-collider positions — the same critique as the original.
--
-- *`G.AncSet C` reused from `FamilyRelationships.lean` (line
--   810).*  Same role as the original's `G.AncSet C`: encodes the LN's
--   `Anc^G(C)` for `C ⊆ J ∪ V` as the indexed-union
--   `⋃_{c ∈ C} G.Anc c`.  Out-of-graph `c ∈ C` contribute
--   `G.Anc c = ∅` (the `w ∈ G` guard inside `Anc`
--   inherits the original's empty-on-out-of-graph behaviour through the
--   mechanical retarget) — but this guarantees only *value*-invariance
--   of the predicate on `C ↦ C ∩ (G.J ∪ G.V)`, not LN-faithfulness of
--   the *signature*; see the `hC` rationale below.
--
-- *Explicit `hC : C ⊆ ↑G.J ∪ ↑G.V` on the signature, with
--   `set_option linter.unusedVariables false in`.*  The LN's
--   `def:sigma_blocking` opens with the typing premise "Let $G = (J, V,
--   E, L)$ be a CDMG and $C \ins J \cup V$ a subset of nodes".  The
--   original (pre-refactor) `IsSigmaOpenGiven` *dropped* this premise and
--   took a bare `C : Set Node`; the strict-equivalence checker flagged
--   that as a CONTENT deviation (the predicate is then declared on a
--   strictly larger class of inputs than the LN gives meaning to —
--   e.g. `C = {x}` for `x ∉ G.J ∪ G.V` parses fine but has no LN
--   referent).  The value-invariance argument above documents that the
--   *predicate value* coincides with the LN's on `C ∩ (G.J ∪ G.V)`, but
--   it does not undo the *signature*-level looseness.  The refactor
--   takes the fix: add the explicit subset hypothesis (load-bearing on
--   the signature, inert in the body — out-of-graph nodes contribute
--   vacuously through the value-invariance just discussed), matching
--   the chapter-wide convention already used by `def_3_18`'s
--   `IsISigmaSeparated` (`ISigmaSeparation.lean:300–305`) and (per its
--   own design block) by `HardInterventionOn`, `NodeSplittingOn`,
--   `NodeSplittingHard`, `AddingInterventionNodes`, and
--   `MarginalizationAndIntervention`.  The `set_option
--   linter.unusedVariables false in` prefix suppresses the unused-binder
--   warning that the chapter convention triggers on every LN-faithful-
--   but-body-inert binder.  Downstream consumer `def_3_18` already has
--   `hC : C ⊆ ↑G.J ∪ ↑G.V` in scope (it threads the same hypothesis on
--   its own signature) and passes it through to `π.refactor_IsSigma…`,
--   so the tightening is propagation-free.
--
-- *Dot-notation `p.IsCollider k` / `p.IsBlockableNonCollider k`.*
--   Both predicates are declared in the `namespace Walk` and
--   take `p : Walk G u v` as their first explicit positional
--   argument, so the dot-notation resolves correctly under the
--   `CDMG.Walk` namespace.  Same idiom used by
--   `IsUnblockableNonCollider` in `BlockableAndUnblockable.lean`.
--
-- *Two-clause conjunction shape preserved.*  Mirrors the LN's bullet-
--   list writing and matches the original's `⟨h_collider, h_blockable⟩`
--   destructure-friendly shape.  A single universal over a sum-typed
--   predicate would also be admissible but would break the one-to-one
--   LN-grep correspondence — same rationale as the original.
set_option linter.unusedVariables false in
-- def_3_17 -- start statement
def IsSigmaOpenGiven {u v : Node} (p : Walk G u v) (C : Set Node)
    (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  (∀ (k : ℕ) (vk : Node), p.vertices[k]? = some vk → p.IsCollider k →
      vk ∈ G.AncSet C) ∧
  (∀ (k : ℕ) (vk : Node), p.vertices[k]? = some vk →
      p.IsBlockableNonCollider k → vk ∉ C)
-- def_3_17 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsSigmaOpenGiven

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsSigmaOpenGiven (was: refactor_IsSigmaOpenGiven)
-- ref: def_3_17 (paragraph "C-σ-open walk") — side-aware refactor
--   (`collider_side_aware`).
--
-- `p.refactor_IsSigmaOpenGiven C hC` iff the walk `p` is `C-σ-open`
-- in the LN's sense, under the *side-aware* per-step arrowhead-
-- contribution reading committed to by the upstream refactor.  Body
-- identical to the original `IsSigmaOpenGiven` (ORIGINAL block above)
-- modulo two mechanical upstream retargets:
-- - `p.IsCollider k` → `p.refactor_IsCollider k`
--   (`CollidersAndNon.lean`, REPLACEMENT block);
-- - `p.IsBlockableNonCollider k` → `p.refactor_IsBlockableNonCollider k`
--   (`BlockableAndUnblockable.lean`, REPLACEMENT block).
-- The two-clause conjunction, the per-position universal via
-- `p.vertices[k]? = some vk`, the asymmetric blockable-only
-- quantification on clause (ii), the `hC` LN-faithful subset
-- hypothesis, and the `set_option linter.unusedVariables false in`
-- prefix are all preserved verbatim — only the upstream classifier
-- references retarget.
--
-- ## Design choice — refactor_IsSigmaOpenGiven
--
-- *DEPENDENT row, not a root.*  The σ-open def's `Prop`-level two-
--   clause shape does NOT commit on its own to any particular reading
--   of "collider at position k" or "blockable non-collider at position
--   k" — it only ranges over whichever upstream
--   `p.refactor_IsCollider` / `p.refactor_IsBlockableNonCollider`
--   predicates the body references.  The `collider_side_aware`
--   refactor's load-bearing design choice — reading arrowhead-presence
--   off the `WalkStep`'s *constructor tag* via `refactor_HeadAtSource`
--   / `refactor_HeadAtTarget` rather than via a node-equality test on
--   shared source/target type indices at a self-loop — is encapsulated
--   entirely in `def_3_15`'s row (the `refactor_HeadAtSource` /
--   `refactor_HeadAtTarget` helpers and the `refactor_IsCollider` /
--   `refactor_IsNonCollider` predicates built on them).  σ-open is
--   therefore pulled into the refactor table as a DEPENDENT, not as a
--   root: its OWN shape needs no revision; only its two classifier-
--   references must retarget to the side-aware partners for the side-
--   aware semantics to propagate from `def_3_15` / `def_3_16` to here.
--   Mechanical port suffices.
--
-- *Why the refactor needs to touch this predicate.*  Mechanically only,
--   not semantically.  Two upstream classifiers referenced in the body
--   have themselves been refactored under `collider_side_aware`:
--   `def_3_15`'s `IsCollider` is replaced by the side-aware
--   `refactor_IsCollider` (which reads arrowhead-presence off the
--   `WalkStep`'s *constructor tag* via `refactor_HeadAtTarget` /
--   `refactor_HeadAtSource`, rather than via a node-equality test
--   against the shared source/target type indices at a self-loop), and
--   `def_3_16`'s `IsBlockableNonCollider` is replaced by the side-aware
--   `refactor_IsBlockableNonCollider` (which retargets its first
--   conjunct `p.IsNonCollider k` → `p.refactor_IsNonCollider k` for
--   the same reason).  σ-open's body needs to reference both side-
--   aware partners, otherwise the unqualified dot-notation resolves to
--   the ORIGINAL non-side-aware defs during the refactor window (see
--   the name-shadowing bullet below).  This row carries NO head-
--   contribution logic of its own — the side-aware reading is
--   implemented entirely at def_3_15's row in the helpers
--   `refactor_HeadAtSource` / `refactor_HeadAtTarget` and propagates
--   through `refactor_IsCollider` / `refactor_IsNonCollider` /
--   `refactor_IsBlockableNonCollider` to σ-open here purely via the
--   two retargeted references.  Cf. the analogous mechanical-retarget
--   block in `refactor_IsBlockableNonCollider`
--   (`BlockableAndUnblockable.lean:651-687`) — that is the canonical
--   template this design block mirrors.
--
-- *Agreement on non-self-loop walks; strict refinement at self-loops.*
--   On every walk that does NOT traverse a directed self-loop step,
--   the side-aware classifiers `refactor_IsCollider` /
--   `refactor_IsBlockableNonCollider` agree pointwise with the
--   ORIGINAL `IsCollider` / `IsBlockableNonCollider` at every position
--   (see `CollidersAndNon.lean`'s `refactor_IsCollider` design block,
--   "Intended deviation at directed self-loops; agreement elsewhere",
--   for how the writing-mirror L-disjunct re-firing on `.forwardE _`
--   / `.backwardE _` non-trivially realises this agreement at writing-
--   mirror non-self-loop pairs — those simultaneously in `G.E` and
--   `G.L`, admitted by `def_3_1`'s `[edge_set_disjointness_under_specified]`
--   addition).  Composing pointwise: under the refactor
--   `refactor_IsSigmaOpenGiven` agrees with the ORIGINAL
--   `IsSigmaOpenGiven` pointwise on every walk that does not traverse
--   any directed self-loop step.  The side-aware encoding's effect is
--   *localised* to walks containing a directed self-loop step
--   `(v, v) ∈ G.E`, where the next bullet's divergence discussion
--   applies and the manager-accepted deviation
--   `collider_side_aware_at_self_loops` from
--   `leanification/deviations.json` is realised verbatim.
--
-- *What the side-aware upstream buys σ-open classification.*  At a
--   directed self-loop step (encoded as `.forwardE _ : WalkStep G v v`
--   with `u = v`), the ORIGINAL `IsCollider`'s `IsInto` test reads the
--   self-loop's source side at `v` as a head — because the node-
--   equality reading `w = v` collapses both type-index disjuncts of
--   `.forwardE`'s `IsInto` branch and cannot distinguish the
--   traversal-target side from the source side when source and target
--   coincide (see `CollidersAndNon.lean`'s `refactor_IsCollider`
--   design block, "Why the refactor needs to touch this predicate").
--   Consequence: an interior position adjacent to a directed self-
--   loop is classified as a *collider* under the ORIGINAL reading,
--   but as a *non-collider* under the side-aware reading
--   (`refactor_HeadAtSource` on `.forwardE _` returns `False`, because
--   its single L-disjunct `s(v, v) ∈ G.L` is vacuously false at a
--   self-loop by `def_3_1`'s `hL_irrefl`).  σ-open's clause (i)
--   universally quantifies over collider positions, so under the
--   side-aware reading the set of positions clause (i) must constrain
--   is *strictly smaller* at any walk traversing a directed self-loop
--   — the self-loop-adjacent position no longer imposes the
--   `v_k ∈ Anc^G(C)` requirement at all.  σ-open's clause (ii) ranges
--   over blockable non-collider positions, and that set expands
--   correspondingly: the newly-non-collider self-loop-adjacent
--   position becomes a candidate for the side-aware blockable /
--   unblockable classification, with the canonical tex's "Treatment
--   of directed self-loops" reading governing the disambiguation
--   (a self-loop alone never disqualifies an interior position from
--   being unblockable — the position's blockable / unblockable
--   classification depends on the OTHER walk-incident edge if any).
--   σ-open inherits this strict refinement at self-loops *without
--   re-stating* the disambiguation here: the manager-accepted
--   deviation `collider_side_aware_at_self_loops` from
--   `leanification/deviations.json` propagates to the σ-open level
--   structurally via the upstream classifier retargets, not via any
--   new code at this row.
--
-- *Why the retarget to `refactor_IsCollider` and
--   `refactor_IsBlockableNonCollider` is required during the refactor
--   window.*  Both pairs of defs (ORIGINAL + REPLACEMENT) coexist in
--   scope while the refactor is in flight.  The unqualified dot-
--   notation `p.IsCollider` / `p.IsBlockableNonCollider` in the body
--   would resolve to the ORIGINAL non-side-aware
--   `Walk.IsCollider` / `Walk.IsBlockableNonCollider` (literal-name
--   match wins over namespace lookup), pairing σ-open's intended
--   side-aware quantification with the non-side-aware ORIGINAL
--   upstream — breaking the very property the refactor exists to fix
--   (the manager-accepted deviation
--   `collider_side_aware_at_self_loops`).  Concretely, on a position
--   adjacent to a directed self-loop the ORIGINAL `IsCollider` returns
--   `True` (the position is a collider under the `IsInto` node-
--   equality reading) but the side-aware `refactor_IsCollider`
--   returns `False`; pairing σ-open with the ORIGINAL collider
--   classifier would therefore *spuriously* impose the
--   `v_k ∈ Anc^G(C)` requirement on the self-loop-adjacent position
--   even though under the canonical side-aware reading no such
--   requirement applies there.  The REPLACEMENT body explicitly
--   references `p.refactor_IsCollider` and
--   `p.refactor_IsBlockableNonCollider`, so the quartet (σ-open,
--   σ-blocked, collider classifier, blockable classifier) form the
--   side-aware classification chain pointwise on every walk and
--   every position.  After Phase 7 cleanup, the whole-word renames
--   `refactor_IsCollider → IsCollider`,
--   `refactor_IsBlockableNonCollider → IsBlockableNonCollider`,
--   `refactor_IsSigmaOpenGiven → IsSigmaOpenGiven`, and
--   `refactor_IsSigmaBlockedGiven → IsSigmaBlockedGiven` restore the
--   body's surface form to its pre-refactor reading
--   `p.IsCollider k` / `p.IsBlockableNonCollider k` — but now
--   resolving to the *unique* (post-rename) side-aware defs, since
--   the ORIGINAL upstream blocks have been deleted by the same
--   cleanup pass.  Same name-shadowing argument used in
--   `refactor_IsBlockableNonCollider`
--   (`BlockableAndUnblockable.lean:651-687`).
--
-- *Shape unchanged from ORIGINAL.*  The `Prop`-level two-clause
--   conjunction, the per-position universal via
--   `p.vertices[k]? = some vk` Option-membership lookup convention,
--   the asymmetric blockable-only quantification on clause (ii)
--   (per the addition `[claim_type_mismatch_vertex_vs_walk]`'s
--   exclusion of any per-vertex extension of σ-open to unblockable
--   positions), the `hC : C ⊆ ↑G.J ∪ ↑G.V` LN-faithful subset
--   hypothesis on the signature (matching the chapter-wide convention
--   shared by `def_3_18`'s `IsISigmaSeparated` and the other
--   `C`-conditioned predicates listed in the ORIGINAL block's `hC`
--   rationale), and the `set_option linter.unusedVariables false in`
--   prefix that suppresses the unused-binder warning on the LN-
--   faithful-but-body-inert `hC` are all preserved verbatim.  Only
--   the upstream classifier references retarget; everything else is
--   byte-identical to the ORIGINAL.
set_option linter.unusedVariables false in
-- def_3_17 -- start statement
def refactor_IsSigmaOpenGiven {u v : Node} (p : Walk G u v) (C : Set Node)
    (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  (∀ (k : ℕ) (vk : Node), p.vertices[k]? = some vk → p.refactor_IsCollider k →
      vk ∈ G.AncSet C) ∧
  (∀ (k : ℕ) (vk : Node), p.vertices[k]? = some vk →
      p.refactor_IsBlockableNonCollider k → vk ∉ C)
-- def_3_17 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsSigmaOpenGiven

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: IsSigmaBlockedGiven
-- ref: def_3_17 (paragraph "C-σ-blocked walk") — refactor
--
-- `p.IsSigmaBlockedGiven C` iff the walk `p` is
-- `C-σ-blocked` in the LN's sense — the positive existential
-- disjunction dual of `IsSigmaOpenGiven`:
--   (i)   there exists a position `k` on `p` and vertex `vk` with
--         `p.vertices[k]? = some vk`, `p.IsCollider k`,
--         and `vk ∉ G.AncSet C`; OR
--   (ii)  there exists a position `k` on `p` and vertex `vk` with
--         `p.vertices[k]? = some vk`,
--         `p.IsBlockableNonCollider k`, and `vk ∈ C`.
--
-- Body identical to the original `Walk.IsSigmaBlockedGiven` (ORIGINAL
-- block above) modulo the same five mechanical upstream retargets as
-- `IsSigmaOpenGiven`.  The positive existential disjunction
-- shape, the three-conjunct-per-existential structure, and the
-- asymmetric quantification over blockable non-colliders ONLY are all
-- preserved verbatim.
--
-- ## Design choice — IsSigmaBlockedGiven
--
-- *Why the refactor needs to touch this predicate.*  Mechanically only,
--   not semantically.  Same five upstream retargets as
--   `IsSigmaOpenGiven`; same retention of the LN's literal
--   `∃ … \notin Anc^G(C) ∨ ∃ … \in C` writing.  The heavy design
--   rationale lives in the ORIGINAL block's comment above (positive
--   existential disjunction NOT `¬ IsSigmaOpenGiven`; same `(k, vk)`
--   pair encoding as the open form; conjunction shape inside the
--   existential).
--
-- *Upstream-driven inheritance: constructor-choice invariance of the
--   blocking witness.*  Same property as `IsSigmaOpenGiven`
--   (see its design block above), specialised to the existential
--   dual: a blocking witness `⟨k, vk, h_lookup, h_collider, h_anc⟩`
--   (clause i) or `⟨k, vk, h_lookup, h_blockable, h_inC⟩` (clause
--   ii) constructed from a `Walk G u v` is *invariant* under
--   the walker's constructor-tag typification on writing-mirror walks
--   — because the upstream `IsCollider` and
--   `IsBlockableNonCollider` predicates (which provide
--   `h_collider` and `h_blockable`) are themselves constructor-choice
--   invariant per the typed-WalkStep + `Sym2 Node` design.  Under the
--   original ordered-pair encoding, the same LN walk position could
--   produce a spurious blocking witness — or fail to produce a real
--   one — depending on writing-mirror typification, which propagated
--   forward to `def_3_18`'s σ-separation and produced
--   CONTENT-class divergences on writing-mirror CDMGs.  Under the
--   refactor that source of divergence is structurally eliminated at
--   the *upstream* predicate layer; no σ-blocked-level code performs
--   the fix.  Walk reversal preserves the blocking witness for the
--   same reason as the σ-open case: an L-step's `.bidir` witness
--   `s(u, v) ∈ G.L` is reversal-invariant by `Sym2`-quotient swap-
--   equality, so a reversed walk yields the same `(k, vk)` witness
--   (modulo re-indexing) without any `hL_symm` lemma invocation —
--   the structural ingredient that the eventual σ-separation
--   symmetry argument needs at the σ-blocked existential.
--
-- *Downstream consumers of this REPLACEMENT.*  The immediate
--   refactor-table consumer is `def_3_18` (`ISigmaSeparation`), which
--   pattern-matches on `IsSigmaBlockedGiven` via its negated
--   form to encode `A ⊥^σ B | C` as a universal-over-walks claim.
--   Future downstream consumers under the same refactor (not in the
--   current refactor table; flagged in `def_3_1`'s refactor design
--   block as the *driving* motivation for the `Sym2 Node` encoding of
--   `L`): the LN's future `claim_3_22` (σ-separation symmetry on
--   writing-mirror CDMGs) — which closes by construction under the
--   refactor precisely because the σ-blocked existential witness is
--   reversal-invariant; and the LN's future `claim_3_21` (the
--   trailing-remark reformulation about unblockable non-colliders
--   being σ-open, excluded from *this* row per
--   `[claim_type_mismatch_vertex_vs_walk]`).  Re-stating σ-blocked's
--   existential shape to fold either claim into the def site was
--   rejected for the same reason as the σ-open case: those claims
--   are orthogonal to the def's shape and folding either in would
--   force a re-derivation rather than a port.
--
-- *Why NOT re-thinking the σ-blocked def shape under the refactor.*
--   Same rationale as `IsSigmaOpenGiven`: the typed-
--   WalkStep encoding strengthens the per-position predicates the
--   existential ranges over but does not motivate a re-design at the
--   walk-level σ-blocked layer.  A `Bool`-valued structural-recursion
--   encoding (`Walk.cons`-pattern matching the way
--   `IsCollider` and `IsBifurcationWithSplit` do)
--   was considered and rejected: (a) it would lose the `Prop`-level
--   existential structure that downstream proofs constructively
--   exploit when forming `Or.inl ⟨k, vk, _, _, _⟩` /
--   `Or.inr ⟨k, vk, _, _, _⟩` witnesses; (b) the recursive shape
--   would make the σ-open / σ-blocked De Morgan duality harder to
--   state (the existential dual of a recursive conjunction is not
--   syntactically symmetric to the recursive conjunction itself);
--   (c) the mechanical port preserves the LN-grep one-to-one
--   correspondence at the def site.
--
-- *Positive existential disjunction preserved, NOT
--   `¬ IsSigmaOpenGiven`.*  The original's three-reason
--   rationale (ORIGINAL block above) carries through verbatim under the
--   refactor: (a) it mirrors the LN's `∃ … \notin Anc^G(C) ∨ ∃ … \in C`
--   writing literally; (b) downstream proofs that *construct* a blocking
--   witness can directly form `Or.inl ⟨k, vk, _, _, _⟩` /
--   `Or.inr ⟨k, vk, _, _, _⟩` terms; (c) the equivalence
--   `¬ p.IsSigmaOpenGiven C ↔ p.IsSigmaBlockedGiven C`
--   is a standalone (classical) De Morgan lemma to be proved when a
--   downstream row needs it — not a definitional reduction the def-shape
--   forces.  Encoding `IsSigmaBlockedGiven` as
--   `¬ IsSigmaOpenGiven` was considered: same rejection
--   rationale as the original.
--
-- *Same `(k, vk)` pair encoding as `IsSigmaOpenGiven`.*  The
--   existential takes `∃ k vk` pinning both the position index and the
--   vertex at that position via `p.vertices[k]? = some vk`.
--   Keeping both classifiers structurally symmetric makes the De Morgan
--   duality lemma (when proved downstream) align witness-to-witness on
--   each clause — same property as the original.
--
-- *Asymmetric quantification preserved: clause (ii) ranges over
--   blockable non-colliders ONLY.*  Same critique as
--   `IsSigmaOpenGiven`: encoding clause (ii) with
--   `IsNonCollider k ∧ vk ∈ C` would under-fire by admitting
--   unblockable non-collider positions inside `C` as blocking witnesses,
--   which is NOT what the LN says.  The addition
--   `[claim_type_mismatch_vertex_vs_walk]`'s exclusion of any per-vertex
--   "unblockable ⇒ open" extension applies verbatim to this clause.
--
-- *Mutually exclusive and jointly exhaustive — by classical De Morgan,
--   not by Lean reduction.*  Same property as the original: the def-
--   shape does not force the negation equivalence, which is left as a
--   standalone (classical) downstream lemma.  See the "Positive
--   existential disjunction" bullet above for the rationale.
--
-- *Explicit `hC : C ⊆ ↑G.J ∪ ↑G.V` on the signature, with
--   `set_option linter.unusedVariables false in`.*  Same rationale as
--   `IsSigmaOpenGiven`'s `hC`-rationale bullet above —
--   LN-faithful subset hypothesis, load-bearing on the signature, inert
--   in the body (out-of-graph nodes contribute vacuously to the
--   existential disjunction via the same `G.AncSet C` value-
--   invariance and the walk-vertex-in-`G` walk-type guarantee).  Same
--   chapter-wide convention as `def_3_18`'s `IsISigmaSeparated`.
set_option linter.unusedVariables false in
-- def_3_17 -- start statement
def IsSigmaBlockedGiven {u v : Node} (p : Walk G u v) (C : Set Node)
    (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  (∃ (k : ℕ) (vk : Node),
      p.vertices[k]? = some vk ∧ p.IsCollider k ∧ vk ∉ G.AncSet C) ∨
  (∃ (k : ℕ) (vk : Node),
      p.vertices[k]? = some vk ∧ p.IsBlockableNonCollider k ∧ vk ∈ C)
-- def_3_17 -- end statement
-- REFACTOR-BLOCK-ORIGINAL-END: IsSigmaBlockedGiven

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: IsSigmaBlockedGiven (was: refactor_IsSigmaBlockedGiven)
-- ref: def_3_17 (paragraph "C-σ-blocked walk") — side-aware refactor
--   (`collider_side_aware`).
--
-- `p.refactor_IsSigmaBlockedGiven C hC` iff the walk `p` is
-- `C-σ-blocked` in the LN's sense — the positive existential
-- disjunction dual of `refactor_IsSigmaOpenGiven`, under the
-- *side-aware* per-step arrowhead-contribution reading committed to
-- by the upstream refactor.  Body identical to the original
-- `IsSigmaBlockedGiven` (ORIGINAL block above) modulo the same two
-- mechanical upstream retargets as `refactor_IsSigmaOpenGiven`:
-- - `p.IsCollider k` → `p.refactor_IsCollider k`
--   (`CollidersAndNon.lean`, REPLACEMENT block);
-- - `p.IsBlockableNonCollider k` → `p.refactor_IsBlockableNonCollider k`
--   (`BlockableAndUnblockable.lean`, REPLACEMENT block).
-- The positive existential disjunction shape, the three-conjunct-
-- per-existential structure, the asymmetric blockable-only
-- quantification on clause (ii), the `hC` LN-faithful subset
-- hypothesis, and the `set_option linter.unusedVariables false in`
-- prefix are all preserved verbatim — only the upstream classifier
-- references retarget.
--
-- ## Design choice — refactor_IsSigmaBlockedGiven
--
-- *DEPENDENT row, not a root.*  Same DEPENDENT framing as
--   `refactor_IsSigmaOpenGiven` (see its DEPENDENT-framing bullet
--   above), specialised to the existential dual: σ-blocked's
--   positive existential disjunction shape does NOT commit on its
--   own to any particular reading of arrowhead-presence at self-
--   loops; it only ranges over whichever upstream
--   `p.refactor_IsCollider` / `p.refactor_IsBlockableNonCollider`
--   predicates the body references.  The refactor's load-bearing
--   design choice (constructor-tag arrowhead-presence reading via
--   `refactor_HeadAtSource` / `refactor_HeadAtTarget`) is
--   encapsulated entirely in `def_3_15`'s row — NOT here.
--   σ-blocked is pulled into the refactor table as a DEPENDENT,
--   not as a root: its OWN shape needs no revision; only the two
--   classifier-references inside its two existential clauses must
--   retarget to the side-aware partners for the side-aware
--   semantics to propagate from `def_3_15` / `def_3_16` to here.
--   Mechanical port suffices.
--
-- *Why the refactor needs to touch this predicate.*  Mechanically only,
--   not semantically.  Same two upstream retargets as
--   `refactor_IsSigmaOpenGiven` — both clauses of the existential
--   disjunction reference the side-aware refactor partners
--   `refactor_IsCollider` and `refactor_IsBlockableNonCollider`,
--   rather than the ORIGINAL non-side-aware defs.  This row carries
--   NO head-contribution logic of its own; the side-aware reading is
--   implemented entirely at def_3_15's row in the helpers
--   `refactor_HeadAtSource` / `refactor_HeadAtTarget` and propagates
--   to here through the retargeted references.  Cf. the analogous
--   mechanical-retarget block in `refactor_IsBlockableNonCollider`
--   (`BlockableAndUnblockable.lean:651-687`) — that is the canonical
--   template this design block mirrors, specialised to the
--   existential dual.
--
-- *Agreement on non-self-loop walks; strict refinement of the
--   blocking-witness set at self-loops.*  On every walk that does NOT
--   traverse a directed self-loop step, the side-aware classifiers
--   `refactor_IsCollider` / `refactor_IsBlockableNonCollider` agree
--   pointwise with the ORIGINAL `IsCollider` /
--   `IsBlockableNonCollider` at every position
--   (`CollidersAndNon.lean`'s `refactor_IsCollider` design block
--   "Intended deviation at directed self-loops; agreement elsewhere"
--   documents the writing-mirror L-disjunct re-firing on
--   `.forwardE _` / `.backwardE _` that realises this agreement at
--   writing-mirror non-self-loop pairs).  Composing pointwise: a
--   blocking witness `⟨k, vk, h_lookup, classifier_h, membership_h⟩`
--   for `refactor_IsSigmaBlockedGiven` exists at `(k, vk)` iff a
--   blocking witness for the ORIGINAL `IsSigmaBlockedGiven` exists at
--   the same `(k, vk)`, on every walk that does not traverse any
--   directed self-loop step.  The side-aware encoding's effect is
--   *localised* to walks containing a directed self-loop step
--   `(v, v) ∈ G.E`, where the next bullet's witness-set refinement
--   discussion applies and the manager-accepted deviation
--   `collider_side_aware_at_self_loops` from
--   `leanification/deviations.json` is realised verbatim.
--
-- *Side-aware blocking witness construction.*  A blocking witness
--   `⟨k, vk, h_lookup, h_collider, h_anc⟩` (clause i) or
--   `⟨k, vk, h_lookup, h_blockable, h_inC⟩` (clause ii) is now formed
--   against the side-aware classifiers `refactor_IsCollider` /
--   `refactor_IsBlockableNonCollider`.  On walks traversing directed
--   self-loops, the ORIGINAL `IsSigmaBlockedGiven` could admit a
--   *spurious* clause-(i) blocking witness from a self-loop-adjacent
--   position that the ORIGINAL `IsCollider` falsely classified as a
--   collider via the `IsInto` node-equality reading (which collapses
--   both self-loop sides — see `CollidersAndNon.lean`'s
--   `refactor_IsCollider` design block, "Why the refactor needs to
--   touch this predicate"); under the refactor that source of false
--   witnesses is structurally eliminated at the upstream layer
--   because the side-aware `refactor_IsCollider` does not fire at the
--   self-loop-adjacent position (the `.forwardE _` source-side head-
--   contribution `refactor_HeadAtSource` is `False` via the
--   vacuously-false `s(v, v) ∈ G.L` disjunct under `def_3_1`'s
--   `hL_irrefl`).  The newly-non-collider self-loop-adjacent position
--   becomes a candidate for the side-aware blockable / unblockable
--   classification, and a clause-(ii) blocking witness can be formed
--   from it iff the position is blockable AND `vk ∈ C` — exactly
--   matching the canonical tex's "Treatment of directed self-loops"
--   reading.  The net effect is that the σ-blocked existential admits
--   a *strictly refined* witness set under the refactor at any walk
--   traversing a directed self-loop, with the manager-accepted
--   deviation `collider_side_aware_at_self_loops` from
--   `leanification/deviations.json` propagating to the σ-blocked
--   level through the upstream classifiers — no σ-blocked-level code
--   performs the fix.  This is the existential-dual specialisation of
--   the σ-open "strictly smaller collider set" observation in
--   `refactor_IsSigmaOpenGiven`'s design block above.
--
-- *Why the retarget to `refactor_IsCollider` and
--   `refactor_IsBlockableNonCollider` is required during the refactor
--   window.*  Same name-shadowing argument as
--   `refactor_IsSigmaOpenGiven`: the unqualified dot-notation
--   `p.IsCollider` / `p.IsBlockableNonCollider` would resolve to the
--   ORIGINAL non-side-aware
--   `Walk.IsCollider` / `Walk.IsBlockableNonCollider` (literal-name
--   match wins over namespace lookup), pairing σ-blocked's intended
--   side-aware existential with the non-side-aware ORIGINAL upstream
--   — breaking the property the refactor exists to fix.  After Phase
--   7 cleanup, the whole-word renames collapse the body's surface
--   form back to its pre-refactor reading `p.IsCollider k` /
--   `p.IsBlockableNonCollider k`, now resolving to the unique side-
--   aware defs (the ORIGINAL upstream blocks are deleted by the same
--   cleanup pass).  Cf. `refactor_IsBlockableNonCollider`'s
--   name-shadowing block (`BlockableAndUnblockable.lean:651-687`).
--
-- *Positive existential disjunction preserved, NOT
--   `¬ refactor_IsSigmaOpenGiven`.*  The original's three-reason
--   rationale (ORIGINAL block above) carries through verbatim under
--   the refactor:
--   (a) it mirrors the LN's `∃ … \notin Anc^G(C) ∨ ∃ … \in C`
--       writing literally;
--   (b) downstream proofs that *construct* a blocking witness can
--       directly form `Or.inl ⟨k, vk, _, _, _⟩` /
--       `Or.inr ⟨k, vk, _, _, _⟩` terms;
--   (c) the equivalence
--       `¬ p.refactor_IsSigmaOpenGiven C hC ↔
--       p.refactor_IsSigmaBlockedGiven C hC` is a standalone
--       (classical) De Morgan lemma to be proved when a downstream
--       row needs it — not a definitional reduction the def-shape
--       forces.
--   Encoding `refactor_IsSigmaBlockedGiven` as
--   `¬ refactor_IsSigmaOpenGiven` was considered: same rejection
--   rationale as the original.  The refactor's upstream encoding
--   change does not motivate revisiting this choice — it strengthens
--   the per-position classifiers the existential ranges over but
--   does not motivate a re-design at the walk-level σ-blocked layer.
--
-- *Shape unchanged from ORIGINAL.*  The `(k, vk)` pair encoding
--   (same as the σ-open form, so the eventual classical De Morgan
--   duality lemma aligns witness-to-witness on each clause), the
--   three-conjunct-per-existential structure
--   (`p.vertices[k]? = some vk ∧ classifier ∧ membership`), the
--   asymmetric blockable-only quantification on clause (ii) (per
--   the addition `[claim_type_mismatch_vertex_vs_walk]`'s exclusion
--   of any per-vertex extension of σ-open to unblockable positions,
--   applying verbatim to the existential dual — clause (ii)'s
--   `IsNonCollider k ∧ vk ∈ C` would under-fire by admitting
--   unblockable non-collider positions inside `C` as blocking
--   witnesses), the `hC : C ⊆ ↑G.J ∪ ↑G.V` LN-faithful subset
--   hypothesis on the signature (matching the chapter-wide
--   convention), and the `set_option linter.unusedVariables false
--   in` prefix that suppresses the unused-binder warning on the
--   LN-faithful-but-body-inert `hC` are all preserved verbatim.
--   Only the upstream classifier references retarget; everything
--   else is byte-identical to the ORIGINAL.
set_option linter.unusedVariables false in
-- def_3_17 -- start statement
def refactor_IsSigmaBlockedGiven {u v : Node} (p : Walk G u v) (C : Set Node)
    (hC : C ⊆ ↑G.J ∪ ↑G.V) : Prop :=
  (∃ (k : ℕ) (vk : Node),
      p.vertices[k]? = some vk ∧ p.refactor_IsCollider k ∧ vk ∉ G.AncSet C) ∨
  (∃ (k : ℕ) (vk : Node),
      p.vertices[k]? = some vk ∧ p.refactor_IsBlockableNonCollider k ∧ vk ∈ C)
-- def_3_17 -- end statement
-- REFACTOR-BLOCK-REPLACEMENT-END: IsSigmaBlockedGiven

end Walk

end CDMG

end Causality
