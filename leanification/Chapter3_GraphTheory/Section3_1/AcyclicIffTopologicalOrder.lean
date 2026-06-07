import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Chapter3_GraphTheory.Section3_1.CDMGTypes

namespace Causality

/-!
# Acyclicity is equivalent to existence of a topological order (`claim_3_2`)

This file formalises the LN lemma block `claim_3_2` from `graphs.tex`,
immediately following `def-topological-order`:

> A CDMG `G = (J, V, E, L)` is acyclic if and only if it has a
> topological order.

The authoritative spec is the rewritten canonical tex statement at
`leanification/Chapter3_GraphTheory/Section3_1/tex/`
`claim_3_2_statement_AcyclicIffTopologicalOrder.tex`, verified
equivalent to the LN block.  The row carries an empty
`addition_to_the_LN`; the LN-critic wording-check returned
`NO_SUBTLETIES`.  The literal LN sentence is authoritative.

Both sides of the biconditional refer to upstream chapter-3 predicates
already in this folder:

* `G.IsAcyclic` from `def_3_6` (`Acyclicity.lean`) — there does not
  exist a non-trivial directed walk from any node `v ∈ J ∪ V` back to
  itself.
* `G.IsTopologicalOrder lt` from `def_3_8` (`TopologicalOrder.lean`) —
  the four-conjunct `Prop` predicate on an external relation
  `lt : Node → Node → Prop` asserting (i) irreflexivity on `J ∪ V`,
  (ii) transitivity on `J ∪ V`, (iii) trichotomy on `J ∪ V`, and (iv)
  `v ∈ Pa^G(w) → lt v w` (parents precede their children).

Because `def_3_8` characterises *which* relations qualify as a
topological order (rather than asserting one exists), "G has a
topological order" reads in Lean as the existential
`∃ lt : Node → Node → Prop, G.IsTopologicalOrder lt` — exactly the
shape that `def_3_8`'s "Downstream consumers" design block
anticipates.  The label set `L` of `def_3_1` plays no role on either
side of the biconditional; the result is a property of the
`(J, V, E)`-skeleton of `G` only.

The theorem body is filled in by `prove_claim_in_lean` (Manager B),
following the verified TeX proof at
`tex/claim_3_2_proof_AcyclicIffTopologicalOrder.tex`.  Proof-only
helpers (walk concatenation, source/target-in-`G` for non-trivial
directed walks, single-edge directed walk, walk-induction on `lt`)
live just below the `variable` block, outside the marker zones
because they are not statement content.

## Refactor `total_order_helper` (in progress)

This row is a DEPENDENT in the refactor `total_order_helper` (root:
`def_3_8` -- see `TopologicalOrder.lean`'s `## Refactor` section).
The root refactor split `IsTopologicalOrder` from a flat 4-way `∧`
into a nested 2-conjunct `IsTotalOrder ∧ parent_precedes`, naming
the strict-total-order sub-concept `IsTotalOrder`.  Below we add a
`refactor_acyclic_iff_topological_order` that references the new
`refactor_IsTopologicalOrder` (wrapped in matching
`-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: …` / `…-END: …` markers); the
original `acyclic_iff_topological_order` -- wrapped in
`-- REFACTOR-BLOCK-ORIGINAL-BEGIN: …` / `…-END: …` markers -- stays
in place untouched until Phase 7 cleanup, so the build stays green
throughout.  The *statement shape* is unchanged: it remains
`G.IsAcyclic ↔ ∃ lt, G.<topological-order-predicate> lt`; only the
referenced predicate flips.  The *proof body* differs from the
original in exactly two surgical sites -- the (⇒)-direction
`refine` (constructor-side flip from flat `?_, ?_, ?_, ?_` to
nested `⟨?_, ?_, ?_⟩, ?_`) and the (⇐)-direction `rintro`
(destructure-side flip from flat `⟨lt, hi, htr, htri, hp⟩` to
nested `⟨lt, ⟨hi, htr, htri⟩, hp⟩`) -- mirroring `def_3_8`'s
nested 2-conjunct shape.  Every other step (the walk-reachability
preorder, Szpilrajn extension, the four sub-proofs, the (⇐)
contradiction via `Walk.lt_of_directedWalk_pos`) is byte-identical
to the original.  Proof-only helpers (lines below the `variable`
block) are shared by both versions and carry no marker block of
their own.
-/

namespace CDMG

-- ## Design choice — statement context
--
-- *`Node : Type*` with `[DecidableEq Node]`.*  Inherited verbatim from
--   `def_3_1` (`CDMG.lean`).  Both fixtures are load-bearing here
--   because the theorem signature references `CDMG Node`, `G.IsAcyclic`
--   and `G.IsTopologicalOrder`, each of which depends on
--   `[DecidableEq Node]` (the `Finset`-backed membership tests in
--   `G.J ∪ G.V`, the `v ∈ G` quantifier scope via the `Membership`
--   instance from `def_3_2`, and the `Walk.IsDirectedWalk` recursive
--   check in `def_3_6` all require it).  Stronger instances
--   (`Fintype`, `LinearOrder`) are not needed at the statement level
--   and would over-commit — the proof body (handled separately) may
--   need them locally.
--
-- *Three-dash `--- start helper` marker (not the two-dash
--   `-- start statement`).*  Matches the convention in every sibling
--   file in this folder (`CDMG.lean`, `CDMGNotation.lean`,
--   `Walks.lean`, `EdgeRelations.lean`, `CDMGRestrictions.lean`,
--   `Acyclicity.lean`, `CDMGTypes.lean`, `TopologicalOrder.lean`).
--   The two-dash marker is reserved for declarations whose body is the
--   formalised LN content of the row; this `variable` line is
--   statement-typing infrastructure binding the implicit `Node` type
--   and its `DecidableEq` instance that the theorem's signature
--   references.
-- claim_3_2 --- start helper
variable {Node : Type*} [DecidableEq Node]
-- claim_3_2 --- end helper

-- ## Proof-only helpers
--
-- The lemmas below are infrastructure for the proof of `claim_3_2`.
-- They are deliberately private and carry no marker comments — markers
-- are reserved for declarations whose body is the formalised LN content
-- of a row, and these are just walk-level plumbing the proof needs
-- (concatenation, length / directedness preservation under
-- concatenation, target-membership for a non-trivial directed walk, the
-- single-edge directed walk witnessing the parent → child step).
-- See `tex/claim_3_2_proof_AcyclicIffTopologicalOrder.tex` for the TeX
-- proof these helpers implement.

/-- Concatenate two walks `p : u → v` and `q : v → w` into a walk `u → w`. -/
private def Walk.comp {G : CDMG Node} :
    ∀ {u v w : Node}, Walk G u v → Walk G v w → Walk G u w
  | _, _, _, .nil _ _, q => q
  | _, _, _, .cons v a h p, q => .cons v a h (p.comp q)

private lemma Walk.length_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      (p.comp q).length = p.length + q.length
  | _, _, _, .nil _ _, q => by
      simp [Walk.comp, Walk.length]
  | _, _, _, .cons _ _ _ p, q => by
      simp [Walk.comp, Walk.length, Walk.length_comp p q, Nat.add_comm, Nat.add_left_comm]

private lemma Walk.isDirectedWalk_comp {G : CDMG Node} :
    ∀ {u v w : Node} (p : Walk G u v) (q : Walk G v w),
      p.IsDirectedWalk → q.IsDirectedWalk → (p.comp q).IsDirectedWalk
  | _, _, _, .nil _ _, _, _, hq => hq
  | _, _, _, .cons _ _ _ p, q, hp, hq => by
      obtain ⟨h1, h2, h3⟩ := hp
      exact ⟨h1, h2, Walk.isDirectedWalk_comp p q h3 hq⟩

/-- The source of a non-trivial directed walk lies in `G`. -/
private lemma Walk.source_in_G_of_directedWalk_pos {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → u ∈ G
  | _, _, .nil _ _, _, hlen => by simp [Walk.length] at hlen
  | _, _, .cons _ _ _ _, hp, _ => by
      obtain ⟨ha_eq, ha_E, _⟩ := hp
      have h_edge : (_, _) ∈ G.E := ha_eq ▸ ha_E
      exact (G.hE_subset h_edge).1

/-- The target of a non-trivial directed walk lies in `G`. -/
private lemma Walk.target_in_G_of_directedWalk_pos {G : CDMG Node} :
    ∀ {u v : Node} (p : Walk G u v),
      p.IsDirectedWalk → p.length ≥ 1 → v ∈ G := by
  intro u v p
  induction p with
  | nil _ _ => intro _ hlen; simp [Walk.length] at hlen
  | @cons u w v a h q ih =>
      intro hdir _
      obtain ⟨ha_eq, ha_E, hq_dir⟩ := hdir
      have h_edge : (u, v) ∈ G.E := ha_eq ▸ ha_E
      by_cases hq_len : q.length ≥ 1
      · exact ih hq_dir hq_len
      · -- q is the trivial walk; q : Walk G v w with v = w forced by `Walk.nil`
        have hlen0 : q.length = 0 := by omega
        match q, hq_dir, hlen0 with
        | .nil _ _, _, _ =>
            exact Finset.mem_union_right _ (G.hE_subset h_edge).2

/-- A single edge `(u, v) ∈ G.E` (with `v ∈ G`) is witnessed by a
length-1 directed walk `u → v`. -/
private lemma Walk.singleEdge_directedWalk {G : CDMG Node}
    {u v : Node} (hv : v ∈ G) (huv : (u, v) ∈ G.E) :
    ∃ p : Walk G u v, p.IsDirectedWalk ∧ p.length ≥ 1 := by
  have hstep : G.WalkStep u (u, v) v := Or.inl ⟨rfl, Or.inl huv⟩
  refine ⟨Walk.cons v (u, v) hstep (Walk.nil v hv), ?_, ?_⟩
  · exact ⟨rfl, huv, trivial⟩
  · simp [Walk.length]

/-- Along a non-trivial directed walk, a topological order forces
`lt` between source and target.  Used in the (⇐) direction of
`claim_3_2`: a hypothetical directed self-loop `v → … → v` would
contradict irreflexivity of any topological order. -/
private lemma Walk.lt_of_directedWalk_pos {G : CDMG Node}
    {lt : Node → Node → Prop}
    (h_trans : ∀ u ∈ G, ∀ v ∈ G, ∀ w ∈ G, lt u v → lt v w → lt u w)
    (h_parent : ∀ v w, v ∈ G.Pa w → lt v w) :
    ∀ {x y : Node} (p : Walk G x y),
      p.IsDirectedWalk → p.length ≥ 1 → lt x y := by
  intro x y p
  induction p with
  | nil _ _ => intro _ hlen; simp [Walk.length] at hlen
  | @cons u w v a h q ih =>
      intro hdir _
      obtain ⟨ha_eq, ha_E, hq_dir⟩ := hdir
      have h_edge : (u, v) ∈ G.E := ha_eq ▸ ha_E
      have hu : u ∈ G := (G.hE_subset h_edge).1
      have hv : v ∈ G := Finset.mem_union_right _ (G.hE_subset h_edge).2
      have hlt_uv : lt u v := h_parent u v ⟨hu, h_edge⟩
      by_cases hq_len : q.length ≥ 1
      · -- recurse on `q`
        have hw : w ∈ G :=
          Walk.target_in_G_of_directedWalk_pos q hq_dir hq_len
        have hlt_vw : lt v w := ih hq_dir hq_len
        exact h_trans u hu v hv w hw hlt_uv hlt_vw
      · -- `q` is the trivial walk; `v = w`.
        have hlen0 : q.length = 0 := by omega
        match q, hq_dir, hlen0 with
        | .nil _ _, _, _ => exact hlt_uv

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: acyclic_iff_topological_order
-- ref: claim_3_2
-- A CDMG `G = (J, V, E, L)` is acyclic (in the sense of `def_3_6`) iff
-- there exists a topological order of `G` (in the sense of `def_3_8`).
-- Equivalently: iff there exists a strict total order `lt` on `J ∪ V`
-- — irreflexive, transitive, and trichotomous — under which every
-- parent precedes every child (`v ∈ Pa^G(w) → lt v w`).  The label
-- set `L` plays no role on either side of the biconditional.
/-
LN tex (verbatim from `graphs.tex`, the `\begin{Lem}` block
immediately following `def-topological-order`):

  A CDMG `G = (J, V, E, L)` is acyclic if and only if it has a
  topological order.

Rewritten canonical tex (see
`tex/claim_3_2_statement_AcyclicIffTopologicalOrder.tex`):

  Let `G = (J, V, E, L)` be a CDMG.  Then `G` is acyclic (in the sense
  of def_3_6) iff there exists a topological order of `G` (in the
  sense of def_3_8); equivalently, `G` is acyclic iff there exists a
  strict total order `<` on `J ∪ V` — i.e.\ a binary relation `<` on
  `J ∪ V` that is irreflexive, transitive, and trichotomous — such
  that, for every `v, w ∈ J ∪ V`, `v ∈ Pa^G(w) ⟹ v < w`.  The label
  set `L` plays no role on either side of the biconditional.
-/
-- ## Design choice
--
-- *Biconditional `↔` mirrors the LN's "if and only if" verbatim.*  A
--   single `Iff` packages both directions; consumers reach `.mp`
--   (acyclic ⟹ a topological order exists — the workhorse projection
--   for chapter 4–10's CBN factorisation, do-calculus, and
--   d-separation arguments that index a parent-first traversal over an
--   ADMG, since `IsADMG` carries `IsAcyclic` as its first conjunct per
--   `CDMGTypes.lean`) or `.mpr` (topological order ⟹ acyclic — the
--   certificate route used by causal-discovery algorithms in chapter
--   11+ that construct an ordering and need to conclude acyclicity)
--   without a per-direction lemma split.  Splitting into two named
--   theorems `acyclic_implies_topological_order` /
--   `topological_order_implies_acyclic` was considered and rejected:
--   the LN treats this as one claim, every downstream site we have
--   visibility into needs only one direction at a time (and reaches
--   it via `.mp` / `.mpr` at zero cost), and the bundled `↔` keeps
--   the LN ↔ Lean cross-reference grep-able under a single name.
--
-- *RHS is `∃ lt : Node → Node → Prop, G.IsTopologicalOrder lt` — an
--   existential over a bare relation, not over a bundled
--   `LinearOrder Node` / subtype-restricted strict-total-order
--   structure.*  Forced by `def_3_8`'s upstream design: its
--   `IsTopologicalOrder` is a property of an external `lt`, not a
--   bundled-existence structure (see `TopologicalOrder.lean`'s
--   "Predicate over an external ordering" block, whose "Downstream
--   consumers" paragraph literally anticipates this row's
--   `∃ lt, G.IsTopologicalOrder lt` shape).  Bundled alternatives
--   considered and rejected:
--   (a) `∃ lt : LinearOrder Node, …` — Mathlib's `LinearOrder` forces
--     totality / transitivity / antisymmetry on the *full* `Node`
--     type, excluding perfectly valid orders that leave nodes outside
--     `J ∪ V` unrelated; the LN only requires totality on `J ∪ V`.
--   (b) `∃ lt : StrictOrder ↥(G.J ∪ G.V), …` (subtype-restricted) —
--     avoids over-commitment but forces every downstream consumer to
--     coerce nodes across the `↥(G.J ∪ G.V)` boundary at every use
--     site.  `def_3_8` rejected this on the predicate side for the
--     same reason, and we inherit the choice here.
--   (c) A `∃!`-strengthened or `Classical.choice`-ed canonical order
--     would inject uniqueness / arbitrariness that the LN does not
--     commit to: many topological orders generally exist (any linear
--     refinement of the parent-precedence partial order qualifies),
--     and the LN never picks one.
--   Consumers `obtain ⟨lt, hlt⟩ := …` to get a concrete order, then
--   destructure `hlt` via `def_3_8`'s 4-conjunct
--   `⟨hi, htr, htri, hp⟩` shape.
--
-- *Only `(G : CDMG Node)` is hypothesised — no `[Fintype Node]`, no
--   re-stated CDMG-shape constraints, no extra typeclasses beyond the
--   chapter-standard `[DecidableEq Node]` binder.*  Every shape
--   constraint the biconditional rests on (finite `J, V`,
--   `Disjoint J V`, `E ⊆ (J ∪ V) × V`, label symmetry / irreflexivity)
--   is baked into the `CDMG` record from `def_3_1` (`CDMG.lean`);
--   `[DecidableEq Node]` on the surrounding `variable` line is what
--   `G.IsAcyclic` (its `Walk.IsDirectedWalk` recursion) and
--   `G.IsTopologicalOrder lt` (its `v ∈ G` quantifiers and `G.Pa w`
--   reference) reach through to typecheck.  `[Fintype Node]` was
--   considered — a constructive topological-sort proof of the `.mp`
--   direction may want it locally to enumerate `(G.J ∪ G.V).toList`
--   — and rejected at the *statement* level: the proof body's local
--   needs should not leak into the surface signature, and the
--   `Finset`-valued `G.J` / `G.V` already supply finiteness on
--   `J ∪ V`, which is exactly the domain on which the order must be
--   total.
--
-- *Labels `L` are correctly absent from both sides of the
--   biconditional.*  `IsAcyclic` (`def_3_6`) only inspects directed
--   walks built from `G.E`; `IsTopologicalOrder` (`def_3_8`) only
--   references the parent set `Pa^G(w)` (a directed-edge construct
--   from `def_3_5`).  Neither reads `G.L`, matching the LN's silence
--   on labels in this block.  Consumers operating on labelled graphs
--   (chapter 4–10 CBN / do-calculus arguments on ADMGs, where
--   bidirected `L`-edges encode hidden common causes) lose nothing by
--   ignoring `G.L` here — acyclicity and topological order are
--   properties of the `(J, V, E)`-skeleton alone.
--
-- *Mathlib re-use.*  None at the type / typeclass level for the
--   statement; the existential binds a bare `Node → Node → Prop`
--   rather than a Mathlib `LinearOrder` / `IsStrictTotalOrder`
--   instance, for the over-commitment reason above.  The proof body
--   (deferred to the sibling `prove_claim_in_lean` worker) is free to
--   invoke Mathlib's finite-set / Finset / List ordering machinery
--   locally — typical routes: for `.mp`, a recursive minimum-element
--   pick on `(G.J ∪ G.V).toList` driven by `def_3_6`'s `IsAcyclic`
--   ruling out empty-source obstructions; for `.mpr`, a `Walk`-length
--   induction contradiction combining irreflexivity, transitivity, and
--   parent-precedes from `def_3_8`'s 4-conjunct — without affecting
--   this statement's signature.
--
-- *Known limitation: non-canonical witness.*  The `∃` deliberately
--   does not designate a canonical topological order — many may exist
--   (any linear refinement of the parent-precedence partial order
--   qualifies), and the LN never picks one.  Downstream theorems that
--   need to fix a specific order must either pass `lt` as an explicit
--   hypothesis or `Classical.choice`-extract it at the use site
--   (inheriting the non-canonicality).  This matches the LN's
--   treatment and is intentional, not an API gap.
-- claim_3_2 -- start statement
theorem acyclic_iff_topological_order (G : CDMG Node) :
    G.IsAcyclic ↔ ∃ lt : Node → Node → Prop, G.IsTopologicalOrder lt
-- claim_3_2 -- end statement
:= by
  -- TeX proof: tex/claim_3_2_proof_AcyclicIffTopologicalOrder.tex
  constructor
  · -- (⇒) Acyclic ⇒ a topological order exists.
    --
    -- Following the LN proof: define the reflexive walk-reachability
    -- relation `le₀ u v := u = v ∨ ∃ directed walk u → v of length ≥ 1`,
    -- show it is a partial order (refl/trans via walk concatenation,
    -- antisymm via acyclicity), then apply Mathlib's Szpilrajn
    -- extension (`extend_partialOrder`) to obtain a linear order `s`
    -- extending `le₀`.  Reading `lt u v := s u v ∧ u ≠ v` gives the
    -- strict total order witnessing `IsTopologicalOrder`.
    --
    -- This is a "semantic" Leanification of the LN's inductive
    -- parent-less-pick construction: where the LN picks `v_1, …, v_K`
    -- by hand and reads off the order, we package the same partial
    -- order (walk reachability) and invoke Szpilrajn to do the
    -- enumeration.  The two constructions produce the same kind of
    -- witness (any topological order qualifies; the LN never picks a
    -- canonical one).
    intro hac
    let le₀ : Node → Node → Prop := fun u v =>
      u = v ∨ ∃ p : Walk G u v, p.IsDirectedWalk ∧ p.length ≥ 1
    -- Reflexivity, transitivity, antisymmetry of `le₀`.
    have hrefl : ∀ a, le₀ a a := fun _ => Or.inl rfl
    have htrans : ∀ a b c, le₀ a b → le₀ b c → le₀ a c := by
      intros a b c hab hbc
      rcases hab with heq | ⟨p, hp_dir, hp_len⟩
      · subst heq; exact hbc
      rcases hbc with heq | ⟨q, hq_dir, hq_len⟩
      · subst heq; exact Or.inr ⟨p, hp_dir, hp_len⟩
      · refine Or.inr ⟨p.comp q,
          Walk.isDirectedWalk_comp p q hp_dir hq_dir, ?_⟩
        rw [Walk.length_comp]; omega
    have hantisymm : ∀ a b, le₀ a b → le₀ b a → a = b := by
      intros a b hab hba
      rcases hab with heq | ⟨p, hp_dir, hp_len⟩
      · exact heq
      rcases hba with heq | ⟨q, hq_dir, hq_len⟩
      · exact heq.symm
      · -- Both `p : a → b` and `q : b → a` non-trivial directed walks.
        -- Concatenate to a non-trivial directed walk `a → a`, contradict
        -- acyclicity at `a` (`a ∈ G` from the source of `p`).
        exfalso
        have ha : a ∈ G :=
          Walk.source_in_G_of_directedWalk_pos p hp_dir hp_len
        refine hac a ha ⟨p.comp q,
          Walk.isDirectedWalk_comp p q hp_dir hq_dir, ?_⟩
        rw [Walk.length_comp]; omega
    haveI : Std.Refl le₀ := ⟨hrefl⟩
    haveI : IsTrans Node le₀ := ⟨htrans⟩
    haveI : Std.Antisymm le₀ := ⟨hantisymm⟩
    haveI : IsPreorder Node le₀ := {}
    haveI : IsPartialOrder Node le₀ := {}
    -- Szpilrajn extension: a linear order `s` with `le₀ ≤ s`.
    obtain ⟨s, hs_lo, h_sub⟩ := extend_partialOrder le₀
    -- Promote `hs_lo` to an active typeclass instance so the inherited
    -- `IsTrans` / `Std.Total` / `Std.Antisymm` are resolvable by name
    -- (without `haveI` they sit as a regular hypothesis, invisible to
    -- typeclass synthesis — hence the unification failures otherwise
    -- triggered by `Std.Total.total v w`).
    haveI : IsLinearOrder Node s := hs_lo
    -- The strict version of `s` is our topological order.
    refine ⟨fun u v => s u v ∧ u ≠ v, ?_, ?_, ?_, ?_⟩
    · -- Irreflexivity on `G`: `¬ (s v v ∧ v ≠ v)` from `v ≠ v`.
      intro v _ hlt
      exact hlt.2 rfl
    · -- Transitivity on `G`.
      intros u _ v _ w _ huv hvw
      obtain ⟨hsuv, hne_uv⟩ := huv
      obtain ⟨hsvw, hne_vw⟩ := hvw
      refine ⟨IsTrans.trans u v w hsuv hsvw, ?_⟩
      intro huw
      subst huw
      -- `s u v` and `s v u` with antisymm gives `u = v`, contradicting `hne_uv`.
      exact hne_uv (Std.Antisymm.antisymm u v hsuv hsvw)
    · -- Trichotomy on `G`: from totality of `s`.
      intros v _ w _
      by_cases h : v = w
      · right; left; exact h
      · rcases (Std.Total.total (r := s) v w) with hvw | hwv
        · left; exact ⟨hvw, h⟩
        · right; right; exact ⟨hwv, fun heq => h heq.symm⟩
    · -- Parent precedes: `u ∈ Pa^G(w) → lt u w`.
      intros u w hu_in_Pa
      obtain ⟨hu, huw_E⟩ := hu_in_Pa
      have hw : w ∈ G :=
        Finset.mem_union_right _ (G.hE_subset huw_E).2
      have hle₀_uw : le₀ u w :=
        Or.inr (Walk.singleEdge_directedWalk hw huw_E)
      have hsuw : s u w := h_sub _ _ hle₀_uw
      refine ⟨hsuw, ?_⟩
      intro heq
      subst heq
      -- A self-loop `(u, u) ∈ G.E` would give a length-1 directed walk
      -- `u → u`, contradicting acyclicity at `u`.
      exact hac u hu (Walk.singleEdge_directedWalk hu huw_E)
  · -- (⇐) A topological order ⇒ acyclic.
    --
    -- LN argument: a non-trivial directed walk `v = v_0 → v_1 → ⋯ →
    -- v_n = v` with `n ≥ 1` would give a chain `v_0 < v_1 < ⋯ < v_n =
    -- v_0` under any topological order, contradicting irreflexivity.
    -- Encoded as `Walk.lt_of_directedWalk_pos` above (which uses
    -- parent-precedes and transitivity to walk along edges) and
    -- combined with the topological order's irreflexivity field.
    rintro ⟨lt, hi, htr, htri, hp⟩
    intro v hv ⟨p, hp_dir, hp_len⟩
    exact hi v hv (Walk.lt_of_directedWalk_pos htr hp p hp_dir hp_len)
-- REFACTOR-BLOCK-ORIGINAL-END: acyclic_iff_topological_order

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: acyclic_iff_topological_order (was: refactor_acyclic_iff_topological_order)
-- ref: claim_3_2 (refactor)
-- A CDMG `G = (J, V, E, L)` is acyclic (in the sense of `def_3_6`) iff
-- there exists a topological order of `G` (in the sense of `def_3_8`,
-- post-refactor: the nested 2-conjunct `IsTotalOrder ∧ parent_precedes`
-- shape -- see `TopologicalOrder.lean`).  The statement is identical in
-- *shape* to the original: `G.IsAcyclic ↔ ∃ lt, G.<...> lt`; only the
-- referenced predicate flips from the original flat-4 `IsTopologicalOrder`
-- to the refactored nested-2 `refactor_IsTopologicalOrder`.
/-
LN tex (rewritten canonical statement for `claim_3_2`):

  Let `G = (J, V, E, L)` be a CDMG.  Then `G` is acyclic (in the sense
  of def_3_6) iff there exists a topological order of `G` (in the
  sense of def_3_8); equivalently, `G` is acyclic iff there exists a
  strict total order `<` on `J ∪ V` — i.e.\ a binary relation `<` on
  `J ∪ V` that is irreflexive, transitive, and trichotomous — such
  that, for every `v, w ∈ J ∪ V`, `v ∈ Pa^G(w) ⟹ v < w`.  The label
  set `L` plays no role on either side of the biconditional.
-/
-- ## Design choice
--
-- *Shape of the biconditional.*  The signature
--     `G.IsAcyclic ↔ ∃ lt : Node → Node → Prop, G.refactor_IsTopologicalOrder lt`
--   is the literal rendering of the LN's "is acyclic iff has a
--   topological order": `↔` for "iff", `∃ lt : Node → Node → Prop` for
--   "has a", and `refactor_IsTopologicalOrder` for "topological order"
--   -- the predicate from `def_3_8` (`TopologicalOrder.lean`)
--   characterising which `lt` qualify, with content
--     `G.refactor_IsTotalOrder lt ∧ (∀ v w, v ∈ G.Pa w → lt v w)`
--   (the strict-total-order helper `refactor_IsTotalOrder` plus parent
--   precedence).  The biconditional is bundled in a single `Iff`:
--   consumers reach `.mp` (acyclic ⟹ a topological order exists -- the
--   workhorse projection for chapter 4+ CBN factorisation / do-calculus
--   that index parent-first traversals over an ADMG, since `IsADMG`
--   carries `IsAcyclic` as its first conjunct per `CDMGTypes.lean`) or
--   `.mpr` (topological order ⟹ acyclic -- the certificate route used
--   by causal-discovery algorithms in chapter 11+ that construct an
--   ordering and need to conclude acyclicity) without a per-direction
--   lemma split.  Splitting into two named theorems was considered and
--   rejected: the LN treats this as one claim, every downstream site
--   needs only one direction at a time (reached via `.mp` / `.mpr` at
--   zero cost), and the bundled `↔` keeps the LN ↔ Lean cross-reference
--   grep-able under a single name.
--
-- *Why the nested 2-conjunct shape for "topological order".*  Inherited
--   from `def_3_8` (`TopologicalOrder.lean`): the four atomic axioms
--   (irreflexivity, transitivity, trichotomy, parent-precedes) are
--   packaged so that the first three -- a strict total order on
--   `J ∪ V` -- live in a separately-named predicate
--   `refactor_IsTotalOrder G lt` that downstream rows (e.g. `def_3_9`'s
--   `Pred` / `PredLE`) can carry as an explicit hypothesis without
--   dragging the parent-precedence requirement along.  The LN-level
--   mathematical content of `claim_3_2` is *unchanged* by this
--   packaging -- the predicate unfolds to the same four atomic
--   propositions in the same order -- only how "is a topological order"
--   is *expressed* in Lean.  Naming the strict-total-order sub-concept
--   is what makes the rest of the chapter able to refer to it directly;
--   see `TopologicalOrder.lean` for the predicate definitions and the
--   sub-concept's motivation.
--
-- *Why `∃ lt : Node → Node → Prop` over a bundled order.*  Bare
--   `Node → Node → Prop` matches the LN's phrasing "has a topological
--   order" most directly: a topological order is *data* (a relation
--   between specific nodes), not a typeclass, and `∃` is the most
--   direct rendering of "has".  Bundled alternatives considered and
--   rejected:
--   * `[LinearOrder Node]` typeclass forces totality / transitivity /
--     antisymmetry on the *full* `Node` type, excluding perfectly
--     valid orders that leave nodes outside `J ∪ V` unrelated -- the
--     LN only requires totality on `J ∪ V`.
--   * Subtype-restricted `LinearOrder ↥(G.J ∪ G.V)` avoids the
--     over-commitment but forces every consumer to coerce nodes across
--     the `↥`-boundary at every use site.  `def_3_8`'s predicate
--     rejected this on the same grounds; we inherit the choice.
--   * `List Node` ordered by index would bake in a specific enumeration
--     -- the LN reasons about topological order as a property of a
--     relation, not as a list, and the proof's parent-less-pick
--     construction can produce many distinct lists from the same
--     partial order.
--   * `∃!`-strengthened or `Classical.choice`-extracted canonical order
--     would inject uniqueness the LN never claims; many linear
--     refinements of the parent-precedence partial order qualify.
--   The chosen shape preserves the LN's reasoning about *which* order
--   to pick (the proof constructs one by walk-reachability + Szpilrajn
--   extension) without committing the type to any global order
--   structure.
--
-- *Proof body: same mathematics, witness-assembly tracks the nested
--   shape.*  The proof's *mathematical* structure follows the LN
--   verbatim:
--   * (⇒) walk-reachability `le₀ u v := u = v ∨ ∃ directed walk
--     u → v of length ≥ 1` is shown to be a partial order (refl / trans
--     via `Walk.comp`, antisymm via acyclicity ruling out the cycle
--     formed by concatenating opposing non-trivial walks), Mathlib's
--     Szpilrajn `extend_partialOrder` yields a linear refinement `s`,
--     and `lt u v := s u v ∧ u ≠ v` reads off the strict order
--     witnessing `refactor_IsTopologicalOrder` -- a "semantic"
--     Leanification of the LN's inductive parent-less-pick
--     construction.
--   * (⇐) a hypothetical non-trivial directed cycle `v → ⋯ → v` would
--     force `lt v v` via `Walk.lt_of_directedWalk_pos` (which walks
--     along edges using transitivity + parent-precedes), contradicting
--     irreflexivity.
--   The *witness assembly* tracks the nested encoding via
--   `refactor_IsTotalOrder`'s natural smart constructor: in (⇒) the
--   final `refine ⟨fun u v => s u v ∧ u ≠ v, ⟨?_, ?_, ?_⟩, ?_⟩` is the
--   anonymous-constructor analogue of `refactor_IsTotalOrder.intro`
--   for the three total-order axioms (irreflexivity / transitivity /
--   trichotomy), followed by the parent-precedes conjunct; in (⇐) the
--   opening `rintro ⟨lt, ⟨hi, htr, htri⟩, hp⟩` destructures the
--   existential with the matching nested pattern, putting the four
--   hypotheses needed for the contradiction in scope under their
--   natural names.  Only the witness-assembly differs from a flat-4
--   encoding -- every other line (the `le₀` relation, the `hrefl` /
--   `htrans` / `hantisymm` lemmas, the `IsPreorder` / `IsPartialOrder`
--   typeclass promotions via `haveI`, the `extend_partialOrder` call,
--   the four sub-proofs of irreflexivity / transitivity / trichotomy /
--   parent-precedes, the `Walk.lt_of_directedWalk_pos` invocation) is
--   independent of the topological-order predicate's internal shape.
--
-- *Proof-only helpers (above the theorem, outside the marker zone).*
--   The walk-level plumbing -- `Walk.comp`, `Walk.length_comp`,
--   `Walk.isDirectedWalk_comp`, `Walk.source_in_G_of_directedWalk_pos`,
--   `Walk.target_in_G_of_directedWalk_pos`,
--   `Walk.singleEdge_directedWalk`, `Walk.lt_of_directedWalk_pos` --
--   is generic infrastructure: it operates on raw
--   `lt : Node → Node → Prop` plus the directed-walk recursion from
--   `def_3_6` and does not mention `IsTopologicalOrder`, so it is
--   unaffected by the predicate's packaging.  See the `## Proof-only
--   helpers` block at the top of the namespace for the documentation.
--
-- *Surface signature minimal.*  Only `(G : CDMG Node)` is hypothesised;
--   no `[Fintype Node]`, no re-stated CDMG-shape constraints, just the
--   chapter-standard `[DecidableEq Node]` binder from the surrounding
--   `variable` line.  Finite `J, V`, `Disjoint J V`, and
--   `E ⊆ (J ∪ V) × V` are baked into the `CDMG` record (`def_3_1`);
--   `[DecidableEq Node]` is what `G.IsAcyclic`'s `Walk.IsDirectedWalk`
--   recursion and `refactor_IsTopologicalOrder`'s `G.Pa w` reference
--   reach through to typecheck.  `[Fintype Node]` was considered (a
--   constructive topological-sort variant of the (⇒) direction can want
--   it locally to enumerate `(G.J ∪ G.V).toList`) and rejected at the
--   statement level: the `Finset`-valued `G.J` / `G.V` already supply
--   finiteness on `J ∪ V` -- exactly the domain on which the order
--   must be total -- so leaking the typeclass into the surface
--   signature would over-constrain consumers for no statement-level
--   gain.
--
-- *Labels `L` absent from both sides.*  `G.IsAcyclic` only inspects
--   directed walks built from `G.E`; `G.refactor_IsTopologicalOrder lt`
--   only references the parent set `Pa^G(w)` (a directed-edge
--   construct from `def_3_5`).  Neither reads `G.L`, matching the LN's
--   silence on labels here -- this is a property of the
--   `(J, V, E)`-skeleton alone.  Chapter 4+ consumers operating on
--   labelled (A)DMGs lose nothing by ignoring `G.L` here; acyclicity
--   and topological order are skeleton-level properties.
--
-- *Known limitation: non-canonical witness.*  The `∃` deliberately
--   does not designate a canonical topological order; many linear
--   refinements of the parent-precedence partial order qualify, and
--   the LN never picks one.  Downstream theorems that need to fix a
--   specific order pass `lt` as an explicit hypothesis or
--   `Classical.choice`-extract from the existential (inheriting the
--   non-canonicality).  This matches the LN's treatment and is
--   intentional, not an API gap.
-- claim_3_2 -- start statement
theorem refactor_acyclic_iff_topological_order (G : CDMG Node) :
    G.IsAcyclic ↔ ∃ lt : Node → Node → Prop, G.refactor_IsTopologicalOrder lt
-- claim_3_2 -- end statement
:= by
  -- TeX proof: tex/refactor_claim_3_2_proof_AcyclicIffTopologicalOrder.tex
  constructor
  · -- (⇒) Acyclic ⇒ a topological order exists.
    --
    -- Following the LN proof: define the reflexive walk-reachability
    -- relation `le₀ u v := u = v ∨ ∃ directed walk u → v of length ≥ 1`,
    -- show it is a partial order (refl/trans via walk concatenation,
    -- antisymm via acyclicity), then apply Mathlib's Szpilrajn
    -- extension (`extend_partialOrder`) to obtain a linear order `s`
    -- extending `le₀`.  Reading `lt u v := s u v ∧ u ≠ v` gives the
    -- strict total order witnessing `IsTopologicalOrder`.
    --
    -- This is a "semantic" Leanification of the LN's inductive
    -- parent-less-pick construction: where the LN picks `v_1, …, v_K`
    -- by hand and reads off the order, we package the same partial
    -- order (walk reachability) and invoke Szpilrajn to do the
    -- enumeration.  The two constructions produce the same kind of
    -- witness (any topological order qualifies; the LN never picks a
    -- canonical one).
    intro hac
    let le₀ : Node → Node → Prop := fun u v =>
      u = v ∨ ∃ p : Walk G u v, p.IsDirectedWalk ∧ p.length ≥ 1
    -- Reflexivity, transitivity, antisymmetry of `le₀`.
    have hrefl : ∀ a, le₀ a a := fun _ => Or.inl rfl
    have htrans : ∀ a b c, le₀ a b → le₀ b c → le₀ a c := by
      intros a b c hab hbc
      rcases hab with heq | ⟨p, hp_dir, hp_len⟩
      · subst heq; exact hbc
      rcases hbc with heq | ⟨q, hq_dir, hq_len⟩
      · subst heq; exact Or.inr ⟨p, hp_dir, hp_len⟩
      · refine Or.inr ⟨p.comp q,
          Walk.isDirectedWalk_comp p q hp_dir hq_dir, ?_⟩
        rw [Walk.length_comp]; omega
    have hantisymm : ∀ a b, le₀ a b → le₀ b a → a = b := by
      intros a b hab hba
      rcases hab with heq | ⟨p, hp_dir, hp_len⟩
      · exact heq
      rcases hba with heq | ⟨q, hq_dir, hq_len⟩
      · exact heq.symm
      · -- Both `p : a → b` and `q : b → a` non-trivial directed walks.
        -- Concatenate to a non-trivial directed walk `a → a`, contradict
        -- acyclicity at `a` (`a ∈ G` from the source of `p`).
        exfalso
        have ha : a ∈ G :=
          Walk.source_in_G_of_directedWalk_pos p hp_dir hp_len
        refine hac a ha ⟨p.comp q,
          Walk.isDirectedWalk_comp p q hp_dir hq_dir, ?_⟩
        rw [Walk.length_comp]; omega
    haveI : Std.Refl le₀ := ⟨hrefl⟩
    haveI : IsTrans Node le₀ := ⟨htrans⟩
    haveI : Std.Antisymm le₀ := ⟨hantisymm⟩
    haveI : IsPreorder Node le₀ := {}
    haveI : IsPartialOrder Node le₀ := {}
    -- Szpilrajn extension: a linear order `s` with `le₀ ≤ s`.
    obtain ⟨s, hs_lo, h_sub⟩ := extend_partialOrder le₀
    -- Promote `hs_lo` to an active typeclass instance so the inherited
    -- `IsTrans` / `Std.Total` / `Std.Antisymm` are resolvable by name
    -- (without `haveI` they sit as a regular hypothesis, invisible to
    -- typeclass synthesis — hence the unification failures otherwise
    -- triggered by `Std.Total.total v w`).
    haveI : IsLinearOrder Node s := hs_lo
    -- The strict version of `s` is our topological order.
    refine ⟨fun u v => s u v ∧ u ≠ v, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- Irreflexivity on `G`: `¬ (s v v ∧ v ≠ v)` from `v ≠ v`.
      intro v _ hlt
      exact hlt.2 rfl
    · -- Transitivity on `G`.
      intros u _ v _ w _ huv hvw
      obtain ⟨hsuv, hne_uv⟩ := huv
      obtain ⟨hsvw, hne_vw⟩ := hvw
      refine ⟨IsTrans.trans u v w hsuv hsvw, ?_⟩
      intro huw
      subst huw
      -- `s u v` and `s v u` with antisymm gives `u = v`, contradicting `hne_uv`.
      exact hne_uv (Std.Antisymm.antisymm u v hsuv hsvw)
    · -- Trichotomy on `G`: from totality of `s`.
      intros v _ w _
      by_cases h : v = w
      · right; left; exact h
      · rcases (Std.Total.total (r := s) v w) with hvw | hwv
        · left; exact ⟨hvw, h⟩
        · right; right; exact ⟨hwv, fun heq => h heq.symm⟩
    · -- Parent precedes: `u ∈ Pa^G(w) → lt u w`.
      intros u w hu_in_Pa
      obtain ⟨hu, huw_E⟩ := hu_in_Pa
      have hw : w ∈ G :=
        Finset.mem_union_right _ (G.hE_subset huw_E).2
      have hle₀_uw : le₀ u w :=
        Or.inr (Walk.singleEdge_directedWalk hw huw_E)
      have hsuw : s u w := h_sub _ _ hle₀_uw
      refine ⟨hsuw, ?_⟩
      intro heq
      subst heq
      -- A self-loop `(u, u) ∈ G.E` would give a length-1 directed walk
      -- `u → u`, contradicting acyclicity at `u`.
      exact hac u hu (Walk.singleEdge_directedWalk hu huw_E)
  · -- (⇐) A topological order ⇒ acyclic.
    --
    -- LN argument: a non-trivial directed walk `v = v_0 → v_1 → ⋯ →
    -- v_n = v` with `n ≥ 1` would give a chain `v_0 < v_1 < ⋯ < v_n =
    -- v_0` under any topological order, contradicting irreflexivity.
    -- Encoded as `Walk.lt_of_directedWalk_pos` above (which uses
    -- parent-precedes and transitivity to walk along edges) and
    -- combined with the topological order's irreflexivity field.
    rintro ⟨lt, ⟨hi, htr, htri⟩, hp⟩
    intro v hv ⟨p, hp_dir, hp_len⟩
    exact hi v hv (Walk.lt_of_directedWalk_pos htr hp p hp_dir hp_len)
-- REFACTOR-BLOCK-REPLACEMENT-END: acyclic_iff_topological_order

end CDMG

end Causality
