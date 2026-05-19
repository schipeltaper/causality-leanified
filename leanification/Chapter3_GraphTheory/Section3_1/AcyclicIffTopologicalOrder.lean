import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Set.Card
import Mathlib.Logic.Relation
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- The verbatim TeX source of the LN claim is reproduced inside the
-- comments below; some of its lines exceed 100 characters. Disable the
-- style linter for this file so the TeX is kept byte-for-byte identical
-- to `Section3_1/main.tex`.
set_option linter.style.longLine false

/-!
# claim_3_2 — Acyclic ⇔ has a topological order

The second LN claim of subsection 3.1 states the central bridge between
`def_3_6` (acyclicity) and `def_3_8` (topological order): a CDMG is
acyclic if and only if it admits a topological order.

The verified TeX proof is in
`Section3_1/tex_proofs/claim_3_2_AcyclicIffTopologicalOrder.tex`; this
file translates it into Lean tactics.

We share the `Causality.Chapter3` namespace with `def_3_1`–`def_3_8`.
-/

namespace Causality
namespace Chapter3

variable {J V : Type*}

/-! ## Walk concatenation helpers

The TeX proof's (⇒) direction needs to glue together one-step directed
walks (each parent edge) into a longer directed walk that closes back
on itself; we expose `Walk.append` and a `DirectedWalk` closure lemma
locally for that purpose. These helpers are not LN-faceted — they are
elementary list-style operations on `Walk` — so they live as `private`
declarations in this file rather than as separate `data.json` rows.
-/

-- Concatenate two walks. Mirrors `List.append` on the underlying
-- step sequence.
private def CDMG.Walk.append {G : CDMG J V} :
    ∀ {u v w : J ⊕ V}, Walk G u v → Walk G v w → Walk G u w
  | _, _, _, Walk.nil _,      q => q
  | _, _, _, Walk.cons s p,   q => Walk.cons s (Walk.append p q)

-- `stepKinds` of an appended walk is the `++` of the step-kind lists.
private lemma CDMG.Walk.append_stepKinds {G : CDMG J V} :
    ∀ {u v w : J ⊕ V} (p : Walk G u v) (q : Walk G v w),
      (CDMG.Walk.append p q).stepKinds = p.stepKinds ++ q.stepKinds
  | _, _, _, Walk.nil _,    _ => by
      simp [CDMG.Walk.append, Walk.stepKinds]
  | _, _, _, Walk.cons s p, q => by
      simp [CDMG.Walk.append, Walk.stepKinds, CDMG.Walk.append_stepKinds p q]

-- The concatenation of two `DirectedWalk`s is again a `DirectedWalk`.
private lemma CDMG.DirectedWalk.append {G : CDMG J V} {u v w : J ⊕ V}
    {p : Walk G u v} {q : Walk G v w}
    (hp : G.DirectedWalk p) (hq : G.DirectedWalk q) :
    G.DirectedWalk (CDMG.Walk.append p q) := by
  intro k hk
  rw [CDMG.Walk.append_stepKinds] at hk
  rcases List.mem_append.mp hk with h | h
  · exact hp k h
  · exact hq k h

-- A parent edge gives a one-step directed walk.
-- Unfolds `def_3_5`'s `Pa^G(v) = { w | ∃ v' : V, v = Sum.inr v' ∧ G.tuh w v' }`
-- to the single `WalkStep.out` constructor.
private lemma CDMG.directedWalk_of_parent {G : CDMG J V} {u v : J ⊕ V}
    (h : u ∈ G.Pa v) : ∃ p : Walk G u v, G.DirectedWalk p := by
  obtain ⟨v', rfl, htuh⟩ := h
  refine ⟨Walk.cons (WalkStep.out htuh) (Walk.nil _), ?_⟩
  intro k hk
  simp [Walk.stepKinds, WalkStep.kind] at hk
  exact hk

/-! ## (⇐) direction: topological order ⇒ acyclic

Mirrors the (⇐) paragraph of the TeX proof: a directed walk
`v_0 ⟶ v_1 ⟶ ⋯ ⟶ v_n` gives a strict chain `v_0 < v_1 < ⋯ < v_n`
under any topological order; if the walk is non-trivial and closes
(`v_n = v_0`), we contradict irreflexivity of `<`.
-/

-- Helper: under a topological order `T`, any directed walk from `u`
-- to `w` forces `u ≤ w` in `T`'s order. Strict in the `cons` case
-- (handled inside, by `T.parent_lt`).
private lemma CDMG.TopologicalOrder.le_of_directedWalk
    {G : CDMG J V} (T : G.TopologicalOrder) :
    ∀ {u w : J ⊕ V} (p : Walk G u w), G.DirectedWalk p →
      T.toLinearOrder.le u w := by
  letI : LinearOrder (J ⊕ V) := T.toLinearOrder
  intro u w p
  induction p with
  | nil v => intro _; exact le_refl v
  | @cons u' v' w' s rest ih =>
    intro hp
    have hsout : s.kind = StepKind.out :=
      hp s.kind (List.mem_cons_self)
    have hrest : G.DirectedWalk rest := fun k hk =>
      hp k (List.mem_cons_of_mem _ hk)
    have hu_lt : u' < v' := by
      cases s with
      | out h => exact T.parent_lt ⟨_, rfl, h⟩
      | inn _ => simp [WalkStep.kind] at hsout
      | bid _ => simp [WalkStep.kind] at hsout
    exact le_of_lt (lt_of_lt_of_le hu_lt (ih hrest))

private lemma CDMG.isAcyclic_of_nonempty_topologicalOrder
    {G : CDMG J V} (hT : Nonempty G.TopologicalOrder) : G.IsAcyclic := by
  obtain ⟨T⟩ := hT
  letI : LinearOrder (J ⊕ V) := T.toLinearOrder
  intro v p hp
  cases p with
  | nil _ => rfl
  | @cons _ v' _ s rest =>
    exfalso
    have hsout : s.kind = StepKind.out :=
      hp s.kind (List.mem_cons_self)
    have hrest : G.DirectedWalk rest := fun k hk =>
      hp k (List.mem_cons_of_mem _ hk)
    have hv_lt : v < v' := by
      cases s with
      | out h => exact T.parent_lt ⟨_, rfl, h⟩
      | inn _ => simp [WalkStep.kind] at hsout
      | bid _ => simp [WalkStep.kind] at hsout
    have hv'_le : v' ≤ v := T.le_of_directedWalk rest hrest
    exact lt_irrefl _ (lt_of_lt_of_le hv_lt hv'_le)

/-! ## (⇒) direction: acyclic ⇒ topological order

The TeX proof builds the order by iteratively extracting a parent-less
node from the remaining set. We translate this to:

1. Define `parentRel G : (J⊕V) → (J⊕V) → Prop` by `parentRel G u v ↔
   u ∈ G.Pa v` (i.e. `u` is a parent of `v` — there is an edge
   `u ⟶ v`).
2. Show `Relation.TransGen (parentRel G)` is irreflexive (the TeX
   proof's pigeonhole/cycle argument, rephrased: any `TransGen`-cycle
   gives a non-trivial directed walk back to a vertex, contradicting
   acyclicity).
3. Define `topoRank v` as the *number of strict ancestors of `v`*
   (where "strict ancestor" = `TransGen parentRel`-predecessor). Then
   `u ∈ G.Pa v ⟹ topoRank u < topoRank v`: strict ancestors of `u`
   are also strict ancestors of `v` (transitivity), `u` itself is a
   strict ancestor of `v` (by `TransGen.single`) but not of itself
   (step 2), so the strict-ancestor set grows by at least one. This
   substitutes the LN's iterative source-extraction with a one-shot
   cardinality argument — the *strategy* is identical (pigeonhole on
   the finite ancestor set), only the bookkeeping is collapsed.
4. Combine `topoRank` with `Fintype.equivFin` (a noncomputable
   bijection with `Fin (card (J ⊕ V))`) into a single injective
   `ℕ`-valued key, and use `LinearOrder.lift'` to obtain a
   `LinearOrder (J ⊕ V)`. Verify `parent_lt` from the rank inequality.

This requires the finiteness of `J` and `V` (`Fintype J`, `Fintype V`)
— same hypothesis as in the LN proof ("`K := |N|` is finite since
both `J` and `V` are finite by `def_3_1`"). See the design-choice
block at the top of the theorem for the manager-facing flag on this.
-/

-- "Parent of" as a relation. `parentRel G u v` iff `u ∈ G.Pa v`,
-- i.e. there is a directed edge `u ⟶ v` in `G`.
private def CDMG.parentRel (G : CDMG J V) (u v : J ⊕ V) : Prop :=
  u ∈ G.Pa v

-- A `TransGen parentRel` chain unfolds to a directed walk with at
-- least one step. This is the key bridge from the relational picture
-- to `IsAcyclic` — note we phrase non-triviality via
-- `p.stepKinds ≠ []` rather than `p ≠ Walk.nil _` because the latter
-- is ill-typed when `u ≠ v` (`Walk.nil` forces equal endpoints).
private lemma CDMG.directedWalk_stepKinds_ne_nil_of_transGen {G : CDMG J V}
    {u v : J ⊕ V} (h : Relation.TransGen (CDMG.parentRel G) u v) :
    ∃ p : Walk G u v, G.DirectedWalk p ∧ p.stepKinds ≠ [] := by
  induction h with
  | single huv =>
      obtain ⟨v', rfl, htuh⟩ := huv
      refine ⟨Walk.cons (WalkStep.out htuh) (Walk.nil _), ?_, ?_⟩
      · intro k hk
        simp [Walk.stepKinds, WalkStep.kind] at hk
        exact hk
      · simp [Walk.stepKinds]
  | tail _ huv ih =>
      obtain ⟨p, hp_dir, hp_ne⟩ := ih
      obtain ⟨v', rfl, htuh⟩ := huv
      -- Manually attach the final one-step walk so we keep `stepKinds`
      -- inspectable (instead of routing through `directedWalk_of_parent`,
      -- which would hide the structure of the last step).
      refine ⟨CDMG.Walk.append p
                (Walk.cons (WalkStep.out htuh) (Walk.nil _)), ?_, ?_⟩
      · apply CDMG.DirectedWalk.append hp_dir
        intro k hk
        simp [Walk.stepKinds, WalkStep.kind] at hk
        exact hk
      · rw [CDMG.Walk.append_stepKinds]
        intro habs
        exact hp_ne (List.append_eq_nil_iff.mp habs).1

-- Consequently `TransGen parentRel` is irreflexive on an acyclic CDMG.
private lemma CDMG.transGen_parentRel_irrefl {G : CDMG J V}
    (hac : G.IsAcyclic) :
    ∀ v, ¬ Relation.TransGen (CDMG.parentRel G) v v := by
  intro v hv
  obtain ⟨p, hp_dir, hp_ne⟩ :=
    CDMG.directedWalk_stepKinds_ne_nil_of_transGen hv
  have hpnil : p = Walk.nil v := hac v p hp_dir
  apply hp_ne
  rw [hpnil]
  rfl

section ImpliesFinite

-- The (⇒) direction needs `J ⊕ V` to be finite (the TeX proof's
-- pigeonhole/cardinality argument). We take `Finite` rather than
-- `Fintype` because the proof is intrinsically non-computable —
-- `Set.ncard` (used to define `topoRank`) and `Fintype.equivFin`
-- (used to break ties in the linear order) are happy with
-- `Finite + Classical`. Calling code may supply `[Fintype J]
-- [Fintype V]` and Mathlib will derive the `Finite` instances.
variable [Finite J] [Finite V]

-- `topoRank v` = number of *strict* ancestors of `v`, where "strict
-- ancestor" = `TransGen parentRel`-predecessor. Using `Set.ncard`
-- (cardinality-as-`ℕ`) keeps us off the `DecidablePred` treadmill —
-- `Set.ncard` returns the cardinality whenever the set is finite,
-- which it always is here because `J ⊕ V` is finite.
private noncomputable def CDMG.topoRank (G : CDMG J V) (v : J ⊕ V) : ℕ :=
  Set.ncard { u | Relation.TransGen (CDMG.parentRel G) u v }

-- The key rank inequality: a parent has strictly smaller rank.
-- Mirrors the TeX proof's pigeonhole/cycle step, but collapsed: rather
-- than iteratively extracting sources, we observe that the strict-
-- ancestor set of `u` is contained in that of `v` (transitivity), and
-- additionally misses `u` itself (by `transGen_parentRel_irrefl`),
-- while the strict-ancestor set of `v` contains `u`. Hence the latter
-- has strictly more elements.
private lemma CDMG.topoRank_lt_of_parent (G : CDMG J V)
    (hac : G.IsAcyclic) {u v : J ⊕ V} (h : u ∈ G.Pa v) :
    G.topoRank u < G.topoRank v := by
  have hAv_fin :
      ({ w | Relation.TransGen (CDMG.parentRel G) w v } : Set (J ⊕ V)).Finite :=
    Set.toFinite _
  -- strict ancestors of u ⊆ strict ancestors of v (by TransGen.tail)
  have hsub :
      { w | Relation.TransGen (CDMG.parentRel G) w u } ⊆
      { w | Relation.TransGen (CDMG.parentRel G) w v } := by
    intro w hw
    exact hw.tail h
  -- u is a strict ancestor of v (TransGen.single)
  have hu_mem_v : u ∈ { w | Relation.TransGen (CDMG.parentRel G) w v } :=
    Relation.TransGen.single h
  -- u is not a strict ancestor of u (acyclicity)
  have hu_notin_u : u ∉ { w | Relation.TransGen (CDMG.parentRel G) w u } :=
    CDMG.transGen_parentRel_irrefl hac u
  -- Hence the inclusion is strict
  have hssub :
      { w | Relation.TransGen (CDMG.parentRel G) w u } ⊂
      { w | Relation.TransGen (CDMG.parentRel G) w v } := by
    refine ⟨hsub, ?_⟩
    intro habs
    exact hu_notin_u (habs hu_mem_v)
  exact Set.ncard_lt_ncard hssub hAv_fin

-- Build the topological order. Strategy:
-- * `n := card (J ⊕ V)`, `e : (J⊕V) ≃ Fin n` (noncomputable choice).
-- * `f v := topoRank v * n + (e v).val` is injective (different
--   `topoRank`s sit in different "buckets" of width `n`, and within a
--   bucket `e` is injective).
-- * Lift `LinearOrder ℕ` to `J ⊕ V` along `f` (`LinearOrder.lift'`).
-- * `parent_lt` follows from `topoRank_lt_of_parent` plus the same
--   bucket argument.
private noncomputable def CDMG.topologicalOrderOfAcyclic
    (G : CDMG J V) (hac : G.IsAcyclic) : G.TopologicalOrder := by
  classical
  -- `Fintype.equivFin` below needs `Fintype`; derive it from `Finite`.
  haveI : Fintype (J ⊕ V) := Fintype.ofFinite _
  set n := Fintype.card (J ⊕ V) with hn
  let e : (J ⊕ V) ≃ Fin n := Fintype.equivFin (J ⊕ V)
  let f : (J ⊕ V) → ℕ := fun v => G.topoRank v * n + (e v).val
  have hf_inj : Function.Injective f := by
    intro a b hab
    -- Unfold f in hab.
    change G.topoRank a * n + (e a).val = G.topoRank b * n + (e b).val at hab
    have h_ea : (e a).val < n := (e a).isLt
    have h_eb : (e b).val < n := (e b).isLt
    -- First: ranks are equal.
    have h₁ : G.topoRank a = G.topoRank b := by
      rcases lt_trichotomy (G.topoRank a) (G.topoRank b) with hlt | heq | hgt
      · exfalso
        have hexp : (G.topoRank a + 1) * n = G.topoRank a * n + n := by ring
        have hmul : (G.topoRank a + 1) * n ≤ G.topoRank b * n :=
          Nat.mul_le_mul_right n hlt
        linarith
      · exact heq
      · exfalso
        have hexp : (G.topoRank b + 1) * n = G.topoRank b * n + n := by ring
        have hmul : (G.topoRank b + 1) * n ≤ G.topoRank a * n :=
          Nat.mul_le_mul_right n hgt
        linarith
    -- Then: e-images are equal.
    have h₂ : (e a).val = (e b).val := by
      have hrk : G.topoRank a * n = G.topoRank b * n := by rw [h₁]
      linarith
    exact e.injective (Fin.ext h₂)
  let lo : LinearOrder (J ⊕ V) := LinearOrder.lift' f hf_inj
  refine { toLinearOrder := lo, parent_lt := ?_ }
  intro u v huv
  -- Goal: lo.lt u v. By definition of `LinearOrder.lift'` this is `f u < f v`.
  change f u < f v
  have hrank : G.topoRank u < G.topoRank v :=
    CDMG.topoRank_lt_of_parent G hac huv
  have h_eu : (e u).val < n := (e u).isLt
  have h_ev : (e v).val < n := (e v).isLt
  -- f u < (topoRank u + 1) * n ≤ topoRank v * n ≤ f v
  have hexp : (G.topoRank u + 1) * n = G.topoRank u * n + n := by ring
  have hmul : (G.topoRank u + 1) * n ≤ G.topoRank v * n :=
    Nat.mul_le_mul_right n hrank
  change G.topoRank u * n + (e u).val < G.topoRank v * n + (e v).val
  linarith

end ImpliesFinite

/-! ## Main theorem (`claim_3_2`) -/

/-
Source (verbatim from `Section3_1/main.tex`, under `% claim_3_2`):

\begin{claimmark}
\begin{Lem}
        A CDMG  $G=(J,V,E,L)$ is acyclic if and only if it has a topological order.
\end{Lem}
\end{claimmark}
-/

-- claim_3_2 — a CDMG is acyclic iff it admits a topological order.
--
-- TeX proof: tex_proofs/claim_3_2_AcyclicIffTopologicalOrder.tex
--
-- LN fragment:
-- /- A CDMG `G = (J, V, E, L)` is acyclic if and only if it has a
--    topological order. -/
--
-- The biconditional splits into two directions:
--   • (⇒) Acyclic ⇒ admits a topological order. Informally: with no
--     directed cycles, one can repeatedly pick a "source" node (no
--     incoming parent edges among the unpicked) and append it to the
--     end of the order; the resulting linear order satisfies
--     `v ∈ Pa(w) ⟹ v < w`. *This direction relies on the
--     finiteness of `J` and `V`* — the TeX proof's pigeonhole on
--     `R_i ⊆ J ⊕ V` only goes through when `J ⊕ V` is finite. The
--     `[Fintype J] [Fintype V]` hypotheses below were therefore
--     added (manager-flagged); see the finiteness-tension note in
--     the design-choice block immediately above this theorem.
--   • (⇐) Has a topological order ⇒ acyclic. Informally: any directed
--     walk from `v` back to `v` would, by `parent_lt` applied step by
--     step (each step is a parent → child edge by the definition of
--     `DirectedWalk` chained through `Pa`), give a strictly increasing
--     chain from `v` to `v` under `<`, contradicting irreflexivity of
--     `<`. Hence the only directed walk from `v` to `v` is `Walk.nil v`.
--     This direction *does not* use finiteness.
--
-- Design choice — `Nonempty G.TopologicalOrder` as the encoding of
-- "has a topological order". The LN phrasing "*has* a topological
-- order" is an existential: *there exists* a total order on `J ∪ V`
-- with the parent-precedes-child property. The structure
-- `G.TopologicalOrder` (see `TopologicalOrder.lean` lines 50–62) was
-- deliberately introduced as data — `LinearOrder (J ⊕ V)` bundled with
-- the `parent_lt` axiom — so that the existence statement collapses to
-- the single propositional `Nonempty G.TopologicalOrder`, without
-- having to existentially quantify over `LinearOrder (J ⊕ V)` and the
-- parent-precedes-child property separately. The `TopologicalOrder.lean`
-- design-choice block already anticipates this exact use; we honour it
-- here.
--
-- Design choice — one biconditional, not two separate lemmas.
-- LN states `claim_3_2` as a single iff, and the two directions share
-- the same hypotheses (`G : CDMG J V` only). Bundling them as one
-- `↔`-shaped lemma keeps the Lean statement in lockstep with the LN
-- statement (rule 1 of the project's "stay close to the lecture
-- notes"). Downstream consumers that only need one direction can
-- `.mp` / `.mpr` at the call site, which is the standard Lean idiom.
-- Internally we *do* split into two named auxiliary lemmas
-- (`isAcyclic_of_nonempty_topologicalOrder` and
-- `topologicalOrderOfAcyclic`) — see the `private` declarations
-- above — to make the iff proof a one-line combination.
--
-- Design choice — `[Fintype J] [Fintype V]` hypotheses. The LN
-- statement is unconditional (input/output vertex sets are typed but
-- not declared finite at `def_3_1`-time), but the standard textbook
-- proof of (⇒) — including the verified TeX proof in
-- `tex_proofs/claim_3_2_AcyclicIffTopologicalOrder.tex` — uses
-- `K := |J ∪ V| < ∞` essentially: the iterative source-extraction
-- argument peels off `K` sources, and the inner pigeonhole-on-cycle
-- step needs `R_i ⊆ J ∪ V` to be finite. The Lean-level proof
-- below collapses these into one cardinality argument
-- (rank-by-strict-ancestor-count), which still requires the
-- ambient `(J ⊕ V)` to be finite. We flag this addition to the
-- manager: the LN's `def_3_1` introduces `J` and `V` without
-- finiteness, so this is a strengthening of the public statement
-- with hypotheses that match the proof's intrinsic requirement.
-- Without `Fintype`, the LN's strategy fails; an order-extension
-- (Szpilrajn / well-orderings) argument would be needed for the
-- infinite case, which is not what the LN does.
theorem CDMG.acyclic_iff_topologicalOrder [Finite J] [Finite V]
    (G : CDMG J V) : G.IsAcyclic ↔ Nonempty G.TopologicalOrder := by
  refine ⟨fun hac => ⟨G.topologicalOrderOfAcyclic hac⟩, ?_⟩
  exact CDMG.isAcyclic_of_nonempty_topologicalOrder

end Chapter3
end Causality
