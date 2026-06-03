import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder

namespace Causality

/-!
# Acyclic ⟺ admits a topological order: `claim_3_2`

This file formalises the foundational equivalence of `def_3_6`
(acyclicity) and `def_3_8` (existence of a topological order).  Together
with the two predicates themselves, this lemma is the linchpin
chapter-3 result: it lets every downstream consumer that takes
`G.IsAcyclic` as a hypothesis switch to *working with* a topological
order — the form in which chapters 5+ actually use acyclicity (induction
on the topological index, predecessor-based recursion, etc.).
Specifically: `def_3_15`-style acyclification builds a quotient DAG and
extracts a topological order via the forward direction; chapter 8's
iSCM solution-uniqueness proposition `Prp:acyclic_scms_are_simple`
applies this lemma to obtain the iteration index for its
node-by-node solution-construction induction; the FCI completeness
arguments (chapter 11+) likewise pivot from "G is acyclic" to "G has a
topological order" via this equivalence before reasoning about
separation-set enumerations.

## LN block (verbatim)

```
A CDMG  $G=(J,V,E,L)$ is acyclic if and only if it has a topological order.
```

The LN proof (graphs.tex L227-245) runs:
* (⇐)  A directed cycle $v_0 \to \cdots \to v_n = v_0$ would force
       $v_0 < v_1 < \cdots < v_n = v_0$, contradicting irreflexivity.
* (⇒)  Repeatedly select a parentless node in the remaining subgraph;
       since the subgraph is finite and acyclic, such a node exists.

Manager A (this turn) ships the statement only; Manager B will fill the
proof in a subsequent turn.

## Encoding shape (deep design block deferred to `add_design_choice_comments`)

`G.IsAcyclic ↔ ∃ lt : Node → Node → Prop, G.IsTopologicalOrder lt` —
the predicate-form encoding pinned down by the design blocks of
`Acyclicity.lean` (def_3_6) and `TopologicalOrder.lean` (def_3_8).  The
existential mirrors the LN's "has a topological order" noun phrasing
exactly; finiteness of `J ∪ V` (required for the forward direction) is
baked into `CDMG.J / V : Finset Node` via def_3_1's `addition_to_the_LN
[manual_1]`, so the theorem signature carries no separate finiteness
hypothesis.
-/

namespace CDMG

variable {Node : Type*} [DecidableEq Node]

-- ref: claim_3_2
--
-- *Acyclicity ⟺ admits a topological order.*  A CDMG `G` is acyclic
-- iff there exists a strict total order on `G.J ∪ G.V` (a relation
-- `lt : Node → Node → Prop` satisfying `G.IsTopologicalOrder lt`)
-- under which every directed parent precedes its child.  Encoded as
-- a biconditional between the predicate `G.IsAcyclic` (def_3_6) and
-- the existential `∃ lt, G.IsTopologicalOrder lt` (def_3_8).
/-
LN tex (verbatim):

  A CDMG $G=(J,V,E,L)$ is acyclic if and only if it has a topological
  order.
-/
-- ## Design choice
--
-- *Why an existential `∃ lt, G.IsTopologicalOrder lt`, not a
--   structure-equipped CDMG.*  The LN's "has a topological order" is
--   ambiguous between (a) *there exists a topological order on G* and
--   (b) *G comes equipped with a distinguished topological order*.
--   Working-phase wording-check subtlety
--   `has_a_topological_order_existence_vs_equipment` flagged this; we
--   take (a) — the existential.  Topological orders are not unique
--   (any acyclic CDMG with two `Pa`-incomparable vertices admits
--   several valid linearisations of any antichain), so "has a
--   topological order" is naturally a *property* of the bare graph,
--   not a piece of structural data attached to it.  Encoded as a
--   structure (e.g. `Nonempty (TopOrder G)`), the LN-faithful reading
--   would be obscured: the LN's `<` is a *relation*, and the
--   existential binds that same relation directly without record-
--   projection ceremony.  Same paradigm as `def_3_6` ("a CDMG is
--   acyclic" — a property, not a structure).
--
-- *Why a `theorem` (not `def` / `abbrev` / `structure`).*  The
--   statement is a `Prop`-valued biconditional; `theorem` is the
--   canonical Lean shape for an "iff" lemma.  `def` / `abbrev` would
--   be wrong — the declaration is a *proven proposition*, not named
--   data or a notation alias.  The body is `by sorry` at this stage
--   (Manager B will fill the proof in the next turn); the
--   biconditional shape is locked in here.
--
-- *Why `∃ lt : Node → Node → Prop, …`, NOT `∃ lt : {v // v ∈ G.J ∪
--   G.V} → {v // v ∈ G.J ∪ G.V} → Prop, …`.*  The carrier is inherited
--   from `def_3_8` (`IsTopologicalOrder`): a relation on the ambient
--   `Node` type with constraints restricted to `v ∈ G`, NOT a
--   relation on a subtype.  Rationale is recorded in
--   `TopologicalOrder.lean`'s design block: LN-faithfulness ("a total
--   order `<` of `J ∪ V`" reads as a relation on the ambient type with
--   carrier-restricted constraints), composition with `def_3_5`'s
--   `Pa : Node → Finset Node` (subtype lift would need a
--   `Finset`-coercion at every `Pa` lookup), and Mathlib's
--   `LinearOrder` typeclass not being a natural fit on a possibly-
--   empty subtype.  This row inherits that decision; the existential
--   merely lifts the same shape.
--
-- *Finiteness is automatic — both `def_3_8` formulations agree.*  LN
--   wording-check subtlety
--   `claim_finiteness_not_stated_but_required_by_def_3_8` flagged that
--   `def_3_8` gives two formulations of "topological order":
--   (i) a strict total order `<` on `J ∪ V` with parents preceding
--   children, and (ii) an indexing `J ∪ V = {v_1, ..., v_K}` with
--   parents preceding children.  Formulation (ii) only makes literal
--   sense when `J ∪ V` is finite; in the infinite regime, the forward
--   direction under formulation (i) is the Szpilrajn extension
--   theorem and depends on `Choice`.  In our encoding the issue is
--   *dissolved by typing*: `CDMG.J / V : Finset Node` are finite by
--   construction (def_3_1's `addition_to_the_LN [manual_1]` made this
--   a structure field), so `G.J ∪ G.V` is always finite as a `Finset`
--   and the two LN formulations coincide.  No `Choice`-flavoured
--   detour is needed, and no separate finiteness hypothesis appears
--   on the theorem signature.
--
-- *Why no `[Fintype Node]` / `[Finite Node]` typeclass constraint on
--   `Node`.*  Every chapter-3 predicate (`G.IsAcyclic`,
--   `G.IsTopologicalOrder lt`, `G.Pa v`, …) is stated in terms of
--   `G`'s `Finset`-bundled node sets, never the ambient `Node` type.
--   Imposing finiteness on `Node` itself would be a leak: it would
--   propagate to every downstream consumer of `claim_3_2` regardless
--   of whether their `G` touches the whole type.  The chapter
--   convention keeps `Node : Type*` with only `[DecidableEq Node]`
--   (needed for `Finset` membership); this row matches.
--
-- *Bridge role — load-bearing chapter-3 equivalence.*  `claim_3_2` is
--   *the* chapter-3 hinge.  From chapter 4 onward, "acyclic" and "has
--   a topological order" are used interchangeably, and almost every
--   downstream proof that takes `G.IsAcyclic` as a hypothesis funnels
--   through this lemma before doing topological-order induction:
--   `def_3_15`-style acyclification extracts a topological order via
--   the forward direction; chapter-8 `Prp:acyclic_scms_are_simple`
--   obtains the iteration index for its node-by-node
--   solution-construction induction via the same forward direction;
--   the FCI completeness arguments (chapter 11+) pivot from "G is
--   acyclic" to "G has a topological order" before reasoning about
--   separation-set enumerations.  The two directions have very
--   different proof content:
--   * (⇐) **direct** — a directed cycle `v_0 → ... → v_n = v_0`
--     would force `v_0 < v_1 < ... < v_n = v_0`, immediately
--     contradicting irreflexivity of the total-order half.
--   * (⇒) **substantive** — repeatedly select a parentless node in
--     the remaining induced subgraph; finiteness of `G.J ∪ G.V` and
--     acyclicity of the induced subgraph guarantee one exists at
--     each step (otherwise following parent edges would produce a
--     directed cycle, contradicting `G.IsAcyclic`).
--   Manager B will budget proof effort accordingly.
--
-- *Mathlib re-use.*  No direct fit.  Mathlib's
--   `SimpleGraph`/`DiGraph` linearisation results live on undirected
--   or pure-directed graphs without a J/V split or bidirected
--   channel, and quantify a `LinearOrder` on the ambient vertex type
--   rather than a carrier-restricted relation.  The forward
--   direction's "select a parentless node" argument has Mathlib
--   analogues in `Finset.exists_min_image` / `WellFoundedOn`, which
--   Manager B may pull as sub-lemmas, but the overall proof shape
--   (induct on `(G.J ∪ G.V).card`, select a parentless node at each
--   step) is bespoke chapter-3 reasoning that mirrors the LN proof
--   structure verbatim.
--
-- *Constraints / known limitations.*
--   1. **Uniqueness is NOT claimed.**  The existential is purely an
--      existence statement.  Downstream consumers that destructure
--      `∃ lt, G.IsTopologicalOrder lt` bind a *chosen* witness and
--      reason parametrically in it; no uniqueness is ever
--      available.
--   2. **No canonical / algorithmic order is exposed.**  The
--      forward direction produces *some* `lt`; the statement says
--      nothing about whether it is the lexicographic / DFS / Kahn
--      order.  Chapter-8 iSCM iteration uses the indexing form
--      recoverable from `lt` via `Finset.sort lt (G.J ∪ G.V)`,
--      which suffices.
--   3. **No `Decidable` content in the statement.**  The
--      existential produces a `Prop`-level relation; consumers that
--      want `[DecidableRel lt]` add it locally (typically via
--      `Classical.dec`), matching the discipline of `def_3_8`.
--   4. **Empty CDMG is the trivial corner case.**  When
--      `G.J = ∅ ∧ G.V = ∅`, both sides of the iff are vacuously
--      true (no walks → acyclic; any `lt` satisfies the predicate
--      vacuously).  Consistent and unproblematic — flagged here so
--      Manager B's proof doesn't accidentally require a non-empty
--      carrier.
/-! ## Proof helpers (private)

These lemmas underpin the two directions of `claim_3_2`.  They are
*proof-side* helpers, not statement-side, so they sit outside the
`-- claim_3_2 -- start statement` / `-- end statement` markers and
carry no markers of their own.

The (⇐) direction relies on a single lemma chaining the
parents-precede-children axiom along a directed walk.  The (⇒)
direction is bulkier: it builds a list of `G.J ∪ G.V` in topological
order by repeatedly extracting a *source* (a vertex with no parents in
the remaining subgraph), then translates list position into a
`Node → Node → Prop` relation. -/

/-- The source of any walk lies in `G`. -/
private lemma walkSourceMem {G : CDMG Node} :
    ∀ {u v : Node}, Walk G u v → u ∈ G
  | _, _, .nil hv => hv
  | _, _, .cons (.forward h) _ => (G.hE_subset h).1
  | _, _, .cons (.backward h) _ =>
      Finset.mem_union_right _ (G.hE_subset h).2
  | _, _, .cons (.bidir h) _ =>
      Finset.mem_union_right _ (G.hL_subset h).1

/-- The target of any walk lies in `G`. -/
private lemma walkTargetMem {G : CDMG Node} :
    ∀ {u v : Node}, Walk G u v → v ∈ G
  | _, _, .nil hv => hv
  | _, _, .cons _ p => walkTargetMem p

/-- A non-trivial directed walk witnesses `lt u v` under any
topological order.  Induction on `p` — the `nil` case is impossible
(`length = 0`), the `.forward` case discharges via parents-precede +
transitivity (or directly for length-1), and the `.backward / .bidir`
cases reduce `IsDirectedWalk` to `False`. -/
private lemma ltOfDirectedWalkPosLength
    {G : CDMG Node} {lt : Node → Node → Prop} (hlt : G.IsTopologicalOrder lt) :
    ∀ {u v : Node} (p : Walk G u v), p.IsDirectedWalk → 0 < p.length → lt u v := by
  intro u v p
  induction p with
  | nil _ =>
      intro _ hLen
      exact absurd hLen (Nat.lt_irrefl 0)
  | cons e p' ih =>
      intro hDir _
      obtain ⟨⟨_hIrr, hTrans, _hTrich⟩, hPaLt⟩ := hlt
      match e, hDir with
      | .forward h, hDir =>
          -- `hDir : p'.IsDirectedWalk` (definitional).
          have hu_mem : u ∈ G.J ∪ G.V := (G.hE_subset h).1
          have hw_mem : _ ∈ G.J ∪ G.V :=
            Finset.mem_union_right _ (G.hE_subset h).2
          have hu_in_pa : u ∈ G.Pa _ := by
            show u ∈ (G.J ∪ G.V).filter (fun x => (x, _) ∈ G.E)
            exact Finset.mem_filter.mpr ⟨hu_mem, h⟩
          have h_lt_uw : lt u _ := hPaLt hu_in_pa
          by_cases hp'len : 0 < p'.length
          · have h_lt_wv : lt _ v := ih hDir hp'len
            have hv_mem : v ∈ G := walkTargetMem p'
            exact hTrans hu_mem hw_mem hv_mem h_lt_uw h_lt_wv
          · -- `p'.length = 0`, so `p'` is `.nil` and `v` equals the
            -- intermediate vertex.
            push_neg at hp'len
            have hp'_eq : p'.length = 0 := Nat.le_zero.mp hp'len
            match p', hp'_eq with
            | .nil _, _ => exact h_lt_uw
            | .cons _ _, h => simp [Walk.length] at h

/-! ### (⇒) helpers: source existence and topological list -/

/-- A directed walk constructed by chaining "child of" steps `(a (k+1),
a k) ∈ G.E` from `a (i + n)` down to `a i`, with the LN-style
arrowheads all pointing in the walk direction. -/
private def descWalk {G : CDMG Node}
    (a : ℕ → Node) (hE : ∀ k, (a (k + 1), a k) ∈ G.E)
    (i : ℕ) (hAi : a i ∈ G) :
    ∀ n, Walk G (a (i + n)) (a i)
  | 0 => Walk.nil hAi
  | n + 1 =>
      Walk.cons (EdgeStep.forward (hE (i + n))) (descWalk a hE i hAi n)

/-- `descWalk` has length equal to its index argument. -/
private lemma descWalk_length {G : CDMG Node}
    (a : ℕ → Node) (hE : ∀ k, (a (k + 1), a k) ∈ G.E)
    (i : ℕ) (hAi : a i ∈ G) :
    ∀ n, (descWalk a hE i hAi n).length = n
  | 0 => rfl
  | n + 1 => by
      show (descWalk a hE i hAi n).length + 1 = n + 1
      rw [descWalk_length a hE i hAi n]

/-- `descWalk` is a directed walk (every step is `.forward`). -/
private lemma descWalk_isDirected {G : CDMG Node}
    (a : ℕ → Node) (hE : ∀ k, (a (k + 1), a k) ∈ G.E)
    (i : ℕ) (hAi : a i ∈ G) :
    ∀ n, (descWalk a hE i hAi n).IsDirectedWalk
  | 0 => trivial
  | n + 1 => descWalk_isDirected a hE i hAi n

/-- Iterated parent-choice: in a graph where every vertex of `S` has a
parent in `S`, classical choice yields a sequence `a : ℕ → Node` with
`a 0 = v₀`, `a n ∈ S`, and `(a (n + 1), a n) ∈ G.E`. -/
private noncomputable def parentChain {G : CDMG Node} (S : Finset Node)
    (hNoSrc : ∀ v ∈ S, ∃ u ∈ S, (u, v) ∈ G.E)
    (v₀ : Node) (hv₀ : v₀ ∈ S) :
    ℕ → {x : Node // x ∈ S}
  | 0 => ⟨v₀, hv₀⟩
  | n + 1 =>
      let prev := parentChain S hNoSrc v₀ hv₀ n
      ⟨Classical.choose (hNoSrc prev.1 prev.2),
       (Classical.choose_spec (hNoSrc prev.1 prev.2)).1⟩

/-- Each successive `parentChain` step is a parent edge. -/
private lemma parentChain_edge {G : CDMG Node} (S : Finset Node)
    (hNoSrc : ∀ v ∈ S, ∃ u ∈ S, (u, v) ∈ G.E)
    (v₀ : Node) (hv₀ : v₀ ∈ S) (n : ℕ) :
    ((parentChain S hNoSrc v₀ hv₀ (n + 1)).1,
     (parentChain S hNoSrc v₀ hv₀ n).1) ∈ G.E := by
  unfold parentChain
  exact (Classical.choose_spec
    (hNoSrc (parentChain S hNoSrc v₀ hv₀ n).1
      (parentChain S hNoSrc v₀ hv₀ n).2)).2

/-- Source-existence lemma.  In an acyclic CDMG, every nonempty
`Finset Node` contains a vertex with no parents in the finset.

Proof by contradiction + pigeonhole: if every vertex of `S` had a
parent in `S`, iterating choice would build a sequence
`a 0, a 1, …, a |S|` of `|S| + 1` elements all in `S` (cardinality
`|S|`), so by pigeonhole two indices `i < j` agree
(`a i = a j`).  The `descWalk` from `a j` down to `a i` is then a
directed walk of length `j - i ≥ 1` from `a j` to itself,
contradicting `G.IsAcyclic`. -/
private lemma exists_source_of_acyclic
    {G : CDMG Node} (hAcyc : G.IsAcyclic) (S : Finset Node) (hne : S.Nonempty) :
    ∃ v ∈ S, ∀ u ∈ S, (u, v) ∉ G.E := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ v ∈ S, ∃ u ∈ S, (u, v) ∈ G.E`.
  obtain ⟨v₀, hv₀⟩ := hne
  -- Build the parent chain `a : ℕ → {x // x ∈ S}`.
  let a := fun n => parentChain S hcon v₀ hv₀ n
  -- Restrict to `Fin (S.card + 1)`; map into `S` and apply pigeonhole.
  let f : Fin (S.card + 1) → Node := fun i => (a i.val).1
  have hf_mem : ∀ i : Fin (S.card + 1), f i ∈ S := fun i => (a i.val).2
  have hcard : S.card < (Finset.univ : Finset (Fin (S.card + 1))).card := by
    rw [Finset.card_fin]; exact Nat.lt_succ_self _
  obtain ⟨i, _, j, _, hij_ne, hf_eq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.univ)
      (t := S) hcard (fun i _ => hf_mem i)
  -- Without loss of generality, `i.val < j.val`.
  wlog hlt : i.val < j.val with H
  · exact H hAcyc S ⟨v₀, hv₀⟩ hcon v₀ hv₀ a f hf_mem hcard j (Finset.mem_univ _)
      i (Finset.mem_univ _) hij_ne.symm hf_eq.symm
      (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (fun h => hij_ne (Fin.ext h.symm)))
  -- The descWalk witnesses a non-trivial directed cycle at `(a j.val).1`.
  let k := j.val - i.val
  have hki : i.val + k = j.val := by simp [k]; omega
  have hk_pos : 0 < k := Nat.sub_pos_of_lt hlt
  have hAi_in_G : (a i.val).1 ∈ G := hf_mem i
  let p : Walk G (a (i.val + k)).1 (a i.val).1 :=
    descWalk (fun n => (a n).1) (parentChain_edge S hcon v₀ hv₀) i.val
      hAi_in_G k
  -- Rewrite the source via `i.val + k = j.val` so the walk is at `a j.val`.
  have h_src_eq : a (i.val + k) = a j.val := by rw [hki]
  -- Bring it to a walk at `(a j.val).1`.
  have h_cycle_src : (a (i.val + k)).1 = (a j.val).1 := by rw [h_src_eq]
  have hAj_in_G : (a j.val).1 ∈ G := hf_mem j
  -- The endpoints coincide (i.e. it's a cycle) via `f i = f j`.
  have h_target_eq_src : (a i.val).1 = (a j.val).1 := hf_eq
  -- Cast the walk: by `h_target_eq_src` and `h_cycle_src`, both endpoints are `(a j.val).1`.
  have hCycle : ∃ p : Walk G (a j.val).1 (a j.val).1,
      p.IsDirectedWalk ∧ 0 < p.length := by
    -- Use `h_cycle_src` and `h_target_eq_src` to rewrite the type of `p`.
    refine ⟨h_cycle_src ▸ h_target_eq_src ▸ p, ?_, ?_⟩
    · -- After casts, `IsDirectedWalk` is preserved.
      have := descWalk_isDirected (fun n => (a n).1)
        (parentChain_edge S hcon v₀ hv₀) i.val hAi_in_G k
      -- Coerce through the rewrites.
      subst h_cycle_src
      subst h_target_eq_src
      exact this
    · -- length k > 0.
      have := descWalk_length (fun n => (a n).1)
        (parentChain_edge S hcon v₀ hv₀) i.val hAi_in_G k
      subst h_cycle_src
      subst h_target_eq_src
      rw [this]; exact hk_pos
  exact hAcyc (a j.val).1 hAj_in_G hCycle

/-- Existence of a topologically-sorted list for any subset
`S ⊆ G.J ∪ G.V` (with `G.IsAcyclic`).  Proof by strong induction on
`Finset.card`: at the inductive step, extract a source `v` of `S` via
`exists_source_of_acyclic`, prepend `v`, and recurse on `S.erase v`. -/
private lemma exists_topoSortedList
    {G : CDMG Node} (hAcyc : G.IsAcyclic) (S : Finset Node)
    (hSub : S ⊆ G.J ∪ G.V) :
    ∃ l : List Node, l.Nodup ∧ l.toFinset = S ∧
      ∀ u ∈ S, ∀ w ∈ S, (u, w) ∈ G.E → l.idxOf u < l.idxOf w := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hne : S.Nonempty
    · obtain ⟨v, hv, hNoPa⟩ := exists_source_of_acyclic hAcyc S hne
      have herase_card : (S.erase v).card < n := by
        rw [Finset.card_erase_of_mem hv, ← hn]; exact Nat.sub_lt (Finset.card_pos.mpr hne) one_pos
      have hSub' : S.erase v ⊆ G.J ∪ G.V :=
        (Finset.erase_subset v S).trans hSub
      obtain ⟨l_rest, hl_nodup, hl_finset, hl_ord⟩ :=
        ih (S.erase v).card herase_card (S.erase v) hSub' rfl
      refine ⟨v :: l_rest, ?_, ?_, ?_⟩
      · -- Nodup
        refine List.nodup_cons.mpr ⟨?_, hl_nodup⟩
        intro hv_in
        have : v ∈ S.erase v := by
          rw [← hl_finset, List.mem_toFinset]; exact hv_in
        exact (Finset.not_mem_erase v S) this
      · -- toFinset
        rw [List.toFinset_cons, hl_finset, Finset.insert_erase hv]
      · -- order property
        intro u hu w hw hEdge
        by_cases hu_eq_v : u = v
        · -- u = v ∈ head; w must come later (and `w ≠ v` since
          --  `(v, v) ∈ G.E` would be a directed self-loop).
          subst hu_eq_v
          have hw_ne_u : w ≠ u := by
            intro h_eq
            subst h_eq
            have hu_g : u ∈ G := hSub hu
            apply hAcyc u hu_g
            refine ⟨Walk.cons (EdgeStep.forward hEdge) (Walk.nil hu_g), ?_, ?_⟩
            · exact trivial
            · show 0 < (Walk.nil hu_g).length + 1; omega
          have hw_in_erase : w ∈ S.erase v :=
            Finset.mem_erase.mpr ⟨hw_ne_u, hw⟩
          have hw_in_l_rest : w ∈ l_rest := by
            rw [← List.mem_toFinset, hl_finset]; exact hw_in_erase
          show (u :: l_rest).idxOf u < (u :: l_rest).idxOf w
          rw [List.idxOf_cons_self]
          have : (u :: l_rest).idxOf w = l_rest.idxOf w + 1 := by
            rw [List.idxOf_cons]; simp [hw_ne_u.symm]
          rw [this]
          exact Nat.succ_pos _
        · -- u ≠ v.  Either w = v (contradicts source) or both in erase.
          by_cases hw_eq_v : w = v
          · subst hw_eq_v
            exact absurd hEdge (hNoPa u hu)
          · have hu_in_erase : u ∈ S.erase v :=
              Finset.mem_erase.mpr ⟨hu_eq_v, hu⟩
            have hw_in_erase : w ∈ S.erase v :=
              Finset.mem_erase.mpr ⟨hw_eq_v, hw⟩
            have h_idx_rest := hl_ord u hu_in_erase w hw_in_erase hEdge
            have hu_idx : (v :: l_rest).idxOf u = l_rest.idxOf u + 1 := by
              rw [List.idxOf_cons]; simp [hu_eq_v]
            have hw_idx : (v :: l_rest).idxOf w = l_rest.idxOf w + 1 := by
              rw [List.idxOf_cons]; simp [hw_eq_v]
            rw [hu_idx, hw_idx]
            exact Nat.add_lt_add_right h_idx_rest 1
    · -- S empty: list is [].
      refine ⟨[], List.nodup_nil, ?_, ?_⟩
      · rw [List.toFinset_nil]
        exact (Finset.not_nonempty_iff_eq_empty.mp hne).symm
      · intro u hu
        exact absurd hu (by
          have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
          rw [this]; exact Finset.not_mem_empty u)

-- claim_3_2 -- start statement
theorem isAcyclic_iff_exists_topologicalOrder (G : CDMG Node) :
    G.IsAcyclic ↔ ∃ lt : Node → Node → Prop, G.IsTopologicalOrder lt
-- claim_3_2 -- end statement
:= by
  classical
  refine ⟨?_, ?_⟩
  · -- (⇒) acyclic ⟹ topological order exists.
    intro hAcyc
    obtain ⟨l, hl_nodup, hl_finset, hl_ord⟩ :=
      exists_topoSortedList hAcyc (G.J ∪ G.V) Finset.Subset.rfl
    refine ⟨fun u v => l.idxOf u < l.idxOf v, ?_, ?_⟩
    · -- `IsTotalOrderOn`: irreflexivity, transitivity, trichotomy.
      refine ⟨?_, ?_, ?_⟩
      · intro v _hv
        exact Nat.lt_irrefl _
      · intro u v w _hu _hv _hw huv hvw
        exact Nat.lt_trans huv hvw
      · intro v w hv hw
        have hv_in_l : v ∈ l := by rw [← List.mem_toFinset, hl_finset]; exact hv
        have hw_in_l : w ∈ l := by rw [← List.mem_toFinset, hl_finset]; exact hw
        rcases Nat.lt_trichotomy (l.idxOf v) (l.idxOf w) with hlt | heq | hgt
        · exact Or.inl hlt
        · -- equal indices ⟹ same element (using Nodup).
          right; left
          have hv_lt : l.idxOf v < l.length := List.idxOf_lt_length_iff.mpr hv_in_l
          have hw_lt : l.idxOf w < l.length := List.idxOf_lt_length_iff.mpr hw_in_l
          have : l[l.idxOf v] = l[l.idxOf w] := by rw [heq]
          rwa [List.getElem_idxOf hv_lt, List.getElem_idxOf hw_lt] at this
        · exact Or.inr (Or.inr hgt)
    · -- parents-precede-children clause.
      intro v w hv_pa
      -- `v ∈ G.Pa w` means `v ∈ G.J ∪ G.V ∧ (v, w) ∈ G.E`.
      rw [CDMG.Pa, Finset.mem_filter] at hv_pa
      obtain ⟨hv_g, hEdge⟩ := hv_pa
      have hw_g : w ∈ G.J ∪ G.V :=
        Finset.mem_union_right _ (G.hE_subset hEdge).2
      exact hl_ord v hv_g w hw_g hEdge
  · -- (⇐) topological order exists ⟹ acyclic.
    rintro ⟨lt, hlt⟩ v hv ⟨p, hpDir, hpLen⟩
    have h_lt_vv : lt v v := ltOfDirectedWalkPosLength hlt p hpDir hpLen
    exact hlt.1.1 v hv h_lt_vv

end CDMG

end Causality
