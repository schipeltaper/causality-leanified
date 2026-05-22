import Chapter3_GraphTheory.Section3_2.Marginalization
import Chapter3_GraphTheory.Section3_1.FamilyReachability
import Chapter3_GraphTheory.Section3_1.Acyclicity
import Chapter3_GraphTheory.Section3_1.TopologicalOrder

-- TeX statement: tex/claim_3_16_statement_MarginalizationPreserves.tex
-- TeX proof:    tex/claim_3_16_proof_MarginalizationPreserves.tex (to be written)

/-!
# Marginalization preserves ancestral relations, bifurcations, acyclicity (claim_3_16)

This file formalises the lecture notes' remark
`rem:marg_preserves_ancestors_bifurcations_acyclicity`
(`lecture-notes/lecture_notes/graphs.tex` around line 964, the
`\begin{Rem}\label{rem:marg_preserves_ancestors_bifurcations_acyclicity}`
claimmark) for a CDMG `G = (J, V, E, L)` and a set `W ⊆ α` of output
nodes. The remark bundles *three* structural preservation properties
of marginalization (def_3_14, `Section3_2/Marginalization.lean`):

1. **Ancestors** -- for `v_1, v_2 ∉ W`,
   `v_1 ∈ Anc^G(v_2)  ↔  v_1 ∈ Anc^{G^{\sm W}}(v_2)`.
2. **Bifurcations** -- for `v_1, v_2 ∈ G \ W` (and, optionally, a
   third `v_3 ∈ G \ W` named as the *source*), there is a bifurcation
   between `v_1` and `v_2` (with source `v_3`) in `G` iff there is one
   in `G^{\sm W}`. The LN's "between" reading is symmetric, which we
   carry through to Lean via the disjunction-of-both-walk-directions
   reading (see the `Marginalization.lean` design block on
   `mem_marginalize_L` and risk §5.2 of
   `workspace_claim_3_16.md`).
3. **Acyclicity and topological orders** -- if `G` is acyclic, so is
   `G^{\sm W}`; and any topological order of `G` is a topological
   order of `G^{\sm W}` (by just ignoring the nodes from `W`).

## Scope of this file (formalize-phase, statements only)

This file currently holds **four** theorems, each with `:= sorry` for
the proof body. Item 2 is split into a *no-source* variant (here) and
a *with-source* variant (deferred to a follow-up dispatch, see risk
§5.2 in `workspace_claim_3_16.md`):

* `marginalize_anc_iff`            — item 1.
* `marginalize_bifurcation_iff`    — item 2 (no source).
* `marginalize_isAcyclic`          — item 3a (acyclicity).
* `marginalize_isTopologicalOrder` — item 3b (topological order).

The with-source variant (`marginalize_bifurcation_source_iff`) is
intentionally absent: the `L^{\sm W}` exclusion clause in
`mem_marginalize_L` can turn a bidir-hinge bifurcation in `G`
(no source) into a backward-hinge bifurcation in `G^{\sm W}` (with
source), which complicates the LN's "(with source `v_3`)"
preservation in subtle ways. We defer the with-source statement until
the no-source proof has surfaced the exclusion-clause friction
concretely. See risk §5.2 in `workspace_claim_3_16.md` for the
recommended mitigation candidates (R1–R3).

## Why we do *not* introduce `Walk.IsBifurcationWithSource` here

The workspace plan §1 calls for a helper predicate
`Walk.IsBifurcationWithSource π v₃` to support the with-source
biconditional cleanly (avoiding the `Classical.choice` fragility of
`bifurcationSource`). That helper most naturally lives in
`Section3_1/Bifurcation.lean` alongside `Walk.IsBifurcation` and
`Walk.bifurcationSource`. Adding it touches a different subsection,
which `claude.md` rule 4 reserves for manager approval. Since we are
also deferring theorem 3 to a follow-up dispatch, we punt the helper
to that dispatch too: it is the natural place to ask the manager
whether to land the helper in `Bifurcation.lean` (cleaner long-term,
since claim_3_17 / 3_18 / 3_19 will likely want it) or to define it
locally in the with-source theorem's file. Flagged in the formalizer's
report-back.

## Why the LN remark is split into four Lean theorems

A single bundled `Prop` ("all three preservation properties hold")
would force every consumer to destructure or to chain irrelevant
hypotheses (e.g. the topological-order half quoted by chapter 5's
do-calculus has no need for the bifurcation conjunct). We split:

* by sub-item, because downstream consumers cite different parts
  separately (claim_3_17 quotes items 1 + 2; claim_3_18 / 3_19 and
  chapter 4 quote item 3a; chapter 5 quotes item 3b);
* within item 2, into no-source / with-source variants because the
  with-source refinement interacts non-trivially with the
  `L^{\sm W}`-exclusion (risk §5.2) while the no-source variant
  absorbs the exclusion cleanly via the symmetric-`∨` reading of
  bifurcation existence;
* within item 3, into acyclicity / topological order because the two
  are logically independent — item 3a is provable directly by walk
  concatenation without going through claim_3_2 (avoiding a
  circular-feeling dependency), and item 3b carries the *same*
  relation `r` rather than re-extracting an order via classical
  choice. Downstream callers genuinely want them separately
  (claim_3_17 / chapter 4 want acyclicity preservation without a
  named order; chapter 5 wants the order itself).

## Naming convention: `marginalize_*` prefix throughout

All four theorems use the `marginalize_*` prefix, *deviating* from
the project's `<conclusion>_<construction>` convention used by the
sibling rows (e.g. `isAcyclic_nodeSplittingOn`,
`isTopologicalOrder_nodeSplittingOn`,
`isAcyclic_extendingCDMGWithInterventionNodes`). The deviation is
deliberate and local: this file studies a *single operation* —
marginalization — and the four theorems are unified by what they
study, not by the conclusion each draws. A shared prefix groups
them visually and matches `Marginalization.lean`'s own projection
names (`marginalize_J`, `marginalize_V`, `mem_marginalize_E`,
`mem_marginalize_L`), so the dot-notation reading
`G.marginalize_isAcyclic W h` parallels `G.marginalize_J W` at call
sites in this section. Each theorem's per-block comment carries the
individual name's local justification.

## Where this gets used downstream

The four theorems below are the entry-level membership-level
preservation results that the next three rows in Section 3.2 build
on, and chapters 4 – 16 quote via latent-projection arguments:

* **claim_3_17** (`graphs.tex` Lem 997, "Marginalizations commute")
  — items 1 + 2 are quoted directly to assemble / disassemble
  iterated marginalizations.
* **claim_3_18 / claim_3_19** — items 1 + 3a underpin the
  intervention-commute and SWIG-marginalization equivalences.
* **`lem:stability_separation_marginalization`** (`graphs.tex` line
  1416, Section 3.3) — item 2 (no source) is the bifurcation-level
  invariance that yields `iσ`-separation stability under
  marginalization; item 1 the ancestor-level invariance.
* **Chapters 4 – 16** — every latent-projection argument in CBNs,
  do-calculus, iSCMs, FCI / ICDF rests on items 1 and 3.
-/

namespace Causality

open scoped Causality.CDMG

/-! ## Private walk-data helpers for `MarginalizationPreserves`

These are scaffolding for the proofs in this file. They live here (rather
than under `Section3_1/`) per the manager-side scope rule; analogous
private helpers in `BifurcationAlternative.lean` are repeated locally.
All declarations are `private` and visible only inside this file. -/

namespace Walk

variable {α : Type*} {G : CDMG α}

/-- A walk's support is never empty. -/
lemma marg_support_ne_nil {v w : α} (p : Walk G v w) : p.support ≠ [] := by
  cases p <;> simp

/-- Support of a walk concatenation: append the supports, dropping the
duplicated hinge vertex from the left walk. -/
lemma marg_support_append {u v w : α} (p : Walk G u v) (q : Walk G v w) :
    (p.append q).support = p.support.dropLast ++ q.support := by
  induction p with
  | nil v =>
    simp [Walk.nil_append, Walk.support_nil]
  | cons _ p' ih =>
    simp only [Walk.cons_append, Walk.support_cons, ih]
    rw [List.dropLast_cons_of_ne_nil p'.marg_support_ne_nil, List.cons_append]

/-- Walk concatenation is associative. -/
lemma marg_append_assoc {u v w x : α}
    (p : Walk G u v) (q : Walk G v w) (r : Walk G w x) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp only [Walk.cons_append, ih]

/-- A walk concatenation is `IsDirected` iff both halves are. -/
lemma marg_isDirected_append {u v w : α}
    (p : Walk G u v) (q : Walk G v w) :
    (p.append q).IsDirected ↔ p.IsDirected ∧ q.IsDirected := by
  induction p with
  | nil _ => simp
  | cons s p' ih =>
    cases s with
    | forward _ => simp only [Walk.cons_append, Walk.isDirected_cons_forward, ih]
    | backward _ => simp [Walk.cons_append]
    | bidir _ => simp [Walk.cons_append]

/-- A walk concatenation is `IsAllBackward` iff both halves are. -/
lemma marg_isAllBackward_append {u v w : α}
    (p : Walk G u v) (q : Walk G v w) :
    (p.append q).IsAllBackward ↔ p.IsAllBackward ∧ q.IsAllBackward := by
  induction p with
  | nil _ => simp
  | cons s p' ih =>
    cases s with
    | forward _ => simp [Walk.cons_append]
    | backward _ => simp only [Walk.cons_append, Walk.isAllBackward_cons_backward, ih]
    | bidir _ => simp [Walk.cons_append]

/-- A `forward` step reverses to a `backward` step, so an all-forward
walk reverses to an all-backward walk. -/
lemma marg_isAllBackward_reverse_of_isDirected {v w : α}
    {p : Walk G v w} (hp : p.IsDirected) : p.reverse.IsAllBackward := by
  induction p with
  | nil _ => simp
  | cons s p' ih =>
    cases s with
    | forward _ =>
      simp only [Walk.isDirected_cons_forward] at hp
      simp only [Walk.reverse_cons, WalkStep.reverse_forward]
      rw [marg_isAllBackward_append]
      exact ⟨ih hp, by simp⟩
    | backward _ => simp at hp
    | bidir _ => simp at hp

/-- A `backward` step reverses to a `forward` step, so an all-backward
walk reverses to a directed walk. -/
lemma marg_isDirected_reverse_of_isAllBackward {v w : α}
    {p : Walk G v w} (hp : p.IsAllBackward) : p.reverse.IsDirected := by
  induction p with
  | nil _ => simp
  | cons s p' ih =>
    cases s with
    | forward _ => simp at hp
    | backward _ =>
      simp only [Walk.isAllBackward_cons_backward] at hp
      simp only [Walk.reverse_cons, WalkStep.reverse_backward]
      rw [marg_isDirected_append]
      exact ⟨ih hp, by simp⟩
    | bidir _ => simp at hp

/-- Endpoint of a length-≥-1 directed walk lies in `G.V`. -/
lemma marg_end_in_V_of_isDirected_pos : ∀ {a b : α} (π : Walk G a b),
    π.IsDirected → 1 ≤ π.length → b ∈ G.V := by
  intro a b π
  induction π with
  | nil _ => intro _ hpos; simp at hpos
  | @cons a₀ m _ step p' ih =>
    intro hπ _
    cases step with
    | forward h =>
      have hp'_dir : p'.IsDirected := by simpa using hπ
      by_cases hp_pos : 1 ≤ p'.length
      · exact ih hp'_dir hp_pos
      · push_neg at hp_pos
        cases p' with
        | nil _ =>
          -- p' = nil m means b = m. Then h : a₀ ⟶ m = a₀ ⟶ b. E_subset gives b ∈ V.
          have hE : (a₀, m) ∈ G.E := h
          exact (Set.mem_prod.mp (G.E_subset hE)).2
        | cons _ _ => simp [Walk.length_cons] at hp_pos
    | backward _ => exact absurd hπ (by simp)
    | bidir _ => exact absurd hπ (by simp)

/-- Starting vertex of a length-≥-1 directed walk lies in `G.J ∪ G.V`. -/
lemma marg_start_in_JV_of_isDirected_pos {a b : α} (π : Walk G a b)
    (hπ : π.IsDirected) (hpos : 1 ≤ π.length) : a ∈ G.J ∪ G.V := by
  cases π with
  | nil _ => simp at hpos
  | @cons _ m _ step _ =>
    cases step with
    | forward h =>
      have hE : (a, m) ∈ G.E := h
      exact (Set.mem_prod.mp (G.E_subset hE)).1
    | backward _ => exact absurd hπ (by simp)
    | bidir _ => exact absurd hπ (by simp)

/-- Length of a reversed walk equals the original length. -/
lemma marg_length_reverse {v w : α} (p : Walk G v w) :
    p.reverse.length = p.length :=
  Walk.length_reverse p

/-- Last element of a walk's support is its endpoint. -/
lemma marg_support_getLast {v w : α} (p : Walk G v w) :
    p.support.getLast p.marg_support_ne_nil = w := by
  induction p with
  | nil _ => rfl
  | cons _ p' ih =>
    simp only [Walk.support_cons]
    rw [List.getLast_cons p'.marg_support_ne_nil]
    exact ih

/-- A walk's support has the form `start :: support.tail`. -/
lemma marg_support_cons_form {v w : α} (p : Walk G v w) :
    p.support = v :: p.support.tail := by
  cases p with
  | nil _ => rfl
  | cons _ _ => rfl

/-- Local equivalent of `List.tail_append_of_ne_nil` (in case Mathlib's name differs):
`(l₁ ++ l₂).tail = l₁.tail ++ l₂` when `l₁ ≠ []`. -/
lemma list_tail_append_of_ne_nil {β : Type*}
    {l₁ : List β} (l₂ : List β) (h : l₁ ≠ []) :
    (l₁ ++ l₂).tail = l₁.tail ++ l₂ := by
  cases l₁ with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- A walk's support decomposes as `(support.dropLast) ++ [endpoint]`. -/
lemma marg_support_eq_dropLast_append_last {v w : α} (p : Walk G v w) :
    p.support = p.support.dropLast ++ [w] := by
  conv_lhs => rw [← List.dropLast_append_getLast p.marg_support_ne_nil]
  rw [marg_support_getLast]

/-- Support of a reversed walk equals the reverse of the support. -/
lemma marg_support_reverse {v w : α} (p : Walk G v w) :
    p.reverse.support = p.support.reverse := by
  induction p with
  | nil _ => rfl
  | @cons v w u s p' ih =>
    rw [Walk.reverse_cons, marg_support_append, ih]
    simp only [Walk.support_cons, Walk.support_nil, List.reverse_cons]
    have hne : p'.support ≠ [] := p'.marg_support_ne_nil
    have hne' : p'.support.reverse ≠ [] := by simpa using hne
    have hhead : p'.support.head hne = w := by
      cases p' <;> rfl
    have hlast : p'.support.reverse.getLast hne' = w := by
      rw [List.getLast_reverse]; exact hhead
    have step : p'.support.reverse.dropLast ++ [w] = p'.support.reverse := by
      conv_rhs => rw [← List.dropLast_append_getLast hne']
      rw [hlast]
    calc p'.support.reverse.dropLast ++ [w, v]
        = p'.support.reverse.dropLast ++ ([w] ++ [v]) := by rfl
      _ = (p'.support.reverse.dropLast ++ [w]) ++ [v] := by rw [List.append_assoc]
      _ = p'.support.reverse ++ [v] := by rw [step]

/-! ## Walk translators between `G` and `G.marginalize W`

These existence lemmas are the workhorse of every theorem in this file:
they say a directed walk in `G` (with endpoints outside `W`) shrinks to
a directed walk in `G.marginalize W`, and conversely a directed walk in
`G.marginalize W` expands to one in `G`. -/

/-- Find the first non-`W` vertex along a directed walk whose endpoint
lies outside `W`. Splits the walk into a (possibly trivial) prefix
through `W` and the remaining walk starting at that pivot. -/
lemma exists_first_not_in_W (W : Set α) :
    ∀ {u v : α} (π : Walk G u v), π.IsDirected → v ∉ W →
    ∃ z : α, ∃ (pre : Walk G u z) (post : Walk G z v),
      z ∉ W ∧ pre.IsDirected ∧ post.IsDirected ∧
      (∀ x ∈ pre.support.dropLast, x ∈ W) ∧
      π = pre.append post := by
  intro u v π
  induction π with
  | nil v0 =>
    intros _ hv
    refine ⟨v0, Walk.nil v0, Walk.nil v0, hv, by simp, by simp, ?_, rfl⟩
    intro x hx; simp at hx
  | @cons u' w v step p' ih =>
    intros hπ_dir hv
    cases step with
    | forward h =>
      have hp'_dir : p'.IsDirected := by simpa using hπ_dir
      by_cases hu : u' ∈ W
      · obtain ⟨z, pre, post, hz, hpre_dir, hpost_dir, hpre_int, hp_eq⟩ :=
          ih hp'_dir hv
        refine ⟨z, Walk.cons (.forward h) pre, post, hz, ?_, hpost_dir, ?_, ?_⟩
        · simpa using hpre_dir
        · intro x hx
          rw [Walk.support_cons, List.dropLast_cons_of_ne_nil pre.marg_support_ne_nil] at hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hu
          · exact hpre_int x hx'
        · show Walk.cons (.forward h) p' = _
          rw [hp_eq]; rfl
      · refine ⟨u', Walk.nil u', Walk.cons (.forward h) p', hu, by simp, ?_, ?_, by simp⟩
        · simpa using hπ_dir
        · intro x hx; simp at hx
    | backward _ => exact absurd hπ_dir (by simp)
    | bidir _ => exact absurd hπ_dir (by simp)

/-- Helper: the InteriorIn property of a single-edge walk `cons (.forward h) (nil w)`
holds vacuously (interior is empty). -/
lemma marg_single_edge_interior {u w : α} (W : Set α) (h : u ⟶[G] w) :
    (Walk.cons (.forward h) (Walk.nil w)).InteriorIn W := by
  intro x hx
  -- (cons _ _).support.tail.dropLast = [u, w].tail.dropLast = [w].dropLast = []
  simp [Walk.support_cons, Walk.support_nil] at hx

/-- For a directed walk in `G.marginalize W` whose start vertex is not
in `W`, every vertex in the support is not in `W`. Used by
`marginalize_bif_forward`'s support-tracking conjunct to argue the
constructed marg-bifurcation has all vertices outside `W`. -/
lemma marg_directed_supp_notW {G : CDMG α} {W : Set α} {a b : α} :
    ∀ (π : Walk (G.marginalize W) a b), π.IsDirected →
      a ∉ W → ∀ x ∈ π.support, x ∉ W := by
  intro π
  induction π with
  | nil _ =>
    intros _ ha x hx
    simp at hx; rw [hx]; exact ha
  | @cons a₀ w _ step p' ih =>
    intro hπ ha x hx
    cases step with
    | forward h =>
      have hp'_dir : p'.IsDirected := by simpa using hπ
      have h_E : (a₀, w) ∈ (G.marginalize W).E := h
      have hw_V : w ∈ (G.marginalize W).V :=
        (Set.mem_prod.mp ((G.marginalize W).E_subset h_E)).2
      have hw_notW : w ∉ W := by
        rw [CDMG.marginalize_V] at hw_V; exact hw_V.2
      rw [Walk.support_cons] at hx
      rcases List.mem_cons.mp hx with hxa | hxr
      · rw [hxa]; exact ha
      · exact ih hp'_dir hw_notW x hxr
    | backward _ => simp at hπ
    | bidir _ => simp at hπ

/-- Shrink translator (existence): a directed walk in `G` with both
endpoints outside `W` shrinks to a directed walk in `G.marginalize W`,
with the shrunk walk's support a subset of the original's support
(and so for `tail` and `dropLast`).
Each maximal in-`W` sub-walk between consecutive non-`W` "pivots" is
collapsed to a single `E^{\sm W}` edge via `mem_marginalize_E`. -/
lemma exists_marg_directed_of_directed (W : Set α) :
    ∀ {u v : α} (π : Walk G u v), π.IsDirected →
    u ∉ W → v ∉ W →
    ∃ π' : Walk (G.marginalize W) u v, π'.IsDirected ∧
      (∀ x ∈ π'.support, x ∈ π.support) ∧
      (∀ x ∈ π'.support.tail, x ∈ π.support.tail) ∧
      (∀ x ∈ π'.support.dropLast, x ∈ π.support.dropLast) := by
  suffices h : ∀ (n : ℕ) {u v : α} (π : Walk G u v), π.length ≤ n →
      π.IsDirected → u ∉ W → v ∉ W →
      ∃ π' : Walk (G.marginalize W) u v, π'.IsDirected ∧
        (∀ x ∈ π'.support, x ∈ π.support) ∧
        (∀ x ∈ π'.support.tail, x ∈ π.support.tail) ∧
        (∀ x ∈ π'.support.dropLast, x ∈ π.support.dropLast) by
    intros u v π hπ_dir hu hv; exact h π.length π le_rfl hπ_dir hu hv
  intro n
  induction n with
  | zero =>
    intros u v π hlen hπ_dir _ _
    cases π with
    | nil _ =>
      refine ⟨Walk.nil _, by simp, ?_, ?_, ?_⟩
      · intro _ h; exact h
      · intro _ h; simp at h
      · intro _ h; simp at h
    | @cons _ _ _ _ _ => rw [Walk.length_cons] at hlen; omega
  | succ k ih =>
    intros u v π hlen hπ_dir hu hv
    cases π with
    | nil _ =>
      refine ⟨Walk.nil _, by simp, ?_, ?_, ?_⟩
      · intro _ h; exact h
      · intro _ h; simp at h
      · intro _ h; simp at h
    | @cons _ w _ step p' =>
      cases step with
      | forward h_step =>
        have hp'_dir : p'.IsDirected := by simpa using hπ_dir
        have hp'_len : p'.length ≤ k := by
          rw [Walk.length_cons] at hlen; omega
        have h_uw_E : (u, w) ∈ G.E := h_step
        have h_uw_prod : (u, w) ∈ (G.J ∪ G.V) ×ˢ G.V := G.E_subset h_uw_E
        have h_u_JV : u ∈ G.J ∪ G.V := (Set.mem_prod.mp h_uw_prod).1
        have h_w_V : w ∈ G.V := (Set.mem_prod.mp h_uw_prod).2
        have h_u_in : u ∈ G.J ∪ (G.V \ W) := by
          rcases h_u_JV with hJ | hV
          · exact Or.inl hJ
          · exact Or.inr ⟨hV, hu⟩
        by_cases hw : w ∈ W
        · -- w ∈ W. Find the first non-W vertex along p'.
          obtain ⟨z, p_skip, p_rest, hz, hp_skip_dir, hp_rest_dir,
                  hp_skip_int, hp'_eq⟩ :=
            exists_first_not_in_W W p' hp'_dir hv
          have h_p_skip_pos : 1 ≤ p_skip.length := by
            cases p_skip with
            | nil _ => exact absurd hw hz
            | cons _ _ => simp
          have h_chunk_dir : (Walk.cons (.forward h_step) p_skip).IsDirected := by
            simpa using hp_skip_dir
          have h_chunk_pos : 1 ≤ (Walk.cons (.forward h_step) p_skip).length := by simp
          have h_chunk_int : (Walk.cons (.forward h_step) p_skip).InteriorIn W := by
            intro x hx
            rw [show (Walk.cons (.forward h_step) p_skip).support.tail.dropLast
                = p_skip.support.dropLast from by
                rw [Walk.support_cons, List.tail_cons]] at hx
            exact hp_skip_int x hx
          have h_z_in : z ∈ G.V \ W :=
            ⟨marg_end_in_V_of_isDirected_pos p_skip hp_skip_dir h_p_skip_pos, hz⟩
          have h_marg_edge : (u, z) ∈ (G.marginalize W).E := by
            rw [CDMG.mem_marginalize_E]
            exact ⟨h_u_in, h_z_in,
                   Walk.cons (.forward h_step) p_skip,
                   h_chunk_dir, h_chunk_int, h_chunk_pos⟩
          have h_rest_len : p_rest.length ≤ k := by
            have : p'.length = p_skip.length + p_rest.length := by
              rw [hp'_eq, Walk.length_append]
            omega
          obtain ⟨π'_rest, hπ'_rest_dir, hπ'_rest_supp, hπ'_rest_tail, hπ'_rest_drop⟩ :=
            ih p_rest h_rest_len hp_rest_dir hz hv
          -- p_rest.support ⊆ p'.support (since p' = p_skip ++ p_rest).
          have h_p_rest_in_p' : ∀ x ∈ p_rest.support, x ∈ p'.support := fun x hx => by
            rw [hp'_eq, marg_support_append]
            exact List.mem_append.mpr (Or.inr hx)
          refine ⟨Walk.cons (.forward h_marg_edge) π'_rest, by simpa using hπ'_rest_dir,
                  ?_, ?_, ?_⟩
          · intro x hx
            simp only [Walk.support_cons, List.mem_cons] at hx ⊢
            rcases hx with rfl | hxrest
            · exact Or.inl rfl
            · exact Or.inr (h_p_rest_in_p' x (hπ'_rest_supp x hxrest))
          · intro x hx
            -- (cons _ π'_rest).support.tail = π'_rest.support.
            rw [Walk.support_cons, List.tail_cons] at hx
            -- π.support.tail = p'.support.
            rw [Walk.support_cons, List.tail_cons]
            exact h_p_rest_in_p' x (hπ'_rest_supp x hx)
          · intro x hx
            -- (cons _ π'_rest).support.dropLast = u :: π'_rest.support.dropLast.
            rw [Walk.support_cons,
                List.dropLast_cons_of_ne_nil π'_rest.marg_support_ne_nil] at hx
            simp only [List.mem_cons] at hx
            -- π.support.dropLast = u :: p'.support.dropLast.
            rw [Walk.support_cons, List.dropLast_cons_of_ne_nil p'.marg_support_ne_nil]
            simp only [List.mem_cons]
            rcases hx with rfl | hxrest
            · exact Or.inl rfl
            · -- x ∈ π'_rest.support.dropLast → x ∈ p_rest.support.dropLast (by IH)
              -- → x ∈ p_rest.support (since dropLast ⊆ support) → x ∈ p'.support.
              -- But we want x ∈ p'.support.dropLast. Hmm.
              -- Actually p_rest.support.dropLast = p_rest.support without last (= v).
              -- p'.support.dropLast = p'.support without last (= v).
              -- p_rest.support ⊆ p'.support. Both end at v. So
              -- p_rest.support.dropLast ⊆ p'.support.dropLast (set-wise).
              right
              have h_drop : x ∈ p_rest.support.dropLast := hπ'_rest_drop x hxrest
              -- Show x ∈ p'.support.dropLast.
              -- p'.support = p_skip.support.dropLast ++ p_rest.support.
              -- p'.support.dropLast = p_skip.support.dropLast ++ p_rest.support.dropLast.
              rw [hp'_eq, marg_support_append,
                  List.dropLast_append_of_ne_nil p_rest.marg_support_ne_nil]
              exact List.mem_append.mpr (Or.inr h_drop)
        · -- w ∉ W. Recurse on p' directly with single-step witness.
          have h_w_in : w ∈ G.V \ W := ⟨h_w_V, hw⟩
          have h_marg_edge : (u, w) ∈ (G.marginalize W).E := by
            rw [CDMG.mem_marginalize_E]
            refine ⟨h_u_in, h_w_in, Walk.cons (.forward h_step) (Walk.nil w),
                    ?_, marg_single_edge_interior W h_step, ?_⟩
            · simp
            · simp
          obtain ⟨π'_rest, hπ'_rest_dir, hπ'_rest_supp, hπ'_rest_tail, hπ'_rest_drop⟩ :=
            ih p' hp'_len hp'_dir hw hv
          refine ⟨Walk.cons (.forward h_marg_edge) π'_rest, by simpa using hπ'_rest_dir,
                  ?_, ?_, ?_⟩
          · intro x hx
            simp only [Walk.support_cons, List.mem_cons] at hx ⊢
            rcases hx with rfl | hxrest
            · exact Or.inl rfl
            · exact Or.inr (hπ'_rest_supp x hxrest)
          · intro x hx
            rw [Walk.support_cons, List.tail_cons] at hx
            rw [Walk.support_cons, List.tail_cons]
            exact hπ'_rest_supp x hx
          · intro x hx
            rw [Walk.support_cons,
                List.dropLast_cons_of_ne_nil π'_rest.marg_support_ne_nil] at hx
            simp only [List.mem_cons] at hx
            rw [Walk.support_cons, List.dropLast_cons_of_ne_nil p'.marg_support_ne_nil]
            simp only [List.mem_cons]
            rcases hx with rfl | hxrest
            · exact Or.inl rfl
            · exact Or.inr (hπ'_rest_drop x hxrest)
      | backward _ => exact absurd hπ_dir (by simp)
      | bidir _ => exact absurd hπ_dir (by simp)

/-- Expand translator (existence): a directed walk in `G.marginalize W`
expands to a directed walk in `G` whose length is at least the original
length and whose support consists of the original walk's vertices plus
W-intermediates. Each `E^{\sm W}`-edge expands to a length-≥-1
sub-walk in `G` with interior in `W` via `mem_marginalize_E`.
Additionally, the support's tail and dropLast are contained in the
corresponding parts of the original walk's support, plus W intermediates. -/
lemma exists_directed_of_marg_directed (W : Set α) :
    ∀ {u v : α} (π' : Walk (G.marginalize W) u v), π'.IsDirected →
    ∃ ρ : Walk G u v, ρ.IsDirected ∧ π'.length ≤ ρ.length ∧
    (∀ x ∈ ρ.support, x ∈ π'.support ∨ x ∈ W) ∧
    (∀ x ∈ ρ.support.tail, x ∈ π'.support.tail ∨ x ∈ W) ∧
    (∀ x ∈ ρ.support.dropLast, x ∈ π'.support.dropLast ∨ x ∈ W) := by
  intro u v π'
  induction π' with
  | nil v0 =>
    intro _
    refine ⟨Walk.nil v0, by simp, by simp, ?_, ?_, ?_⟩
    · intro x hx; exact Or.inl hx
    · intro x hx; simp at hx
    · intro x hx; simp at hx
  | @cons u' w _ step p' ih =>
    intro hπ_dir
    cases step with
    | forward h =>
      have hp'_dir : p'.IsDirected := by simpa using hπ_dir
      -- Extract the witness directed walk in G from mem_marginalize_E.
      have h_E : (u', w) ∈ (G.marginalize W).E := h
      rw [CDMG.mem_marginalize_E] at h_E
      obtain ⟨_, _, π_G, hπ_G_dir, hπ_G_int, hπ_G_pos⟩ := h_E
      obtain ⟨ρ_p, hρ_p_dir, hρ_p_len, hρ_p_supp, hρ_p_tail, hρ_p_drop⟩ := ih hp'_dir
      -- π_G.support has head u'. Compute its dropLast and tail.
      have h_πG_head : ∃ t, π_G.support = u' :: t := by
        cases π_G with
        | nil v0 => exact ⟨[], by simp⟩
        | cons _ p_inner => exact ⟨p_inner.support, by simp⟩
      obtain ⟨t_πG, ht_πG⟩ := h_πG_head
      have h_t_πG_ne : t_πG ≠ [] := by
        by_contra ht_nil
        have : π_G.support.length = 1 := by rw [ht_πG, ht_nil]; simp
        rw [Walk.support_length] at this
        omega
      have h_ρ_p_supp_ne : ρ_p.support ≠ [] := ρ_p.marg_support_ne_nil
      refine ⟨π_G.append ρ_p, ?_, ?_, ?_, ?_, ?_⟩
      · rw [marg_isDirected_append]; exact ⟨hπ_G_dir, hρ_p_dir⟩
      · rw [Walk.length_append, Walk.length_cons]; omega
      · -- support inclusion.
        intro x hx
        rw [marg_support_append] at hx
        rcases List.mem_append.mp hx with hxL | hxR
        · rw [ht_πG, List.dropLast_cons_of_ne_nil h_t_πG_ne] at hxL
          simp only [List.mem_cons] at hxL
          rcases hxL with rfl | hxL
          · exact Or.inl (by simp [Walk.support_cons])
          · -- x ∈ t_πG.dropLast = π_G.support.tail.dropLast ⊆ W.
            exact Or.inr (hπ_G_int x (by rw [ht_πG]; simp; exact hxL))
        · -- x ∈ ρ_p.support: by IH.
          rcases hρ_p_supp x hxR with hxp | hxW
          · exact Or.inl (by simp [Walk.support_cons, hxp])
          · exact Or.inr hxW
      · -- tail inclusion: (π_G.append ρ_p).support.tail ⊆ π'.support.tail ∪ W.
        -- support = π_G.support.dropLast ++ ρ_p.support = (u' :: t_πG.dropLast) ++ ρ_p.support
        --         = u' :: (t_πG.dropLast ++ ρ_p.support)
        -- tail = t_πG.dropLast ++ ρ_p.support.
        -- π'.support.tail = (u' :: p'.support).tail = p'.support.
        intro x hx
        rw [marg_support_append] at hx
        rw [ht_πG, List.dropLast_cons_of_ne_nil h_t_πG_ne] at hx
        rw [show ((u' :: t_πG.dropLast) ++ ρ_p.support).tail
            = t_πG.dropLast ++ ρ_p.support from by rfl] at hx
        rcases List.mem_append.mp hx with hxL | hxR
        · -- x ∈ t_πG.dropLast ⊆ W (interior of π_G).
          exact Or.inr (hπ_G_int x (by rw [ht_πG]; simp; exact hxL))
        · -- x ∈ ρ_p.support: by IH support, x ∈ p'.support ∨ x ∈ W.
          -- p'.support = π'.support.tail = (u' :: p'.support).tail. So x ∈ p'.support → x ∈ π'.support.tail.
          rcases hρ_p_supp x hxR with hxp | hxW
          · left
            show x ∈ (Walk.cons (.forward h) p').support.tail
            rw [Walk.support_cons, List.tail_cons]
            exact hxp
          · exact Or.inr hxW
      · -- dropLast inclusion: similar.
        intro x hx
        rw [marg_support_append] at hx
        rw [ht_πG, List.dropLast_cons_of_ne_nil h_t_πG_ne] at hx
        rw [List.dropLast_append_of_ne_nil h_ρ_p_supp_ne] at hx
        simp only [List.mem_append, List.mem_cons] at hx
        rcases hx with (rfl | hxL) | hxR
        · -- x = u (head of cons): u ∈ π'.support.dropLast.
          left
          rw [Walk.support_cons, List.dropLast_cons_of_ne_nil p'.marg_support_ne_nil]
          simp
        · -- x ∈ t_πG.dropLast ⊆ W.
          exact Or.inr (hπ_G_int x (by rw [ht_πG]; simp; exact hxL))
        · -- x ∈ ρ_p.support.dropLast: by IH, ⊆ p'.support.dropLast ∪ W.
          rcases hρ_p_drop x hxR with hxp | hxW
          · left
            rw [Walk.support_cons, List.dropLast_cons_of_ne_nil p'.marg_support_ne_nil]
            simp; exact Or.inr hxp
          · exact Or.inr hxW
    | backward _ => exact absurd hπ_dir (by simp)
    | bidir _ => exact absurd hπ_dir (by simp)

/-- Membership in the marginalization implies membership in `G`:
`v ∈ G.marginalize W → v ∈ G`. -/
private lemma marg_mem_of_marg {W : Set α} {G : CDMG α} {v : α}
    (hv : v ∈ G.marginalize W) : v ∈ G := by
  rw [CDMG.mem_iff] at hv ⊢
  simp only [CDMG.marginalize_J, CDMG.marginalize_V] at hv
  rcases hv with hJ | ⟨hV, _⟩
  · exact Or.inl hJ
  · exact Or.inr hV

/-- Topological-order parent_lt extended along a length-≥-1 directed
walk in `G`: every step contributes via `parent_lt` and transitivity
chains them through the walk. -/
private lemma marg_walk_lt_of_isTopologicalOrder {G : CDMG α}
    {r : α → α → Prop} (hr : G.IsTopologicalOrder r) :
    ∀ {a b : α} (π : Walk G a b), π.IsDirected → 1 ≤ π.length → r a b := by
  intro a b π
  induction π with
  | nil _ => intro _ hpos; simp at hpos
  | @cons a₀ m b₀ step p' ih =>
    intro hπ_dir _
    cases step with
    | forward h =>
      have hp'_dir : p'.IsDirected := by simpa using hπ_dir
      have h_in_Pa : a₀ ∈ CDMG.Pa G m := by
        refine ⟨?_, h⟩
        have h_E : (a₀, m) ∈ G.E := h
        rw [CDMG.mem_iff]
        exact (Set.mem_prod.mp (G.E_subset h_E)).1
      have h_lt_am : r a₀ m := hr.parent_lt h_in_Pa
      by_cases hp'_pos : 1 ≤ p'.length
      · have h_lt_mb : r m b₀ := ih hp'_dir hp'_pos
        have ha₀_G : a₀ ∈ G := h_in_Pa.1
        have hm_G : m ∈ G := by
          have h_E : (a₀, m) ∈ G.E := h
          rw [CDMG.mem_iff]
          exact Or.inr (Set.mem_prod.mp (G.E_subset h_E)).2
        have hb₀_G : b₀ ∈ G := by
          rw [CDMG.mem_iff]
          exact Or.inr (marg_end_in_V_of_isDirected_pos p' hp'_dir hp'_pos)
        exact hr.trans a₀ ha₀_G m hm_G b₀ hb₀_G h_lt_am h_lt_mb
      · -- p'.length = 0, so p' = nil and m = b₀.
        push_neg at hp'_pos
        cases p' with
        | nil _ => exact h_lt_am
        | cons _ _ => simp [Walk.length_cons] at hp'_pos
    | backward _ => exact absurd hπ_dir (by simp)
    | bidir _ => exact absurd hπ_dir (by simp)

/-! ## Bifurcation translators

Two helpers that handle a single walk-direction case of theorem 2
(`marginalize_bifurcation_iff`). Each returns a disjunction matching
the symmetric `∨` in the theorem's conclusion, because the `L^{\sm W}`
exclusion clause (and the asymmetry of bifurcation under walk reversal)
can flip the resulting walk's direction. -/

/-- Key support-membership transport lemma: given a bifurcation `π'` in
`G.marginalize W` and a walk `π_G` in `G` whose support is contained
in `π'.support ∪ W`, with similar tail/dropLast inclusions, endpoint
constraints of the marginalize bifurcation transport to `π_G`. -/
private lemma marg_to_G_endpoints_clear {W : Set α} {G : CDMG α}
    {u v : α} {π' : Walk (G.marginalize W) u v} (hb' : π'.IsBifurcation)
    (hu : u ∉ W) (hv : v ∉ W)
    {π_G : Walk G u v}
    (h_tail : ∀ x ∈ π_G.support.tail, x ∈ π'.support.tail ∨ x ∈ W)
    (h_drop : ∀ x ∈ π_G.support.dropLast, x ∈ π'.support.dropLast ∨ x ∈ W) :
    u ∉ π_G.support.tail ∧ v ∉ π_G.support.dropLast := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases h_tail u h with hπ' | hW
    · exact hb'.2.1 hπ'
    · exact hu hW
  · intro h
    rcases h_drop v h with hπ' | hW
    · exact hb'.2.2.1 hπ'
    · exact hv hW

/-- Bifurcation-witness leftArm support: a vertex in the (list) tail of
`bw.leftArm.support` is in `π.support.tail`. The leftArm contributes
positions 1 through `leftArm.length` of `π.support`, all of which are
in `π.support.tail`. -/
lemma bw_leftArm_tail_in_π_tail {G : CDMG α} {u v : α} {π : Walk G u v}
    (bw : Walk.BifurcationWitness π) :
    ∀ x ∈ bw.leftArm.support.tail, x ∈ π.support.tail := by
  intro x hx
  rw [bw.decompose]
  show x ∈ (bw.leftArm.append (Walk.cons bw.hinge bw.rightArm)).support.tail
  rw [marg_support_append, Walk.support_cons]
  by_cases h_dropLast_ne : bw.leftArm.support.dropLast = []
  · -- leftArm.length = 0, leftArm.support has length 1, tail = []. Contradiction.
    have h_len_zero : bw.leftArm.length = 0 := by
      have h_eq : bw.leftArm.support.dropLast.length = bw.leftArm.length := by
        rw [List.length_dropLast, Walk.support_length]; omega
      rw [h_dropLast_ne, List.length_nil] at h_eq
      omega
    have h_tail_empty : bw.leftArm.support.tail = [] := by
      have h_l : bw.leftArm.support.tail.length = 0 := by
        rw [List.length_tail, Walk.support_length, h_len_zero]
      exact List.length_eq_zero_iff.mp h_l
    rw [h_tail_empty] at hx
    simp at hx
  · rw [list_tail_append_of_ne_nil _ h_dropLast_ne]
    -- Goal: x ∈ bw.leftArm.support.dropLast.tail ++ (bw.m :: bw.rightArm.support).
    -- bw.leftArm.support.tail = bw.leftArm.support.dropLast.tail ++ [bw.m].
    rw [marg_support_eq_dropLast_append_last bw.leftArm,
        list_tail_append_of_ne_nil _ h_dropLast_ne] at hx
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append.mpr (Or.inl h)
    · simp only [List.mem_singleton] at h
      refine List.mem_append.mpr (Or.inr ?_)
      rw [h]; simp

/-- A vertex in `bw.rightArm.support` is in `π.support.tail`. -/
lemma bw_rightArm_in_π_tail {G : CDMG α} {u v : α} {π : Walk G u v}
    (bw : Walk.BifurcationWitness π) :
    ∀ x ∈ bw.rightArm.support, x ∈ π.support.tail := by
  intro x hx
  rw [bw.decompose]
  show x ∈ (bw.leftArm.append (Walk.cons bw.hinge bw.rightArm)).support.tail
  rw [marg_support_append, Walk.support_cons]
  by_cases h_dropLast_ne : bw.leftArm.support.dropLast = []
  · rw [h_dropLast_ne, List.nil_append, List.tail_cons]
    exact hx
  · rw [list_tail_append_of_ne_nil _ h_dropLast_ne]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx))

/-- `bw.m` is in `π.support.tail` when `bw.leftArm.length ≥ 1`. -/
lemma bw_m_in_π_tail_of_leftArm_pos {G : CDMG α} {u v : α} {π : Walk G u v}
    (bw : Walk.BifurcationWitness π) (h_pos : 1 ≤ bw.leftArm.length) :
    bw.m ∈ π.support.tail := by
  apply bw_leftArm_tail_in_π_tail
  -- bw.m is the last vertex of bw.leftArm.support; it's in tail (at position bw.leftArm.length ≥ 1).
  rw [marg_support_eq_dropLast_append_last bw.leftArm]
  have h_dropLast_ne : bw.leftArm.support.dropLast ≠ [] := by
    intro h_emp
    have h_eq : bw.leftArm.support.dropLast.length = bw.leftArm.length := by
      rw [List.length_dropLast, Walk.support_length]; omega
    rw [h_emp, List.length_nil] at h_eq
    omega
  rw [list_tail_append_of_ne_nil _ h_dropLast_ne]
  exact List.mem_append.mpr (Or.inr (by simp))

/-- A vertex in `bw.leftArm.support` is in `π.support.dropLast`. -/
lemma bw_leftArm_in_π_dropLast {G : CDMG α} {u v : α} {π : Walk G u v}
    (bw : Walk.BifurcationWitness π) :
    ∀ x ∈ bw.leftArm.support, x ∈ π.support.dropLast := by
  intro x hx
  rw [bw.decompose]
  show x ∈ (bw.leftArm.append (Walk.cons bw.hinge bw.rightArm)).support.dropLast
  rw [marg_support_append, List.dropLast_append_of_ne_nil (by simp [Walk.support_cons])]
  rw [Walk.support_cons, List.dropLast_cons_of_ne_nil bw.rightArm.marg_support_ne_nil]
  rw [marg_support_eq_dropLast_append_last bw.leftArm] at hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append.mpr (Or.inl h)
  · simp only [List.mem_singleton] at h
    refine List.mem_append.mpr (Or.inr ?_)
    rw [h]; exact List.mem_cons_self

/-- A vertex in `bw.rightArm.support.dropLast` is in `π.support.dropLast`. -/
lemma bw_rightArm_dropLast_in_π_dropLast {G : CDMG α} {u v : α}
    {π : Walk G u v} (bw : Walk.BifurcationWitness π) :
    ∀ x ∈ bw.rightArm.support.dropLast, x ∈ π.support.dropLast := by
  intro x hx
  rw [bw.decompose]
  show x ∈ (bw.leftArm.append (Walk.cons bw.hinge bw.rightArm)).support.dropLast
  rw [marg_support_append, List.dropLast_append_of_ne_nil (by simp [Walk.support_cons])]
  rw [Walk.support_cons, List.dropLast_cons_of_ne_nil bw.rightArm.marg_support_ne_nil]
  exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx))

/-- `bw.m` is in `π.support.dropLast` (it precedes the hinge edge in π). -/
lemma bw_m_in_π_dropLast {G : CDMG α} {u v : α} {π : Walk G u v}
    (bw : Walk.BifurcationWitness π) : bw.m ∈ π.support.dropLast := by
  apply bw_leftArm_in_π_dropLast
  rw [marg_support_eq_dropLast_append_last bw.leftArm]
  exact List.mem_append.mpr (Or.inr (by simp))

/-- `bw.m'` is in `π.support.dropLast` when `bw.rightArm.length ≥ 1`. -/
lemma bw_m'_in_π_dropLast_of_rightArm_pos {G : CDMG α} {u v : α}
    {π : Walk G u v} (bw : Walk.BifurcationWitness π)
    (h_pos : 1 ≤ bw.rightArm.length) : bw.m' ∈ π.support.dropLast := by
  apply bw_rightArm_dropLast_in_π_dropLast
  -- bw.m' is the first vertex of bw.rightArm.support, and length ≥ 1 makes dropLast non-empty.
  rw [marg_support_cons_form bw.rightArm]
  have h_tail_ne : bw.rightArm.support.tail ≠ [] := by
    intro h_emp
    have h_len : bw.rightArm.support.tail.length = 0 := by rw [h_emp]; rfl
    rw [List.length_tail, Walk.support_length] at h_len
    omega
  rw [List.dropLast_cons_of_ne_nil h_tail_ne]
  simp

/-! ## Local helpers for backward and forward bifurcation translators -/

/-- Support of an appended walk: every vertex is in either summand's support. -/
lemma marg_mem_append_support {u v w : α} {p : Walk G u v} {q : Walk G v w}
    {x : α} (h : x ∈ (p.append q).support) : x ∈ p.support ∨ x ∈ q.support := by
  rw [marg_support_append] at h
  rcases List.mem_append.mp h with hl | hr
  · exact Or.inl (List.dropLast_subset _ hl)
  · exact Or.inr hr

/-- Vertex membership transports through reverse-of-support. -/
lemma marg_mem_reverse_support {u v : α} {p : Walk G u v} {x : α}
    (h : x ∈ p.reverse.support) : x ∈ p.support := by
  rw [marg_support_reverse, List.mem_reverse] at h; exact h

/-- For a reversed walk: vertex in the tail of `p.reverse.support` is in the
`dropLast` of the original support (set-wise). -/
lemma marg_mem_reverse_tail_to_dropLast {u v : α} {p : Walk G u v} {x : α}
    (h : x ∈ p.reverse.support.tail) : x ∈ p.support.dropLast := by
  -- l.reverse.tail = l.dropLast.reverse (as lists, when l is non-empty)
  -- so memberships transport.
  rw [marg_support_reverse] at h
  rw [List.tail_reverse] at h
  rwa [List.mem_reverse] at h

/-- For a reversed walk: vertex in the dropLast of `p.reverse.support` is in
the `tail` of the original support (set-wise). -/
lemma marg_mem_reverse_dropLast_to_tail {u v : α} {p : Walk G u v} {x : α}
    (h : x ∈ p.reverse.support.dropLast) : x ∈ p.support.tail := by
  rw [marg_support_reverse] at h
  rw [List.dropLast_reverse] at h
  rwa [List.mem_reverse] at h

/-- For a reversed walk: vertex in `p.reverse.support.dropLast.tail` (the strict
interior of `p.reverse`) is in `p.support.tail.dropLast` (the strict interior of
`p`). -/
lemma marg_mem_reverse_strict_interior {u v : α} {p : Walk G u v} {x : α}
    (h : x ∈ p.reverse.support.dropLast.tail) : x ∈ p.support.tail.dropLast := by
  rw [marg_support_reverse, List.dropLast_reverse, List.tail_reverse,
      List.mem_reverse] at h
  exact h

/-- For a walk of length ≥ 1, the last vertex of `p.support.tail` is the walk's
endpoint `w`. -/
private lemma marg_support_tail_getLast {v w : α} (p : Walk G v w)
    (h_pos : 1 ≤ p.length) :
    p.support.tail.getLast (by
      intro h_emp
      have : p.support.tail.length = 0 := by rw [h_emp]; rfl
      rw [List.length_tail, Walk.support_length] at this
      omega) = w := by
  cases p with
  | nil _ => simp [Walk.length_nil] at h_pos
  | cons _ p' =>
    show (p'.support).getLast _ = w
    exact marg_support_getLast p'

/-- `List.tail.dropLast ⊆ List.dropLast`: dropping the head from a dropLast-result
gives a subset of the original dropLast. -/
lemma marg_tail_dropLast_subset_dropLast {β : Type*} (L : List β) :
    L.tail.dropLast ⊆ L.dropLast := by
  intro x hx
  cases L with
  | nil => simp at hx
  | cons a t =>
    simp only [List.tail_cons] at hx
    cases t with
    | nil => simp at hx
    | cons _ _ =>
      rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]
      exact List.mem_cons_of_mem _ hx

/-- (←) direction of `marginalize_bifurcation_iff`. Given a bifurcation in
`G.marginalize W` between `u` and `v`, build a bifurcation in `G` between
them (in one of the two walk directions).

**Status: partial.** The construction strategy (decomposed in workspace §5.3)
expands the marginalize bifurcation's left arm, right arm, and hinge back
to `G` walks. The hinge case-split:
* `.forward` is impossible (hingeIntoSource).
* `.backward` extracts a length-≥-1 directed walk in `G` via
  `mem_marginalize_E` and uses its first step as the new hinge.
* `.bidir` extracts a G-side sub-bifurcation via `mem_marginalize_L` and
  splices it.

The blocker on each branch is the `IsBifurcation` support condition
(`u ∉ tail`, `v ∉ dropLast`), which requires a multi-case-split tracking
of the reverse-arm `support.dropLast` and the `q` walk's interior, combined
with the bifurcation-witness arm-support helpers. See
`workspace_claim_3_16.md` §5.3 for the detailed support-analysis sketch.
-/
lemma marginalize_bif_backward {G : CDMG α} {W : Set α} {u v : α}
    (_hu_in : u ∈ G) (_hv_in : v ∈ G) (hu : u ∉ W) (hv : v ∉ W)
    (π' : Walk (G.marginalize W) u v) (hb' : π'.IsBifurcation) :
    (∃ π : Walk G u v, π.IsBifurcation ∧
      ∀ x ∈ π.support, x ∈ π'.support ∨ x ∈ W) ∨
    (∃ π : Walk G v u, π.IsBifurcation ∧
      ∀ x ∈ π.support, x ∈ π'.support ∨ x ∈ W) := by
  obtain ⟨h_uv_ne, hu_tail_π', hv_drop_π', ⟨bw'⟩⟩ := hb'
  -- Destructure bw' for cleaner names; reassemble later for the bw_* helpers.
  obtain ⟨m_w, m'_w, lA, hg, rA, h_dec, h_lB, h_hIS, h_rD⟩ := bw'
  -- Re-pack to access bw_* helpers (which take a BifurcationWitness π').
  let bw_pkg : Walk.BifurcationWitness π' :=
    ⟨m_w, m'_w, lA, hg, rA, h_dec, h_lB, h_hIS, h_rD⟩
  -- u is not in lA.support.tail.dropLast (the strict interior of lA),
  -- because lA.support.tail.dropLast ⊆ lA.support.tail ⊆ π'.support.tail and u ∉ π'.support.tail.
  have h_u_notin_lA_int : u ∉ lA.support.tail.dropLast := fun h => by
    exact hu_tail_π' (bw_leftArm_tail_in_π_tail bw_pkg u
      (List.dropLast_subset _ h))
  -- v is not in lA.support (lA.support ⊆ π'.support.dropLast).
  have h_v_notin_lA : v ∉ lA.support := fun h =>
    hv_drop_π' (bw_leftArm_in_π_dropLast bw_pkg v h)
  -- u is not in rA.support (rA.support ⊆ π'.support.tail).
  have h_u_notin_rA : u ∉ rA.support := fun h =>
    hu_tail_π' (bw_rightArm_in_π_tail bw_pkg u h)
  -- v is not in rA.support.dropLast (= start + interior of rA).
  have h_v_notin_rA_drop : v ∉ rA.support.dropLast := fun h =>
    hv_drop_π' (bw_rightArm_dropLast_in_π_dropLast bw_pkg v h)
  -- u ≠ m_w when lA.length ≥ 1 (m_w is in π'.support.tail).
  -- u ≠ m'_w (m'_w is in π'.support.tail via bw_rightArm_in_π_tail on first vertex of rA.support).
  have h_u_neq_m' : u ≠ m'_w := by
    intro h_eq
    apply hu_tail_π'
    have h_in_rA : m'_w ∈ rA.support := by
      rw [marg_support_cons_form rA]; exact List.mem_cons_self
    have h_m'_in : m'_w ∈ π'.support.tail :=
      bw_rightArm_in_π_tail bw_pkg m'_w h_in_rA
    rw [← h_eq] at h_m'_in
    exact h_m'_in
  -- v ≠ m_w (m_w is in π'.support.dropLast via bw_m_in_π_dropLast).
  have h_v_neq_m : v ≠ m_w := by
    intro h_eq
    apply hv_drop_π'
    have h_m_in : m_w ∈ π'.support.dropLast := bw_m_in_π_dropLast bw_pkg
    rw [← h_eq] at h_m_in
    exact h_m_in
  -- Expand the reversed leftArm to a G walk.
  have h_lA_rev_dir : lA.reverse.IsDirected :=
    marg_isDirected_reverse_of_isAllBackward h_lB
  obtain ⟨ρ_L, hρ_L_dir, _, hρ_L_supp, hρ_L_tail, hρ_L_drop⟩ :=
    exists_directed_of_marg_directed (G := G) W lA.reverse h_lA_rev_dir
  -- Expand the rightArm.
  obtain ⟨ρ_R, hρ_R_dir, _, hρ_R_supp, hρ_R_tail, hρ_R_drop⟩ :=
    exists_directed_of_marg_directed (G := G) W rA h_rD
  have hρ_L_rev_back : ρ_L.reverse.IsAllBackward :=
    marg_isAllBackward_reverse_of_isDirected hρ_L_dir
  -- u ∉ ρ_L.support.tail.dropLast (strict interior of ρ_L, G-side).
  -- This uses the combined tail+dropLast bounds: ρ_L.support.tail.dropLast ⊆ (lA.reverse.support.tail
  -- ∩ lA.reverse.support.dropLast) ∪ W = lA.reverse.support.tail.dropLast ∪ W.
  -- lA.reverse.support.tail.dropLast (strict interior of lA.reverse) = lA.support.tail.dropLast set-wise.
  -- u ∉ lA.support.tail.dropLast (h_u_notin_lA_int). u ∉ W. Done.
  have h_u_notin_ρL_int : u ∉ ρ_L.support.tail.dropLast := by
    intro h_in
    have h_tail : u ∈ ρ_L.support.tail := List.dropLast_subset _ h_in
    have h_drop : u ∈ ρ_L.support.dropLast :=
      marg_tail_dropLast_subset_dropLast _ h_in
    rcases hρ_L_tail u h_tail with h_lA_t | h_W
    · rcases hρ_L_drop u h_drop with h_lA_d | h_W
      · -- u ∈ lA.reverse.support.tail AND u ∈ lA.reverse.support.dropLast.
        -- → u ∈ lA.reverse.support.tail.dropLast set-wise.
        -- lA.reverse.support.tail.dropLast set-wise: u is in lA.reverse.support strictly between head and last.
        -- lA.reverse goes m_w → ... → u. Strict interior: positions 1..end-1.
        -- This is set-equal to lA.support.tail.dropLast (since reversing a list gives set-equal support tail.dropLast).
        -- Specifically: l.reverse.tail = l.dropLast.reverse, l.reverse.dropLast = l.tail.reverse,
        -- so l.reverse.tail.dropLast = (l.dropLast.reverse).dropLast = (l.dropLast.tail).reverse (set-wise).
        -- Hmm. Let me compute: lA.reverse.support = lA.support.reverse.
        -- lA.reverse.support.tail = lA.support.reverse.tail = (lA.support.dropLast).reverse.
        -- lA.reverse.support.dropLast = lA.support.reverse.dropLast = (lA.support.tail).reverse.
        -- Intersection of these as sets:
        --   (lA.support.dropLast).reverse ∩ (lA.support.tail).reverse
        --   = (lA.support.dropLast ∩ lA.support.tail).reverse  (as sets, since reverse preserves set)
        --   = (lA.support.tail.dropLast).reverse  (since for any list, the intersection of dropLast and tail is tail.dropLast set-wise).
        -- Wait, actually it's the set tail ∩ dropLast = tail.dropLast set-wise (as proven by inspection).
        -- Need to check: u ∈ lA.reverse.support.tail (list/set) AND u ∈ lA.reverse.support.dropLast (list/set).
        -- Goal: u ∈ lA.support.tail.dropLast.
        rw [marg_support_reverse, List.tail_reverse, List.mem_reverse] at h_lA_t
        rw [marg_support_reverse, List.dropLast_reverse, List.mem_reverse] at h_lA_d
        -- h_lA_t : u ∈ lA.support.dropLast.
        -- h_lA_d : u ∈ lA.support.tail.
        -- u ∈ lA.support.tail and lA.support.dropLast → u ∈ lA.support.tail.dropLast (by marg_mem_tail_dropLast).
        -- Apply marg_mem_tail_dropLast: x ∈ tail, x ∈ dropLast → x ∈ tail.dropLast.
        have : u ∈ lA.support.tail.dropLast := by
          -- We have u ∈ lA.support.tail (h_lA_d) and u ∈ lA.support.dropLast (h_lA_t).
          -- We need u ∈ lA.support.tail.dropLast.
          -- lA.support.tail.dropLast = elements at positions 1..lA.length-1.
          -- lA.support.tail = elements at positions 1..lA.length.
          -- lA.support.dropLast = elements at positions 0..lA.length-1.
          -- Intersection: positions 1..lA.length-1. So set-wise, tail ∩ dropLast = tail.dropLast.
          -- For lists, this requires the no-repeats property, which we don't have generally.
          -- But: u ∈ lA.support.tail means u is at some pos i with 1 ≤ i ≤ lA.length.
          -- u ∈ lA.support.dropLast means u is at some pos j with 0 ≤ j ≤ lA.length-1.
          -- If u appears at both an "≥ 1" and a "≤ lA.length-1" position, then either it's the same position
          -- (in 1..lA.length-1, i.e. strict interior) or different positions (i.e., it repeats).
          -- For our purposes, u ∈ tail.dropLast iff u appears at some pos in 1..lA.length-1.
          -- If u is only at positions 0 and lA.length (the endpoints), then u is in tail (pos lA.length) and dropLast (pos 0), but NOT tail.dropLast.
          -- So the marg_mem_tail_dropLast claim is WRONG in general.
          -- Hmm.
          -- Wait, lA.support.tail.dropLast is a fixed list. set-wise it's the set of elements appearing in positions 1..lA.length-1.
          -- u ∈ tail.dropLast iff u appears at some such position.
          -- If u appears only at positions 0 and lA.length (endpoints), then u ∉ tail.dropLast.
          -- But u IS in tail (pos lA.length) and in dropLast (pos 0). So tail ∩ dropLast is NOT necessarily tail.dropLast for lists with duplicates.
          -- BUT: lA.support has u at position 0 (head, since lA starts at u). For u to be at pos lA.length, u = end of lA = m_w. So m_w = u.
          -- In that case, u appears at positions 0 and lA.length. u ∉ positions 1..lA.length-1 (which are in π'.support.tail, hence not u).
          -- So u ∈ tail (because of pos lA.length) and u ∈ dropLast (because of pos 0), but u ∉ tail.dropLast. → marg_mem_tail_dropLast FAILS here.
          --
          -- So if m_w = u, we don't get a contradiction by this route.
          -- But: m_w = u case might still be handled separately (lA.length = 0 trivially, since lA is from u to m_w = u, so empty; but if lA.length ≥ 1, m_w = u means a cycle in lA, which is unusual).
          --
          -- Hmm. OK let me reconsider when m_w = u. lA : Walk (marg) u m_w, with m_w = u. Then lA is a closed walk from u to u.
          -- lA.support has u at head and last. If lA.length = 0, support = [u]. Otherwise it has u and intermediate.
          -- The bifurcation property u ∉ π'.support.tail says u doesn't repeat in π' tail. π'.support has u only at pos 0.
          -- lA.support ⊆ π'.support.dropLast. If u ∈ lA.support.tail (pos ≥ 1 of lA), then u ∈ π'.support.tail (via leftArm tail helper), contradicting u ∉ π'.support.tail.
          -- So u ∉ lA.support.tail. I.e., u doesn't appear at any position ≥ 1 of lA.support.
          -- So m_w = lA.support.getLast ≠ u (if lA.length ≥ 1).
          -- Conclusion: if lA.length ≥ 1, m_w ≠ u.
          --
          -- So: u ∈ lA.support.tail → u appears at pos ≥ 1 → u ∈ π'.support.tail (contradiction).
          -- This is bw_leftArm_tail_in_π_tail + hu_tail_π'.
          --
          -- So if u ∈ lA.support.tail (h_lA_d), we already have a contradiction!
          exact absurd (bw_leftArm_tail_in_π_tail bw_pkg u h_lA_d) hu_tail_π'
        -- We never get here because the contradiction above already returned.
        exact absurd this h_u_notin_lA_int
      · exact hu h_W
    · exact hu h_W
  -- Symmetrically, we need facts about ρ_R for the v-side.
  -- v ∉ ρ_R.support.tail (= the strict tail).
  -- ρ_R.support.tail ⊆ rA.support.tail ∪ W. rA.support.tail ⊆ π'.support.tail (by bw_rightArm_tail wait — we need a different helper).
  -- Actually rA.support ⊆ π'.support.tail (entirely). So rA.support.tail ⊆ π'.support.tail.
  -- And v ∈ rA.support.tail would mean v ∈ π'.support.tail. But that's not directly a contradiction for v.
  -- Wait, we need v ∉ new_walk.support.dropLast. So we care about ρ_R.support.dropLast.
  -- ρ_R.support.dropLast ⊆ rA.support.dropLast ∪ W. rA.support.dropLast ⊆ π'.support.dropLast (by bw_rightArm_dropLast).
  -- v ∉ π'.support.dropLast (hv_drop_π'). v ∉ W (hv). So v ∉ ρ_R.support.dropLast.
  have h_v_notin_ρR_drop : v ∉ ρ_R.support.dropLast := by
    intro h_in
    rcases hρ_R_drop v h_in with hrA | hW
    · exact hv_drop_π' (bw_rightArm_dropLast_in_π_dropLast bw_pkg v hrA)
    · exact hv hW
  -- Case-split on the hinge.
  cases hg with
  | forward h => exact absurd h_hIS (by simp)
  | backward h =>
    -- h : m_w ⟵[marg] m'_w means (m'_w, m_w) ∈ marg.E.
    have h_E : (m'_w, m_w) ∈ (G.marginalize W).E := h
    rw [CDMG.mem_marginalize_E] at h_E
    obtain ⟨_, _, q, hq_dir, hq_int, hq_pos⟩ := h_E
    cases q with
    | nil _ => simp at hq_pos
    | @cons _ y _ step rest =>
      cases step with
      | backward _ => exact absurd hq_dir (by simp)
      | bidir _ => exact absurd hq_dir (by simp)
      | forward h_step =>
        have h_rest_dir : rest.IsDirected := by simpa using hq_dir
        have h_rest_rev_back : rest.reverse.IsAllBackward :=
          marg_isAllBackward_reverse_of_isDirected h_rest_dir
        -- Build the new walk.
        let new_walk : Walk G u v :=
          ρ_L.reverse.append (rest.reverse.append (.cons (.backward h_step) ρ_R))
        -- Useful: q.support = m'_w :: rest.support. q.support.tail = rest.support.
        -- q.support.tail.dropLast = rest.support.dropLast ⊆ W (interior of q).
        have h_rest_dropLast_W : ∀ x ∈ rest.support.dropLast, x ∈ W := by
          intro x hx
          have : x ∈ (Walk.cons (.forward h_step) rest).support.tail.dropLast := by
            rw [Walk.support_cons, List.tail_cons]; exact hx
          exact hq_int x this
        -- y is in W if rest.length ≥ 1 (y is the second vertex of q, an interior of q).
        -- If rest.length = 0, y = m_w (q becomes a single edge m'_w → y = m_w).
        -- We'll handle the y vertex via dichotomy if needed.
        -- The new walk's support:
        -- new_walk.support = ρ_L.reverse.support.dropLast
        --                  ++ rest.reverse.support.dropLast
        --                  ++ (y :: ρ_R.support)
        have h_rest_rev_supp_ne : rest.reverse.support ≠ [] := rest.reverse.marg_support_ne_nil
        have h_ρR_supp_ne : ρ_R.support ≠ [] := ρ_R.marg_support_ne_nil
        have h_new_walk_supp_eq : new_walk.support =
            ρ_L.reverse.support.dropLast ++ rest.reverse.support.dropLast ++
            (y :: ρ_R.support) := by
          show (ρ_L.reverse.append (rest.reverse.append _)).support = _
          rw [marg_support_append, marg_support_append, Walk.support_cons]
          -- Now LHS = ρ_L.reverse.support.dropLast ++ (rest.reverse.support.dropLast ++ (y :: ρ_R.support))
          -- RHS = (ρ_L.reverse.support.dropLast ++ rest.reverse.support.dropLast) ++ (y :: ρ_R.support)
          rw [← List.append_assoc]
        -- The dropLast of new_walk.support:
        -- new_walk.support.dropLast = (ρ_L.reverse.support.dropLast ++ rest.reverse.support.dropLast ++ (y :: ρ_R.support)).dropLast.
        -- (y :: ρ_R.support) is non-empty. Its dropLast = y :: ρ_R.support.dropLast (when ρ_R.support ≠ [], which is always).
        -- Then we have ρ_L.reverse.support.dropLast ++ rest.reverse.support.dropLast ++ (y :: ρ_R.support.dropLast).
        -- Hmm let me just use direct manipulation.
        left
        refine ⟨new_walk, ⟨h_uv_ne, ?_, ?_, ?_⟩, ?_⟩
        · -- u ∉ new_walk.support.tail.
          intro h_u_in
          rw [h_new_walk_supp_eq] at h_u_in
          -- new_walk.support = A ++ B ++ C where A = ρ_L.reverse.support.dropLast,
          -- B = rest.reverse.support.dropLast, C = y :: ρ_R.support.
          -- support.tail = ...
          -- Case 1: A is empty. Then support = B ++ C, support.tail = ...
          by_cases h_A_empty : ρ_L.reverse.support.dropLast = []
          · -- ρ_L.reverse.support.dropLast = [] means ρ_L.reverse.support = [u] (a single vertex), so ρ_L.length = 0, m_w = u.
            -- Subcase analysis on B.
            rw [h_A_empty, List.nil_append] at h_u_in
            by_cases h_B_empty : rest.reverse.support.dropLast = []
            · -- rest.reverse.support.dropLast = [] means rest.length = 0, y = m_w.
              rw [h_B_empty, List.nil_append, List.tail_cons] at h_u_in
              -- h_u_in : u ∈ ρ_R.support.
              -- ρ_R.support ⊆ rA.support ∪ W. So u ∈ rA.support ∨ u ∈ W. Both contradict.
              rcases hρ_R_supp u h_u_in with hrA | hW
              · exact h_u_notin_rA hrA
              · exact hu hW
            · rw [list_tail_append_of_ne_nil _ h_B_empty] at h_u_in
              rcases List.mem_append.mp h_u_in with h_in_B_tail | h_in_C
              · -- h_in_B_tail : u ∈ rest.reverse.support.dropLast.tail.
                -- = u in strict interior of rest.reverse.
                -- This is set-wise = u in rest.support.tail.dropLast = strict interior of rest.
                -- Strict interior of rest is in q's interior (= rest.support.dropLast ⊆ W).
                -- Actually: rest.support.tail.dropLast ⊆ rest.support.dropLast ⊆ W.
                have h_u_in_rd : u ∈ rest.support.tail.dropLast := by
                  rw [marg_support_reverse, List.dropLast_reverse,
                      List.tail_reverse, List.mem_reverse] at h_in_B_tail
                  exact h_in_B_tail
                have h_u_drop : u ∈ rest.support.dropLast :=
                  marg_tail_dropLast_subset_dropLast _ h_u_in_rd
                exact hu (h_rest_dropLast_W u h_u_drop)
              · -- h_in_C : u ∈ (y :: ρ_R.support).
                rcases List.mem_cons.mp h_in_C with h_eq_y | h_in_ρR
                · -- u = y. y is the second vertex of q.
                  -- y is the FIRST interior vertex of q if rest.length ≥ 1, or = m_w if rest.length = 0.
                  -- We're in the case h_B_empty = False, so rest.reverse.support.dropLast ≠ [], so rest.length ≥ 1.
                  -- Then y ∈ q.support.tail.dropLast (the interior of q), so y ∈ W.
                  have h_rest_pos : 1 ≤ rest.length := by
                    by_contra h
                    push_neg at h
                    have h_rest_nil : rest.length = 0 := by omega
                    have : rest.reverse.support.dropLast = [] := by
                      cases hrest : rest with
                      | nil _ => simp [hrest]
                      | cons _ _ => simp [Walk.length_cons, hrest] at h_rest_nil
                    exact h_B_empty this
                  -- u = y. So u ∈ (Walk.cons (.forward h_step) rest).support.tail.dropLast.
                  have h_u_int : u ∈ (Walk.cons (.forward h_step) rest).support.tail.dropLast := by
                    have h_rest_tail_ne : rest.support.tail ≠ [] := by
                      intro h_emp
                      have : rest.support.tail.length = 0 := by rw [h_emp]; rfl
                      rw [List.length_tail, Walk.support_length] at this
                      omega
                    rw [Walk.support_cons, List.tail_cons,
                        marg_support_cons_form rest,
                        List.dropLast_cons_of_ne_nil h_rest_tail_ne]
                    rw [h_eq_y]; exact List.mem_cons_self
                  exact hu (hq_int u h_u_int)
                · -- u ∈ ρ_R.support → u ∈ rA.support ∨ W.
                  rcases hρ_R_supp u h_in_ρR with hrA | hW
                  · exact h_u_notin_rA hrA
                  · exact hu hW
          · -- ρ_L.reverse.support.dropLast ≠ [].
            rw [List.append_assoc, list_tail_append_of_ne_nil _ h_A_empty] at h_u_in
            rcases List.mem_append.mp h_u_in with h_in_A_tail | h_in_BC
            · -- h_in_A_tail : u ∈ ρ_L.reverse.support.dropLast.tail.
              -- This is set-wise = u in strict interior of ρ_L.reverse = u in ρ_L.support.tail.dropLast.
              -- We showed h_u_notin_ρL_int.
              exact h_u_notin_ρL_int (marg_mem_reverse_strict_interior h_in_A_tail)
            · -- u ∈ rest.reverse.support.dropLast ++ (y :: ρ_R.support).
              rcases List.mem_append.mp h_in_BC with h_in_B | h_in_C
              · -- u ∈ rest.reverse.support.dropLast.
                -- = u in rest.reverse.support (drop last). Set-wise = u in rest.support.tail.
                -- u ∈ rest.support.tail means u appears at position 1..end of rest.support.
                -- end of rest is m_w. So u could be m_w (if u = m_w) or interior of rest.
                -- If u = m_w: then m_w = u. Need to check this case.
                -- If u is interior of rest: u ∈ rest.support.tail.dropLast ⊆ W. Contradiction.
                have h_u_rest_tail : u ∈ rest.support.tail :=
                  marg_mem_reverse_dropLast_to_tail h_in_B
                -- u ∈ rest.support.tail. Need: u = m_w (end) or u ∈ interior (in W).
                -- Use: m_w = u is impossible if lA.length ≥ 1 (since u ∉ lA.support.tail, m_w = lA's last is u → would put u in lA.support.tail).
                -- Wait: lA's last is m_w. If lA.length = 0, then m_w = u (lA is nil u).
                -- So m_w = u iff lA.length = 0.
                -- And lA.length = 0 corresponds to lA.reverse.length = 0, so ρ_L.reverse.support.dropLast = ∅ (case h_A_empty was true).
                -- We're in h_A_empty = False, so lA.reverse.length ≥ 1 (since ρ_L.reverse.support.dropLast ≠ ∅).
                -- Actually it's ρ_L.reverse.length ≥ 1, not lA.length ≥ 1.
                -- Hmm: ρ_L.reverse.length = ρ_L.length, which can be ≥ lA.reverse.length (by the expander).
                -- So ρ_L.length ≥ 1 doesn't imply lA.length ≥ 1.
                -- Let me think differently.
                -- u ∈ rest.support.tail. The last element of rest.support is m_w.
                -- If u = m_w: u = m_w. Then we'd need a different argument.
                -- If u is at a position 1..rest.length-1: u ∈ rest.support.dropLast.tail = strict interior of rest.
                -- Wait rest.support.tail = positions 1..rest.length (includes last m_w).
                -- For u to be in rest.support.tail and NOT the last (m_w), need u at position 1..rest.length-1 = interior of rest.
                -- Interior of rest = rest.support.tail.dropLast. rest.support.tail.dropLast ⊆ rest.support.dropLast ⊆ W.
                -- So u ∈ W. Contradiction.
                -- Or u = m_w (the last of rest).
                by_cases h_u_eq_m : u = m_w
                · -- u = m_w. lA : Walk (marg) u m_w with u = m_w. lA is a closed walk.
                  -- We have h_lA_d... hmm this is the case where u = m_w which we need to handle.
                  -- u = m_w. Then m_w ∈ π'.support and m_w ∈ π'.support.dropLast (via bw_m_in_π_dropLast).
                  -- u = m_w = start of π'. So u is the start AND m_w. For the bifurcation IsBifurcation, we have u ≠ v (h_uv_ne).
                  -- u = m_w means lA is a closed walk u → u. The leftArm has length k ≥ 0.
                  -- If lA.length = 0, lA = nil u, m_w = u. This is the trivial leftArm case.
                  -- We're in h_A_empty = False, but ρ_L.reverse is the G-expansion of lA.reverse. lA.length = 0 → lA.reverse = nil u → ρ_L = nil u → ρ_L.reverse = nil u → ρ_L.reverse.support.dropLast = []. So h_A_empty would be True. Contradiction.
                  -- So lA.length ≥ 1. Then lA.support has u at head and m_w = u at last. u appears at positions 0 and lA.length.
                  -- u ∉ π'.support.tail. lA.support \ {head=u} ⊆ π'.support.tail. So u ∉ lA.support.tail. But u IS at position lA.length, which is in lA.support.tail (if lA.length ≥ 1). Contradiction.
                  -- Specifically: u ∈ lA.support.tail (= positions 1..lA.length of lA.support, includes position lA.length = m_w = u).
                  -- → u ∈ π'.support.tail via bw_leftArm_tail_in_π_tail. → contradiction with hu_tail_π'.
                  exfalso
                  apply hu_tail_π'
                  apply bw_leftArm_tail_in_π_tail bw_pkg
                  -- Need: u ∈ lA.support.tail.
                  -- lA goes from u to m_w = u. lA.support has u at last (position lA.length).
                  -- For u ∈ lA.support.tail (set-wise), need lA.length ≥ 1.
                  -- We need to derive lA.length ≥ 1 from h_A_empty = False.
                  -- h_A_empty = False means ρ_L.reverse.support.dropLast ≠ [].
                  -- ρ_L.reverse.support.dropLast = [] iff ρ_L.reverse.length = 0 iff ρ_L.length = 0.
                  -- The expander gives lA.reverse.length ≤ ρ_L.length.
                  -- If lA.length = 0, then lA.reverse.length = 0, ρ_L.length ≥ 0 (could be 0 or more).
                  -- Actually, the expander gives the BIGGER walk, so ρ_L.length ≥ lA.reverse.length = 0. So ρ_L.length could be anything.
                  -- Hmm, ρ_L.length ≥ lA.reverse.length, so if lA.length = 0, ρ_L.length ≥ 0, no info.
                  -- BUT: ρ_L was expanded from lA.reverse. If lA.length = 0, lA.reverse = nil. The expander on nil returns nil (length 0). So ρ_L = nil m_w, ρ_L.length = 0, ρ_L.reverse.support.dropLast = [].
                  -- So h_A_empty = False (ρ_L.reverse.support.dropLast ≠ []) → lA.length ≥ 1.
                  -- Hmm but the expander could potentially expand even nil to non-nil (no, looking at its zero case, it returns nil for nil).
                  -- Let me verify by looking at the expander code.
                  --
                  -- Actually the proof of exists_directed_of_marg_directed has:
                  --   | nil v0 => refine ⟨Walk.nil v0, ...⟩
                  -- So nil → nil. ρ_L.length = lA.reverse.length when lA.reverse is nil.
                  -- ρ_L.length ≥ 1 (since ρ_L.reverse.support.dropLast ≠ []) ↔ lA.length ≥ 1.
                  -- Hmm but ρ_L.length ≥ lA.reverse.length is the bound; reverse implication needs argument.
                  -- Actually: if lA = nil, lA.reverse = nil. Expander on nil produces nil. So ρ_L = nil. ρ_L.length = 0. ρ_L.reverse.support.dropLast = [].
                  -- So h_A_empty would be True if lA.length = 0. Contradiction with h_A_empty = False.
                  -- Hence lA.length ≥ 1.
                  -- Then lA.support.tail = positions 1..lA.length. u ∈ lA.support.tail at position lA.length (= u = m_w).
                  -- Need to formalize this.
                  rw [marg_support_cons_form lA]
                  -- lA.support = u :: lA.support.tail. So lA.support.tail is the list-tail.
                  -- u ∈ lA.support.tail iff u ∈ (u :: lA.support.tail).tail.
                  -- We need u ∈ lA.support.tail. lA.support.tail's last element is m_w (since lA ends at m_w).
                  -- u = m_w. So u is the last of lA.support.tail. So u ∈ lA.support.tail iff lA.support.tail ≠ [].
                  -- lA.support.tail ≠ [] iff lA.support.length ≥ 2 iff lA.length ≥ 1.
                  -- We argued lA.length ≥ 1 above. Let me formalize.
                  have h_lA_pos : 1 ≤ lA.length := by
                    by_contra h_neg
                    push_neg at h_neg
                    
                    have h_lA_nil : lA.length = 0 := by omega
                    -- Derive contradiction: lA.length = 0 → lA.reverse.support = [m_w] (singleton)
                    -- → lA.reverse.support.dropLast = [].
                    -- hρ_L_drop says ρ_L.support.dropLast ⊆ lA.reverse.support.dropLast ∪ W = ∅ ∪ W = W.
                    -- But m_w is the start of ρ_L, so m_w ∈ ρ_L.support.dropLast (when ρ_L.length ≥ 1).
                    -- h_A_empty says ρ_L.reverse.support.dropLast ≠ [], which forces ρ_L.length ≥ 1.
                    -- So m_w ∈ W. Combined with u = m_w (h_u_eq_m) and u ∉ W (hu): contradiction.
                    -- Step 1: ρ_L.length ≥ 1.
                    have h_ρL_pos : 1 ≤ ρ_L.length := by
                      by_contra h_neg2
                      push_neg at h_neg2
                      apply h_A_empty
                      have h_len_zero : ρ_L.length = 0 := by omega
                      have h_supp_len : ρ_L.support.length = 1 := by
                        rw [Walk.support_length, h_len_zero]
                      obtain ⟨a, ha⟩ : ∃ a, ρ_L.support = [a] :=
                        List.length_eq_one_iff.mp h_supp_len
                      rw [marg_support_reverse, ha]
                      simp
                    -- Step 2: m_w ∈ ρ_L.support.dropLast.
                    have h_ρL_drop_ne : ρ_L.support.dropLast ≠ [] := by
                      intro h_emp
                      have : ρ_L.support.dropLast.length = 0 := by rw [h_emp]; rfl
                      rw [List.length_dropLast, Walk.support_length] at this
                      omega
                    have h_ρL_tail_ne : ρ_L.support.tail ≠ [] := by
                      intro h_emp
                      have : ρ_L.support.tail.length = 0 := by rw [h_emp]; rfl
                      rw [List.length_tail, Walk.support_length] at this
                      omega
                    have h_m_w_in_dropLast : m_w ∈ ρ_L.support.dropLast := by
                      rw [marg_support_cons_form ρ_L,
                          List.dropLast_cons_of_ne_nil h_ρL_tail_ne]
                      simp
                    -- Step 3: apply hρ_L_drop.
                    rcases hρ_L_drop m_w h_m_w_in_dropLast with h_in_lA | h_W
                    · -- m_w ∈ lA.reverse.support.dropLast. But lA.length = 0 forces dropLast = [].
                      have h_lA_rev_supp_len : lA.reverse.support.length = 1 := by
                        rw [Walk.support_length, marg_length_reverse, h_lA_nil]
                      obtain ⟨a, ha⟩ : ∃ a, lA.reverse.support = [a] :=
                        List.length_eq_one_iff.mp h_lA_rev_supp_len
                      rw [ha] at h_in_lA
                      simp at h_in_lA
                    · -- m_w ∈ W. With u = m_w: u ∈ W, contradicting hu.
                      apply hu
                      rw [h_u_eq_m]
                      exact h_W
                  -- lA.length ≥ 1.
                  -- lA.support.tail's last element is m_w. u = m_w. So u ∈ lA.support.tail iff lA.support.tail ≠ [].
                  -- lA.support.tail.length = lA.length ≥ 1. So lA.support.tail ≠ [].
                  -- So u ∈ lA.support.tail (as the last element).
                  -- Specifically:
                  show u ∈ (u :: lA.support.tail).tail
                  rw [List.tail_cons]
                  -- Need u ∈ lA.support.tail. lA.support.tail's last is m_w = u. So if lA.support.tail ≠ [], u is in it.
                  have h_lA_tail_ne : lA.support.tail ≠ [] := by
                    intro h_emp
                    have : lA.support.tail.length = 0 := by rw [h_emp]; rfl
                    rw [List.length_tail, Walk.support_length] at this
                    omega
                  -- lA.support.tail's last element = m_w (since lA.support's last is m_w, and tail preserves the last).
                  have h_last_eq : lA.support.tail.getLast h_lA_tail_ne = m_w :=
                    marg_support_tail_getLast lA h_lA_pos
                  -- Construct lA.support.tail.getLast h_lA_tail_ne = u via composition.
                  have h_chain : lA.support.tail.getLast h_lA_tail_ne = u :=
                    h_last_eq.trans h_u_eq_m.symm
                  -- Use explicit motive to avoid dependent-index motive issues.
                  exact @Eq.subst α (fun x => x ∈ lA.support.tail) _ _ h_chain
                    (List.getLast_mem h_lA_tail_ne)
                · -- u ≠ m_w. So u is strict interior of rest. u ∈ rest.support.tail.dropLast.
                  -- u ∈ rest.support.tail, u ≠ m_w (last of rest), so u ∈ rest.support.tail.dropLast (strict interior of rest).
                  -- rest.support.tail = (rest.support.tail.dropLast) ++ [m_w] (when non-empty).
                  -- u ∈ rest.support.tail and u ≠ m_w → u ∈ rest.support.tail.dropLast.
                  -- Then rest.support.tail.dropLast ⊆ rest.support.dropLast (via tail_dropLast_subset_dropLast).
                  -- rest.support.dropLast ⊆ W. → u ∈ W. Contradiction.
                  have h_rest_supp_ne : rest.support ≠ [] := rest.marg_support_ne_nil
                  have h_rest_tail_ne : rest.support.tail ≠ [] := by
                    intro h_emp
                    -- rest.support.tail = [] → rest.length = 0 → rest.reverse.support.dropLast = [].
                    -- But we're in the case h_in_B (non-empty support), so rest.reverse.support.dropLast ≠ [].
                    -- Wait, rest.reverse.support.dropLast non-empty iff rest.length ≥ 1.
                    -- The fact we're using h_in_B means h_in_B : u ∈ rest.reverse.support.dropLast,
                    -- which implies rest.reverse.support.dropLast ≠ []. So rest.length ≥ 1.
                    have : rest.support.tail.length = 0 := by rw [h_emp]; rfl
                    rw [List.length_tail, Walk.support_length] at this
                    -- this : rest.length + 1 - 1 = 0 → rest.length = 0.
                    have h_rest_len : rest.length = 0 := by omega
                    -- rest.length = 0 → rest = nil → rest.reverse.support.dropLast = [].
                    have : rest.reverse.support.dropLast = [] := by
                      cases hrest : rest with
                      | nil _ => simp [hrest]
                      | cons _ _ => simp [Walk.length_cons, hrest] at h_rest_len
                    -- h_in_B : u ∈ rest.reverse.support.dropLast. With this = [], contradiction.
                    rw [this] at h_in_B; simp at h_in_B
                  -- rest.support.tail's last is m_w. u ≠ m_w. u ∈ rest.support.tail.
                  -- → u ∈ rest.support.tail.dropLast.
                  have h_rest_pos : 1 ≤ rest.length := by
                    by_contra h
                    push_neg at h
                    apply h_rest_tail_ne
                    have h_zero : rest.length = 0 := by omega
                    have : rest.support.tail.length = 0 := by
                      rw [List.length_tail, Walk.support_length, h_zero]
                    exact List.length_eq_zero_iff.mp this
                  have h_rest_last : rest.support.tail.getLast h_rest_tail_ne = m_w :=
                    marg_support_tail_getLast rest h_rest_pos
                  -- u ∈ rest.support.tail = rest.support.tail.dropLast ++ [m_w] (using getLast).
                  have h_u_in_dl : u ∈ rest.support.tail.dropLast := by
                    -- u ∈ rest.support.tail. Decompose into dropLast ++ [last].
                    have h_decomp : rest.support.tail =
                        rest.support.tail.dropLast ++ [rest.support.tail.getLast h_rest_tail_ne] :=
                      (List.dropLast_append_getLast h_rest_tail_ne).symm
                    rw [h_decomp] at h_u_rest_tail
                    rcases List.mem_append.mp h_u_rest_tail with h | h
                    · exact h
                    · simp only [List.mem_singleton] at h
                      rw [h_rest_last] at h
                      exact absurd h h_u_eq_m
                  -- u ∈ rest.support.tail.dropLast → u ∈ rest.support.dropLast → u ∈ W.
                  exact hu (h_rest_dropLast_W u
                    (marg_tail_dropLast_subset_dropLast _ h_u_in_dl))
              · -- u ∈ (y :: ρ_R.support).
                rcases List.mem_cons.mp h_in_C with h_eq_y | h_in_ρR
                · -- u = y. Use the same argument as before.
                  by_cases h_rest_pos : 1 ≤ rest.length
                  · have h_rest_tail_ne : rest.support.tail ≠ [] := by
                      intro h_emp
                      have : rest.support.tail.length = 0 := by rw [h_emp]; rfl
                      rw [List.length_tail, Walk.support_length] at this
                      omega
                    have h_u_int : u ∈ (Walk.cons (.forward h_step) rest).support.tail.dropLast := by
                      rw [Walk.support_cons, List.tail_cons,
                          marg_support_cons_form rest,
                          List.dropLast_cons_of_ne_nil h_rest_tail_ne]
                      rw [h_eq_y]; exact List.mem_cons_self
                    exact hu (hq_int u h_u_int)
                  · push_neg at h_rest_pos
                    -- rest.length = 0 → rest = nil m_w → y = m_w. So u = y = m_w.
                    have h_y_eq_m : y = m_w := by
                      have h_rest_len : rest.length = 0 := by omega
                      -- rest : Walk G y m_w, rest.length = 0, so rest = nil and y = m_w.
                      cases rest with
                      | nil _ => rfl
                      | cons _ _ => simp [Walk.length_cons] at h_rest_len
                    -- u = y = m_w. Use the same argument as in the u = m_w case above.
                    have h_u_eq_m : u = m_w := h_eq_y.trans h_y_eq_m
                    -- u = m_w. Then we need to derive a contradiction (similar to above u = m_w handling).
                    -- u ∈ lA.support.tail iff lA.length ≥ 1 (with last = m_w = u).
                    -- lA.length ≥ 1 because h_A_empty is False (we're in the outer h_A_empty = False branch).
                    -- Wait, we're inside the h_A_empty = True (h_A_empty case here is the first one!).
                    -- Let me trace: h_A_empty = True ↔ ρ_L.reverse.support.dropLast = [].
                    -- If h_A_empty is True, then lA.length might be 0 too.
                    -- In which case m_w = u directly. And we are claiming u = m_w. That's CONSISTENT but not contradiction.
                    -- Hmm.
                    -- Actually we're at h_A_empty = True branch (line 1106: by_cases h_A_empty : ... · h_A_empty = True ...)
                    -- Wait let me re-read.
                    -- I see — we're DEEP inside, so we should check.
                    exfalso
                    -- u = m_w = y. Apply h_v_neq_m? No, that's about v.
                    -- Let's go: u = m_w. m_w ∈ π'.support somewhere.
                    -- The simplest: derive m_w ≠ u in the case lA.length ≥ 1. lA.length = 0 is also possible.
                    -- This subcase is genuinely tricky. Let me defer with sorry.
                    -- Actually wait, we ARE in h_A_empty = False here (NOT True). Let me re-check the indentation/branching.
                    -- The h_A_empty case is at line 1106 (rewrite). The first · is h_A_empty = True (line 1107).
                    -- The second · branch is at line 1166 ("ρ_L.reverse.support.dropLast ≠ []"), h_A_empty = False.
                    -- We're inside that second · branch... let me check.
                    -- Looking at the indent: the line 1338 case "u ∈ (y :: ρ_R.support)" is INSIDE the h_A_empty = False branch.
                    -- So we have h_A_empty = False, meaning lA.length ≥ 1 (well, ρ_L.reverse.length ≥ 1).
                    -- If lA.length ≥ 1: u = m_w = end of lA → u ∈ lA.support.tail → u ∈ π'.support.tail → contradiction.
                    -- But we need lA.length ≥ 1 from ρ_L.reverse.length ≥ 1. Yes, via expander.
                    -- The expander gives ρ_L.length ≥ lA.reverse.length = lA.length.
                    -- So ρ_L.length ≥ 1 doesn't imply lA.length ≥ 1. Hmm.
                    -- HOWEVER: if lA.length = 0, then lA.reverse = nil m_w. The expander on nil returns nil. So ρ_L = nil. So ρ_L.length = 0.
                    -- ρ_L.length = 0 → ρ_L.support = [m_w] (single vertex). → ρ_L.reverse = nil m_w → ρ_L.reverse.support.dropLast = [].
                    -- → h_A_empty would be True. Contradiction with h_A_empty = False (we're in this branch).
                    -- So lA.length ≥ 1.
                    have h_lA_pos : 1 ≤ lA.length := by
                      by_contra h_neg
                      push_neg at h_neg
                      have h_lA_zero : lA.length = 0 := by omega
                      -- Same argument as in the u = m_w case: lA.length = 0 → ρ_L.support.dropLast ⊆ W
                      -- (since lA.reverse.support.dropLast = []), and m_w ∈ ρ_L.support.dropLast
                      -- (since ρ_L.length ≥ 1 from h_A_empty). Hence m_w ∈ W, so u = m_w ∈ W,
                      -- contradicting hu.
                      have h_ρL_pos : 1 ≤ ρ_L.length := by
                        by_contra h_neg2
                        push_neg at h_neg2
                        apply h_A_empty
                        have h_len_zero : ρ_L.length = 0 := by omega
                        have h_supp_len : ρ_L.support.length = 1 := by
                          rw [Walk.support_length, h_len_zero]
                        obtain ⟨a, ha⟩ : ∃ a, ρ_L.support = [a] :=
                          List.length_eq_one_iff.mp h_supp_len
                        rw [marg_support_reverse, ha]
                        simp
                      have h_ρL_tail_ne : ρ_L.support.tail ≠ [] := by
                        intro h_emp
                        have : ρ_L.support.tail.length = 0 := by rw [h_emp]; rfl
                        rw [List.length_tail, Walk.support_length] at this
                        omega
                      have h_m_w_in_dropLast : m_w ∈ ρ_L.support.dropLast := by
                        rw [marg_support_cons_form ρ_L,
                            List.dropLast_cons_of_ne_nil h_ρL_tail_ne]
                        simp
                      rcases hρ_L_drop m_w h_m_w_in_dropLast with h_in_lA | h_W
                      · have h_lA_rev_supp_len : lA.reverse.support.length = 1 := by
                          rw [Walk.support_length, marg_length_reverse, h_lA_zero]
                        obtain ⟨a, ha⟩ : ∃ a, lA.reverse.support = [a] :=
                          List.length_eq_one_iff.mp h_lA_rev_supp_len
                        rw [ha] at h_in_lA
                        simp at h_in_lA
                      · apply hu
                        rw [h_u_eq_m]
                        exact h_W
                    -- lA.length ≥ 1. m_w = u. Use bw_leftArm_tail_in_π_tail.
                    apply hu_tail_π'
                    apply bw_leftArm_tail_in_π_tail bw_pkg
                    rw [marg_support_cons_form lA]
                    show u ∈ (u :: lA.support.tail).tail
                    rw [List.tail_cons]
                    have h_lA_tail_ne : lA.support.tail ≠ [] := by
                      intro h_emp
                      have : lA.support.tail.length = 0 := by rw [h_emp]; rfl
                      rw [List.length_tail, Walk.support_length] at this
                      omega
                    have h_last_eq : lA.support.tail.getLast h_lA_tail_ne = m_w :=
                      marg_support_tail_getLast lA h_lA_pos
                    have h_chain : lA.support.tail.getLast h_lA_tail_ne = u :=
                      h_last_eq.trans h_u_eq_m.symm
                    exact @Eq.subst α (fun x => x ∈ lA.support.tail) _ _ h_chain
                      (List.getLast_mem h_lA_tail_ne)
                · -- u ∈ ρ_R.support → u ∈ rA.support ∨ u ∈ W. Both contradict.
                  rcases hρ_R_supp u h_in_ρR with hrA | hW
                  · exact h_u_notin_rA hrA
                  · exact hu hW
        · -- v ∉ new_walk.support.dropLast.
          intro h_v_in
          rw [h_new_walk_supp_eq] at h_v_in
          -- new_walk.support = A ++ B ++ (y :: ρ_R.support).
          -- new_walk.support.dropLast = A ++ B ++ (y :: ρ_R.support).dropLast (since y :: ρ_R is non-empty
          -- and dropLast distributes over ++ when the right side is non-empty).
          -- (y :: ρ_R.support).dropLast = y :: ρ_R.support.dropLast (when ρ_R.support non-empty).
          have h_yρR_ne : (y :: ρ_R.support) ≠ ([] : List α) := List.cons_ne_nil _ _
          rw [List.dropLast_append_of_ne_nil h_yρR_ne] at h_v_in
          -- Now h_v_in : v ∈ (ρ_L.reverse.support.dropLast ++ rest.reverse.support.dropLast)
          --                  ++ (y :: ρ_R.support).dropLast.
          rcases List.mem_append.mp h_v_in with h_in_AB | h_in_C
          · rcases List.mem_append.mp h_in_AB with h_in_A | h_in_B
            · -- v ∈ ρ_L.reverse.support.dropLast.
              have h_v_ρL_tail : v ∈ ρ_L.support.tail :=
                marg_mem_reverse_dropLast_to_tail h_in_A
              rcases hρ_L_tail v h_v_ρL_tail with hlA | hW
              · have h_v_lA : v ∈ lA.support := by
                  rw [marg_support_reverse, List.tail_reverse, List.mem_reverse] at hlA
                  exact List.dropLast_subset _ hlA
                exact h_v_notin_lA h_v_lA
              · exact hv hW
            · -- v ∈ rest.reverse.support.dropLast.
              have h_v_rest_tail : v ∈ rest.support.tail :=
                marg_mem_reverse_dropLast_to_tail h_in_B
              have h_rest_tail_ne : rest.support.tail ≠ [] := by
                intro h_emp
                rw [h_emp] at h_v_rest_tail; simp at h_v_rest_tail
              have h_rest_pos : 1 ≤ rest.length := by
                by_contra h
                push_neg at h
                apply h_rest_tail_ne
                have h_zero : rest.length = 0 := by omega
                have : rest.support.tail.length = 0 := by
                  rw [List.length_tail, Walk.support_length, h_zero]
                exact List.length_eq_zero_iff.mp this
              have h_rest_last : rest.support.tail.getLast h_rest_tail_ne = m_w :=
                marg_support_tail_getLast rest h_rest_pos
              have h_v_in_dl : v ∈ rest.support.tail.dropLast := by
                have h_decomp : rest.support.tail =
                    rest.support.tail.dropLast ++ [rest.support.tail.getLast h_rest_tail_ne] :=
                  (List.dropLast_append_getLast h_rest_tail_ne).symm
                rw [h_decomp] at h_v_rest_tail
                rcases List.mem_append.mp h_v_rest_tail with h | h
                · exact h
                · simp only [List.mem_singleton] at h
                  rw [h_rest_last] at h
                  exact absurd h h_v_neq_m
              exact hv (h_rest_dropLast_W v
                (marg_tail_dropLast_subset_dropLast _ h_v_in_dl))
          · -- v ∈ (y :: ρ_R.support).dropLast = y :: ρ_R.support.dropLast (when ρ_R.support non-empty).
            rw [List.dropLast_cons_of_ne_nil h_ρR_supp_ne] at h_in_C
            simp only [List.mem_cons] at h_in_C
            rcases h_in_C with h_eq_y | h_in_ρR_dl
            · -- v = y.
              by_cases h_rest_pos : 1 ≤ rest.length
              · have h_rest_tail_ne : rest.support.tail ≠ [] := by
                  intro h_emp
                  have : rest.support.tail.length = 0 := by rw [h_emp]; rfl
                  rw [List.length_tail, Walk.support_length] at this
                  omega
                have h_v_int : v ∈ (Walk.cons (.forward h_step) rest).support.tail.dropLast := by
                  rw [Walk.support_cons, List.tail_cons,
                      marg_support_cons_form rest,
                      List.dropLast_cons_of_ne_nil h_rest_tail_ne]
                  rw [h_eq_y]; exact List.mem_cons_self
                exact hv (hq_int v h_v_int)
              · push_neg at h_rest_pos
                have h_rest_len : rest.length = 0 := by omega
                have h_y_eq_m : y = m_w := by
                  cases rest with
                  | nil _ => rfl
                  | cons _ _ => simp [Walk.length_cons] at h_rest_len
                exact h_v_neq_m (h_eq_y.trans h_y_eq_m)
            · -- v ∈ ρ_R.support.dropLast.
              exact h_v_notin_ρR_drop h_in_ρR_dl
        · -- BifurcationWitness.
          refine ⟨?_⟩
          refine
            { m := y
              m' := m'_w
              leftArm := ρ_L.reverse.append rest.reverse
              hinge := .backward h_step
              rightArm := ρ_R
              decompose := ?_
              leftBackward := ?_
              hingeIntoSource := by simp
              rightDirected := hρ_R_dir }
          · -- decompose: new_walk = leftArm.append (cons hinge rightArm)
            -- new_walk = ρ_L.reverse.append (rest.reverse.append (cons (.backward h_step) ρ_R))
            --       = (ρ_L.reverse.append rest.reverse).append (cons (.backward h_step) ρ_R)
            -- by associativity.
            symm
            exact marg_append_assoc ρ_L.reverse rest.reverse _
          · -- leftBackward.
            rw [marg_isAllBackward_append]
            exact ⟨hρ_L_rev_back, h_rest_rev_back⟩
        · -- Support tracking: ∀ x ∈ new_walk.support, x ∈ π'.support ∨ x ∈ W.
          intro x hx
          rw [h_new_walk_supp_eq] at hx
          rcases List.mem_append.mp hx with hAB | hC
          · rcases List.mem_append.mp hAB with hA | hB
            · -- x ∈ ρ_L.reverse.support.dropLast → ρ_L.support → π'.support ∨ W.
              have hx_ρL : x ∈ ρ_L.reverse.support := List.dropLast_subset _ hA
              have hx_ρL' : x ∈ ρ_L.support := marg_mem_reverse_support hx_ρL
              rcases hρ_L_supp x hx_ρL' with hlA | hW
              · have hx_lA : x ∈ lA.support := marg_mem_reverse_support hlA
                exact Or.inl (List.dropLast_subset _
                  (bw_leftArm_in_π_dropLast bw_pkg x hx_lA))
              · exact Or.inr hW
            · -- x ∈ rest.reverse.support.dropLast.
              have hx_rest : x ∈ rest.reverse.support := List.dropLast_subset _ hB
              have hx_rest' : x ∈ rest.support := marg_mem_reverse_support hx_rest
              rw [marg_support_eq_dropLast_append_last rest] at hx_rest'
              rcases List.mem_append.mp hx_rest' with hint | h_end
              · exact Or.inr (h_rest_dropLast_W x hint)
              · simp at h_end
                rw [h_end]
                exact Or.inl (List.dropLast_subset _ (bw_m_in_π_dropLast bw_pkg))
          · -- x ∈ y :: ρ_R.support.
            rcases List.mem_cons.mp hC with rfl | hx_ρR
            · -- x = y. Case on rest.length.
              by_cases h_rest_pos : 1 ≤ rest.length
              · refine Or.inr (h_rest_dropLast_W x ?_)
                have h_rest_tail_ne : rest.support.tail ≠ [] := by
                  intro h_emp
                  have : rest.support.tail.length = 0 := by rw [h_emp]; rfl
                  rw [List.length_tail, Walk.support_length] at this; omega
                rw [marg_support_cons_form rest,
                    List.dropLast_cons_of_ne_nil h_rest_tail_ne]
                exact List.mem_cons_self
              · push_neg at h_rest_pos
                have h_rest_zero : rest.length = 0 := by omega
                have h_y_eq_m : x = m_w := by
                  cases rest with
                  | nil _ => rfl
                  | cons _ _ => simp [Walk.length_cons] at h_rest_zero
                rw [h_y_eq_m]
                exact Or.inl (List.dropLast_subset _ (bw_m_in_π_dropLast bw_pkg))
            · rcases hρ_R_supp x hx_ρR with hrA | hW
              · exact Or.inl (List.mem_of_mem_tail
                  (bw_rightArm_in_π_tail bw_pkg x hrA))
              · exact Or.inr hW
  | bidir h =>
    -- h : (m_w, m'_w) ∈ (G.marginalize W).L.
    have h_L : (m_w, m'_w) ∈ (G.marginalize W).L := h
    rw [CDMG.mem_marginalize_L] at h_L
    obtain ⟨_, _, _, _, _, h_bif_disj⟩ := h_L
    rcases h_bif_disj with ⟨σ, hσ_bif, hσ_int⟩ | ⟨σ, hσ_bif, hσ_int⟩
    · -- Subcase A: σ : Walk G m_w m'_w with σ.IsBifurcation ∧ σ.InteriorIn W.
      obtain ⟨h_mw_neq_mwp, h_mw_tail_σ, h_mwp_drop_σ, ⟨σ_bw⟩⟩ := hσ_bif
      -- Build new_walk in G between u and v.
      let new_walk : Walk G u v :=
        ρ_L.reverse.append
          (σ_bw.leftArm.append (.cons σ_bw.hinge (σ_bw.rightArm.append ρ_R)))
      -- Compute new_walk.support directly.
      have h_new_walk_supp : new_walk.support =
          ρ_L.reverse.support.dropLast ++ σ_bw.leftArm.support.dropLast ++
            (σ_bw.m :: σ_bw.rightArm.support.dropLast ++ ρ_R.support) := by
        show (ρ_L.reverse.append
              (σ_bw.leftArm.append (.cons σ_bw.hinge (σ_bw.rightArm.append ρ_R)))).support = _
        rw [marg_support_append, marg_support_append, Walk.support_cons, marg_support_append,
            ← List.append_assoc]
        rfl
      -- σ.support decomposition via σ_bw.decompose (rewrite on LHS only to dodge motive issues).
      have h_σ_supp : σ.support =
          σ_bw.leftArm.support.dropLast ++ (σ_bw.m :: σ_bw.rightArm.support) := by
        conv_lhs => rw [σ_bw.decompose]
        rw [marg_support_append, Walk.support_cons]
      -- σ.support.dropLast removes the last element (= m'_w, end of σ_bw.rightArm).
      have h_rA_supp_ne : σ_bw.rightArm.support ≠ [] := σ_bw.rightArm.marg_support_ne_nil
      have h_σ_supp_dropLast : σ.support.dropLast =
          σ_bw.leftArm.support.dropLast ++ (σ_bw.m :: σ_bw.rightArm.support.dropLast) := by
        rw [h_σ_supp]
        rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
        congr 1
        rw [List.dropLast_cons_of_ne_nil h_rA_supp_ne]
      -- σ_bw.rightArm.support.dropLast in W: interior position.
      -- σ_bw.m in W when σ_bw.leftArm.length ≥ 1.
      -- σ_bw.m' in W when σ_bw.rightArm.length ≥ 1.
      -- Helper: σ_bw.leftArm.support.dropLast.tail ⊆ σ.support.tail.dropLast (set-wise).
      -- σ_bw.leftArm.support.dropLast in σ.support.dropLast (positions 0..lA.length-1).
      -- σ_bw.rightArm.support.dropLast in σ.support.tail.dropLast positions...
      have h_ρR_supp_ne : ρ_R.support ≠ [] := ρ_R.marg_support_ne_nil
      have h_rA_inner_ne : (σ_bw.m :: σ_bw.rightArm.support.dropLast ++ ρ_R.support) ≠ [] :=
        List.cons_ne_nil _ _
      -- Key helper: σ_bw.leftArm.support.dropLast.tail ⊆ σ.support.tail.dropLast.
      -- Used to transfer "u ∈ leftArm interior" → "u ∈ σ-interior" → "u ∈ W".
      have h_lA_dl_tail_subset : ∀ x ∈ σ_bw.leftArm.support.dropLast.tail,
          x ∈ σ.support.tail.dropLast := by
        intro x hx
        -- σ.support.tail = σ_bw.leftArm.support.dropLast.tail ++ (σ_bw.m :: σ_bw.rightArm.support)
        -- when σ_bw.leftArm.support.dropLast ≠ [] (which is implied by hx).
        have h_B_ne : σ_bw.leftArm.support.dropLast ≠ [] := by
          intro h_emp; rw [h_emp] at hx; simp at hx
        have h_σ_tail : σ.support.tail =
            σ_bw.leftArm.support.dropLast.tail ++ (σ_bw.m :: σ_bw.rightArm.support) := by
          rw [h_σ_supp, list_tail_append_of_ne_nil _ h_B_ne]
        rw [h_σ_tail]
        rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
        rw [List.dropLast_cons_of_ne_nil h_rA_supp_ne]
        exact List.mem_append.mpr (Or.inl hx)
      -- Similarly: σ_bw.rightArm.support.dropLast ⊆ σ.support.tail.dropLast.
      have h_rA_dl_subset : ∀ x ∈ σ_bw.rightArm.support.dropLast,
          x ∈ σ.support.tail.dropLast := by
        intro x hx
        -- σ.support.tail = σ_bw.leftArm.support.dropLast.tail ++ (σ_bw.m :: σ_bw.rightArm.support)
        -- if leftArm.support.dropLast ≠ []; else σ.support.tail = σ_bw.rightArm.support.
        -- σ.support.tail.dropLast ⊇ σ_bw.m :: σ_bw.rightArm.support.dropLast (or similar).
        have h_σ_int_eq : σ.support.tail.dropLast =
            (σ.support.tail.dropLast) := rfl
        -- Use σ.support.dropLast = lA.dropLast ++ (σ_bw.m :: rA.dropLast).
        -- σ.support.tail.dropLast = (σ.support.tail).dropLast.
        -- (σ.support.dropLast).tail = σ.support.tail.dropLast (when σ.support.dropLast is non-empty).
        -- σ.support.dropLast = lA.dropLast ++ (σ_bw.m :: rA.dropLast). lA.dropLast and rA-piece may be empty.
        clear h_σ_int_eq
        by_cases h_B_ne : σ_bw.leftArm.support.dropLast = []
        · -- leftArm empty. σ.support = σ_bw.m :: σ_bw.rightArm.support.
          -- σ.support.tail = σ_bw.rightArm.support. σ.support.tail.dropLast = σ_bw.rightArm.support.dropLast.
          have h_σ_tail : σ.support.tail = σ_bw.rightArm.support := by
            rw [h_σ_supp, h_B_ne, List.nil_append]; rfl
          rw [h_σ_tail]; exact hx
        · -- leftArm non-empty. σ.support.tail.dropLast contains σ_bw.m :: σ_bw.rightArm.support.dropLast at the end.
          have h_σ_tail : σ.support.tail =
              σ_bw.leftArm.support.dropLast.tail ++ (σ_bw.m :: σ_bw.rightArm.support) := by
            rw [h_σ_supp, list_tail_append_of_ne_nil _ h_B_ne]
          rw [h_σ_tail]
          rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
          rw [List.dropLast_cons_of_ne_nil h_rA_supp_ne]
          exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx))
      -- σ_bw.m ∈ σ.support.tail.dropLast (always, regardless of leftArm.length).
      -- Reason: σ_bw.m is at position σ_bw.leftArm.length of σ.support, which is in [0, σ.length-1] since σ.length ≥ σ_bw.leftArm.length + 1.
      -- If σ_bw.leftArm.length = 0, position is 0, so σ_bw.m = m_w (NOT in tail.dropLast).
      -- If σ_bw.leftArm.length ≥ 1, position ≥ 1, so in tail; and ≤ σ.length-1, so in dropLast.
      -- So σ_bw.m ∈ σ.support.tail.dropLast iff σ_bw.leftArm.length ≥ 1.
      have h_σm_in_tail_dl_of_lA_pos : 1 ≤ σ_bw.leftArm.length → σ_bw.m ∈ σ.support.tail.dropLast := by
        intro h_lA_pos
        have h_B_ne : σ_bw.leftArm.support.dropLast ≠ [] := by
          intro h_emp
          have h_len : σ_bw.leftArm.support.dropLast.length = σ_bw.leftArm.length := by
            rw [List.length_dropLast, Walk.support_length]; omega
          rw [h_emp, List.length_nil] at h_len; omega
        have h_σ_tail : σ.support.tail =
            σ_bw.leftArm.support.dropLast.tail ++ (σ_bw.m :: σ_bw.rightArm.support) := by
          rw [h_σ_supp, list_tail_append_of_ne_nil _ h_B_ne]
        rw [h_σ_tail]
        rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
        rw [List.dropLast_cons_of_ne_nil h_rA_supp_ne]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_self))
      left
      refine ⟨new_walk, ⟨h_uv_ne, ?_, ?_, ?_⟩, ?_⟩
      · -- u ∉ new_walk.support.tail.
        intro h_u_in
        rw [h_new_walk_supp] at h_u_in
        -- new_walk.support = A ++ B ++ E where A = ρ_L.reverse.support.dropLast,
        -- B = σ_bw.leftArm.support.dropLast,
        -- E = σ_bw.m :: σ_bw.rightArm.support.dropLast ++ ρ_R.support.
        -- Case on A:
        by_cases h_A_empty : ρ_L.reverse.support.dropLast = []
        · -- A = []. ρ_L.length = 0 → m_w = u.
          rw [h_A_empty, List.nil_append] at h_u_in
          have h_ρL_zero : ρ_L.length = 0 := by
            have h_len : ρ_L.reverse.support.dropLast.length = ρ_L.length := by
              rw [List.length_dropLast, Walk.support_length, marg_length_reverse]; omega
            rw [h_A_empty, List.length_nil] at h_len; omega
          have h_m_eq_u : m_w = u := by
            cases ρ_L with
            | nil _ => rfl
            | cons _ _ => simp [Walk.length_cons] at h_ρL_zero
          -- Case on B:
          by_cases h_B_empty : σ_bw.leftArm.support.dropLast = []
          · -- A = [], B = []. h_u_in : u ∈ (σ_bw.m :: rA.dl ++ ρ_R.s).tail.
            rw [h_B_empty, List.nil_append, List.cons_append, List.tail_cons] at h_u_in
            rcases List.mem_append.mp h_u_in with h_in_rA_dl | h_in_ρR
            · exact hu (hσ_int u (h_rA_dl_subset u h_in_rA_dl))
            · rcases hρ_R_supp u h_in_ρR with hrA | hW
              · exact h_u_notin_rA hrA
              · exact hu hW
          · -- A = [], B ≠ []. New support = B ++ E. New support starts with m_w = u.
            rw [list_tail_append_of_ne_nil _ h_B_empty] at h_u_in
            rcases List.mem_append.mp h_u_in with h_in_B_tail | h_in_E
            · exact hu (hσ_int u (h_lA_dl_tail_subset u h_in_B_tail))
            · -- u ∈ E. After cons_append normalization:
              -- E = σ_bw.m :: (σ_bw.rightArm.support.dropLast ++ ρ_R.support).
              rw [List.cons_append] at h_in_E
              rcases List.mem_cons.mp h_in_E with h_eq_σm | h_in_rest
              · -- u = σ_bw.m. σ_bw.m ∈ σ.support.tail.dropLast (since lA non-empty here).
                have h_lAσ_pos : 1 ≤ σ_bw.leftArm.length := by
                  by_contra h_neg
                  push_neg at h_neg
                  have h_zero : σ_bw.leftArm.length = 0 := by omega
                  apply h_B_empty
                  have h_supp_len : σ_bw.leftArm.support.length = 1 := by
                    rw [Walk.support_length, h_zero]
                  obtain ⟨a, ha⟩ : ∃ a, σ_bw.leftArm.support = [a] :=
                    List.length_eq_one_iff.mp h_supp_len
                  rw [ha]; rfl
                apply hu
                rw [h_eq_σm]
                exact hσ_int σ_bw.m (h_σm_in_tail_dl_of_lA_pos h_lAσ_pos)
              · rcases List.mem_append.mp h_in_rest with h_in_rA_dl | h_in_ρR
                · exact hu (hσ_int u (h_rA_dl_subset u h_in_rA_dl))
                · rcases hρ_R_supp u h_in_ρR with hrA | hW
                  · exact h_u_notin_rA hrA
                  · exact hu hW
        · -- A ≠ []. m_w ≠ u.
          rw [List.append_assoc, list_tail_append_of_ne_nil _ h_A_empty] at h_u_in
          rcases List.mem_append.mp h_u_in with h_in_A_tail | h_in_BE
          · exact h_u_notin_ρL_int (marg_mem_reverse_strict_interior h_in_A_tail)
          · -- u ∈ B ++ E. Need m_w ≠ u to discharge the m_w head of B.
            -- Derive lA.length ≥ 1.
            have h_lA_pos : 1 ≤ lA.length := by
              by_contra h_neg
              push_neg at h_neg
              have h_lA_zero : lA.length = 0 := by omega
              have h_m_eq_u' : m_w = u := by
                cases lA with
                | nil _ => rfl
                | cons _ _ => simp [Walk.length_cons] at h_lA_zero
              -- ρ_L.length must be 0 (otherwise contradiction via hρ_L_drop on m_w).
              -- Once ρ_L.length = 0, ρ_L = nil, ρ_L.reverse.support.dropLast = [], contradicting h_A_empty.
              apply h_A_empty
              by_cases h_ρL_zero : ρ_L.length = 0
              · cases ρ_L with
                | nil _ => simp
                | cons _ _ => simp [Walk.length_cons] at h_ρL_zero
              · exfalso
                push_neg at h_ρL_zero
                have h_ρL_pos : 1 ≤ ρ_L.length := by omega
                have h_ρL_tail_ne : ρ_L.support.tail ≠ [] := by
                  intro h_emp
                  have : ρ_L.support.tail.length = 0 := by rw [h_emp]; rfl
                  rw [List.length_tail, Walk.support_length] at this; omega
                have h_m_w_in_dl : m_w ∈ ρ_L.support.dropLast := by
                  rw [marg_support_cons_form ρ_L, List.dropLast_cons_of_ne_nil h_ρL_tail_ne]
                  simp
                rcases hρ_L_drop m_w h_m_w_in_dl with h_in_lA | h_W
                · have h_lA_rev_supp_len : lA.reverse.support.length = 1 := by
                    rw [Walk.support_length, marg_length_reverse, h_lA_zero]
                  obtain ⟨a, ha⟩ : ∃ a, lA.reverse.support = [a] :=
                    List.length_eq_one_iff.mp h_lA_rev_supp_len
                  rw [ha] at h_in_lA; simp at h_in_lA
                · exact hu (h_m_eq_u' ▸ h_W)
            -- m_w ≠ u via lA.length ≥ 1.
            have h_m_neq_u : m_w ≠ u := fun h_eq =>
              hu_tail_π' (h_eq ▸ bw_m_in_π_tail_of_leftArm_pos bw_pkg h_lA_pos)
            rcases List.mem_append.mp h_in_BE with h_in_B | h_in_E
            · -- u ∈ σ_bw.leftArm.support.dropLast. Either head (m_w) or tail.
              have h_B_ne : σ_bw.leftArm.support.dropLast ≠ [] := by
                intro h_emp; rw [h_emp] at h_in_B; simp at h_in_B
              have h_lA_head : σ_bw.leftArm.support = m_w :: σ_bw.leftArm.support.tail :=
                marg_support_cons_form σ_bw.leftArm
              have h_lA_tail_ne : σ_bw.leftArm.support.tail ≠ [] := by
                intro h_emp
                rw [h_lA_head, h_emp] at h_B_ne
                simp at h_B_ne
              have h_B_eq : σ_bw.leftArm.support.dropLast =
                  m_w :: σ_bw.leftArm.support.tail.dropLast := by
                conv_lhs => rw [h_lA_head]
                exact List.dropLast_cons_of_ne_nil h_lA_tail_ne
              rw [h_B_eq] at h_in_B
              rcases List.mem_cons.mp h_in_B with h_eq | h_in_tail_dl
              · exact h_m_neq_u h_eq.symm
              · have : u ∈ σ_bw.leftArm.support.dropLast.tail := by
                  rw [h_B_eq, List.tail_cons]; exact h_in_tail_dl
                exact hu (hσ_int u (h_lA_dl_tail_subset u this))
            · -- u ∈ E. After cons_append normalization:
              rw [List.cons_append] at h_in_E
              rcases List.mem_cons.mp h_in_E with h_eq_σm | h_in_rest
              · -- u = σ_bw.m.
                by_cases h_lAσ_pos : 1 ≤ σ_bw.leftArm.length
                · apply hu
                  rw [h_eq_σm]
                  exact hσ_int σ_bw.m (h_σm_in_tail_dl_of_lA_pos h_lAσ_pos)
                · push_neg at h_lAσ_pos
                  have h_lAσ_zero : σ_bw.leftArm.length = 0 := by omega
                  have aux : ∀ {a b : α} (p : Walk G a b), p.length = 0 → a = b := by
                    intros a b p hp
                    cases p with
                    | nil _ => rfl
                    | cons _ _ => simp [Walk.length_cons] at hp
                  have h_σm_eq_mw : σ_bw.m = m_w := (aux σ_bw.leftArm h_lAσ_zero).symm
                  exact h_m_neq_u (h_eq_σm.trans h_σm_eq_mw).symm
              · rcases List.mem_append.mp h_in_rest with h_in_rA_dl | h_in_ρR
                · exact hu (hσ_int u (h_rA_dl_subset u h_in_rA_dl))
                · rcases hρ_R_supp u h_in_ρR with hrA | hW
                  · exact h_u_notin_rA hrA
                  · exact hu hW
      · -- v ∉ new_walk.support.dropLast.
        intro h_v_in
        rw [h_new_walk_supp] at h_v_in
        -- new_walk.support = (A ++ B) ++ (σ_bw.m :: σ_bw.rightArm.support.dropLast ++ ρ_R.support).
        -- The right part is non-empty, so dropLast distributes.
        have h_E_ne : (σ_bw.m :: σ_bw.rightArm.support.dropLast ++ ρ_R.support) ≠ [] := by
          rw [List.cons_append]; exact List.cons_ne_nil _ _
        rw [List.dropLast_append_of_ne_nil h_E_ne] at h_v_in
        -- Inner part: ((σ_bw.m :: σ_bw.rightArm.support.dropLast) ++ ρ_R.support).dropLast
        -- = (σ_bw.m :: σ_bw.rightArm.support.dropLast) ++ ρ_R.support.dropLast (since ρ_R.support ≠ []).
        rw [List.dropLast_append_of_ne_nil h_ρR_supp_ne] at h_v_in
        -- h_v_in : v ∈ (ρ_L.reverse.support.dropLast ++ σ_bw.leftArm.support.dropLast)
        --              ++ (σ_bw.m :: σ_bw.rightArm.support.dropLast ++ ρ_R.support.dropLast).
        rcases List.mem_append.mp h_v_in with h_in_AB | h_in_C
        · rcases List.mem_append.mp h_in_AB with h_in_A | h_in_B
          · -- v ∈ ρ_L.reverse.support.dropLast → v ∈ ρ_L.support.tail.
            have h_v_ρL_tail : v ∈ ρ_L.support.tail :=
              marg_mem_reverse_dropLast_to_tail h_in_A
            rcases hρ_L_tail v h_v_ρL_tail with hlA | hW
            · have h_v_lA : v ∈ lA.support := by
                rw [marg_support_reverse, List.tail_reverse, List.mem_reverse] at hlA
                exact List.dropLast_subset _ hlA
              exact h_v_notin_lA h_v_lA
            · exact hv hW
          · -- v ∈ σ_bw.leftArm.support.dropLast.
            -- σ_bw.leftArm.support.dropLast starts with m_w (head). v = m_w contradicts h_v_neq_m.
            -- Otherwise v is in σ_bw.leftArm.support.dropLast.tail ⊆ σ.support.tail.dropLast ⊆ W.
            have h_B_ne : σ_bw.leftArm.support.dropLast ≠ [] := by
              intro h_emp; rw [h_emp] at h_in_B; simp at h_in_B
            have h_lA_head : σ_bw.leftArm.support = m_w :: σ_bw.leftArm.support.tail :=
              marg_support_cons_form σ_bw.leftArm
            have h_lA_tail_ne : σ_bw.leftArm.support.tail ≠ [] := by
              intro h_emp
              rw [h_lA_head, h_emp] at h_B_ne
              simp at h_B_ne
            have h_B_eq : σ_bw.leftArm.support.dropLast =
                m_w :: σ_bw.leftArm.support.tail.dropLast := by
              conv_lhs => rw [h_lA_head]
              exact List.dropLast_cons_of_ne_nil h_lA_tail_ne
            rw [h_B_eq] at h_in_B
            rcases List.mem_cons.mp h_in_B with h_eq | h_in_tail_dl
            · exact h_v_neq_m h_eq
            · have : v ∈ σ_bw.leftArm.support.dropLast.tail := by
                rw [h_B_eq, List.tail_cons]; exact h_in_tail_dl
              exact hv (hσ_int v (h_lA_dl_tail_subset v this))
        · -- v ∈ (σ_bw.m :: σ_bw.rightArm.support.dropLast) ++ ρ_R.support.dropLast.
          -- Cons_append: this equals σ_bw.m :: (σ_bw.rightArm.support.dropLast ++ ρ_R.support.dropLast).
          rcases List.mem_append.mp h_in_C with h_in_left | h_in_ρR_dl
          · -- v ∈ σ_bw.m :: σ_bw.rightArm.support.dropLast.
            rcases List.mem_cons.mp h_in_left with h_eq_σm | h_in_rA_dl
            · -- v = σ_bw.m.
              by_cases h_lAσ_pos : 1 ≤ σ_bw.leftArm.length
              · apply hv
                rw [h_eq_σm]
                exact hσ_int σ_bw.m (h_σm_in_tail_dl_of_lA_pos h_lAσ_pos)
              · push_neg at h_lAσ_pos
                have h_lAσ_zero : σ_bw.leftArm.length = 0 := by omega
                have aux : ∀ {a b : α} (p : Walk G a b), p.length = 0 → a = b := by
                  intros a b p hp
                  cases p with
                  | nil _ => rfl
                  | cons _ _ => simp [Walk.length_cons] at hp
                have h_σm_eq_mw : σ_bw.m = m_w := (aux σ_bw.leftArm h_lAσ_zero).symm
                exact h_v_neq_m (h_eq_σm.trans h_σm_eq_mw)
            · exact hv (hσ_int v (h_rA_dl_subset v h_in_rA_dl))
          · -- v ∈ ρ_R.support.dropLast.
            rcases hρ_R_drop v h_in_ρR_dl with hrA | hW
            · exact h_v_notin_rA_drop hrA
            · exact hv hW
      · -- BifurcationWitness.
        refine ⟨?_⟩
        refine
          { m := σ_bw.m
            m' := σ_bw.m'
            leftArm := ρ_L.reverse.append σ_bw.leftArm
            hinge := σ_bw.hinge
            rightArm := σ_bw.rightArm.append ρ_R
            decompose := ?_
            leftBackward := ?_
            hingeIntoSource := σ_bw.hingeIntoSource
            rightDirected := ?_ }
        · -- decompose: new_walk = leftArm.append (.cons hinge rightArm).
          symm
          exact marg_append_assoc ρ_L.reverse σ_bw.leftArm _
        · -- leftBackward.
          rw [marg_isAllBackward_append]
          exact ⟨hρ_L_rev_back, σ_bw.leftBackward⟩
        · -- rightDirected.
          rw [marg_isDirected_append]
          exact ⟨σ_bw.rightDirected, hρ_R_dir⟩
      · -- Support tracking (.bidir-fwd subcase): new_walk.support ⊆ π'.support ∪ W.
        -- σ : Walk G m_w m'_w with σ.InteriorIn W (from hσ_int).
        -- σ.support's vertices are in {m_w, m'_w} ∪ W (interior in W; endpoints).
        -- Both m_w, m'_w ∈ π'.support.
        have h_σ_len_pos : 1 ≤ σ.length := by
          by_contra h
          push_neg at h
          have h_zero : σ.length = 0 := by omega
          have h_mm : m_w = m'_w := by
            cases σ with
            | nil _ => rfl
            | cons _ _ => simp [Walk.length_cons] at h_zero
          exact h_mw_neq_mwp h_mm
        have h_tail_ne : σ.support.tail ≠ [] := by
          intro h
          have : σ.support.tail.length = 0 := by rw [h]; rfl
          rw [List.length_tail, Walk.support_length] at this; omega
        have h_σ_supp_bound : ∀ x ∈ σ.support, x ∈ π'.support ∨ x ∈ W := by
          intro x hx
          by_cases hx_int : x ∈ σ.support.tail.dropLast
          · exact Or.inr (hσ_int x hx_int)
          · -- x ∈ σ.support, x ∉ interior. Then x = m_w or x = m'_w.
            have h_in : x ∈ σ.support.dropLast ∨ x = m'_w := by
              rw [marg_support_eq_dropLast_append_last σ] at hx
              rcases List.mem_append.mp hx with h | h
              · exact Or.inl h
              · simp at h; exact Or.inr h
            cases h_in with
            | inr h_eq =>
              rw [h_eq]
              refine Or.inl (List.mem_of_mem_tail (bw_rightArm_in_π_tail bw_pkg m'_w ?_))
              rw [marg_support_cons_form bw_pkg.rightArm]
              exact List.mem_cons_self
            | inl h_drop =>
              rw [marg_support_cons_form σ] at h_drop
              rw [List.dropLast_cons_of_ne_nil h_tail_ne] at h_drop
              rcases List.mem_cons.mp h_drop with rfl | hxt
              · exact Or.inl (List.dropLast_subset _ (bw_m_in_π_dropLast bw_pkg))
              · exact absurd hxt hx_int
        -- Now use h_σ_supp_bound on each piece of new_walk.support.
        intro x hx
        rw [h_new_walk_supp] at hx
        rcases List.mem_append.mp hx with hAB | hC
        · rcases List.mem_append.mp hAB with hA | hB
          · -- x ∈ ρ_L.reverse.support.dropLast.
            have hx_ρL : x ∈ ρ_L.reverse.support := List.dropLast_subset _ hA
            have hx_ρL' : x ∈ ρ_L.support := marg_mem_reverse_support hx_ρL
            rcases hρ_L_supp x hx_ρL' with hlA | hW
            · exact Or.inl (List.dropLast_subset _
                (bw_leftArm_in_π_dropLast bw_pkg x (marg_mem_reverse_support hlA)))
            · exact Or.inr hW
          · -- x ∈ σ_bw.leftArm.support.dropLast ⊆ σ.support.
            have hx_σ : x ∈ σ.support := by
              rw [h_σ_supp]
              exact List.mem_append.mpr (Or.inl hB)
            exact h_σ_supp_bound x hx_σ
        · -- x ∈ σ_bw.m :: σ_bw.rightArm.support.dropLast ++ ρ_R.support.
          rcases List.mem_append.mp hC with hC₁ | hC₂
          · rcases List.mem_cons.mp hC₁ with rfl | hxr
            · -- x = σ_bw.m. σ_bw.m ∈ σ.support (in leftArm's last position).
              have hx_σ : σ_bw.m ∈ σ.support := by
                rw [h_σ_supp]
                refine List.mem_append.mpr (Or.inr ?_)
                exact List.mem_cons_self
              exact h_σ_supp_bound _ hx_σ
            · -- x ∈ σ_bw.rightArm.support.dropLast ⊆ σ_bw.rightArm.support ⊆ σ.support.
              have hx_rA : x ∈ σ_bw.rightArm.support := List.dropLast_subset _ hxr
              have hx_σ : x ∈ σ.support := by
                rw [h_σ_supp]
                refine List.mem_append.mpr (Or.inr ?_)
                exact List.mem_cons_of_mem _ hx_rA
              exact h_σ_supp_bound x hx_σ
          · -- x ∈ ρ_R.support.
            rcases hρ_R_supp x hC₂ with hrA | hW
            · exact Or.inl (List.mem_of_mem_tail
                (bw_rightArm_in_π_tail bw_pkg x hrA))
            · exact Or.inr hW
    · -- Subcase B: σ : Walk G m'_w m_w with σ.IsBifurcation ∧ σ.InteriorIn W.
      obtain ⟨h_mwp_neq_mw, h_mwp_tail_σ, h_mw_drop_σ, ⟨σ_bw⟩⟩ := hσ_bif
      have hρ_R_rev_back : ρ_R.reverse.IsAllBackward :=
        marg_isAllBackward_reverse_of_isDirected hρ_R_dir
      -- Build new_walk in G between v and u.
      let new_walk : Walk G v u :=
        ρ_R.reverse.append
          (σ_bw.leftArm.append (.cons σ_bw.hinge (σ_bw.rightArm.append ρ_L)))
      -- Compute new_walk.support directly.
      have h_new_walk_supp : new_walk.support =
          ρ_R.reverse.support.dropLast ++ σ_bw.leftArm.support.dropLast ++
            (σ_bw.m :: σ_bw.rightArm.support.dropLast ++ ρ_L.support) := by
        show (ρ_R.reverse.append
              (σ_bw.leftArm.append (.cons σ_bw.hinge (σ_bw.rightArm.append ρ_L)))).support = _
        rw [marg_support_append, marg_support_append, Walk.support_cons, marg_support_append,
            ← List.append_assoc]
        rfl
      -- σ.support decomposition (here σ : Walk G m'_w m_w).
      have h_σ_supp : σ.support =
          σ_bw.leftArm.support.dropLast ++ (σ_bw.m :: σ_bw.rightArm.support) := by
        conv_lhs => rw [σ_bw.decompose]
        rw [marg_support_append, Walk.support_cons]
      have h_rA_supp_ne : σ_bw.rightArm.support ≠ [] := σ_bw.rightArm.marg_support_ne_nil
      have h_σ_supp_dropLast : σ.support.dropLast =
          σ_bw.leftArm.support.dropLast ++ (σ_bw.m :: σ_bw.rightArm.support.dropLast) := by
        rw [h_σ_supp]
        rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
        congr 1
        rw [List.dropLast_cons_of_ne_nil h_rA_supp_ne]
      have h_ρL_supp_ne : ρ_L.support ≠ [] := ρ_L.marg_support_ne_nil
      -- Helper: σ_bw.leftArm.support.dropLast.tail ⊆ σ.support.tail.dropLast.
      have h_lA_dl_tail_subset : ∀ x ∈ σ_bw.leftArm.support.dropLast.tail,
          x ∈ σ.support.tail.dropLast := by
        intro x hx
        have h_B_ne : σ_bw.leftArm.support.dropLast ≠ [] := by
          intro h_emp; rw [h_emp] at hx; simp at hx
        have h_σ_tail : σ.support.tail =
            σ_bw.leftArm.support.dropLast.tail ++ (σ_bw.m :: σ_bw.rightArm.support) := by
          rw [h_σ_supp, list_tail_append_of_ne_nil _ h_B_ne]
        rw [h_σ_tail]
        rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
        rw [List.dropLast_cons_of_ne_nil h_rA_supp_ne]
        exact List.mem_append.mpr (Or.inl hx)
      have h_rA_dl_subset : ∀ x ∈ σ_bw.rightArm.support.dropLast,
          x ∈ σ.support.tail.dropLast := by
        intro x hx
        by_cases h_B_ne : σ_bw.leftArm.support.dropLast = []
        · have h_σ_tail : σ.support.tail = σ_bw.rightArm.support := by
            rw [h_σ_supp, h_B_ne, List.nil_append]; rfl
          rw [h_σ_tail]; exact hx
        · have h_σ_tail : σ.support.tail =
              σ_bw.leftArm.support.dropLast.tail ++ (σ_bw.m :: σ_bw.rightArm.support) := by
            rw [h_σ_supp, list_tail_append_of_ne_nil _ h_B_ne]
          rw [h_σ_tail]
          rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
          rw [List.dropLast_cons_of_ne_nil h_rA_supp_ne]
          exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx))
      have h_σm_in_tail_dl_of_lA_pos : 1 ≤ σ_bw.leftArm.length → σ_bw.m ∈ σ.support.tail.dropLast := by
        intro h_lA_pos
        have h_B_ne : σ_bw.leftArm.support.dropLast ≠ [] := by
          intro h_emp
          have h_len : σ_bw.leftArm.support.dropLast.length = σ_bw.leftArm.length := by
            rw [List.length_dropLast, Walk.support_length]; omega
          rw [h_emp, List.length_nil] at h_len; omega
        have h_σ_tail : σ.support.tail =
            σ_bw.leftArm.support.dropLast.tail ++ (σ_bw.m :: σ_bw.rightArm.support) := by
          rw [h_σ_supp, list_tail_append_of_ne_nil _ h_B_ne]
        rw [h_σ_tail]
        rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
        rw [List.dropLast_cons_of_ne_nil h_rA_supp_ne]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_self))
      -- v-side analogs of h_u_notin_ρL_int, h_v_notin_ρR_drop.
      -- v ∉ ρ_R.support.tail.dropLast (strict interior of ρ_R, G-side).
      have h_v_notin_ρR_tail_dl : v ∉ ρ_R.support.tail.dropLast := by
        intro h_in
        have h_tail : v ∈ ρ_R.support.tail := List.dropLast_subset _ h_in
        have h_drop : v ∈ ρ_R.support.dropLast :=
          marg_tail_dropLast_subset_dropLast _ h_in
        rcases hρ_R_drop v h_drop with h_rA_d | h_W
        · exact h_v_notin_rA_drop h_rA_d
        · exact hv h_W
      -- u ∉ ρ_L.support.dropLast (u is the END of ρ_L; doesn't appear before).
      have h_u_notin_ρL_drop : u ∉ ρ_L.support.dropLast := by
        intro h_in
        rcases hρ_L_drop u h_in with hlA | hW
        · have h_u_lA_tail : u ∈ lA.support.tail := by
            rw [marg_support_reverse, List.dropLast_reverse, List.mem_reverse] at hlA
            exact hlA
          exact hu_tail_π' (bw_leftArm_tail_in_π_tail bw_pkg u h_u_lA_tail)
        · exact hu hW
      right
      refine ⟨new_walk, ⟨h_uv_ne.symm, ?_, ?_, ?_⟩, ?_⟩
      · -- v ∉ new_walk.support.tail.
        intro h_v_in
        rw [h_new_walk_supp] at h_v_in
        by_cases h_A_empty : ρ_R.reverse.support.dropLast = []
        · -- ρ_R.length = 0 → m'_w = v.
          rw [h_A_empty, List.nil_append] at h_v_in
          have h_ρR_zero : ρ_R.length = 0 := by
            have h_len : ρ_R.reverse.support.dropLast.length = ρ_R.length := by
              rw [List.length_dropLast, Walk.support_length, marg_length_reverse]; omega
            rw [h_A_empty, List.length_nil] at h_len; omega
          have h_mp_eq_v : m'_w = v := by
            cases ρ_R with
            | nil _ => rfl
            | cons _ _ => simp [Walk.length_cons] at h_ρR_zero
          by_cases h_B_empty : σ_bw.leftArm.support.dropLast = []
          · rw [h_B_empty, List.nil_append, List.cons_append, List.tail_cons] at h_v_in
            rcases List.mem_append.mp h_v_in with h_in_rA_dl | h_in_ρL
            · exact hv (hσ_int v (h_rA_dl_subset v h_in_rA_dl))
            · -- v ∈ ρ_L.support → v ∈ lA.reverse.support ∨ v ∈ W.
              rcases hρ_L_supp v h_in_ρL with hlA | hW
              · -- lA.reverse.support set-wise = lA.support.
                have h_v_lA : v ∈ lA.support := by
                  rw [marg_support_reverse, List.mem_reverse] at hlA; exact hlA
                exact h_v_notin_lA h_v_lA
              · exact hv hW
          · rw [list_tail_append_of_ne_nil _ h_B_empty] at h_v_in
            rcases List.mem_append.mp h_v_in with h_in_B_tail | h_in_E
            · exact hv (hσ_int v (h_lA_dl_tail_subset v h_in_B_tail))
            · rw [List.cons_append] at h_in_E
              rcases List.mem_cons.mp h_in_E with h_eq_σm | h_in_rest
              · have h_lAσ_pos : 1 ≤ σ_bw.leftArm.length := by
                  by_contra h_neg
                  push_neg at h_neg
                  have h_zero : σ_bw.leftArm.length = 0 := by omega
                  apply h_B_empty
                  have h_supp_len : σ_bw.leftArm.support.length = 1 := by
                    rw [Walk.support_length, h_zero]
                  obtain ⟨a, ha⟩ : ∃ a, σ_bw.leftArm.support = [a] :=
                    List.length_eq_one_iff.mp h_supp_len
                  rw [ha]; rfl
                apply hv
                rw [h_eq_σm]
                exact hσ_int σ_bw.m (h_σm_in_tail_dl_of_lA_pos h_lAσ_pos)
              · rcases List.mem_append.mp h_in_rest with h_in_rA_dl | h_in_ρL
                · exact hv (hσ_int v (h_rA_dl_subset v h_in_rA_dl))
                · rcases hρ_L_supp v h_in_ρL with hlA | hW
                  · have h_v_lA : v ∈ lA.support := by
                      rw [marg_support_reverse, List.mem_reverse] at hlA; exact hlA
                    exact h_v_notin_lA h_v_lA
                  · exact hv hW
        · -- ρ_R.reverse.support.dropLast ≠ []. ρ_R.length ≥ 1. m'_w ≠ v.
          rw [List.append_assoc, list_tail_append_of_ne_nil _ h_A_empty] at h_v_in
          rcases List.mem_append.mp h_v_in with h_in_A_tail | h_in_BE
          · -- v ∈ ρ_R.reverse.support.dropLast.tail → v ∈ ρ_R.support.tail.dropLast.
            exact h_v_notin_ρR_tail_dl (marg_mem_reverse_strict_interior h_in_A_tail)
          · -- Derive rA.length ≥ 1, then m'_w ≠ v.
            have h_rA_pos : 1 ≤ rA.length := by
              by_contra h_neg
              push_neg at h_neg
              have h_rA_zero : rA.length = 0 := by omega
              have aux : ∀ {a b : α} (p : Walk (G.marginalize W) a b), p.length = 0 → a = b := by
                intros a b p hp
                cases p with
                | nil _ => rfl
                | cons _ _ => simp [Walk.length_cons] at hp
              have h_mp_eq_v : m'_w = v := aux rA h_rA_zero
              apply h_A_empty
              by_cases h_ρR_zero : ρ_R.length = 0
              · cases ρ_R with
                | nil _ => simp
                | cons _ _ => simp [Walk.length_cons] at h_ρR_zero
              · exfalso
                push_neg at h_ρR_zero
                have h_ρR_pos : 1 ≤ ρ_R.length := by omega
                -- m'_w ∈ ρ_R.support.dropLast (start of ρ_R, ρ_R.length ≥ 1).
                have h_ρR_tail_ne : ρ_R.support.tail ≠ [] := by
                  intro h_emp
                  have : ρ_R.support.tail.length = 0 := by rw [h_emp]; rfl
                  rw [List.length_tail, Walk.support_length] at this; omega
                have h_mp_in_dl : m'_w ∈ ρ_R.support.dropLast := by
                  rw [marg_support_cons_form ρ_R, List.dropLast_cons_of_ne_nil h_ρR_tail_ne]
                  simp
                rcases hρ_R_drop m'_w h_mp_in_dl with h_in_rA | h_W
                · -- h_in_rA : m'_w ∈ rA.support.dropLast. But rA.length = 0 → rA.support = [m'_w].
                  --   rA.support.dropLast = []. Contradiction.
                  have h_rA_supp_len : rA.support.length = 1 := by
                    rw [Walk.support_length, h_rA_zero]
                  obtain ⟨a, ha⟩ : ∃ a, rA.support = [a] :=
                    List.length_eq_one_iff.mp h_rA_supp_len
                  rw [ha] at h_in_rA; simp at h_in_rA
                · exact hv (h_mp_eq_v ▸ h_W)
            have h_mp_neq_v : m'_w ≠ v := fun h_eq => by
              apply hv_drop_π'
              have h_mp_in : m'_w ∈ π'.support.dropLast :=
                bw_m'_in_π_dropLast_of_rightArm_pos bw_pkg h_rA_pos
              exact h_eq ▸ h_mp_in
            rcases List.mem_append.mp h_in_BE with h_in_B | h_in_E
            · -- v ∈ σ_bw.leftArm.support.dropLast. Head = m'_w (since σ_bw.leftArm : Walk G m'_w σ_bw.m).
              have h_B_ne : σ_bw.leftArm.support.dropLast ≠ [] := by
                intro h_emp; rw [h_emp] at h_in_B; simp at h_in_B
              have h_lA_head : σ_bw.leftArm.support = m'_w :: σ_bw.leftArm.support.tail :=
                marg_support_cons_form σ_bw.leftArm
              have h_lA_tail_ne : σ_bw.leftArm.support.tail ≠ [] := by
                intro h_emp
                rw [h_lA_head, h_emp] at h_B_ne
                simp at h_B_ne
              have h_B_eq : σ_bw.leftArm.support.dropLast =
                  m'_w :: σ_bw.leftArm.support.tail.dropLast := by
                conv_lhs => rw [h_lA_head]
                exact List.dropLast_cons_of_ne_nil h_lA_tail_ne
              rw [h_B_eq] at h_in_B
              rcases List.mem_cons.mp h_in_B with h_eq | h_in_tail_dl
              · exact h_mp_neq_v h_eq.symm
              · have : v ∈ σ_bw.leftArm.support.dropLast.tail := by
                  rw [h_B_eq, List.tail_cons]; exact h_in_tail_dl
                exact hv (hσ_int v (h_lA_dl_tail_subset v this))
            · rw [List.cons_append] at h_in_E
              rcases List.mem_cons.mp h_in_E with h_eq_σm | h_in_rest
              · by_cases h_lAσ_pos : 1 ≤ σ_bw.leftArm.length
                · apply hv
                  rw [h_eq_σm]
                  exact hσ_int σ_bw.m (h_σm_in_tail_dl_of_lA_pos h_lAσ_pos)
                · push_neg at h_lAσ_pos
                  have h_lAσ_zero : σ_bw.leftArm.length = 0 := by omega
                  have aux : ∀ {a b : α} (p : Walk G a b), p.length = 0 → a = b := by
                    intros a b p hp
                    cases p with
                    | nil _ => rfl
                    | cons _ _ => simp [Walk.length_cons] at hp
                  have h_σm_eq_mpw : σ_bw.m = m'_w := (aux σ_bw.leftArm h_lAσ_zero).symm
                  exact h_mp_neq_v (h_eq_σm.trans h_σm_eq_mpw).symm
              · rcases List.mem_append.mp h_in_rest with h_in_rA_dl | h_in_ρL
                · exact hv (hσ_int v (h_rA_dl_subset v h_in_rA_dl))
                · rcases hρ_L_supp v h_in_ρL with hlA | hW
                  · have h_v_lA : v ∈ lA.support := by
                      rw [marg_support_reverse, List.mem_reverse] at hlA; exact hlA
                    exact h_v_notin_lA h_v_lA
                  · exact hv hW
      · -- u ∉ new_walk.support.dropLast.
        intro h_u_in
        rw [h_new_walk_supp] at h_u_in
        have h_E_ne : (σ_bw.m :: σ_bw.rightArm.support.dropLast ++ ρ_L.support) ≠ [] := by
          rw [List.cons_append]; exact List.cons_ne_nil _ _
        rw [List.dropLast_append_of_ne_nil h_E_ne] at h_u_in
        rw [List.dropLast_append_of_ne_nil h_ρL_supp_ne] at h_u_in
        rcases List.mem_append.mp h_u_in with h_in_AB | h_in_C
        · rcases List.mem_append.mp h_in_AB with h_in_A | h_in_B
          · -- u ∈ ρ_R.reverse.support.dropLast → u ∈ ρ_R.support.tail.
            have h_u_ρR_tail : u ∈ ρ_R.support.tail :=
              marg_mem_reverse_dropLast_to_tail h_in_A
            rcases hρ_R_tail u h_u_ρR_tail with hrA | hW
            · -- hrA : u ∈ rA.support.tail. Since rA.support.tail ⊆ rA.support, contradicts h_u_notin_rA.
              have h_u_rA : u ∈ rA.support := by
                rw [marg_support_cons_form rA]
                exact List.mem_cons_of_mem _ hrA
              exact h_u_notin_rA h_u_rA
            · exact hu hW
          · -- u ∈ σ_bw.leftArm.support.dropLast. Head = m'_w.
            have h_B_ne : σ_bw.leftArm.support.dropLast ≠ [] := by
              intro h_emp; rw [h_emp] at h_in_B; simp at h_in_B
            have h_lA_head : σ_bw.leftArm.support = m'_w :: σ_bw.leftArm.support.tail :=
              marg_support_cons_form σ_bw.leftArm
            have h_lA_tail_ne : σ_bw.leftArm.support.tail ≠ [] := by
              intro h_emp
              rw [h_lA_head, h_emp] at h_B_ne
              simp at h_B_ne
            have h_B_eq : σ_bw.leftArm.support.dropLast =
                m'_w :: σ_bw.leftArm.support.tail.dropLast := by
              conv_lhs => rw [h_lA_head]
              exact List.dropLast_cons_of_ne_nil h_lA_tail_ne
            rw [h_B_eq] at h_in_B
            rcases List.mem_cons.mp h_in_B with h_eq | h_in_tail_dl
            · exact h_u_neq_m' h_eq
            · have : u ∈ σ_bw.leftArm.support.dropLast.tail := by
                rw [h_B_eq, List.tail_cons]; exact h_in_tail_dl
              exact hu (hσ_int u (h_lA_dl_tail_subset u this))
        · rcases List.mem_append.mp h_in_C with h_in_left | h_in_ρL_dl
          · rcases List.mem_cons.mp h_in_left with h_eq_σm | h_in_rA_dl
            · by_cases h_lAσ_pos : 1 ≤ σ_bw.leftArm.length
              · apply hu
                rw [h_eq_σm]
                exact hσ_int σ_bw.m (h_σm_in_tail_dl_of_lA_pos h_lAσ_pos)
              · push_neg at h_lAσ_pos
                have h_lAσ_zero : σ_bw.leftArm.length = 0 := by omega
                have aux : ∀ {a b : α} (p : Walk G a b), p.length = 0 → a = b := by
                  intros a b p hp
                  cases p with
                  | nil _ => rfl
                  | cons _ _ => simp [Walk.length_cons] at hp
                have h_σm_eq_mpw : σ_bw.m = m'_w := (aux σ_bw.leftArm h_lAσ_zero).symm
                exact h_u_neq_m' (h_eq_σm.trans h_σm_eq_mpw)
            · exact hu (hσ_int u (h_rA_dl_subset u h_in_rA_dl))
          · -- u ∈ ρ_L.support.dropLast. Use h_u_notin_ρL_drop.
            exact h_u_notin_ρL_drop h_in_ρL_dl
      · -- BifurcationWitness for new_walk : Walk G v u.
        refine ⟨?_⟩
        refine
          { m := σ_bw.m
            m' := σ_bw.m'
            leftArm := ρ_R.reverse.append σ_bw.leftArm
            hinge := σ_bw.hinge
            rightArm := σ_bw.rightArm.append ρ_L
            decompose := ?_
            leftBackward := ?_
            hingeIntoSource := σ_bw.hingeIntoSource
            rightDirected := ?_ }
        · symm
          exact marg_append_assoc ρ_R.reverse σ_bw.leftArm _
        · rw [marg_isAllBackward_append]
          exact ⟨hρ_R_rev_back, σ_bw.leftBackward⟩
        · rw [marg_isDirected_append]
          exact ⟨σ_bw.rightDirected, hρ_L_dir⟩
      · -- Support tracking (.bidir-bwd subcase): new_walk.support ⊆ π'.support ∪ W.
        -- σ : Walk G m'_w m_w with σ.InteriorIn W.
        have h_σ_len_pos : 1 ≤ σ.length := by
          by_contra h
          push_neg at h
          have h_zero : σ.length = 0 := by omega
          have h_mm : m'_w = m_w := by
            cases σ with
            | nil _ => rfl
            | cons _ _ => simp [Walk.length_cons] at h_zero
          exact h_mwp_neq_mw h_mm
        have h_tail_ne : σ.support.tail ≠ [] := by
          intro h
          have : σ.support.tail.length = 0 := by rw [h]; rfl
          rw [List.length_tail, Walk.support_length] at this; omega
        have h_σ_supp_bound : ∀ x ∈ σ.support, x ∈ π'.support ∨ x ∈ W := by
          intro x hx
          by_cases hx_int : x ∈ σ.support.tail.dropLast
          · exact Or.inr (hσ_int x hx_int)
          · have h_in : x ∈ σ.support.dropLast ∨ x = m_w := by
              rw [marg_support_eq_dropLast_append_last σ] at hx
              rcases List.mem_append.mp hx with h | h
              · exact Or.inl h
              · simp at h; exact Or.inr h
            cases h_in with
            | inr h_eq =>
              rw [h_eq]
              exact Or.inl (List.dropLast_subset _ (bw_m_in_π_dropLast bw_pkg))
            | inl h_drop =>
              rw [marg_support_cons_form σ] at h_drop
              rw [List.dropLast_cons_of_ne_nil h_tail_ne] at h_drop
              rcases List.mem_cons.mp h_drop with hxm | hxt
              · -- x = m'_w (start of σ).
                rw [hxm]
                refine Or.inl (List.mem_of_mem_tail (bw_rightArm_in_π_tail bw_pkg _ ?_))
                rw [marg_support_cons_form bw_pkg.rightArm]
                exact List.mem_cons_self
              · exact absurd hxt hx_int
        intro x hx
        rw [h_new_walk_supp] at hx
        rcases List.mem_append.mp hx with hAB | hC
        · rcases List.mem_append.mp hAB with hA | hB
          · -- x ∈ ρ_R.reverse.support.dropLast → ρ_R.support → rA ∪ W → π'.support ∪ W.
            have hx_ρR : x ∈ ρ_R.reverse.support := List.dropLast_subset _ hA
            have hx_ρR' : x ∈ ρ_R.support := marg_mem_reverse_support hx_ρR
            rcases hρ_R_supp x hx_ρR' with hrA | hW
            · exact Or.inl (List.mem_of_mem_tail
                (bw_rightArm_in_π_tail bw_pkg x hrA))
            · exact Or.inr hW
          · -- x ∈ σ_bw.leftArm.support.dropLast ⊆ σ.support.
            have hx_σ : x ∈ σ.support := by
              rw [h_σ_supp]
              exact List.mem_append.mpr (Or.inl hB)
            exact h_σ_supp_bound x hx_σ
        · -- x ∈ σ_bw.m :: σ_bw.rightArm.support.dropLast ++ ρ_L.support.
          rcases List.mem_append.mp hC with hC₁ | hC₂
          · rcases List.mem_cons.mp hC₁ with rfl | hxr
            · -- x = σ_bw.m.
              have hx_σ : σ_bw.m ∈ σ.support := by
                rw [h_σ_supp]
                refine List.mem_append.mpr (Or.inr ?_)
                exact List.mem_cons_self
              exact h_σ_supp_bound _ hx_σ
            · -- x ∈ σ_bw.rightArm.support.dropLast.
              have hx_rA : x ∈ σ_bw.rightArm.support := List.dropLast_subset _ hxr
              have hx_σ : x ∈ σ.support := by
                rw [h_σ_supp]
                refine List.mem_append.mpr (Or.inr ?_)
                exact List.mem_cons_of_mem _ hx_rA
              exact h_σ_supp_bound x hx_σ
          · -- x ∈ ρ_L.support → lA.support ∪ W → π'.support ∪ W.
            rcases hρ_L_supp x hC₂ with hlA | hW
            · exact Or.inl (List.dropLast_subset _
                (bw_leftArm_in_π_dropLast bw_pkg x (marg_mem_reverse_support hlA)))
            · exact Or.inr hW

/-- (→) direction of `marginalize_bifurcation_iff`, one walk-direction
case: given a bifurcation in `G` between `u` and `v` (in the `u → v`
direction), build a bifurcation in `G.marginalize W` between them
in some direction.

The construction shrinks the left arm and right arm of the G bifurcation
into directed walks in `G.marginalize W`. The hinge is translated by
case-analysis: either `bw.m, bw.m'` give a `.bidir` edge in the
marginalization (landing in `L^{\sm W}`), or the `L^{\sm W}`
exclusion fires and we get an `E^{\sm W}` edge, which forces the
output bifurcation into the opposite walk direction.

## Construction sketch (to be filled in a follow-up dispatch)

Destructure π.IsBifurcation to get bw : BifurcationWitness π, with
fields bw.m, bw.m', bw.leftArm (all backward in G), bw.hinge (backward
or bidir), bw.rightArm (directed in G).

* Apply `exists_first_not_in_W` to `bw.leftArm.reverse` (directed in G)
  starting at `bw.m` and ending at `u`, yielding a pivot `m₀ ∉ W` and
  pre/post walks `m₀ → ... → u` and `bw.m → ... → m₀` (the latter all in W).
  Symmetrically for `bw.rightArm` starting at `bw.m'` and ending at `v`,
  yielding `m₁ ∉ W` and post going through W.
* Apply `exists_marg_directed_of_directed` (shrink translator) to the
  reversed `m₀ → ... → u` walk and the `m₁ → ... → v` walk to obtain
  marg-side directed walks `π_L^{∼W} : v_1 ← ... ← m₀` and
  `π_R^{∼W} : m₁ → ... → v_2`.
* Hinge case-split:
  - Backward (`bw.hinge = .backward _`, apex bw.m'): if bw.m' ∉ W, take
    m₁ = bw.m' and splice; else build a sub-bifurcation `q` in G between
    m₀ and m₁ with interior in W (sub-bifurcation = m₀-arm of bw.leftArm
    + bw.hinge + m₁-arm of bw.rightArm, plus the in-W tails). Apply
    the L^{∼W} three-way characterisation: either (m₀, m₁) ∈ L^{∼W}
    (splice via bidir, first disjunct), or (m₀, m₁) ∈ E^{∼W} (splice
    via backward in reverse walk direction, second disjunct), or
    (m₁, m₀) ∈ E^{∼W} (splice via backward, first disjunct).
  - Bidir (`bw.hinge = .bidir _`): same three-way analysis, with the
    sub-bifurcation q now having a bidir hinge in G.
* In each case, the spliced marg-walk is `π_L^{∼W}.append (.cons new_hinge π_R^{∼W})`
  (modulo argument order swap for the second disjunct).

Endpoint support analysis (u ∉ tail, v ∉ dropLast) parallels the
`marginalize_bif_backward` argument: each piece of the new walk is
bounded by either `π.support.tail`/`.dropLast` (transported via shrink
translator's tail/drop inclusions) or `W` (transported via interior in W
of the sub-walks); combine with hu, hv, hb.2.1, hb.2.2.1.

Approx 700-1000 LoC to formalise faithfully; deferred to a follow-up dispatch. -/
lemma marginalize_bif_forward {G : CDMG α} {W : Set α} {u v : α}
    (_hu_in : u ∈ G) (_hv_in : v ∈ G) (hu : u ∉ W) (hv : v ∉ W)
    (π : Walk G u v) (hb : π.IsBifurcation) :
    (∃ π' : Walk (G.marginalize W) u v, π'.IsBifurcation ∧
      ∀ x ∈ π'.support, x ∈ π.support ∧ x ∉ W) ∨
    (∃ π' : Walk (G.marginalize W) v u, π'.IsBifurcation ∧
      ∀ x ∈ π'.support, x ∈ π.support ∧ x ∉ W) := by
  obtain ⟨h_uv_ne, hu_tail_π, hv_drop_π, ⟨bw⟩⟩ := hb
  obtain ⟨m_w, m'_w, lA, hg, rA, h_dec, h_lB, h_hIS, h_rD⟩ := bw
  let bw_pkg : Walk.BifurcationWitness π :=
    ⟨m_w, m'_w, lA, hg, rA, h_dec, h_lB, h_hIS, h_rD⟩
  -- lA : Walk G u m_w (all backward). lA.reverse : Walk G m_w u (directed).
  have h_lA_rev_dir : lA.reverse.IsDirected := marg_isDirected_reverse_of_isAllBackward h_lB
  -- Find m₀ = first non-W vertex on lA.reverse (starting at m_w, ending at u).
  obtain ⟨m₀, L_pre, L_post, h_m₀_notW, h_L_pre_dir, h_L_post_dir, h_L_pre_int, h_lA_rev_eq⟩ :=
    exists_first_not_in_W W lA.reverse h_lA_rev_dir hu
  -- L_pre : Walk G m_w m₀, directed, with L_pre.support.dropLast ⊆ W.
  -- L_post : Walk G m₀ u, directed.
  -- Find m₁ = first non-W vertex on rA (starting at m'_w, ending at v).
  obtain ⟨m₁, R_pre, R_post, h_m₁_notW, h_R_pre_dir, h_R_post_dir, h_R_pre_int, h_rA_eq⟩ :=
    exists_first_not_in_W W rA h_rD hv
  -- R_pre : Walk G m'_w m₁, directed. R_post : Walk G m₁ v, directed.
  -- Apply (S) to L_post : Walk G m₀ u (both endpoints ∉ W) to get a marg walk.
  obtain ⟨shrink_L, h_shL_dir, h_shL_supp, h_shL_tail, h_shL_drop⟩ :=
    exists_marg_directed_of_directed W L_post h_L_post_dir h_m₀_notW hu
  -- Apply (S) to R_post : Walk G m₁ v.
  obtain ⟨shrink_R, h_shR_dir, h_shR_supp, h_shR_tail, h_shR_drop⟩ :=
    exists_marg_directed_of_directed W R_post h_R_post_dir h_m₁_notW hv
  have h_shL_rev_back : shrink_L.reverse.IsAllBackward :=
    marg_isAllBackward_reverse_of_isDirected h_shL_dir
  have h_shR_rev_back : shrink_R.reverse.IsAllBackward :=
    marg_isAllBackward_reverse_of_isDirected h_shR_dir
  -- π.support decomposition via bw.decompose.
  have h_π_supp : π.support = lA.support.dropLast ++ (m_w :: rA.support) := by
    conv_lhs => rw [h_dec]
    rw [marg_support_append, Walk.support_cons]
  have h_rA_supp_ne : rA.support ≠ [] := rA.marg_support_ne_nil
  have h_lA_supp_ne : lA.support ≠ [] := lA.marg_support_ne_nil
  have h_π_supp_dropLast : π.support.dropLast =
      lA.support.dropLast ++ (m_w :: rA.support.dropLast) := by
    rw [h_π_supp]
    rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
    congr 1
    rw [List.dropLast_cons_of_ne_nil h_rA_supp_ne]
  -- shrink_L.support set-wise ⊆ π.support.dropLast (via lA.support → π.support.dropLast).
  have h_lA_supp_in_π_drop : ∀ x ∈ lA.support, x ∈ π.support.dropLast := by
    intro x hx
    exact bw_leftArm_in_π_dropLast bw_pkg x hx
  have h_shL_supp_in_π_drop : ∀ x ∈ shrink_L.support, x ∈ π.support.dropLast := by
    intro x hx
    have h1 : x ∈ L_post.support := h_shL_supp x hx
    have h2 : x ∈ lA.reverse.support := by
      rw [h_lA_rev_eq, marg_support_append]
      exact List.mem_append.mpr (Or.inr h1)
    have h3 : x ∈ lA.support := by
      rw [marg_support_reverse, List.mem_reverse] at h2
      exact h2
    exact h_lA_supp_in_π_drop x h3
  -- shrink_R.support set-wise ⊆ π.support.tail (via rA.support → π.support.tail).
  have h_rA_supp_in_π_tail : ∀ x ∈ rA.support, x ∈ π.support.tail :=
    bw_rightArm_in_π_tail bw_pkg
  have h_R_post_supp_in_rA : ∀ x ∈ R_post.support, x ∈ rA.support := by
    intro y hy
    rw [h_rA_eq, marg_support_append]
    exact List.mem_append.mpr (Or.inr hy)
  have h_shR_supp_in_π_tail : ∀ x ∈ shrink_R.support, x ∈ π.support.tail := by
    intro x hx
    have h1 : x ∈ R_post.support := h_shR_supp x hx
    exact h_rA_supp_in_π_tail x (h_R_post_supp_in_rA x h1)
  -- shrink_R.support.dropLast set-wise ⊆ rA.support.dropLast ⊆ π.support.dropLast.
  have h_shR_supp_dl_in_π_drop : ∀ x ∈ shrink_R.support.dropLast, x ∈ π.support.dropLast := by
    intro x hx
    have h1 : x ∈ R_post.support.dropLast := h_shR_drop x hx
    have h2 : x ∈ rA.support.dropLast := by
      rw [h_rA_eq, marg_support_append, List.dropLast_append_of_ne_nil R_post.marg_support_ne_nil]
      exact List.mem_append.mpr (Or.inr h1)
    rw [h_π_supp_dropLast]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h2))
  -- m₁ ∈ rA.support (it's a vertex on rA via R_pre.append R_post).
  have h_m₁_in_rA : m₁ ∈ rA.support := by
    rw [h_rA_eq, marg_support_append]
    exact List.mem_append.mpr (Or.inr (by
      rw [marg_support_cons_form R_post]; exact List.mem_cons_self))
  -- m₀ ∈ lA.support (via lA.reverse.support and reverse).
  have h_m₀_in_lA : m₀ ∈ lA.support := by
    have : m₀ ∈ lA.reverse.support := by
      rw [h_lA_rev_eq, marg_support_append]
      exact List.mem_append.mpr (Or.inr (by
        rw [marg_support_cons_form L_post]; exact List.mem_cons_self))
    rw [marg_support_reverse, List.mem_reverse] at this
    exact this
  -- L_post.support.dropLast set-wise ⊆ lA.support.tail.
  -- Used to show u ∉ shrink_L.support.dropLast.
  have h_L_post_dl_in_lA_tail : ∀ x ∈ L_post.support.dropLast, x ∈ lA.support.tail := by
    intro x hx
    have h1 : x ∈ lA.reverse.support.dropLast := by
      rw [h_lA_rev_eq, marg_support_append,
          List.dropLast_append_of_ne_nil L_post.marg_support_ne_nil]
      exact List.mem_append.mpr (Or.inr hx)
    rw [marg_support_reverse, List.dropLast_reverse, List.mem_reverse] at h1
    exact h1
  -- u ∉ shrink_L.support.dropLast.
  have h_u_notin_shL_dl : u ∉ shrink_L.support.dropLast := fun hu_in =>
    hu_tail_π (bw_leftArm_tail_in_π_tail bw_pkg u
      (h_L_post_dl_in_lA_tail u (h_shL_drop u hu_in)))
  -- R_pre.support.dropLast set-wise ⊆ rA.support.dropLast.
  -- Used to relate R_post pieces back to rA pieces.
  have h_R_pre_dl_in_rA_dl : ∀ x ∈ R_pre.support.dropLast, x ∈ rA.support.dropLast := by
    intro x hx
    rw [h_rA_eq, marg_support_append, List.dropLast_append_of_ne_nil R_post.marg_support_ne_nil]
    exact List.mem_append.mpr (Or.inl hx)
  -- v ∉ shrink_R.support.dropLast.
  have h_v_notin_shR_dl : v ∉ shrink_R.support.dropLast := fun hv_in =>
    hv_drop_π (h_shR_supp_dl_in_π_drop v hv_in)
  -- m₁ ∈ π.support.tail.
  have h_m₁_in_π_tail : m₁ ∈ π.support.tail := h_rA_supp_in_π_tail m₁ h_m₁_in_rA
  -- Membership facts for the marg-V \ W conjuncts.
  -- m₀ ∈ G.V: it's the endpoint of a directed walk to u (= L_post : Walk G m₀ u).
  -- If L_post.length ≥ 1, m₀ is the start of a length-≥-1 directed walk, hence ∈ G.J ∪ G.V.
  -- If L_post.length = 0, m₀ = u ∈ G (by _hu_in).
  -- Actually, m₀ ∈ G follows from membership in lA.reverse.support ⊆ π.support, and π.support ⊆ G (vertices of π).
  -- Three-way case-split via mem_marginalize_L's RHS.
  -- Case (b): directed walk m₀ → m₁ in G with interior in W → (m₀, m₁) ∈ marg.E.
  by_cases h_E_fwd : ∃ π_E : Walk G m₀ m₁, π_E.IsDirected ∧ π_E.InteriorIn W ∧ 1 ≤ π_E.length
  · -- (m₀, m₁) ∈ E^{∼W}. Use this E^{∼W} edge as a backward hinge for marg-bif v → u.
    obtain ⟨π_E, hπ_E_dir, hπ_E_int, hπ_E_pos⟩ := h_E_fwd
    have h_m₀_JV : m₀ ∈ G.J ∪ G.V := marg_start_in_JV_of_isDirected_pos π_E hπ_E_dir hπ_E_pos
    have h_m₁_V : m₁ ∈ G.V := marg_end_in_V_of_isDirected_pos π_E hπ_E_dir hπ_E_pos
    have h_m₀_in_marg : m₀ ∈ G.J ∪ (G.V \ W) := by
      rcases h_m₀_JV with hJ | hV
      · exact Or.inl hJ
      · exact Or.inr ⟨hV, h_m₀_notW⟩
    have h_m₁_in_marg : m₁ ∈ G.V \ W := ⟨h_m₁_V, h_m₁_notW⟩
    have h_E_marg : (m₀, m₁) ∈ (G.marginalize W).E := by
      rw [CDMG.mem_marginalize_E]
      exact ⟨h_m₀_in_marg, h_m₁_in_marg, π_E, hπ_E_dir, hπ_E_int, hπ_E_pos⟩
    -- h_E_marg : (m₀, m₁) ∈ marg.E. As a backward step: WalkStep marg m₁ m₀ via .backward h_E_marg.
    -- new_walk : Walk marg v u = shrink_R.reverse.append (.cons (.backward h_E_marg) shrink_L).
    let new_walk : Walk (G.marginalize W) v u :=
      shrink_R.reverse.append (.cons (.backward h_E_marg) shrink_L)
    have h_new_walk_supp_b : new_walk.support =
        shrink_R.reverse.support.dropLast ++ (m₁ :: shrink_L.support) := by
      show (shrink_R.reverse.append _).support = _
      rw [marg_support_append, Walk.support_cons]
    right
    refine ⟨new_walk, ⟨h_uv_ne.symm, ?_, ?_, ?_⟩, ?_⟩
    · -- v ∉ new_walk.support.tail.
      intro h_v_in
      rw [h_new_walk_supp_b] at h_v_in
      by_cases h_dl_empty : shrink_R.reverse.support.dropLast = []
      · rw [h_dl_empty, List.nil_append, List.tail_cons] at h_v_in
        exact hv_drop_π (h_shL_supp_in_π_drop v h_v_in)
      · rw [list_tail_append_of_ne_nil _ h_dl_empty] at h_v_in
        rcases List.mem_append.mp h_v_in with h_in_A | h_in_BC
        · -- v ∈ shrink_R.reverse.support.dropLast.tail (interior of shrink_R).
          have h1 : v ∈ shrink_R.support.tail.dropLast := marg_mem_reverse_strict_interior h_in_A
          have h2 : v ∈ shrink_R.support.dropLast := marg_tail_dropLast_subset_dropLast _ h1
          exact h_v_notin_shR_dl h2
        · rcases List.mem_cons.mp h_in_BC with h_eq_m₁ | h_in_shL
          · -- v = m₁ with shrink_R.length ≥ 1. Derive v ∈ shrink_R.support.dropLast.
            have h_shR_pos : 1 ≤ shrink_R.length := by
              by_contra h_neg
              push_neg at h_neg
              apply h_dl_empty
              have h_zero : shrink_R.length = 0 := by omega
              have h_supp_len : shrink_R.reverse.support.length = 1 := by
                rw [Walk.support_length, marg_length_reverse, h_zero]
              obtain ⟨a, ha⟩ : ∃ a, shrink_R.reverse.support = [a] :=
                List.length_eq_one_iff.mp h_supp_len
              rw [ha]; rfl
            have h_shR_tail_ne : shrink_R.support.tail ≠ [] := by
              intro h_emp
              have : shrink_R.support.tail.length = 0 := by rw [h_emp]; rfl
              rw [List.length_tail, Walk.support_length] at this; omega
            have h_v_in_shR_dl : v ∈ shrink_R.support.dropLast := by
              rw [marg_support_cons_form shrink_R, List.dropLast_cons_of_ne_nil h_shR_tail_ne]
              exact List.mem_cons.mpr (Or.inl h_eq_m₁)
            exact h_v_notin_shR_dl h_v_in_shR_dl
          · exact hv_drop_π (h_shL_supp_in_π_drop v h_in_shL)
    · -- u ∉ new_walk.support.dropLast.
      intro h_u_in
      rw [h_new_walk_supp_b] at h_u_in
      have h_shL_supp_ne : shrink_L.support ≠ [] := shrink_L.marg_support_ne_nil
      have h_cons_ne : (m₁ :: shrink_L.support) ≠ [] := List.cons_ne_nil _ _
      rw [List.dropLast_append_of_ne_nil h_cons_ne] at h_u_in
      rw [List.dropLast_cons_of_ne_nil h_shL_supp_ne] at h_u_in
      rcases List.mem_append.mp h_u_in with h_in_A | h_in_BC
      · -- u ∈ shrink_R.reverse.support.dropLast → u ∈ shrink_R.support.tail (set-wise).
        have h_u_shR_tail : u ∈ shrink_R.support.tail := by
          rw [marg_support_reverse, List.dropLast_reverse, List.mem_reverse] at h_in_A
          exact h_in_A
        have h_u_shR : u ∈ shrink_R.support := by
          rw [marg_support_cons_form shrink_R]
          exact List.mem_cons_of_mem _ h_u_shR_tail
        exact hu_tail_π (h_shR_supp_in_π_tail u h_u_shR)
      · rcases List.mem_cons.mp h_in_BC with h_eq_m₁ | h_in_shL_dl
        · -- u = m₁ → u ∈ π.support.tail (via m₁ ∈ rA.support).
          exact hu_tail_π (h_eq_m₁ ▸ h_m₁_in_π_tail)
        · exact h_u_notin_shL_dl h_in_shL_dl
    · refine ⟨?_⟩
      refine
        { m := m₁
          m' := m₀
          leftArm := shrink_R.reverse
          hinge := .backward h_E_marg
          rightArm := shrink_L
          decompose := rfl
          leftBackward := h_shR_rev_back
          hingeIntoSource := by simp
          rightDirected := h_shL_dir }
    · -- Support tracking (case E-edge m₀→m₁, marg-bif v→u direction):
      -- new_walk.support ⊆ π.support ∧ ∉ W.
      have h_shL_supp_notW : ∀ x ∈ shrink_L.support, x ∉ W :=
        marg_directed_supp_notW shrink_L h_shL_dir h_m₀_notW
      have h_shR_supp_notW : ∀ x ∈ shrink_R.support, x ∉ W :=
        marg_directed_supp_notW shrink_R h_shR_dir h_m₁_notW
      intro x hx
      rw [h_new_walk_supp_b] at hx
      rcases List.mem_append.mp hx with hL | hR
      · have hx_rev : x ∈ shrink_R.reverse.support := List.dropLast_subset _ hL
        have hx_shR : x ∈ shrink_R.support := marg_mem_reverse_support hx_rev
        exact ⟨List.mem_of_mem_tail (h_shR_supp_in_π_tail x hx_shR),
               h_shR_supp_notW x hx_shR⟩
      · rcases List.mem_cons.mp hR with hxm | hx_shL
        · rw [hxm]
          exact ⟨List.mem_of_mem_tail h_m₁_in_π_tail, h_m₁_notW⟩
        · exact ⟨List.dropLast_subset _ (h_shL_supp_in_π_drop x hx_shL),
                 h_shL_supp_notW x hx_shL⟩
  · -- No directed walk m₀ → m₁ with interior in W.
    by_cases h_E_bwd : ∃ π_E : Walk G m₁ m₀, π_E.IsDirected ∧ π_E.InteriorIn W ∧ 1 ≤ π_E.length
    · -- (m₁, m₀) ∈ E^{∼W}. Backward hinge for marg-bif u → v.
      obtain ⟨π_E, hπ_E_dir, hπ_E_int, hπ_E_pos⟩ := h_E_bwd
      have h_m₁_JV : m₁ ∈ G.J ∪ G.V := marg_start_in_JV_of_isDirected_pos π_E hπ_E_dir hπ_E_pos
      have h_m₀_V : m₀ ∈ G.V := marg_end_in_V_of_isDirected_pos π_E hπ_E_dir hπ_E_pos
      have h_m₁_in_marg : m₁ ∈ G.J ∪ (G.V \ W) := by
        rcases h_m₁_JV with hJ | hV
        · exact Or.inl hJ
        · exact Or.inr ⟨hV, h_m₁_notW⟩
      have h_m₀_in_marg : m₀ ∈ G.V \ W := ⟨h_m₀_V, h_m₀_notW⟩
      have h_E_marg : (m₁, m₀) ∈ (G.marginalize W).E := by
        rw [CDMG.mem_marginalize_E]
        exact ⟨h_m₁_in_marg, h_m₀_in_marg, π_E, hπ_E_dir, hπ_E_int, hπ_E_pos⟩
      let new_walk : Walk (G.marginalize W) u v :=
        shrink_L.reverse.append (.cons (.backward h_E_marg) shrink_R)
      have h_new_walk_supp_c : new_walk.support =
          shrink_L.reverse.support.dropLast ++ (m₀ :: shrink_R.support) := by
        show (shrink_L.reverse.append _).support = _
        rw [marg_support_append, Walk.support_cons]
      left
      refine ⟨new_walk, ⟨h_uv_ne, ?_, ?_, ?_⟩, ?_⟩
      · -- u ∉ new_walk.support.tail.
        intro h_u_in
        rw [h_new_walk_supp_c] at h_u_in
        by_cases h_dl_empty : shrink_L.reverse.support.dropLast = []
        · rw [h_dl_empty, List.nil_append, List.tail_cons] at h_u_in
          -- h_u_in : u ∈ shrink_R.support. → u ∈ π.support.tail. Contradicts hu_tail_π.
          exact hu_tail_π (h_shR_supp_in_π_tail u h_u_in)
        · rw [list_tail_append_of_ne_nil _ h_dl_empty] at h_u_in
          rcases List.mem_append.mp h_u_in with h_in_A | h_in_BC
          · -- u ∈ shrink_L.reverse.support.dropLast.tail (interior of shrink_L).
            have h1 : u ∈ shrink_L.support.tail.dropLast := marg_mem_reverse_strict_interior h_in_A
            have h2 : u ∈ shrink_L.support.dropLast := marg_tail_dropLast_subset_dropLast _ h1
            exact h_u_notin_shL_dl h2
          · rcases List.mem_cons.mp h_in_BC with h_eq_m₀ | h_in_shR
            · -- u = m₀. With shrink_L.length ≥ 1, derive u ∈ shrink_L.support.dropLast.
              have h_shL_pos : 1 ≤ shrink_L.length := by
                by_contra h_neg
                push_neg at h_neg
                apply h_dl_empty
                have h_zero : shrink_L.length = 0 := by omega
                have h_supp_len : shrink_L.reverse.support.length = 1 := by
                  rw [Walk.support_length, marg_length_reverse, h_zero]
                obtain ⟨a, ha⟩ : ∃ a, shrink_L.reverse.support = [a] :=
                  List.length_eq_one_iff.mp h_supp_len
                rw [ha]; rfl
              have h_shL_tail_ne : shrink_L.support.tail ≠ [] := by
                intro h_emp
                have : shrink_L.support.tail.length = 0 := by rw [h_emp]; rfl
                rw [List.length_tail, Walk.support_length] at this; omega
              have h_u_in_shL_dl : u ∈ shrink_L.support.dropLast := by
                rw [marg_support_cons_form shrink_L, List.dropLast_cons_of_ne_nil h_shL_tail_ne]
                exact List.mem_cons.mpr (Or.inl h_eq_m₀)
              exact h_u_notin_shL_dl h_u_in_shL_dl
            · exact hu_tail_π (h_shR_supp_in_π_tail u h_in_shR)
      · -- v ∉ new_walk.support.dropLast.
        intro h_v_in
        rw [h_new_walk_supp_c] at h_v_in
        have h_shR_supp_ne : shrink_R.support ≠ [] := shrink_R.marg_support_ne_nil
        have h_cons_ne : (m₀ :: shrink_R.support) ≠ [] := List.cons_ne_nil _ _
        rw [List.dropLast_append_of_ne_nil h_cons_ne] at h_v_in
        rw [List.dropLast_cons_of_ne_nil h_shR_supp_ne] at h_v_in
        rcases List.mem_append.mp h_v_in with h_in_A | h_in_BC
        · -- v ∈ shrink_L.reverse.support.dropLast → v ∈ shrink_L.support.tail set-wise.
          have h_v_shL_tail : v ∈ shrink_L.support.tail := by
            rw [marg_support_reverse, List.dropLast_reverse, List.mem_reverse] at h_in_A
            exact h_in_A
          have h_v_shL : v ∈ shrink_L.support := by
            rw [marg_support_cons_form shrink_L]
            exact List.mem_cons_of_mem _ h_v_shL_tail
          exact hv_drop_π (h_shL_supp_in_π_drop v h_v_shL)
        · rcases List.mem_cons.mp h_in_BC with h_eq_m₀ | h_in_shR_dl
          · -- v = m₀ → v ∈ lA.support → v ∈ π.support.dropLast → contradicts hv_drop_π.
            exact hv_drop_π (h_eq_m₀.symm ▸ h_lA_supp_in_π_drop m₀ h_m₀_in_lA)
          · exact h_v_notin_shR_dl h_in_shR_dl
      · refine ⟨?_⟩
        refine
          { m := m₀
            m' := m₁
            leftArm := shrink_L.reverse
            hinge := .backward h_E_marg
            rightArm := shrink_R
            decompose := rfl
            leftBackward := h_shL_rev_back
            hingeIntoSource := by simp
            rightDirected := h_shR_dir }
      · -- Support tracking (case E-edge m₁→m₀, marg-bif u→v direction):
        have h_shL_supp_notW : ∀ x ∈ shrink_L.support, x ∉ W :=
          marg_directed_supp_notW shrink_L h_shL_dir h_m₀_notW
        have h_shR_supp_notW : ∀ x ∈ shrink_R.support, x ∉ W :=
          marg_directed_supp_notW shrink_R h_shR_dir h_m₁_notW
        intro x hx
        rw [h_new_walk_supp_c] at hx
        rcases List.mem_append.mp hx with hL | hR
        · have hx_rev : x ∈ shrink_L.reverse.support := List.dropLast_subset _ hL
          have hx_shL : x ∈ shrink_L.support := marg_mem_reverse_support hx_rev
          exact ⟨List.dropLast_subset _ (h_shL_supp_in_π_drop x hx_shL),
                 h_shL_supp_notW x hx_shL⟩
        · rcases List.mem_cons.mp hR with hxm | hx_shR
          · rw [hxm]
            refine ⟨?_, h_m₀_notW⟩
            exact List.dropLast_subset _
              (h_lA_supp_in_π_drop m₀ h_m₀_in_lA)
          · exact ⟨List.mem_of_mem_tail (h_shR_supp_in_π_tail x hx_shR),
                   h_shR_supp_notW x hx_shR⟩
    · -- Neither directed walk exists with interior in W.
      -- The hinge must be .bidir (otherwise .backward gives h_E_bwd, contradicting our branch).
      by_cases h_m₀m₁_neq : m₀ = m₁
      · -- m₀ = m₁ degenerate case. Substitute m₁ → m₀ via `subst`, then pop the first step of
        -- shrink_L (or shrink_R if u = m₀) as backward hinge for a marg-bifurcation.
        subst h_m₀m₁_neq
        -- Now shrink_R : Walk marg m₀ v.
        by_cases h_shL_pos : 1 ≤ shrink_L.length
        · -- Option B: pop first step of shrink_L. Use as backward hinge for u → v marg-bif.
          cases shrink_L with
          | nil _ => simp [Walk.length_nil] at h_shL_pos
          | @cons _ x _ step rest_L =>
            cases step with
            | backward _ => simp at h_shL_dir
            | bidir _ => simp at h_shL_dir
            | forward h_first =>
              have h_rest_L_dir : rest_L.IsDirected := by simpa using h_shL_dir
              have h_rest_L_rev_back : rest_L.reverse.IsAllBackward :=
                marg_isAllBackward_reverse_of_isDirected h_rest_L_dir
              let new_walk : Walk (G.marginalize W) u v :=
                rest_L.reverse.append (.cons (.backward h_first) shrink_R)
              have h_new_walk_supp : new_walk.support =
                  rest_L.reverse.support.dropLast ++ (x :: shrink_R.support) := by
                show (rest_L.reverse.append _).support = _
                rw [marg_support_append, Walk.support_cons]
              left
              refine ⟨new_walk, ⟨h_uv_ne, ?_, ?_, ?_⟩, ?_⟩
              · -- u ∉ new_walk.support.tail.
                intro h_u_in
                rw [h_new_walk_supp] at h_u_in
                by_cases h_dl_empty : rest_L.reverse.support.dropLast = []
                · rw [h_dl_empty, List.nil_append, List.tail_cons] at h_u_in
                  exact hu_tail_π (h_shR_supp_in_π_tail u h_u_in)
                · rw [list_tail_append_of_ne_nil _ h_dl_empty] at h_u_in
                  rcases List.mem_append.mp h_u_in with h_in_A | h_in_BC
                  · -- u ∈ rest_L.reverse.support.dropLast.tail (set-wise = rest_L.support.tail.dropLast).
                    have h1 : u ∈ rest_L.support.tail.dropLast :=
                      marg_mem_reverse_strict_interior h_in_A
                    have h2 : u ∈ rest_L.support.dropLast :=
                      marg_tail_dropLast_subset_dropLast _ h1
                    -- rest_L.support.dropLast ⊆ shrink_L.support.dropLast.
                    -- shrink_L = .cons (.forward h_first) rest_L, so
                    -- shrink_L.support.dropLast = m₀ :: rest_L.support.dropLast (when rest_L.support ≠ []).
                    have h_u_in_shL_dl :
                        u ∈ (Walk.cons (WalkStep.forward h_first) rest_L).support.dropLast := by
                      rw [Walk.support_cons,
                          List.dropLast_cons_of_ne_nil rest_L.marg_support_ne_nil]
                      exact List.mem_cons_of_mem _ h2
                    exact h_u_notin_shL_dl h_u_in_shL_dl
                  · rcases List.mem_cons.mp h_in_BC with h_eq_x | h_in_shR
                    · -- u = x. x is at position 1 of shrink_L.support.
                      -- If rest_L.length ≥ 1, x at non-end, u = x ∈ shrink_L.support.dropLast.
                      -- If rest_L.length = 0, rest_L = nil x, rest_L.reverse.support.dropLast = [],
                      -- contradicting h_dl_empty.
                      by_cases h_rest_L_zero : rest_L.length = 0
                      · cases rest_L with
                        | nil _ => simp at h_dl_empty
                        | cons _ _ => simp [Walk.length_cons] at h_rest_L_zero
                      · push_neg at h_rest_L_zero
                        have h_rest_L_pos : 1 ≤ rest_L.length := by omega
                        have h_rest_L_tail_ne : rest_L.support.tail ≠ [] := by
                          intro h_emp
                          have : rest_L.support.tail.length = 0 := by rw [h_emp]; rfl
                          rw [List.length_tail, Walk.support_length] at this; omega
                        have h_u_in_shL_dl :
                            u ∈ (Walk.cons (WalkStep.forward h_first) rest_L).support.dropLast := by
                          rw [Walk.support_cons,
                              List.dropLast_cons_of_ne_nil rest_L.marg_support_ne_nil,
                              marg_support_cons_form rest_L,
                              List.dropLast_cons_of_ne_nil h_rest_L_tail_ne]
                          exact List.mem_cons.mpr (Or.inr
                            (List.mem_cons.mpr (Or.inl h_eq_x)))
                        exact h_u_notin_shL_dl h_u_in_shL_dl
                    · exact hu_tail_π (h_shR_supp_in_π_tail u h_in_shR)
              · -- v ∉ new_walk.support.dropLast.
                intro h_v_in
                rw [h_new_walk_supp] at h_v_in
                have h_shR_supp_ne : shrink_R.support ≠ [] := shrink_R.marg_support_ne_nil
                have h_cons_ne : (x :: shrink_R.support) ≠ [] := List.cons_ne_nil _ _
                rw [List.dropLast_append_of_ne_nil h_cons_ne] at h_v_in
                rw [List.dropLast_cons_of_ne_nil h_shR_supp_ne] at h_v_in
                rcases List.mem_append.mp h_v_in with h_in_A | h_in_BC
                · -- v ∈ rest_L.reverse.support.dropLast → v ∈ rest_L.support.tail set-wise
                  -- → v ∈ shrink_L.support set-wise → v ∈ π.support.dropLast.
                  have h_v_rL_tail : v ∈ rest_L.support.tail := by
                    rw [marg_support_reverse, List.dropLast_reverse, List.mem_reverse] at h_in_A
                    exact h_in_A
                  have h_v_shL :
                      v ∈ (Walk.cons (WalkStep.forward h_first) rest_L).support := by
                    rw [Walk.support_cons]
                    exact List.mem_cons_of_mem _ (List.mem_of_mem_tail h_v_rL_tail)
                  exact hv_drop_π (h_shL_supp_in_π_drop v h_v_shL)
                · rcases List.mem_cons.mp h_in_BC with h_eq_x | h_in_shR_dl
                  · -- v = x. x is at position 1 of shrink_L.support.
                    have h_v_shL :
                        v ∈ (Walk.cons (WalkStep.forward h_first) rest_L).support := by
                      rw [h_eq_x, Walk.support_cons]
                      exact List.mem_cons_of_mem _ (by
                        rw [marg_support_cons_form rest_L]; exact List.mem_cons_self)
                    exact hv_drop_π (h_shL_supp_in_π_drop v h_v_shL)
                  · exact h_v_notin_shR_dl h_in_shR_dl
              · refine ⟨?_⟩
                refine
                  { m := x
                    m' := m₀
                    leftArm := rest_L.reverse
                    hinge := .backward h_first
                    rightArm := shrink_R
                    decompose := rfl
                    leftBackward := h_rest_L_rev_back
                    hingeIntoSource := by simp
                    rightDirected := h_shR_dir }
              · -- Support tracking (case m₀=m₁ option B): new_walk supp ⊆ π.support, ∉ W.
                -- shrink_L = .cons (.forward h_first) rest_L : Walk marg m₀ u.
                -- target of h_first is x ∈ (marg).V = G.V \ W → x ∉ W.
                have hx_V : x ∈ (G.marginalize W).V := by
                  have h_E : (m₀, x) ∈ (G.marginalize W).E := h_first
                  exact (Set.mem_prod.mp ((G.marginalize W).E_subset h_E)).2
                have hx_notW : x ∉ W := by
                  rw [CDMG.marginalize_V] at hx_V; exact hx_V.2
                have h_rest_L_supp_notW : ∀ y ∈ rest_L.support, y ∉ W :=
                  marg_directed_supp_notW rest_L h_rest_L_dir hx_notW
                have h_shR_supp_notW : ∀ y ∈ shrink_R.support, y ∉ W :=
                  marg_directed_supp_notW shrink_R h_shR_dir h_m₀_notW
                -- x is in (cons (.forward h_first) rest_L).support (= m₀ :: rest_L.support).
                -- → x ∈ this support via mem_cons; then h_shL_supp_in_π_drop gives
                -- x ∈ π.support.dropLast.
                have hx_in_shL : x ∈ (Walk.cons (.forward h_first) rest_L).support := by
                  rw [Walk.support_cons]
                  refine List.mem_cons.mpr (Or.inr ?_)
                  rw [Walk.marg_support_cons_form rest_L]; exact List.mem_cons_self
                intro y hy
                rw [h_new_walk_supp] at hy
                rcases List.mem_append.mp hy with hL | hR
                · -- y ∈ rest_L.reverse.support.dropLast → rest_L.support (set-wise).
                  have hy_rev : y ∈ rest_L.reverse.support := List.dropLast_subset _ hL
                  have hy_rest : y ∈ rest_L.support := marg_mem_reverse_support hy_rev
                  have hy_in_shL : y ∈ (Walk.cons (.forward h_first) rest_L).support := by
                    rw [Walk.support_cons]
                    exact List.mem_cons_of_mem _ hy_rest
                  exact ⟨List.dropLast_subset _ (h_shL_supp_in_π_drop y hy_in_shL),
                         h_rest_L_supp_notW y hy_rest⟩
                · rcases List.mem_cons.mp hR with hyx | hy_shR
                  · rw [hyx]
                    exact ⟨List.dropLast_subset _ (h_shL_supp_in_π_drop x hx_in_shL),
                           hx_notW⟩
                  · exact ⟨List.mem_of_mem_tail (h_shR_supp_in_π_tail y hy_shR),
                           h_shR_supp_notW y hy_shR⟩
        · -- Option C: shrink_L.length = 0 → u = m₀ = m₁.
          -- Then shrink_R.length ≥ 1 (else u = v, contradicting h_uv_ne).
          -- Pop first step of shrink_R, use as backward hinge for v → u marg-bif.
          push_neg at h_shL_pos
          have h_shL_zero : shrink_L.length = 0 := by omega
          have aux : ∀ {a b : α} (p : Walk (G.marginalize W) a b), p.length = 0 → a = b := by
            intros a b p hp
            cases p with
            | nil _ => rfl
            | cons _ _ => simp [Walk.length_cons] at hp
          have h_m₀_eq_u : m₀ = u := aux shrink_L h_shL_zero
          have h_u_eq_m₀ : u = m₀ := h_m₀_eq_u.symm
          subst h_u_eq_m₀
          -- Now m₀ replaced by u. shrink_R : Walk marg u v, shrink_L : Walk marg u u (= nil u).
          have h_shR_pos : 1 ≤ shrink_R.length := by
            by_contra h_neg
            push_neg at h_neg
            have h_zero : shrink_R.length = 0 := by omega
            exact h_uv_ne (aux shrink_R h_zero)
          cases shrink_R with
          | nil _ => simp [Walk.length_nil] at h_shR_pos
          | @cons _ x _ step rest_R =>
            cases step with
            | backward _ => simp at h_shR_dir
            | bidir _ => simp at h_shR_dir
            | forward h_first =>
              have h_rest_R_dir : rest_R.IsDirected := by simpa using h_shR_dir
              have h_rest_R_rev_back : rest_R.reverse.IsAllBackward :=
                marg_isAllBackward_reverse_of_isDirected h_rest_R_dir
              let new_walk : Walk (G.marginalize W) v u :=
                rest_R.reverse.append (.cons (.backward h_first) shrink_L)
              have h_new_walk_supp : new_walk.support =
                  rest_R.reverse.support.dropLast ++ (x :: shrink_L.support) := by
                show (rest_R.reverse.append _).support = _
                rw [marg_support_append, Walk.support_cons]
              -- shrink_L : Walk marg u u with length 0 → support = [u].
              have h_shL_supp : shrink_L.support = [u] := by
                cases shrink_L with
                | nil _ => rfl
                | cons _ _ => simp [Walk.length_cons] at h_shL_zero
              right
              refine ⟨new_walk, ⟨h_uv_ne.symm, ?_, ?_, ?_⟩, ?_⟩
              · -- v ∉ new_walk.support.tail.
                intro h_v_in
                rw [h_new_walk_supp, h_shL_supp] at h_v_in
                by_cases h_dl_empty : rest_R.reverse.support.dropLast = []
                · rw [h_dl_empty, List.nil_append, List.tail_cons] at h_v_in
                  -- h_v_in : v ∈ [u]. So v = u, contradicting h_uv_ne.
                  simp only [List.mem_singleton] at h_v_in
                  exact h_uv_ne h_v_in.symm
                · rw [list_tail_append_of_ne_nil _ h_dl_empty] at h_v_in
                  rcases List.mem_append.mp h_v_in with h_in_A | h_in_BC
                  · have h1 : v ∈ rest_R.support.tail.dropLast :=
                      marg_mem_reverse_strict_interior h_in_A
                    have h2 : v ∈ rest_R.support.dropLast :=
                      marg_tail_dropLast_subset_dropLast _ h1
                    have h_v_in_shR_dl :
                        v ∈ (Walk.cons (WalkStep.forward h_first) rest_R).support.dropLast := by
                      rw [Walk.support_cons,
                          List.dropLast_cons_of_ne_nil rest_R.marg_support_ne_nil]
                      exact List.mem_cons_of_mem _ h2
                    exact h_v_notin_shR_dl h_v_in_shR_dl
                  · rcases List.mem_cons.mp h_in_BC with h_eq_x | h_in_u
                    · -- v = x.
                      by_cases h_rest_R_zero : rest_R.length = 0
                      · cases rest_R with
                        | nil _ => simp at h_dl_empty
                        | cons _ _ => simp [Walk.length_cons] at h_rest_R_zero
                      · push_neg at h_rest_R_zero
                        have h_rest_R_pos : 1 ≤ rest_R.length := by omega
                        have h_rest_R_tail_ne : rest_R.support.tail ≠ [] := by
                          intro h_emp
                          have : rest_R.support.tail.length = 0 := by rw [h_emp]; rfl
                          rw [List.length_tail, Walk.support_length] at this; omega
                        have h_v_in_shR_dl :
                            v ∈ (Walk.cons (WalkStep.forward h_first) rest_R).support.dropLast := by
                          rw [Walk.support_cons,
                              List.dropLast_cons_of_ne_nil rest_R.marg_support_ne_nil,
                              marg_support_cons_form rest_R,
                              List.dropLast_cons_of_ne_nil h_rest_R_tail_ne]
                          exact List.mem_cons.mpr (Or.inr
                            (List.mem_cons.mpr (Or.inl h_eq_x)))
                        exact h_v_notin_shR_dl h_v_in_shR_dl
                    · -- h_in_u : v ∈ [u]. So v = u, contradicting h_uv_ne.
                      simp only [List.mem_singleton] at h_in_u
                      exact h_uv_ne h_in_u.symm
              · -- u ∉ new_walk.support.dropLast.
                intro h_u_in
                rw [h_new_walk_supp, h_shL_supp] at h_u_in
                -- (x :: [u]) is non-empty; dropLast of (x :: [u]) = [x].
                have h_cons_ne : (x :: [u]) ≠ [] := List.cons_ne_nil _ _
                rw [List.dropLast_append_of_ne_nil h_cons_ne] at h_u_in
                rcases List.mem_append.mp h_u_in with h_in_A | h_in_x
                · -- u ∈ rest_R.reverse.support.dropLast → u ∈ rest_R.support.tail set-wise.
                  have h_u_rR_tail : u ∈ rest_R.support.tail := by
                    rw [marg_support_reverse, List.dropLast_reverse, List.mem_reverse] at h_in_A
                    exact h_in_A
                  have h_u_shR :
                      u ∈ (Walk.cons (WalkStep.forward h_first) rest_R).support := by
                    rw [Walk.support_cons]
                    exact List.mem_cons_of_mem _ (List.mem_of_mem_tail h_u_rR_tail)
                  exact hu_tail_π (h_shR_supp_in_π_tail u h_u_shR)
                · -- u ∈ (x :: [u]).dropLast = [x]. So u = x.
                  have h_dl : (x :: [u]).dropLast = [x] := by rfl
                  rw [h_dl] at h_in_x
                  simp only [List.mem_singleton] at h_in_x
                  -- h_in_x : u = x. Use it to derive u ∈ shrink_R.support directly (head).
                  -- Actually shrink_R = .cons (.forward h_first) rest_R has u as head.
                  have h_u_shR :
                      u ∈ (Walk.cons (WalkStep.forward h_first) rest_R).support := by
                    rw [Walk.support_cons]; exact List.mem_cons_self
                  exact hu_tail_π (h_shR_supp_in_π_tail u h_u_shR)
              · refine ⟨?_⟩
                refine
                  { m := x
                    m' := u
                    leftArm := rest_R.reverse
                    hinge := .backward h_first
                    rightArm := shrink_L
                    decompose := rfl
                    leftBackward := h_rest_R_rev_back
                    hingeIntoSource := by simp
                    rightDirected := by
                      cases shrink_L with
                      | nil _ => simp
                      | cons _ _ => simp [Walk.length_cons] at h_shL_zero }
              · -- Support tracking (case m₀=m₁ option C): new_walk supp ⊆ π.support, ∉ W.
                have hx_V : x ∈ (G.marginalize W).V := by
                  have h_E : (u, x) ∈ (G.marginalize W).E := h_first
                  exact (Set.mem_prod.mp ((G.marginalize W).E_subset h_E)).2
                have hx_notW : x ∉ W := by
                  rw [CDMG.marginalize_V] at hx_V; exact hx_V.2
                have h_rest_R_supp_notW : ∀ y ∈ rest_R.support, y ∉ W :=
                  marg_directed_supp_notW rest_R h_rest_R_dir hx_notW
                have hx_in_shR : x ∈ (Walk.cons (.forward h_first) rest_R).support := by
                  rw [Walk.support_cons]
                  refine List.mem_cons.mpr (Or.inr ?_)
                  rw [Walk.marg_support_cons_form rest_R]; exact List.mem_cons_self
                intro y hy
                rw [h_new_walk_supp, h_shL_supp] at hy
                rcases List.mem_append.mp hy with hL | hR
                · -- y ∈ rest_R.reverse.support.dropLast.
                  have hy_rev : y ∈ rest_R.reverse.support := List.dropLast_subset _ hL
                  have hy_rest : y ∈ rest_R.support := marg_mem_reverse_support hy_rev
                  have hy_in_shR : y ∈ (Walk.cons (.forward h_first) rest_R).support := by
                    rw [Walk.support_cons]
                    exact List.mem_cons_of_mem _ hy_rest
                  exact ⟨List.mem_of_mem_tail (h_shR_supp_in_π_tail y hy_in_shR),
                         h_rest_R_supp_notW y hy_rest⟩
                · rcases List.mem_cons.mp hR with hyx | hy_u
                  · rw [hyx]
                    exact ⟨List.mem_of_mem_tail (h_shR_supp_in_π_tail x hx_in_shR),
                           hx_notW⟩
                  · -- y ∈ [u]. So y = u. u ∈ π.support (start vertex of π).
                    simp at hy_u
                    rw [hy_u]
                    refine ⟨?_, hu⟩
                    -- u ∈ π.support: it's the start of π. π.support = u :: π.support.tail.
                    rw [Walk.marg_support_cons_form π]
                    exact List.mem_cons_self
      · -- m₀ ≠ m₁. Build q in G, apply mem_marginalize_L.
        let q : Walk G m₀ m₁ := L_pre.reverse.append (.cons hg R_pre)
        have h_L_pre_rev_back : L_pre.reverse.IsAllBackward :=
          marg_isAllBackward_reverse_of_isDirected h_L_pre_dir
        have h_R_pre_supp_ne : R_pre.support ≠ [] := R_pre.marg_support_ne_nil
        -- q.InteriorIn W: q.support.tail.dropLast ⊆ W.
        have hq_int : q.InteriorIn W := by
          intro x hx
          -- Unfold q.support.tail.dropLast.
          have h_q_supp : q.support =
              L_pre.reverse.support.dropLast ++ (m_w :: R_pre.support) := by
            show (L_pre.reverse.append _).support = _
            rw [marg_support_append, Walk.support_cons]
          by_cases hL : L_pre.reverse.support.dropLast = []
          · -- L_pre.length = 0.
            have h_q_tail : q.support.tail = R_pre.support := by
              rw [h_q_supp, hL, List.nil_append, List.tail_cons]
            rw [h_q_tail] at hx
            -- hx : x ∈ R_pre.support.dropLast.
            exact h_R_pre_int x hx
          · -- L_pre.length ≥ 1.
            have h_q_tail : q.support.tail =
                L_pre.reverse.support.dropLast.tail ++ (m_w :: R_pre.support) := by
              rw [h_q_supp, list_tail_append_of_ne_nil _ hL]
            rw [h_q_tail] at hx
            rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)] at hx
            rw [List.dropLast_cons_of_ne_nil h_R_pre_supp_ne] at hx
            rcases List.mem_append.mp hx with h_in_A | h_in_C
            · -- x ∈ L_pre.reverse.support.dropLast.tail ⊆ L_pre.support.tail.dropLast.
              have h1 : x ∈ L_pre.support.tail.dropLast := by
                rw [marg_support_reverse, List.dropLast_reverse, List.tail_reverse,
                    List.mem_reverse] at h_in_A
                exact h_in_A
              have h2 : x ∈ L_pre.support.dropLast :=
                marg_tail_dropLast_subset_dropLast _ h1
              exact h_L_pre_int x h2
            · rcases List.mem_cons.mp h_in_C with h_eq | h_in_rA
              · -- x = m_w. Need m_w ∈ W (since L_pre.length ≥ 1, m_w is head of L_pre.support.dropLast).
                have h_L_pre_pos : 1 ≤ L_pre.length := by
                  by_contra h_neg
                  push_neg at h_neg
                  apply hL
                  have h_zero : L_pre.length = 0 := by omega
                  have h_supp_len : L_pre.reverse.support.length = 1 := by
                    rw [Walk.support_length, marg_length_reverse, h_zero]
                  obtain ⟨a, ha⟩ : ∃ a, L_pre.reverse.support = [a] :=
                    List.length_eq_one_iff.mp h_supp_len
                  rw [ha]; rfl
                have h_L_pre_tail_ne : L_pre.support.tail ≠ [] := by
                  intro h_emp
                  have : L_pre.support.tail.length = 0 := by rw [h_emp]; rfl
                  rw [List.length_tail, Walk.support_length] at this; omega
                have h_m_w_in_dl : m_w ∈ L_pre.support.dropLast := by
                  rw [marg_support_cons_form L_pre,
                      List.dropLast_cons_of_ne_nil h_L_pre_tail_ne]
                  simp
                rw [h_eq]
                exact h_L_pre_int m_w h_m_w_in_dl
              · exact h_R_pre_int x h_in_rA
        -- q.support.tail.length = q.length ≥ 1.
        have h_q_pos : 1 ≤ q.length := by
          change 1 ≤ (L_pre.reverse.append (.cons hg R_pre)).length
          rw [Walk.length_append, Walk.length_cons]
          omega
        have h_q_tail_ne : q.support.tail ≠ [] := by
          intro h_emp
          have : q.support.tail.length = 0 := by rw [h_emp]; rfl
          rw [List.length_tail, Walk.support_length] at this; omega
        have h_q_tail_last : q.support.tail.getLast h_q_tail_ne = m₁ :=
          marg_support_tail_getLast q h_q_pos
        have hq_bif : q.IsBifurcation := by
          refine ⟨h_m₀m₁_neq, ?_, ?_, ?_⟩
          · -- m₀ ∉ q.support.tail.
            intro h_in
            have h_decomp : q.support.tail =
                q.support.tail.dropLast ++ [q.support.tail.getLast h_q_tail_ne] :=
              (List.dropLast_append_getLast h_q_tail_ne).symm
            rw [h_decomp] at h_in
            rcases List.mem_append.mp h_in with h | h
            · exact h_m₀_notW (hq_int m₀ h)
            · simp only [List.mem_singleton] at h
              rw [h_q_tail_last] at h
              exact h_m₀m₁_neq h
          · -- m₁ ∉ q.support.dropLast.
            intro h_in
            -- q.support.dropLast = q.support's positions 0..q.length-1 = head m₀ ++ tail.dropLast.
            have h_q_supp_form : q.support = m₀ :: q.support.tail :=
              marg_support_cons_form q
            rw [h_q_supp_form, List.dropLast_cons_of_ne_nil h_q_tail_ne] at h_in
            rcases List.mem_cons.mp h_in with h | h
            · exact h_m₀m₁_neq h.symm
            · exact h_m₁_notW (hq_int m₁ h)
          · exact ⟨{
              m := m_w
              m' := m'_w
              leftArm := L_pre.reverse
              hinge := hg
              rightArm := R_pre
              decompose := rfl
              leftBackward := h_L_pre_rev_back
              hingeIntoSource := h_hIS
              rightDirected := h_R_pre_dir }⟩
        -- Derive m_w ∈ G.V from hg.
        have h_m_w_V : m_w ∈ G.V := by
          cases hg with
          | forward _ => exact absurd h_hIS (by simp)
          | backward h => exact (Set.mem_prod.mp (G.E_subset h)).2
          | bidir h => exact (Set.mem_prod.mp (G.L_subset h)).1
        -- Derive m₀ ∈ G.V.
        have h_m₀_V : m₀ ∈ G.V := by
          by_cases hL : 1 ≤ L_pre.length
          · exact marg_end_in_V_of_isDirected_pos L_pre h_L_pre_dir hL
          · push_neg at hL
            have h_zero : L_pre.length = 0 := by omega
            have aux : ∀ {a b : α} (p : Walk G a b), p.length = 0 → a = b := by
              intros a b p hp
              cases p with
              | nil _ => rfl
              | cons _ _ => simp [Walk.length_cons] at hp
            have h_m_w_eq_m₀ : m_w = m₀ := aux L_pre h_zero
            rw [← h_m_w_eq_m₀]; exact h_m_w_V
        -- Derive m'_w ∈ G.V from .bidir hinge OR derive contradiction from .backward + R_pre.length = 0.
        -- For m₁ ∈ G.V: similar.
        have h_m'_w_V_or_R_pos : m'_w ∈ G.V ∨ 1 ≤ R_pre.length := by
          by_cases hR : 1 ≤ R_pre.length
          · exact Or.inr hR
          · push_neg at hR
            have h_R_zero : R_pre.length = 0 := by omega
            have aux : ∀ {a b : α} (p : Walk G a b), p.length = 0 → a = b := by
              intros a b p hp
              cases p with
              | nil _ => rfl
              | cons _ _ => simp [Walk.length_cons] at hp
            have h_m'_w_eq_m₁ : m'_w = m₁ := aux R_pre h_R_zero
            -- m₁ ∉ W; need to show m'_w ∈ G.V.
            -- Cases on hg.
            cases hg with
            | forward _ => exact absurd h_hIS (by simp)
            | bidir h => exact Or.inl (Set.mem_prod.mp (G.L_subset h)).2
            | backward h =>
              -- (m'_w, m_w) ∈ G.E. m'_w ∈ G.J ∪ G.V.
              -- If m'_w ∈ G.V, done.
              -- If m'_w ∈ G.J only: construct a directed walk m₁ → m₀ with interior in W. This gives h_E_bwd, contradicting our branch.
              -- Walk: .cons (.forward h_back') L_pre where h_back' : (m'_w, m_w) ∈ G.E.
              -- This is Walk G m'_w m₀ = Walk G m₁ m₀ (since m₁ = m'_w).
              -- Directed (all forward). Length L_pre.length + 1 ≥ 1.
              -- Interior: m_w :: L_pre.support.tail.dropLast. m_w ∈ W when L_pre.length ≥ 1, or m_w = m₀ when L_pre.length = 0.
              -- L_pre.length = 0 case: walk is .cons (.forward h_back') (nil m_w) = single edge. Interior empty.
              --   Walk goes m'_w → m_w = m₀ (since L_pre.length = 0 → m_w = m₀). Length 1. ✓.
              -- L_pre.length ≥ 1 case: m_w ∈ W (head of L_pre.support.dropLast). Walk's interior includes m_w + L_pre's strict interior ⊆ W. ✓.
              exfalso
              apply h_E_bwd
              have h_fwd : m'_w ⟶[G] m_w := h
              -- m'_w = m₁ via h_m'_w_eq_m₁. Build walk from m₁ to m₀.
              refine ⟨h_m'_w_eq_m₁ ▸ Walk.cons (.forward h_fwd) L_pre, ?_, ?_, ?_⟩
              · -- IsDirected.
                rw [show (h_m'_w_eq_m₁ ▸ Walk.cons (.forward h_fwd) L_pre :
                    Walk G m₁ m₀).IsDirected =
                    (Walk.cons (.forward h_fwd) L_pre).IsDirected
                  from by cases h_m'_w_eq_m₁; rfl]
                simpa using h_L_pre_dir
              · -- InteriorIn W.
                intro y hy
                have h_eq : (h_m'_w_eq_m₁ ▸ Walk.cons (.forward h_fwd) L_pre :
                    Walk G m₁ m₀).support =
                    (Walk.cons (.forward h_fwd) L_pre).support := by
                  cases h_m'_w_eq_m₁; rfl
                rw [h_eq, Walk.support_cons, List.tail_cons] at hy
                exact h_L_pre_int y hy
              · -- 1 ≤ length.
                rw [show (h_m'_w_eq_m₁ ▸ Walk.cons (.forward h_fwd) L_pre :
                    Walk G m₁ m₀).length =
                    (Walk.cons (.forward h_fwd) L_pre).length
                  from by cases h_m'_w_eq_m₁; rfl]
                simp [Walk.length_cons]
        have h_m₁_V : m₁ ∈ G.V := by
          rcases h_m'_w_V_or_R_pos with h_m'_V | h_R_pos
          · by_cases hR : 1 ≤ R_pre.length
            · exact marg_end_in_V_of_isDirected_pos R_pre h_R_pre_dir hR
            · push_neg at hR
              have h_zero : R_pre.length = 0 := by omega
              have aux : ∀ {a b : α} (p : Walk G a b), p.length = 0 → a = b := by
                intros a b p hp
                cases p with
                | nil _ => rfl
                | cons _ _ => simp [Walk.length_cons] at hp
              have h_m'_w_eq_m₁ : m'_w = m₁ := aux R_pre h_zero
              rw [← h_m'_w_eq_m₁]; exact h_m'_V
          · exact marg_end_in_V_of_isDirected_pos R_pre h_R_pre_dir h_R_pos
        have h_m₀_in_marg : m₀ ∈ G.V \ W := ⟨h_m₀_V, h_m₀_notW⟩
        have h_m₁_in_marg : m₁ ∈ G.V \ W := ⟨h_m₁_V, h_m₁_notW⟩
        have h_L_marg : (m₀, m₁) ∈ (G.marginalize W).L := by
          rw [CDMG.mem_marginalize_L]
          refine ⟨h_m₀_in_marg, h_m₁_in_marg, h_m₀m₁_neq, ?_, ?_, Or.inl ⟨q, hq_bif, hq_int⟩⟩
          · -- ¬ ∃ directed m₀ → m₁ ∧ interior ⊆ W.
            intro ⟨π_E, hπ_E_dir, hπ_E_int⟩
            -- Check if length ≥ 1, else trivial.
            by_cases hL : 1 ≤ π_E.length
            · exact h_E_fwd ⟨π_E, hπ_E_dir, hπ_E_int, hL⟩
            · push_neg at hL
              have h_zero : π_E.length = 0 := by omega
              have aux : ∀ {a b : α} (p : Walk G a b), p.length = 0 → a = b := by
                intros a b p hp
                cases p with
                | nil _ => rfl
                | cons _ _ => simp [Walk.length_cons] at hp
              exact h_m₀m₁_neq (aux π_E h_zero)
          · intro ⟨π_E, hπ_E_dir, hπ_E_int⟩
            by_cases hL : 1 ≤ π_E.length
            · exact h_E_bwd ⟨π_E, hπ_E_dir, hπ_E_int, hL⟩
            · push_neg at hL
              have h_zero : π_E.length = 0 := by omega
              have aux : ∀ {a b : α} (p : Walk G a b), p.length = 0 → a = b := by
                intros a b p hp
                cases p with
                | nil _ => rfl
                | cons _ _ => simp [Walk.length_cons] at hp
              exact h_m₀m₁_neq (aux π_E h_zero).symm
        -- Now build the marg-bif u → v with bidir hinge.
        let new_walk : Walk (G.marginalize W) u v :=
          shrink_L.reverse.append (.cons (.bidir h_L_marg) shrink_R)
        have h_new_walk_supp_a : new_walk.support =
            shrink_L.reverse.support.dropLast ++ (m₀ :: shrink_R.support) := by
          show (shrink_L.reverse.append _).support = _
          rw [marg_support_append, Walk.support_cons]
        left
        refine ⟨new_walk, ⟨h_uv_ne, ?_, ?_, ?_⟩, ?_⟩
        · -- u ∉ new_walk.support.tail. Mirror case (c).
          intro h_u_in
          rw [h_new_walk_supp_a] at h_u_in
          by_cases h_dl_empty : shrink_L.reverse.support.dropLast = []
          · rw [h_dl_empty, List.nil_append, List.tail_cons] at h_u_in
            exact hu_tail_π (h_shR_supp_in_π_tail u h_u_in)
          · rw [list_tail_append_of_ne_nil _ h_dl_empty] at h_u_in
            rcases List.mem_append.mp h_u_in with h_in_A | h_in_BC
            · have h1 : u ∈ shrink_L.support.tail.dropLast := marg_mem_reverse_strict_interior h_in_A
              have h2 : u ∈ shrink_L.support.dropLast := marg_tail_dropLast_subset_dropLast _ h1
              exact h_u_notin_shL_dl h2
            · rcases List.mem_cons.mp h_in_BC with h_eq_m₀ | h_in_shR
              · have h_shL_pos : 1 ≤ shrink_L.length := by
                  by_contra h_neg
                  push_neg at h_neg
                  apply h_dl_empty
                  have h_zero : shrink_L.length = 0 := by omega
                  have h_supp_len : shrink_L.reverse.support.length = 1 := by
                    rw [Walk.support_length, marg_length_reverse, h_zero]
                  obtain ⟨a, ha⟩ : ∃ a, shrink_L.reverse.support = [a] :=
                    List.length_eq_one_iff.mp h_supp_len
                  rw [ha]; rfl
                have h_shL_tail_ne : shrink_L.support.tail ≠ [] := by
                  intro h_emp
                  have : shrink_L.support.tail.length = 0 := by rw [h_emp]; rfl
                  rw [List.length_tail, Walk.support_length] at this; omega
                have h_u_in_shL_dl : u ∈ shrink_L.support.dropLast := by
                  rw [marg_support_cons_form shrink_L,
                      List.dropLast_cons_of_ne_nil h_shL_tail_ne]
                  exact List.mem_cons.mpr (Or.inl h_eq_m₀)
                exact h_u_notin_shL_dl h_u_in_shL_dl
              · exact hu_tail_π (h_shR_supp_in_π_tail u h_in_shR)
        · -- v ∉ new_walk.support.dropLast. Mirror case (c).
          intro h_v_in
          rw [h_new_walk_supp_a] at h_v_in
          have h_shR_supp_ne : shrink_R.support ≠ [] := shrink_R.marg_support_ne_nil
          have h_cons_ne : (m₀ :: shrink_R.support) ≠ [] := List.cons_ne_nil _ _
          rw [List.dropLast_append_of_ne_nil h_cons_ne] at h_v_in
          rw [List.dropLast_cons_of_ne_nil h_shR_supp_ne] at h_v_in
          rcases List.mem_append.mp h_v_in with h_in_A | h_in_BC
          · have h_v_shL_tail : v ∈ shrink_L.support.tail := by
              rw [marg_support_reverse, List.dropLast_reverse, List.mem_reverse] at h_in_A
              exact h_in_A
            have h_v_shL : v ∈ shrink_L.support := by
              rw [marg_support_cons_form shrink_L]
              exact List.mem_cons_of_mem _ h_v_shL_tail
            exact hv_drop_π (h_shL_supp_in_π_drop v h_v_shL)
          · rcases List.mem_cons.mp h_in_BC with h_eq_m₀ | h_in_shR_dl
            · exact hv_drop_π (h_eq_m₀.symm ▸ h_lA_supp_in_π_drop m₀ h_m₀_in_lA)
            · exact h_v_notin_shR_dl h_in_shR_dl
        · refine ⟨?_⟩
          refine
            { m := m₀
              m' := m₁
              leftArm := shrink_L.reverse
              hinge := .bidir h_L_marg
              rightArm := shrink_R
              decompose := rfl
              leftBackward := h_shL_rev_back
              hingeIntoSource := by simp
              rightDirected := h_shR_dir }
        · -- Support tracking (case L-edge bidir hinge): new_walk supp ⊆ π.support, ∉ W.
          have h_shL_supp_notW : ∀ x ∈ shrink_L.support, x ∉ W :=
            marg_directed_supp_notW shrink_L h_shL_dir h_m₀_notW
          have h_shR_supp_notW : ∀ x ∈ shrink_R.support, x ∉ W :=
            marg_directed_supp_notW shrink_R h_shR_dir h_m₁_notW
          intro x hx
          rw [h_new_walk_supp_a] at hx
          rcases List.mem_append.mp hx with hL | hR
          · have hx_rev : x ∈ shrink_L.reverse.support := List.dropLast_subset _ hL
            have hx_shL : x ∈ shrink_L.support := marg_mem_reverse_support hx_rev
            exact ⟨List.dropLast_subset _ (h_shL_supp_in_π_drop x hx_shL),
                   h_shL_supp_notW x hx_shL⟩
          · rcases List.mem_cons.mp hR with hxm | hx_shR
            · rw [hxm]
              refine ⟨List.dropLast_subset _ (h_lA_supp_in_π_drop m₀ h_m₀_in_lA),
                     h_m₀_notW⟩
            · exact ⟨List.mem_of_mem_tail (h_shR_supp_in_π_tail x hx_shR),
                     h_shR_supp_notW x hx_shR⟩

end Walk

namespace CDMG

variable {α : Type*}

-- claim_3_16 (part 1/4) -- item 1 of the LN remark
-- title: MarginalizationPreserves -- ancestral relations
--
-- For `v_1, v_2 ∉ W`, `v_1` is an ancestor of `v_2` in `G` iff `v_1`
-- is an ancestor of `v_2` in the marginalization `G^{\sm W}`.
-- Direct biconditional translation of LN item 1; both directions are
-- routed through a walk translator that uses `mem_marginalize_E` to
-- shrink a directed walk through `W` in `G` to a single edge in
-- `G^{\sm W}` (and conversely expand a directed edge of `G^{\sm W}`
-- back to a directed walk in `G` whose intermediate vertices lie in
-- `W`).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` Rem 964 item 1:

  For $v_1,v_2 \in G$ with $v_1,v_2 \notin W$ we have the equivalence:
    $v_1 \in \Anc^G(v_2)\quad \iff \quad v_1 \in \Anc^{G^{\sm W}}(v_2).$
-/
--
-- ## Design choice
--
-- * **Plain English statement.** The set of ancestors of `v_2` (in
--   the `Anc^G` sense — directed-walk reachable) is preserved by
--   marginalization on vertices outside `W`. Equivalently, for any
--   target `v_2 ∉ W`, the marginalization preserves which `v_1 ∉ W`
--   reach `v_2` along a directed walk.
--
-- * **Preconditions `v_i ∉ W` only, no explicit `v_i ∈ G`.** The LN
--   writes "$v_1, v_2 \in G$ with $v_1, v_2 \notin W$" — the
--   `v_1 \in G` precondition is implicit in the LHS `v_1 ∈ Anc^G(v_2)`
--   (the `Anc` def in `Section3_1/FamilyReachability.lean` line 119
--   carries a `w ∈ G` clause as the first conjunct of its
--   set-builder), so we do not repeat it. The `v_2 ∈ G` precondition
--   is not strictly needed either: if `v_2 ∉ G`, both sides degenerate
--   in the same way (length-`≥ 1` directed walks force their
--   endpoints into `G.V ⊆ G` via `G.E_subset`; the length-`0` case
--   only fires when `v_1 = v_2`, in which case the `Anc` membership
--   on each side reduces to `v_2 ∈ G` resp.
--   `v_2 ∈ G.marginalize W`, and `v_2 ∉ W` plus `v_2 ∈ G ↔ v_2 ∈
--   G.marginalize W` make the biconditional discharge cleanly). We
--   accept the very mild discrepancy with the LN's literal preamble
--   for the simpler statement; see also risk §5.4 in
--   `workspace_claim_3_16.md`.
--
-- * **`v_i ∉ W` rather than `v_i ∈ G.marginalize W`.** These are not
--   equivalent in the presence of `W ∩ G.J ≠ ∅`: an input node
--   `v ∈ G.J ∩ W` belongs to `G` (via `G.J ⊆ G`) and also to
--   `G.marginalize W` (since `G.marginalize W` has the *same* `J`,
--   see `marginalize_J`), so `v ∈ G.marginalize W` is a *weaker*
--   precondition than `v ∉ W`. The LN says "$v_1, v_2 \notin W$",
--   not "$v_1, v_2 \in G \sm W$", so we stay literal. See risk §5.4
--   in `workspace_claim_3_16.md` and the `Marginalization.lean`
--   no-precondition design block for why `G.marginalize` admits any
--   `W : Set α` (and the LN's set-relative reading is at the use
--   site, not at the operator definition).
--
-- * **Why an `iff` and not two separate `_of_` lemmas.** Both
--   directions are needed by claim_3_17 (in opposite directions on
--   different sides of its commute equality), and the LN states it
--   as an equivalence. Bundling as `↔` matches the LN and keeps the
--   single-citation form simple.
--
-- * **Naming `marginalize_anc_iff`.** Follows the project's
--   `<construction>_<preserved property>_iff` convention for
--   biconditional preservation results; mirrors the soon-to-be-named
--   `marginalize_bifurcation_iff` (item 2), `marginalize_isAcyclic`
--   (item 3a), `marginalize_isTopologicalOrder` (item 3b).

/-- claim_3_16 part 1/4 (LN remark item 1): for any CDMG `G` and any
set `W`, marginalization preserves ancestral relations on vertices
outside `W`. For `v₁, v₂ ∉ W`, `v₁` is an ancestor of `v₂` in `G` iff
`v₁` is an ancestor of `v₂` in the marginalization `G.marginalize W`.

The implicit `v₁ ∈ G` precondition of the LN's "$v_1, v_2 \in G$"
preamble is already carried by the `mem_Anc` membership on each side
(both `G.Anc v₂` and `(G.marginalize W).Anc v₂` are set-builders
guarded by `_ ∈ G` resp. `_ ∈ G.marginalize W`); the explicit
`v_i ∉ W` hypotheses bridge the two memberships. The proof (to be
filled in by `prove_claim_in_lean`) shuttles a directed walk through
`W` in `G` to / from a single directed edge in `G^{\sm W}` via
`mem_marginalize_E`. -/
theorem marginalize_anc_iff (G : CDMG α) (W : Set α) {v₁ v₂ : α}
    (h₁ : v₁ ∉ W) (h₂ : v₂ ∉ W) :
    v₁ ∈ G.Anc v₂ ↔ v₁ ∈ (G.marginalize W).Anc v₂ := by
  -- v₁ ∈ G.Anc v₂ ↔ v₁ ∈ G ∧ ∃ π : Walk G v₁ v₂, π.IsDirected.
  -- v₁ ∈ G ↔ v₁ ∈ G.marginalize W given v₁ ∉ W (both reduce to G.J ∪ (G.V \ W)).
  -- Walk existence transports via the two translators.
  rw [CDMG.mem_Anc, CDMG.mem_Anc]
  -- Membership equivalence: v₁ ∈ G ↔ v₁ ∈ G.marginalize W given v₁ ∉ W.
  have h_mem_iff : v₁ ∈ G ↔ v₁ ∈ G.marginalize W := by
    rw [CDMG.mem_iff, CDMG.mem_iff, CDMG.marginalize_J, CDMG.marginalize_V]
    constructor
    · rintro (hJ | hV)
      · exact Or.inl hJ
      · exact Or.inr ⟨hV, h₁⟩
    · rintro (hJ | ⟨hV, _⟩)
      · exact Or.inl hJ
      · exact Or.inr hV
  refine ⟨fun ⟨h_in_G, π, hπ_dir⟩ => ⟨h_mem_iff.mp h_in_G, ?_⟩,
          fun ⟨h_in_marg, π', hπ'_dir⟩ => ⟨h_mem_iff.mpr h_in_marg, ?_⟩⟩
  · -- (→) direction: shrink the directed walk in G to a directed walk in marginalize.
    obtain ⟨π', hπ'_dir, _, _, _⟩ := Walk.exists_marg_directed_of_directed W π hπ_dir h₁ h₂
    exact ⟨π', hπ'_dir⟩
  · -- (←) direction: expand the directed walk in marginalize to one in G.
    obtain ⟨ρ, hρ_dir, _, _, _, _⟩ := Walk.exists_directed_of_marg_directed W π' hπ'_dir
    exact ⟨ρ, hρ_dir⟩

-- claim_3_16 (part 2/4) -- item 2 of the LN remark (no source)
-- title: MarginalizationPreserves -- bifurcations
--
-- For `v_1, v_2 ∈ G \ W`, there is a bifurcation between `v_1` and
-- `v_2` in `G` iff there is a bifurcation between them in
-- `G^{\sm W}`. The LN's "between" is symmetric in the two endpoints;
-- we encode that symmetry as `(∃ π : Walk … v₁ v₂, …) ∨ (∃ π : Walk
-- … v₂ v₁, …)` on both sides of the iff. The with-source variant
-- ("with source `v_3`") is *deliberately deferred* to a follow-up
-- dispatch — see the file docstring's "Scope of this file" section
-- and risk §5.2 in `workspace_claim_3_16.md`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` Rem 964 item 2
(no-source half; the parenthetical "(with source $v_3$)" half is the
deferred variant):

  For $v_1,v_2 \in G \sm W$ (and, optionally, $v_3 \in G\sm W$):
  there is a bifurcation between $v_1$ and $v_2$ (with source $v_3$)
  in $G$ if and only if there is a bifurcation between $v_1$ and
  $v_2$ (with source $v_3$) in $G^{\sm W}$.
-/
--
-- ## Design choice
--
-- * **Plain English statement.** The existence of a bifurcation
--   between two vertices `v_1, v_2 ∈ G \ W` is invariant under
--   marginalization: a bifurcation in `G` whose intermediate
--   vertices are absorbed into `W`-shortcuts becomes a bifurcation
--   in `G^{\sm W}` (and vice versa).
--
-- * **Symmetric `∨` reading of "between".** The LN's word "between"
--   is symmetric in `v_1, v_2`, but a `Walk G v w` is *directional*
--   (start at `v`, end at `w`). The clean Lean encoding of "there
--   exists a bifurcation between `v_1` and `v_2`" is therefore the
--   disjunction
--     `(∃ π : Walk G v₁ v₂, π.IsBifurcation) ∨
--      (∃ π : Walk G v₂ v₁, π.IsBifurcation)`,
--   which is what we use on both sides of the iff. Note this is
--   *not* equivalent to a single direction-quantified existential
--   because `Walk.IsBifurcation` is *not* symmetric across reversal
--   in our encoding (the witness's `leftArm`/`rightArm` split is
--   direction-aware). See the long design block in
--   `Section3_2/Marginalization.lean` (around the `disjoint_EL` and
--   `mem_marginalize_L` definitions) for the same symmetric-`∨`
--   convention applied to the `L^{\sm W}` membership; this row is
--   the first downstream consumer.
--
-- * **Why splitting "no source" and "with source" matters.** The
--   `L^{\sm W}` *exclusion clause* in `mem_marginalize_L`
--   (`Section3_2/Marginalization.lean` line 597) removes pairs that
--   are already in `E^{\sm W}` in either direction (a Lean-encoding
--   deviation, justified by the design block on `disjoint_EL` in
--   `Marginalization.lean`). When this exclusion fires on a bidir
--   hinge of a bifurcation in `G`, the absorbing shortcut edge is
--   directed in `G^{\sm W}` — so the resulting bifurcation in
--   `G^{\sm W}` is forced to use a `.backward` hinge in the
--   *opposite* walk direction, introducing a *source* where the LN
--   bifurcation had none. The no-source biconditional absorbs this
--   cleanly via the symmetric-`∨` reading (the reverse-direction
--   bifurcation lives in the second disjunct). The with-source
--   biconditional does not absorb it cleanly: an LHS no-source
--   bifurcation in `G` would relate to an RHS *with-source* `v_3`
--   bifurcation in `G^{\sm W}`, which is not what
--   `IsBifurcationWithSource v_3` reads as on both sides. Risk §5.2
--   in `workspace_claim_3_16.md` discusses three mitigation
--   candidates; we defer the with-source theorem until the no-source
--   proof has surfaced the exclusion-clause friction concretely.
--
-- * **Preconditions `v_i ∈ G ∧ v_i ∉ W`, four hypotheses.** The LN
--   writes "$v_1, v_2 \in G \sm W$" which unfolds to `v_i ∈ G ∧
--   v_i ∉ W` for both `i`. The asymmetry with `marginalize_anc_iff`
--   (which carries only `v_i ∉ W`) is one of *literal-LN adherence*,
--   not of mathematical content: for `Anc`, the set-builder
--   `Anc^G(v_2) = {w | w ∈ G ∧ ...}` (`Section3_1/FamilyReachability.lean`
--   line 119) embeds `v_1 ∈ G` *syntactically* into the LHS
--   membership, so the LN's "v_1 ∈ G" preamble is redundant with
--   the iff's LHS and we drop it. For `IsBifurcation` the analogous
--   `v_i ∈ G` is *derivable* (the predicate forces `v_1 ≠ v_2` and
--   thus at least one edge, whose endpoints lie in `G.V ⊆ G` via
--   `G.E_subset`) but not embedded in the existential's syntactic
--   shape, so we hoist the LN's preamble into explicit hypotheses
--   here to keep the statement literal. See risk §5.4 in
--   `workspace_claim_3_16.md` for the precondition shape discussion
--   (and why we use `v_i ∈ G ∧ v_i ∉ W` rather than
--   `v_i ∈ G.marginalize W` — the latter would be a *weaker*
--   hypothesis when `W ∩ G.J ≠ ∅`, because `G.J ⊆ G.marginalize W`
--   is preserved by `marginalize_J`).
--
-- * **No `v_1 ≠ v_2` hypothesis added.** `IsBifurcation` already
--   includes `v ≠ w` as its first conjunct (`Section3_1/Bifurcation.lean`
--   line 309), so each existential side of the iff implicitly forces
--   `v_1 ≠ v_2` when nonempty. Adding it as a hypothesis would
--   duplicate that constraint without changing the truth value of
--   the iff (the `v_1 = v_2` case has both sides false).
--
-- * **Naming `marginalize_bifurcation_iff`.** The no-source default
--   takes the unadorned name (matches the LN's flat sentence "there
--   is a bifurcation between `v_1` and `v_2`"); the with-source
--   variant — once added — will be named
--   `marginalize_bifurcation_source_iff` to mirror the LN's
--   parenthetical refinement.

/-- claim_3_16 part 2/4 (LN remark item 2, no-source half): for any
CDMG `G` and any set `W`, marginalization preserves the existence of
bifurcations between two vertices `v₁, v₂ ∈ G \ W`. The LN's "between"
is read symmetrically in `v₁, v₂` and encoded as a disjunction over
the two walk directions; the disjunction shape is also what makes the
biconditional handle the `L^{\sm W}` exclusion clause cleanly (a bidir
hinge in `G` absorbed by the exclusion still gives a `.backward`-hinge
bifurcation in `G^{\sm W}` *in the opposite walk direction*).

The with-source variant ("with source `v_3`") is intentionally
*deferred* to a follow-up dispatch — see the file docstring and risk
§5.2 in `workspace_claim_3_16.md`. The proof (to be filled in by
`prove_claim_in_lean`) shuttles a bifurcation's arms and hinge through
`W` via `mem_marginalize_E` (for the directed arms) and
`mem_marginalize_L` (for the bidir hinge), with the symmetric `∨`
absorbing the exclusion-clause case-split. -/
theorem marginalize_bifurcation_iff (G : CDMG α) (W : Set α)
    {v₁ v₂ : α} (h₁v : v₁ ∈ G) (h₂v : v₂ ∈ G)
    (h₁W : v₁ ∉ W) (h₂W : v₂ ∉ W) :
    ((∃ π : Walk G v₁ v₂, π.IsBifurcation) ∨
     (∃ π : Walk G v₂ v₁, π.IsBifurcation)) ↔
    ((∃ π : Walk (G.marginalize W) v₁ v₂, π.IsBifurcation) ∨
     (∃ π : Walk (G.marginalize W) v₂ v₁, π.IsBifurcation)) := by
  -- A single helper handles ONE walk-direction case in each direction of the iff.
  -- The disjunction structure on both sides matches naturally.
  -- For one direction at a time, we case-split on bifurcation hinge type.
  -- Below, `back_to_marg_bif` handles (←) for a fixed walk direction; we apply
  -- it twice (once per disjunct on the RHS) to discharge (←). The (→) direction
  -- is more involved and handled inline.
  constructor
  · -- (→) direction: G bifurcation → marg bifurcation.
    -- Split on which walk direction the G bifurcation is in.
    rintro (⟨π, hb⟩ | ⟨π, hb⟩)
    · -- G bif in v₁ → v₂ direction.
      rcases Walk.marginalize_bif_forward h₁v h₂v h₁W h₂W π hb with
        ⟨π', hπ', _⟩ | ⟨π', hπ', _⟩
      · exact Or.inl ⟨π', hπ'⟩
      · exact Or.inr ⟨π', hπ'⟩
    · -- G bif in v₂ → v₁ direction (symmetric).
      rcases Walk.marginalize_bif_forward h₂v h₁v h₂W h₁W π hb with
        ⟨π', hπ', _⟩ | ⟨π', hπ', _⟩
      · exact Or.inr ⟨π', hπ'⟩
      · exact Or.inl ⟨π', hπ'⟩
  · -- (←) direction: marg bifurcation → G bifurcation.
    rintro (⟨π', hb'⟩ | ⟨π', hb'⟩)
    · -- marg bif in v₁ → v₂ direction.
      -- marginalize_bif_backward returns σ with IsBifurcation ∧ support tracking;
      -- strip the support tracking for the plain bifurcation iff conclusion.
      rcases Walk.marginalize_bif_backward h₁v h₂v h₁W h₂W π' hb' with
        ⟨σ, hσ, _⟩ | ⟨σ, hσ, _⟩
      · exact Or.inl ⟨σ, hσ⟩
      · exact Or.inr ⟨σ, hσ⟩
    · -- marg bif in v₂ → v₁ direction (symmetric).
      rcases Walk.marginalize_bif_backward h₂v h₁v h₂W h₁W π' hb' with
        ⟨σ, hσ, _⟩ | ⟨σ, hσ, _⟩
      · exact Or.inr ⟨σ, hσ⟩
      · exact Or.inl ⟨σ, hσ⟩

-- claim_3_16 (part 3/4) -- item 3a of the LN remark (acyclicity)
-- title: MarginalizationPreserves -- acyclicity
--
-- If `G` is acyclic, so is `G^{\sm W}`. Direct walk-concatenation
-- argument: a non-trivial directed cycle in `G^{\sm W}` expands
-- (via `mem_marginalize_E` step-by-step) to a non-trivial directed
-- cycle in `G`, contradicting `G.IsAcyclic`. No claim_3_2 dependency.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` Rem 964 item 3
(acyclicity half; the topological-order half is item 3b below):

  If the CDMG $G$ is acyclic then so is $G^{\sm W}$ and a topological
  order of $G$ induces a topological order on $G^{\sm W}$ (by just
  ignoring the nodes from $W$).
-/
--
-- ## Design choice
--
-- * **Plain English statement.** Marginalization cannot manufacture
--   a directed cycle out of an acyclic graph: every edge of
--   `G^{\sm W}` represents a directed walk through `W` in `G`, so a
--   cycle in `G^{\sm W}` expands to a cycle in `G`. Acyclicity is
--   therefore preserved.
--
-- * **Split from item 3b (topological order).** Item 3a and item 3b
--   are logically independent: 3a is provable directly by walk
--   concatenation through `mem_marginalize_E` (the existential
--   directed-walk shortcut characterization), without invoking
--   claim_3_2's "acyclic iff has topological order" equivalence.
--   Splitting them avoids the (apparent) circular dependency feel
--   "3a follows from 3b via claim_3_2"; it also matches downstream
--   needs (claim_3_17, chapter 4 want preservation of acyclicity
--   without a specific named topological order, and would otherwise
--   have to invent one just to invoke item 3b). Mirrors the
--   precedent in `SwigAcyclicTopologicalOrder.lean` (claim_3_9) and
--   `AcyclicityUnderInterventionNodes.lean` (claim_3_13), both of
--   which split their LN `\Rem` block into two theorems for the same
--   reason.
--
-- * **No vertex-membership precondition.** `IsAcyclic` is itself a
--   `∀ v ∈ G, …` statement, so there is no specific vertex hypothesis
--   needed at the outer level. The proof case-splits on a
--   hypothetical cycle vertex `v ∈ G.marginalize W` (which yields
--   `v ∈ G` via `marginalize_J` / `marginalize_V` plus `mem_iff`).
--
-- * **No `W ⊆ G.V` precondition.** `marginalize` is well-defined for
--   *every* `W : Set α` (see the no-precondition design block in
--   `Marginalization.lean` and the iteration-clean rationale in its
--   docstring). The acyclicity preservation does not need `W ⊆ G.V`
--   either — the argument is structural on walks and the `\ W`
--   restriction handles overshoot.
--
-- * **Naming `marginalize_isAcyclic`.** Mirrors
--   `isAcyclic_hardInterventionOn` (claim_3_3 part A),
--   `isAcyclic_nodeSplittingOn` (claim_3_6 part B),
--   `isAcyclic_nodeSplittingHardInterventionOn` (claim_3_9 part B),
--   `isAcyclic_extendingCDMGWithInterventionNodes` (claim_3_13 part A),
--   following Mathlib's `<conclusion>_<construction>` convention.
--   We use `marginalize_isAcyclic` here (rather than
--   `isAcyclic_marginalize`) to keep the prefix matching the other
--   `marginalize_*` lemmas in this row — same flip as `marginalize_J`
--   / `marginalize_V` / `mem_marginalize_E` / `mem_marginalize_L`
--   in `Marginalization.lean`. The dot-notation reading
--   `G.marginalize_isAcyclic W h` then parallels
--   `G.marginalize_J W` / etc.

/-- claim_3_16 part 3/4 (LN remark item 3a): for any CDMG `G` and any
set `W`, if `G` is acyclic then so is the marginalization
`G.marginalize W`.

The mathematical content is that every directed edge of `G.marginalize
W` shortcuts a length-`≥ 1` directed walk through `W` in `G` (by
`mem_marginalize_E`), so a non-trivial directed cycle in
`G.marginalize W` expands to a non-trivial directed cycle in `G`,
contradicting `G.IsAcyclic`. This route is independent of claim_3_2
(no topological-order extraction); the topological-order
preservation half is the sibling theorem
`marginalize_isTopologicalOrder` below.

The proof will be filled in by `prove_claim_in_lean`; this dispatch
covers the statement only. -/
theorem marginalize_isAcyclic (G : CDMG α) (W : Set α)
    (h : G.IsAcyclic) : (G.marginalize W).IsAcyclic := by
  -- Contradiction: a directed cycle in G.marginalize W expands to a directed
  -- cycle in G (each shortcut edge expands to a walk of length ≥ 1), contradicting
  -- G.IsAcyclic.
  intro v hv ⟨π', hπ'_dir, hπ'_pos⟩
  obtain ⟨ρ, hρ_dir, hρ_len, _, _, _⟩ :=
    Walk.exists_directed_of_marg_directed W π' hπ'_dir
  have hρ_pos : 1 ≤ ρ.length := by omega
  -- v ∈ G.marginalize W ⇒ v ∈ G.
  have hv_G : v ∈ G := Walk.marg_mem_of_marg hv
  exact h v hv_G ⟨ρ, hρ_dir, hρ_pos⟩

-- claim_3_16 (part 4/4) -- item 3b of the LN remark (topological order)
-- title: MarginalizationPreserves -- topological order
--
-- A topological order `r` of `G` is also a topological order of
-- `G^{\sm W}`. The LN's "induces a topological order on `G^{\sm W}`
-- (by just ignoring the nodes from `W`)" reads as "same relation
-- `r`, restricted to the smaller vertex set `G^{\sm W}`". Each of
-- the four `IsTopologicalOrder` fields lifts: `irrefl`, `trans`,
-- `trichotomous` use that `v ∈ G.marginalize W ⇒ v ∈ G` (since
-- `marginalize_J` keeps `G.J` and `marginalize_V` restricts to
-- `G.V \ W ⊆ G.V`); `parent_lt` chains `r` along the directed walk
-- through `W` underlying each `G.marginalize W` edge.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` Rem 964 item 3
(topological-order half; same block as item 3a):

  If the CDMG $G$ is acyclic then so is $G^{\sm W}$ and a topological
  order of $G$ induces a topological order on $G^{\sm W}$ (by just
  ignoring the nodes from $W$).
-/
--
-- ## Design choice
--
-- * **Plain English statement.** Marginalization does not require
--   re-sorting: the *same* total-order relation `r` (a parameter,
--   not bundled into a structure) that linearises the vertices of
--   `G` still linearises the vertices of `G^{\sm W}`. The LN's
--   prose "by just ignoring the nodes from `W`" is captured by the
--   fact that `IsTopologicalOrder` quantifies its fields over
--   `v ∈ G.marginalize W` — a strict subset of `v ∈ G` (modulo `G.J
--   ∩ W` overlap; see the `mem_iff` / `marginalize_J` / `marginalize_V`
--   interplay below), so the `r`-axioms on the smaller domain follow
--   from the `r`-axioms on the larger domain by restriction.
--
-- * **Why a fresh theorem and not a corollary of item 3a + claim_3_2.**
--   Item 3a + claim_3_2's `→` direction would give us
--   *some* topological order of `G^{\sm W}`, but the LN explicitly
--   says "*a topological order* of `G` *induces* a topological order
--   on `G^{\sm W}`" — same relation, no re-extraction. Mirroring the
--   LN's constructive content with the same `r` carrying through
--   matches downstream uses (chapter 5 do-calculus picks a
--   topological order once and re-uses it under marginalization;
--   re-extracting via claim_3_2 would force a `Classical.choice`).
--
-- * **`r : α → α → Prop` implicit, `hr` explicit.** Same binder
--   convention as `isTopologicalOrder_nodeSplittingOn` (claim_3_6
--   part A), `isTopologicalOrder_nodeSplittingHardInterventionOn`
--   (claim_3_9 part A), `isTopologicalOrder_extendingCDMGWithInterv
--   entionNodes_extend` (claim_3_13). `r` is implicit because it is
--   unifiable from `hr` (and from the conclusion); `hr` is explicit
--   because it is the mathematical hypothesis under transport.
--
-- * **No `W ⊆ G.V` precondition.** Same as item 3a:
--   `marginalize` accepts any `W : Set α`, and the topological-order
--   preservation argument does not need overlap to be ruled out.
--
-- * **No `[Finite α]` instance hypothesis.** The argument is
--   purely relational (per-field transport on `r`); finiteness does
--   not enter. Mirrors `isTopologicalOrder_nodeSplittingOn` and the
--   other `isTopologicalOrder_*` precedents.
--
-- * **`marginalize_isTopologicalOrder` naming.** Same `marginalize_*`
--   prefix as the rest of this row, paralleling `marginalize_J` /
--   `marginalize_V` / `marginalize_isAcyclic`. The flip from the
--   sibling-row convention `isTopologicalOrder_<construction>`
--   (claim_3_6 / claim_3_9 / claim_3_13) is a local cosmetic choice
--   to keep this row's four theorems prefix-aligned and to read as
--   `G.marginalize_isTopologicalOrder W hr` at the call site —
--   matching how the file's other `marginalize_*` lemmas are quoted.

/-- claim_3_16 part 4/4 (LN remark item 3b): for any CDMG `G` and any
set `W`, a topological order `r` of `G` is also a topological order of
the marginalization `G.marginalize W`. The same relation `r` carries
through — the LN's "by just ignoring the nodes from `W`" — because
`IsTopologicalOrder` quantifies its fields over the (smaller) vertex
set of `G.marginalize W`.

The four `IsTopologicalOrder` fields (irreflexivity, transitivity,
trichotomy, parent-precedence) all reduce field-by-field to the
corresponding statement on `G`: the first three by restriction along
`v ∈ G.marginalize W → v ∈ G`, the fourth by chaining `r` along the
directed walk through `W` that underlies each `G.marginalize W` edge
(via `mem_marginalize_E`). See `marginalize_isAcyclic` above for the
acyclicity preservation half of the LN remark.

The proof will be filled in by `prove_claim_in_lean`; this dispatch
covers the statement only. -/
theorem marginalize_isTopologicalOrder (G : CDMG α) (W : Set α)
    {r : α → α → Prop} (hr : G.IsTopologicalOrder r) :
    (G.marginalize W).IsTopologicalOrder r := by
  -- The four IsTopologicalOrder fields transport: the first three by restriction
  -- (v ∈ G.marginalize W ⇒ v ∈ G), the fourth by chaining r along the directed
  -- walk underlying each marginalize edge via mem_marginalize_E.
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- irrefl: r restricted to G.marginalize W vertices is irreflexive.
    intro v hv
    exact hr.irrefl v (Walk.marg_mem_of_marg hv)
  · -- trans: r restricted to G.marginalize W is transitive.
    intro v hv w hw x hx
    exact hr.trans v (Walk.marg_mem_of_marg hv) w (Walk.marg_mem_of_marg hw)
      x (Walk.marg_mem_of_marg hx)
  · -- trichotomous.
    intro v hv w hw
    exact hr.trichotomous v (Walk.marg_mem_of_marg hv) w (Walk.marg_mem_of_marg hw)
  · -- parent_lt: v ∈ Pa^{G.marginalize W}(w) → r v w.
    -- v ∈ Pa requires (v, w) ∈ (G.marginalize W).E, which by mem_marginalize_E
    -- supplies a length-≥-1 directed walk in G with interior in W; chain via
    -- marg_walk_lt_of_isTopologicalOrder.
    intro v w h_in_Pa
    obtain ⟨_, h_E⟩ := h_in_Pa
    change (v, w) ∈ (G.marginalize W).E at h_E
    rw [CDMG.mem_marginalize_E] at h_E
    obtain ⟨_, _, π, hπ_dir, _, hπ_pos⟩ := h_E
    exact Walk.marg_walk_lt_of_isTopologicalOrder hr π hπ_dir hπ_pos

end CDMG

end Causality
