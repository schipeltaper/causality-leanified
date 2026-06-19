import Chapter3_GraphTheory.Section3_2.MarginalizationPreserves

-- TeX statement: tex/claim_3_17_statement_MarginalizationsCommute.tex
-- TeX proof:    tex/claim_3_17_proof_MarginalizationsCommute.tex

/-!
# Marginalizations commute (claim_3_17)

This file formalises the lecture notes' lemma "marginalizations
commute" -- `lecture-notes/lecture_notes/graphs.tex` Lem at lines
995 -- 1005. The LN states the chained equality

  `(G^{\sm W₁})^{\sm W₂} = (G^{\sm W₂})^{\sm W₁} = G^{\sm (W₁ ∪ W₂)}`

under the preconditions `W₁, W₂ ⊆ V` and `W₁, W₂` disjoint. In our
Lean encoding the `W₁, W₂ ⊆ G.V` part is unnecessary:
`G.marginalize W` is well-defined for every `W : Set α` (see the
design notes in `Section3_2/Marginalization.lean` lines 258 -- 286,
which cite *this very row* as one of the load-bearing iteration tests
that justified dropping the precondition). The disjointness
hypothesis is kept -- it is load-bearing in the LN's statement and in
the walk-concatenation argument of the LN's proof.

Mirroring the proven `HardInterventionsCommute.lean` (claim_3_11),
the LN's chained equality is split into two theorems:

* `marginalize_marginalize` -- the **fusion** lemma, the central
  content of the LN's triple equality:
  `(G.marginalize W₁).marginalize W₂ = G.marginalize (W₁ ∪ W₂)`.
  This is the natural rewrite rule and the form every downstream
  consumer actually uses.
* `marginalize_comm` -- the **commute** corollary: a one-line
  consequence of the fusion lemma plus `Set.union_comm`. Pairs
  naturally with the fusion form so callers that need to *reorder*
  two marginalizations (without collapsing) have a direct lemma to
  hand.

## Where this gets used downstream

* **`graphs.tex` line 984** -- the bifurcation-preservation argument
  of the LN's Remark on marginalization + bifurcations does
  `induction on #W`, peeling one node `w ∈ W` at a time and citing
  `Lemma~\ref{marginalizations-commute}` to flatten the resulting
  iterated marginalization back into `G^{\sm W}`. In Lean this is
  exactly an `induction`-step rewrite via the fusion lemma below.
* **`graphs.tex` line 1426** -- the d-separation invariance theorem
  ("d-separation is preserved under marginalization of nodes outside
  `A ∪ B ∪ C`") opens its proof by citing
  `Lemma~\ref{marginalizations-commute}` and inducting on `#D`,
  reducing to the single-node case `D = {u}`. Again the fusion lemma
  is the load-bearing rewrite that closes the inductive step.
* **claim_3_18** (`graphs.tex` Lem at line 1122, "Marginalization and
  intervention commute") -- composes both marginalization equalities
  with `hardInterventionOn` rewrites; iteration of latent projections
  past an intervention is exactly what the fusion form lets us
  perform.
* **Chapter 4 onwards** -- every latent-projection / hidden-variable
  compression argument that iterates marginalization uses the fusion
  lemma as a `rw` step. CBNs, do-calculus, iSCMs, identification, and
  the FCI / ICDF discovery pipeline all reuse this collapse.
-/

namespace Causality

open scoped Causality.CDMG

namespace CDMG

variable {α : Type*}

/-! ## Helpers for `marginalize_marginalize` (mixed private / public)

These helpers package the recurring component-wise pattern of the proof
(`mk_eq_of_data` for CDMG-extensionality) and the interior-tracking
walk-translation idiom (bifurcation arms expand / contract through
`W₁` using the directed translators of `MarginalizationPreserves`).
The `marg_*` and walk translator helpers in
`MarginalizationPreserves.lean` are reused directly.

**Visibility split.** The CDMG-extensionality / list-massaging glue
(`mk_eq_of_data`, `list_tail_dropLast`, `start_in_support_dropLast`,
`support_append_dropLast`, `support_tail_in_V_of_isDirected`) stays
`private` -- those are one-shot tools for this file's main proof.
The seven *interior-tracking walk translators*
(`lift_directed_walk`, `shrink_directed_walk`,
`directed_walk_iff`, `directed_walk_iff_no_length`,
`lift_bifurcation_walk`, `shrink_bifurcation_walk`,
`bifurcation_walk_iff_no_length`) are **public**: they form the
walk-translation API between `G` and `G.marginalize W` that
`Section3_3/SigmaOpenWalkMarginalization.lean` (the per-vertex
lift / contract layer used by claim_3_25) needs. The seven were
originally `private` -- they existed only to support the
`marginalize_marginalize` proof below -- but the
σ-open walk preservation argument needed in
`lem:stability_separation_marginalization` (claim_3_25) requires
exactly this `(G, G.marginalize W)` interior-tracking layer, with no
clean route through any other existing public API. Manager sign-off
for the cross-subsection promotion is recorded in
`Section3_3/workspace_claim_3_25.md` Manager B turn 4 (and §D.2 of
the leanification diagnostic). Public exposure is API-only: nothing
about the proofs changes, signatures stay identical, and no
downstream caller in `Section3_2/` depends on the visibility (the
sole consumer here is `marginalize_marginalize`, in the same file). -/

/-- CDMG-extensionality helper: two CDMGs are equal as soon as their
four data fields `J / V / E / L` agree. The six prop fields close by
`rfl` once the data fields are pinned down (proof irrelevance under
Lean 4's definitional rule). Mirrors `mk_eq_of_data` in
`HardInterventionsCommute.lean`; kept `private` because it is a
one-shot shortcut used only by `marginalize_marginalize` below. -/
private theorem mk_eq_of_data {G H : CDMG α}
    (hJ : G.J = H.J) (hV : G.V = H.V) (hE : G.E = H.E) (hL : G.L = H.L) :
    G = H := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := G
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := H
  subst hJ
  subst hV
  subst hE
  subst hL
  rfl

/-- A small list-level commutation: `l.tail.dropLast = l.dropLast.tail`.
Mirrors the analogous `list_tail_dropLast` in
`BifurcationAlternative.lean`; copied locally because that one is
`private`. Used pervasively below to swap between the
`Walk.InteriorIn`-expanding form `support.tail.dropLast` and the
form `support.dropLast.tail` that arises from `support_cons`-style
unfolding. -/
private lemma list_tail_dropLast {β : Type*} (l : List β) :
    l.tail.dropLast = l.dropLast.tail := by
  cases l with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest' => rfl


/-- Lift a directed walk in `G.marginalize W₁` with interior in `W₂`
to a directed walk in `G` with interior in `W₁ ∪ W₂` of at least the
same length. Each step of the input expands (via `mem_marginalize_E`)
to a length-≥-1 directed walk in `G` whose interior lies in `W₁`;
the meeting vertices between consecutive expansions are interior
vertices of the input, hence lie in `W₂`. -/
lemma lift_directed_walk (G : CDMG α) (W₁ W₂ : Set α) :
    ∀ {a b : α} (π : Walk (G.marginalize W₁) a b),
      π.IsDirected → π.InteriorIn W₂ →
      ∃ ρ : Walk G a b, ρ.IsDirected ∧ ρ.InteriorIn (W₁ ∪ W₂) ∧
        π.length ≤ ρ.length := by
  intro a b π
  induction π with
  | nil v =>
    intros _ _
    refine ⟨Walk.nil v, by simp, ?_, by simp⟩
    intro x hx; simp at hx
  | @cons a₀ m b₀ step p' ih =>
    intro hπ_dir hπ_int
    cases step with
    | forward h =>
      have hp'_dir : p'.IsDirected := by simpa using hπ_dir
      -- Extract σ : Walk G a₀ m via mem_marginalize_E.
      have h_E : (a₀, m) ∈ (G.marginalize W₁).E := h
      rw [CDMG.mem_marginalize_E] at h_E
      obtain ⟨_, _, σ, hσ_dir, hσ_int_W₁, hσ_pos⟩ := h_E
      -- Casework on p' to derive p'.InteriorIn W₂ and m ∈ W₂ (when p' is non-trivial).
      cases p' with
      | nil =>
        -- p' = nil, so b₀ = m. ρ = σ.
        refine ⟨σ, hσ_dir, ?_, ?_⟩
        · intro x hx
          exact Or.inl (hσ_int_W₁ x hx)
        · simp [Walk.length_cons]
          exact hσ_pos
      | @cons _ s' _ step' p'' =>
        -- p' = cons step' p''.  s' is the intermediate vertex (target of step').
        -- The walk (cons step' p'') has type Walk (G.marg W₁) m b₀.
        -- Derive m ∈ W₂ and p'.InteriorIn W₂.
        have hm_in_W₂ : m ∈ W₂ := by
          apply hπ_int
          -- π.support = a₀ :: m :: p''.support; .tail.dropLast = m :: p''.support.dropLast
          show m ∈ (Walk.cons (.forward h) (Walk.cons step' p'')).support.tail.dropLast
          rw [show (Walk.cons (.forward h) (Walk.cons step' p'')).support
                = a₀ :: m :: p''.support from by simp [Walk.support_cons],
              List.tail_cons, List.dropLast_cons_of_ne_nil p''.marg_support_ne_nil]
          exact List.mem_cons_self
        have hp'_int : (Walk.cons step' p'').InteriorIn W₂ := by
          intro x hx
          apply hπ_int
          show x ∈ (Walk.cons (.forward h) (Walk.cons step' p'')).support.tail.dropLast
          rw [show (Walk.cons (.forward h) (Walk.cons step' p'')).support
                = a₀ :: m :: p''.support from by simp [Walk.support_cons],
              List.tail_cons, List.dropLast_cons_of_ne_nil p''.marg_support_ne_nil]
          refine List.mem_cons.mpr (Or.inr ?_)
          show x ∈ p''.support.dropLast
          rw [show (Walk.cons step' p'').support.tail.dropLast = p''.support.dropLast
                from by simp [Walk.support_cons]] at hx
          exact hx
        obtain ⟨ρ_p', hρ_p'_dir, hρ_p'_int, hρ_p'_len⟩ := ih hp'_dir hp'_int
        -- ρ = σ.append ρ_p'
        refine ⟨σ.append ρ_p', ?_, ?_, ?_⟩
        · rw [Walk.marg_isDirected_append]
          exact ⟨hσ_dir, hρ_p'_dir⟩
        · -- ρ.InteriorIn (W₁ ∪ W₂)
          intro x hx
          -- ρ.support = σ.support.dropLast ++ ρ_p'.support
          -- ρ.support.tail.dropLast: needs careful list reasoning.
          -- We use the fact: ρ.support = σ.support.dropLast ++ ρ_p'.support.
          -- σ.length ≥ 1, so σ.support has length ≥ 2, so σ.support.dropLast is non-empty.
          -- σ.support.dropLast starts with a₀ (the first vertex of σ).
          -- So ρ.support.tail = σ.support.dropLast.tail ++ ρ_p'.support.
          -- Now whether the dropLast cuts into ρ_p'.support or into σ.support.dropLast.tail depends on ρ_p'.support.
          -- ρ_p'.support is non-empty (always). If ρ_p'.length ≥ 1, ρ_p'.support has length ≥ 2, so .dropLast non-empty.
          -- Then ρ.support.tail.dropLast = σ.support.dropLast.tail ++ ρ_p'.support.dropLast.
          -- Set-wise: ⊆ σ.support.tail.dropLast ∪ {m} ∪ ρ_p'.support.dropLast.tail ∪ {m}? Hmm.
          -- Let me just go through the cases.
          rw [Walk.marg_support_append] at hx
          -- hx : x ∈ (σ.support.dropLast ++ ρ_p'.support).tail.dropLast
          -- σ.support.dropLast is non-empty (σ.length ≥ 1 means σ.support has length ≥ 2).
          have hσ_dl_ne : σ.support.dropLast ≠ [] := by
            intro h
            have hlen : σ.support.dropLast.length = 0 := by rw [h]; rfl
            rw [List.length_dropLast, Walk.support_length] at hlen
            omega
          have hρ_p'_ne : ρ_p'.support ≠ [] := ρ_p'.marg_support_ne_nil
          -- (σ.support.dropLast ++ ρ_p'.support).tail = σ.support.dropLast.tail ++ ρ_p'.support.
          rw [Walk.list_tail_append_of_ne_nil _ hσ_dl_ne] at hx
          -- Now hx : x ∈ (σ.support.dropLast.tail ++ ρ_p'.support).dropLast
          -- ρ_p'.support is non-empty so dropLast strips its last.
          rw [List.dropLast_append_of_ne_nil hρ_p'_ne] at hx
          -- hx : x ∈ σ.support.dropLast.tail ++ ρ_p'.support.dropLast
          rcases List.mem_append.mp hx with hxL | hxR
          · -- x ∈ σ.support.dropLast.tail, i.e., x ∈ σ.support.tail.dropLast (set-wise).
            -- So x ∈ σ's interior ⊆ W₁.
            have hxσ : x ∈ σ.support.tail.dropLast := by
              rw [list_tail_dropLast]; exact hxL
            exact Or.inl (hσ_int_W₁ x hxσ)
          · -- x ∈ ρ_p'.support.dropLast.
            -- ρ_p'.support.dropLast = m :: ρ_p'.support.dropLast.tail (when length ≥ 1)
            --    OR ρ_p'.support.dropLast = [] when ρ_p'.length = 0.
            -- In either case, x ∈ ρ_p'.support.dropLast means x = m or x ∈ ρ_p'.support.dropLast.tail.
            -- (ρ_p'.support.dropLast.tail = ρ_p'.support.tail.dropLast = ρ_p's interior).
            -- ρ_p'.support starts with m (always: ρ_p' : Walk G m b₀, support.head = m).
            -- So ρ_p'.support = m :: ρ_p'.support.tail.
            -- ρ_p'.support.dropLast = (m :: ρ_p'.support.tail).dropLast.
            -- If ρ_p'.support.tail = []: ρ_p'.support.dropLast = (m :: []).dropLast = [].
            --   So x ∈ [] is impossible.
            -- If ρ_p'.support.tail ≠ []: ρ_p'.support.dropLast = m :: ρ_p'.support.tail.dropLast.
            --   So x = m or x ∈ ρ_p'.support.tail.dropLast (= ρ_p's interior).
            by_cases h_tail_empty : ρ_p'.support.tail = []
            · -- This means ρ_p'.support has length 1, so ρ_p' = nil. So ρ_p'.support.dropLast = [].
              have hsupp : ρ_p'.support = [m] := by
                rw [Walk.marg_support_cons_form, h_tail_empty]
              have hdrop : ρ_p'.support.dropLast = [] := by
                rw [hsupp]; simp
              rw [hdrop] at hxR
              simp at hxR
            · have hsupp_eq : ρ_p'.support = m :: ρ_p'.support.tail :=
                Walk.marg_support_cons_form ρ_p'
              rw [hsupp_eq, List.dropLast_cons_of_ne_nil h_tail_empty] at hxR
              rcases List.mem_cons.mp hxR with rfl | hxR'
              · exact Or.inr hm_in_W₂
              · -- hxR' : x ∈ ρ_p'.support.tail.dropLast
                exact hρ_p'_int x hxR'
        · -- length bound
          rw [Walk.length_cons, Walk.length_append]
          omega
    | backward _ => simp at hπ_dir
    | bidir _ => simp at hπ_dir

/-- For a walk `p : Walk G u v` with `1 ≤ p.length`, `u ∈ p.support.dropLast`. -/
private lemma start_in_support_dropLast {G : CDMG α} {u v : α}
    (p : Walk G u v) (h : 1 ≤ p.length) :
    u ∈ p.support.dropLast := by
  rw [Walk.marg_support_cons_form p]
  have h_tail_ne : p.support.tail ≠ [] := by
    intro he
    have : p.support.tail.length = 0 := by rw [he]; rfl
    rw [List.length_tail, Walk.support_length] at this
    omega
  rw [List.dropLast_cons_of_ne_nil h_tail_ne]
  exact List.mem_cons_self

/-- `(p.append q).support.dropLast = p.support.dropLast ++ q.support.dropLast`
when `q.support` is non-empty (always the case). Useful for relating
`Walk.append` to per-summand `dropLast` membership. -/
private lemma support_append_dropLast {G : CDMG α} {u v w : α}
    (p : Walk G u v) (q : Walk G v w) :
    (p.append q).support.dropLast =
      p.support.dropLast ++ q.support.dropLast := by
  rw [Walk.marg_support_append, List.dropLast_append_of_ne_nil q.marg_support_ne_nil]

/-- Shrink a directed walk in `G` to a directed walk in `G.marginalize W₁`,
with the strict invariant that the marginalized walk's interior is a
subset of the source walk's interior (as a set), and the marginalized
walk has length ≤ the source's length (so triviality is preserved in
both directions). Mirrors `exists_marg_directed_of_directed` but
additionally tracks `π.support.tail.dropLast ⊆ σ.support.tail.dropLast`
and `π.length ≤ σ.length`, which together with the length-pos
preservation are needed by claim_3_17's E-component proof to derive
`π.InteriorIn W₂` from `σ.InteriorIn (W₁ ∪ W₂)` and to obtain
`1 ≤ π.length`. -/
lemma shrink_directed_walk (G : CDMG α) (W₁ : Set α) :
    ∀ (n : ℕ) {a b : α} (σ : Walk G a b), σ.length ≤ n →
      σ.IsDirected →
      a ∈ G.J ∪ (G.V \ W₁) → b ∉ W₁ →
      ∃ π : Walk (G.marginalize W₁) a b, π.IsDirected ∧
        (∀ x ∈ π.support.tail.dropLast, x ∈ σ.support.tail.dropLast) ∧
        π.length ≤ σ.length ∧
        (1 ≤ σ.length → 1 ≤ π.length) := by
  intro n
  induction n with
  | zero =>
    intros a b σ hlen _ _ _
    cases σ with
    | nil _ =>
      refine ⟨Walk.nil _, by simp, ?_, by simp, by intro h; simp at h⟩
      intro x hx; simp at hx
    | @cons _ _ _ _ _ => rw [Walk.length_cons] at hlen; omega
  | succ k ih =>
    intros a b σ hlen hσ_dir ha hb
    cases σ with
    | nil _ =>
      refine ⟨Walk.nil _, by simp, ?_, by simp, by intro h; simp at h⟩
      intro x hx; simp at hx
    | @cons _ w _ step p' =>
      cases step with
      | forward h =>
        have hp'_dir : p'.IsDirected := by simpa using hσ_dir
        have hp'_len : p'.length ≤ k := by
          rw [Walk.length_cons] at hlen; omega
        have h_uw_E : (a, w) ∈ G.E := h
        have h_uw_prod : (a, w) ∈ (G.J ∪ G.V) ×ˢ G.V := G.E_subset h_uw_E
        have h_w_V : w ∈ G.V := (Set.mem_prod.mp h_uw_prod).2
        have hp'_ne : p'.support ≠ [] := p'.marg_support_ne_nil
        -- π.support.tail.dropLast = p'.support.dropLast (the "target" set).
        have hπ_int_eq : (Walk.cons (.forward h) p').support.tail.dropLast
            = p'.support.dropLast := by
          rw [Walk.support_cons, List.tail_cons]
        by_cases hw : w ∈ W₁
        · -- w ∈ W₁ branch.
          obtain ⟨z, p_skip, p_rest, hz, hp_skip_dir, hp_rest_dir,
                  hp_skip_int, hp'_eq⟩ :=
            Walk.exists_first_not_in_W W₁ p' hp'_dir hb
          have h_p_skip_pos : 1 ≤ p_skip.length := by
            cases p_skip with
            | nil _ => exact absurd hw hz
            | cons _ _ => simp
          have h_chunk_dir : (Walk.cons (.forward h) p_skip).IsDirected := by
            simpa using hp_skip_dir
          have h_chunk_pos : 1 ≤ (Walk.cons (.forward h) p_skip).length := by simp
          have h_chunk_int : (Walk.cons (.forward h) p_skip).InteriorIn W₁ := by
            intro x hx
            rw [show (Walk.cons (.forward h) p_skip).support.tail.dropLast
                  = p_skip.support.dropLast from by
                  rw [Walk.support_cons, List.tail_cons]] at hx
            exact hp_skip_int x hx
          have h_z_in : z ∈ G.V \ W₁ :=
            ⟨Walk.marg_end_in_V_of_isDirected_pos p_skip hp_skip_dir h_p_skip_pos, hz⟩
          have h_marg_edge : (a, z) ∈ (G.marginalize W₁).E := by
            rw [CDMG.mem_marginalize_E]
            exact ⟨ha, h_z_in,
                   Walk.cons (.forward h) p_skip,
                   h_chunk_dir, h_chunk_int, h_chunk_pos⟩
          have h_p_rest_len : p_rest.length ≤ k := by
            have : p'.length = p_skip.length + p_rest.length := by
              rw [hp'_eq, Walk.length_append]
            omega
          have h_z_in_marg : z ∈ G.J ∪ (G.V \ W₁) := Or.inr h_z_in
          obtain ⟨π_rest, hπ_rest_dir, hπ_rest_strict, hπ_rest_len, hπ_rest_pos⟩ :=
            ih p_rest h_p_rest_len hp_rest_dir h_z_in_marg hb
          have h_p_rest_ne : p_rest.support ≠ [] := p_rest.marg_support_ne_nil
          refine ⟨Walk.cons (.forward h_marg_edge) π_rest, ?_, ?_, ?_, ?_⟩
          · simpa using hπ_rest_dir
          · -- Strict tracking: π.support.tail.dropLast ⊆ σ.support.tail.dropLast = p'.support.dropLast.
            -- π.support.tail.dropLast = π_rest.support.dropLast.
            -- p'.support.dropLast = p_skip.support.dropLast ++ p_rest.support.dropLast.
            intro x hx
            rw [Walk.support_cons, List.tail_cons] at hx
            -- x ∈ π_rest.support.dropLast.
            -- Cases on whether π_rest is non-trivial.
            show x ∈ (Walk.cons (.forward h) p').support.tail.dropLast
            rw [hπ_int_eq, hp'_eq, support_append_dropLast]
            -- Goal: x ∈ p_skip.support.dropLast ++ p_rest.support.dropLast.
            -- Sub-goal: show x ∈ p_rest.support.dropLast.
            refine List.mem_append.mpr (Or.inr ?_)
            -- π_rest.support.dropLast ⊆ p_rest.support.dropLast.
            -- π_rest.support = z :: π_rest.support.tail. π_rest.support.dropLast = z :: π_rest.support.tail.dropLast OR [].
            -- Either way, x = z or x ∈ π_rest.support.tail.dropLast.
            by_cases h_π_rest_len : 1 ≤ π_rest.length
            · -- π_rest non-trivial. π_rest.support.dropLast = z :: π_rest.support.tail.dropLast.
              have h_π_rest_tail_ne : π_rest.support.tail ≠ [] := by
                intro he
                have : π_rest.support.tail.length = 0 := by rw [he]; rfl
                rw [List.length_tail, Walk.support_length] at this
                omega
              rw [Walk.marg_support_cons_form π_rest,
                  List.dropLast_cons_of_ne_nil h_π_rest_tail_ne] at hx
              rcases List.mem_cons.mp hx with rfl | hxr
              · -- x = z. Need z ∈ p_rest.support.dropLast.
                -- π_rest non-trivial AND hπ_rest_len : π_rest.length ≤ p_rest.length
                -- → p_rest.length ≥ 1 → z is in p_rest.support.dropLast (head of dropLast).
                have h_p_rest_pos : 1 ≤ p_rest.length :=
                  le_trans h_π_rest_len hπ_rest_len
                exact start_in_support_dropLast p_rest h_p_rest_pos
              · -- x ∈ π_rest.support.tail.dropLast. By IH (strict tracking).
                have h_in_p_rest_int : x ∈ p_rest.support.tail.dropLast :=
                  hπ_rest_strict x hxr
                -- p_rest.support.tail.dropLast ⊆ p_rest.support.dropLast (set-wise).
                rw [list_tail_dropLast] at h_in_p_rest_int
                exact List.mem_of_mem_tail h_in_p_rest_int
            · -- π_rest trivial. π_rest.support.dropLast = [].
              push_neg at h_π_rest_len
              cases π_rest with
              | nil _ => simp at hx
              | cons _ _ => simp [Walk.length_cons] at h_π_rest_len
          · -- Length bound: π.length ≤ σ.length.
            -- π.length = 1 + π_rest.length ≤ 1 + p_rest.length ≤ 1 + p'.length = σ.length.
            rw [Walk.length_cons, Walk.length_cons]
            have h_p'_len_eq : p'.length = p_skip.length + p_rest.length := by
              rw [hp'_eq, Walk.length_append]
            omega
          · intro _; simp [Walk.length_cons]
        · -- w ∉ W₁ branch.
          have h_w_in : w ∈ G.V \ W₁ := ⟨h_w_V, hw⟩
          have h_marg_edge : (a, w) ∈ (G.marginalize W₁).E := by
            rw [CDMG.mem_marginalize_E]
            refine ⟨ha, h_w_in, Walk.cons (.forward h) (Walk.nil w),
                    ?_, Walk.marg_single_edge_interior W₁ h, ?_⟩
            · simp
            · simp
          have h_w_in_marg : w ∈ G.J ∪ (G.V \ W₁) := Or.inr h_w_in
          obtain ⟨π_rest, hπ_rest_dir, hπ_rest_strict, hπ_rest_len, hπ_rest_pos⟩ :=
            ih p' hp'_len hp'_dir h_w_in_marg hb
          refine ⟨Walk.cons (.forward h_marg_edge) π_rest, ?_, ?_, ?_, ?_⟩
          · simpa using hπ_rest_dir
          · -- Strict tracking: π.support.tail.dropLast ⊆ p'.support.dropLast.
            intro x hx
            rw [Walk.support_cons, List.tail_cons] at hx
            show x ∈ (Walk.cons (.forward h) p').support.tail.dropLast
            rw [hπ_int_eq]
            -- x ∈ π_rest.support.dropLast.
            by_cases h_π_rest_len_pos : 1 ≤ π_rest.length
            · have h_π_rest_tail_ne : π_rest.support.tail ≠ [] := by
                intro he
                have : π_rest.support.tail.length = 0 := by rw [he]; rfl
                rw [List.length_tail, Walk.support_length] at this
                omega
              rw [Walk.marg_support_cons_form π_rest,
                  List.dropLast_cons_of_ne_nil h_π_rest_tail_ne] at hx
              rcases List.mem_cons.mp hx with rfl | hxr
              · -- x = w. Need w ∈ p'.support.dropLast. p'.length ≥ 1 by length bound.
                have h_p'_pos : 1 ≤ p'.length :=
                  le_trans h_π_rest_len_pos hπ_rest_len
                exact start_in_support_dropLast p' h_p'_pos
              · -- x ∈ π_rest.support.tail.dropLast → x ∈ p'.support.tail.dropLast ⊆ p'.support.dropLast.
                have h_in_p'_int : x ∈ p'.support.tail.dropLast :=
                  hπ_rest_strict x hxr
                rw [list_tail_dropLast] at h_in_p'_int
                exact List.mem_of_mem_tail h_in_p'_int
            · push_neg at h_π_rest_len_pos
              cases π_rest with
              | nil _ => simp at hx
              | cons _ _ => simp [Walk.length_cons] at h_π_rest_len_pos
          · -- Length bound: π.length ≤ σ.length.
            rw [Walk.length_cons, Walk.length_cons]
            omega
          · intro _; simp [Walk.length_cons]
      | backward _ => simp at hσ_dir
      | bidir _ => simp at hσ_dir

/-- For a directed walk in `G` of length ≥ 1, every vertex of
`support.tail` (i.e., every non-head vertex) lies in `G.V`. The
support's tail consists of targets of forward steps; each target is
in `G.V` by `G.E_subset`. -/
private lemma support_tail_in_V_of_isDirected {G : CDMG α} {a b : α} :
    ∀ (π : Walk G a b), π.IsDirected → ∀ x ∈ π.support.tail, x ∈ G.V := by
  intro π
  induction π with
  | nil v =>
    intro _ x hx
    simp at hx
  | @cons a₀ w _ step p' ih =>
    intro hπ x hx
    cases step with
    | forward h =>
      have hp'_dir : p'.IsDirected := by simpa using hπ
      rw [Walk.support_cons, List.tail_cons, p'.marg_support_cons_form] at hx
      rcases List.mem_cons.mp hx with hxw | hxr
      · -- hxw : x = w. h : a₀ ⟶[G] w gives w ∈ G.V via E_subset.
        rw [hxw]
        exact (Set.mem_prod.mp (G.E_subset (h : (a₀, w) ∈ G.E))).2
      · exact ih hp'_dir x hxr
    | backward _ => simp at hπ
    | bidir _ => simp at hπ

/-- Directed-walk iff (E component): under the right endpoint
constraints, the existence of a directed walk in `G.marginalize W₁`
with interior in `W₂` is equivalent to the existence of a directed
walk in `G` with interior in `W₁ ∪ W₂`. Both directions go through
the lift / shrink helpers above; the `InteriorIn W₂` extraction in
the shrink direction combines the strict-interior tracking with the
fact that vertices in `(G.marginalize W₁)` walks avoid `W₁`. -/
lemma directed_walk_iff (G : CDMG α) (W₁ W₂ : Set α)
    {a b : α} (ha : a ∈ G.J ∪ (G.V \ (W₁ ∪ W₂)))
    (hb : b ∈ G.V \ (W₁ ∪ W₂)) :
    (∃ π : Walk (G.marginalize W₁) a b,
        π.IsDirected ∧ π.InteriorIn W₂ ∧ 1 ≤ π.length)
    ↔ (∃ σ : Walk G a b,
        σ.IsDirected ∧ σ.InteriorIn (W₁ ∪ W₂) ∧ 1 ≤ σ.length) := by
  constructor
  · rintro ⟨π, hπ_dir, hπ_int, hπ_pos⟩
    obtain ⟨σ, hσ_dir, hσ_int, hσ_len⟩ :=
      lift_directed_walk G W₁ W₂ π hπ_dir hπ_int
    exact ⟨σ, hσ_dir, hσ_int, le_trans hπ_pos hσ_len⟩
  · rintro ⟨σ, hσ_dir, hσ_int, hσ_pos⟩
    have ha' : a ∈ G.J ∪ (G.V \ W₁) := by
      rcases ha with hJ | hV
      · exact Or.inl hJ
      · exact Or.inr ⟨hV.1, fun h => hV.2 (Or.inl h)⟩
    have hb' : b ∉ W₁ := fun h => hb.2 (Or.inl h)
    obtain ⟨π, hπ_dir, hπ_strict, _, hπ_pos⟩ :=
      shrink_directed_walk G W₁ σ.length σ le_rfl hσ_dir ha' hb'
    refine ⟨π, hπ_dir, ?_, hπ_pos hσ_pos⟩
    intro x hx
    -- x ∈ π.support.tail.dropLast → x ∈ σ.support.tail.dropLast → x ∈ W₁ ∪ W₂.
    have hx_σ : x ∈ σ.support.tail.dropLast := hπ_strict x hx
    have hx_in : x ∈ W₁ ∪ W₂ := hσ_int x hx_σ
    -- x ∉ W₁ (interior vertex of π : Walk (G.marg W₁) ...).
    have hx_not_W₁ : x ∉ W₁ := by
      have hx_tail : x ∈ π.support.tail := List.dropLast_subset _ hx
      have hx_V : x ∈ (G.marginalize W₁).V :=
        support_tail_in_V_of_isDirected π hπ_dir x hx_tail
      rw [CDMG.marginalize_V] at hx_V
      exact hx_V.2
    rcases hx_in with hW₁ | hW₂
    · exact absurd hW₁ hx_not_W₁
    · exact hW₂

/-- Directed-walk iff for the L-component "no directed walk" clauses
(no length constraint). Given distinct endpoints, the trivial walk
is unavailable, so any witness has length ≥ 1; this reduces to
`directed_walk_iff` modulo the `(... ∧ 1 ≤ length) ↔ (...)` reshuffle. -/
lemma directed_walk_iff_no_length (G : CDMG α) (W₁ W₂ : Set α)
    {a b : α} (ha : a ∈ G.V \ (W₁ ∪ W₂))
    (hb : b ∈ G.V \ (W₁ ∪ W₂)) (hab : a ≠ b) :
    (∃ π : Walk (G.marginalize W₁) a b, π.IsDirected ∧ π.InteriorIn W₂)
    ↔ (∃ σ : Walk G a b, σ.IsDirected ∧ σ.InteriorIn (W₁ ∪ W₂)) := by
  have h_aux : ∀ {γ : CDMG α} {a' b' : α} (π : Walk γ a' b'),
      a' ≠ b' → 1 ≤ π.length := by
    intro γ a' b' π hne
    cases π with
    | nil _ => exact absurd rfl hne
    | cons _ _ => simp
  have ha' : a ∈ G.J ∪ (G.V \ (W₁ ∪ W₂)) := Or.inr ha
  constructor
  · rintro ⟨π, hπ_dir, hπ_int⟩
    obtain ⟨σ, hσ_dir, hσ_int, _⟩ :=
      (directed_walk_iff G W₁ W₂ ha' hb).mp ⟨π, hπ_dir, hπ_int, h_aux π hab⟩
    exact ⟨σ, hσ_dir, hσ_int⟩
  · rintro ⟨σ, hσ_dir, hσ_int⟩
    obtain ⟨π, hπ_dir, hπ_int, _⟩ :=
      (directed_walk_iff G W₁ W₂ ha' hb).mpr ⟨σ, hσ_dir, hσ_int, h_aux σ hab⟩
    exact ⟨π, hπ_dir, hπ_int⟩

/-! ## Bifurcation translators for the L component

These helpers handle the bifurcation existential of the L-component
iff via a two-step reduction:

1. `marginalize_bifurcation_iff` (claim_3_16, public, no interior
   tracking) gives the bifurcation existence iff between `G` and
   `G.marginalize W₁`.
2. The interior tracking follows from the IsBifurcation property
   (endpoints don't appear in the interior) combined with a support
   inclusion that we derive separately.

For lift (marg → G): we explicitly construct `σ` using the marg
witness and our directed translators, with `σ`'s support contained
in `π'.support ∪ W₁` (and therefore `σ`'s interior, which excludes
`a, b`, lies in `(π'.support \ {a,b}) ∪ W₁ ⊆ W₂ ∪ W₁`).

For shrink (G → marg): symmetric construction.

In either direction, the hinge case-split (`.backward` vs `.bidir`)
is the structurally hardest piece. The `.bidir` case uses
`mem_marginalize_L` (lift) or constructs a new `L^{∼W₁}` edge
(shrink) for the hinge.

**Implementation note (deferred to follow-up dispatch).** The full
bifurcation translators with strict interior tracking are large
(estimated ~1000 LoC per direction). The current implementation
defers them to the manager's follow-up dispatch. The structure of
`bifurcation_walk_iff_no_length` is correct: it reduces to two
helper lemmas, each of which has a clear specification and would
mirror the existing `Walk.marginalize_bif_backward` /
`Walk.marginalize_bif_forward` proofs (`MarginalizationPreserves.lean`
lines 919 / 2285) with an additional support-tracking conjunct
added throughout. -/

/-- Marg-side bifurcation lifts to a G-side bifurcation with interior
in `W₁ ∪ W₂`. Proof: invoke
`Walk.marginalize_bif_backward` (modified to track support inclusion
in `π.support ∪ W₁`); then derive `σ.InteriorIn (W₁ ∪ W₂)` via the
following observation: `σ`'s interior consists of vertices `x` that
are in `σ.support` but distinct from the endpoints `a, b` (by
`σ.IsBifurcation`'s `a ∉ tail`, `b ∉ dropLast` clauses). By the
support tracking, `x ∈ π.support ∨ x ∈ W₁`. If `x ∈ W₁`, done. If
`x ∈ π.support` and `x ≠ a, b`, then `x` is in `π`'s interior, hence
in `W₂` (by `hint_π`). Either way `x ∈ W₁ ∪ W₂`. -/
lemma lift_bifurcation_walk (G : CDMG α) (W₁ W₂ : Set α)
    (_hd : Disjoint W₁ W₂)
    {a b : α} (ha : a ∈ G.V \ (W₁ ∪ W₂)) (hb : b ∈ G.V \ (W₁ ∪ W₂))
    (π : Walk (G.marginalize W₁) a b)
    (hb_π : π.IsBifurcation) (hint_π : π.InteriorIn W₂) :
    (∃ σ : Walk G a b, σ.IsBifurcation ∧ σ.InteriorIn (W₁ ∪ W₂)) ∨
    (∃ σ : Walk G b a, σ.IsBifurcation ∧ σ.InteriorIn (W₁ ∪ W₂)) := by
  -- Membership facts: a, b ∈ G follow from ha, hb (ha.1 : a ∈ G.V, similarly).
  have ha_in_G : a ∈ G := Or.inr ha.1
  have hb_in_G : b ∈ G := Or.inr hb.1
  have ha_W₁ : a ∉ W₁ := fun h => ha.2 (Or.inl h)
  have hb_W₁ : b ∉ W₁ := fun h => hb.2 (Or.inl h)
  have ha_W₂ : a ∉ W₂ := fun h => ha.2 (Or.inr h)
  have hb_W₂ : b ∉ W₂ := fun h => hb.2 (Or.inr h)
  -- Apply marginalize_bif_backward (modified to track support in π.support ∪ W₁).
  rcases Walk.marginalize_bif_backward (W := W₁) ha_in_G hb_in_G ha_W₁ hb_W₁ π hb_π with
    ⟨σ, hb_σ, hsupp⟩ | ⟨σ, hb_σ, hsupp⟩
  · -- σ : Walk G a b case.
    refine Or.inl ⟨σ, hb_σ, ?_⟩
    -- Show σ.InteriorIn (W₁ ∪ W₂).
    intro x hx
    -- x ∈ σ.support.tail.dropLast. Therefore x ∈ σ.support, x ≠ a, x ≠ b.
    have hx_supp : x ∈ σ.support :=
      List.mem_of_mem_tail (List.dropLast_subset _ hx)
    have hx_neq_a : x ≠ a := by
      intro h_eq
      have hx_tail : x ∈ σ.support.tail := List.dropLast_subset _ hx
      rw [h_eq] at hx_tail
      exact hb_σ.2.1 hx_tail
    have hx_neq_b : x ≠ b := by
      intro h_eq
      have hx_dl_tail : x ∈ σ.support.dropLast.tail := by
        rw [← list_tail_dropLast]; exact hx
      have hx_drop : x ∈ σ.support.dropLast := List.mem_of_mem_tail hx_dl_tail
      rw [h_eq] at hx_drop
      exact hb_σ.2.2.1 hx_drop
    -- Use support tracking: x ∈ π.support ∨ x ∈ W₁.
    rcases hsupp x hx_supp with hxπ | hxW₁
    · -- x ∈ π.support. Combined with x ≠ a, b, x is in π's interior, hence in W₂.
      have hx_int_π : x ∈ π.support.tail.dropLast := by
        rw [Walk.marg_support_eq_dropLast_append_last π] at hxπ
        rcases List.mem_append.mp hxπ with h_drop | h_end
        · have h_π_tail_ne : π.support.tail ≠ [] := by
            intro h
            have : π.support.tail.length = 0 := by rw [h]; rfl
            rw [List.length_tail, Walk.support_length] at this
            have h_π_pos : 1 ≤ π.length := Walk.length_pos_of_isBifurcation hb_π
            omega
          rw [Walk.marg_support_cons_form π,
              List.dropLast_cons_of_ne_nil h_π_tail_ne] at h_drop
          rcases List.mem_cons.mp h_drop with h_eq | h_int
          · exact absurd h_eq hx_neq_a
          · exact h_int
        · simp at h_end; exact absurd h_end hx_neq_b
      exact Or.inr (hint_π x hx_int_π)
    · exact Or.inl hxW₁
  · -- σ : Walk G b a case.
    refine Or.inr ⟨σ, hb_σ, ?_⟩
    intro x hx
    have hx_supp : x ∈ σ.support :=
      List.mem_of_mem_tail (List.dropLast_subset _ hx)
    have hx_neq_b : x ≠ b := by
      intro h_eq
      have hx_tail : x ∈ σ.support.tail := List.dropLast_subset _ hx
      rw [h_eq] at hx_tail
      exact hb_σ.2.1 hx_tail
    have hx_neq_a : x ≠ a := by
      intro h_eq
      have hx_dl_tail : x ∈ σ.support.dropLast.tail := by
        rw [← list_tail_dropLast]; exact hx
      have hx_drop : x ∈ σ.support.dropLast := List.mem_of_mem_tail hx_dl_tail
      rw [h_eq] at hx_drop
      exact hb_σ.2.2.1 hx_drop
    rcases hsupp x hx_supp with hxπ | hxW₁
    · have hx_int_π : x ∈ π.support.tail.dropLast := by
        rw [Walk.marg_support_eq_dropLast_append_last π] at hxπ
        rcases List.mem_append.mp hxπ with h_drop | h_end
        · have h_π_tail_ne : π.support.tail ≠ [] := by
            intro h
            have : π.support.tail.length = 0 := by rw [h]; rfl
            rw [List.length_tail, Walk.support_length] at this
            have h_π_pos : 1 ≤ π.length := Walk.length_pos_of_isBifurcation hb_π
            omega
          rw [Walk.marg_support_cons_form π,
              List.dropLast_cons_of_ne_nil h_π_tail_ne] at h_drop
          rcases List.mem_cons.mp h_drop with h_eq | h_int
          · exact absurd h_eq hx_neq_a
          · exact h_int
        · simp at h_end; exact absurd h_end hx_neq_b
      exact Or.inr (hint_π x hx_int_π)
    · exact Or.inl hxW₁

/-- G-side bifurcation shrinks to a marg-side bifurcation with
interior in `W₂`. Proof: invoke `Walk.marginalize_bif_forward`
(modified to track support inclusion in `σ.support` and
W-avoidance); derive `π.InteriorIn W₂` via: for any interior vertex
`x` of `π`, `x ≠ a, x ≠ b` (by `π.IsBifurcation`), `x ∈ σ.support`
(support tracking) → `x ∈ σ.support.tail.dropLast` (set-wise
position analysis) → `x ∈ W₁ ∪ W₂` (by `hint_σ`); combined with
`x ∉ W₁` (W-avoidance tracking) gives `x ∈ W₂`. -/
lemma shrink_bifurcation_walk (G : CDMG α) (W₁ W₂ : Set α)
    (_hd : Disjoint W₁ W₂)
    {a b : α} (ha : a ∈ G.V \ (W₁ ∪ W₂)) (hb : b ∈ G.V \ (W₁ ∪ W₂))
    (σ : Walk G a b)
    (hb_σ : σ.IsBifurcation) (hint_σ : σ.InteriorIn (W₁ ∪ W₂)) :
    (∃ π : Walk (G.marginalize W₁) a b,
        π.IsBifurcation ∧ π.InteriorIn W₂) ∨
    (∃ π : Walk (G.marginalize W₁) b a,
        π.IsBifurcation ∧ π.InteriorIn W₂) := by
  have ha_in_G : a ∈ G := Or.inr ha.1
  have hb_in_G : b ∈ G := Or.inr hb.1
  have ha_W₁ : a ∉ W₁ := fun h => ha.2 (Or.inl h)
  have hb_W₁ : b ∉ W₁ := fun h => hb.2 (Or.inl h)
  -- Apply marginalize_bif_forward (modified to track support ⊆ σ.support, ∉ W₁).
  rcases Walk.marginalize_bif_forward (W := W₁) ha_in_G hb_in_G ha_W₁ hb_W₁ σ hb_σ with
    ⟨π, hb_π, hsupp⟩ | ⟨π, hb_π, hsupp⟩
  · -- π : Walk (G.marg W₁) a b case.
    refine Or.inl ⟨π, hb_π, ?_⟩
    intro x hx
    -- x ∈ π.support.tail.dropLast. So x ∈ π.support, x ≠ a, x ≠ b.
    have hx_supp : x ∈ π.support :=
      List.mem_of_mem_tail (List.dropLast_subset _ hx)
    have hx_neq_a : x ≠ a := by
      intro h_eq
      have hx_tail : x ∈ π.support.tail := List.dropLast_subset _ hx
      rw [h_eq] at hx_tail
      exact hb_π.2.1 hx_tail
    have hx_neq_b : x ≠ b := by
      intro h_eq
      have hx_dl_tail : x ∈ π.support.dropLast.tail := by
        rw [← list_tail_dropLast]; exact hx
      have hx_drop : x ∈ π.support.dropLast := List.mem_of_mem_tail hx_dl_tail
      rw [h_eq] at hx_drop
      exact hb_π.2.2.1 hx_drop
    -- From support tracking: x ∈ σ.support ∧ x ∉ W₁.
    have ⟨hx_σ, hx_notW⟩ := hsupp x hx_supp
    -- x ∈ σ.support, x ≠ a, x ≠ b → x ∈ σ.support.tail.dropLast (interior of σ).
    have hx_int_σ : x ∈ σ.support.tail.dropLast := by
      rw [Walk.marg_support_eq_dropLast_append_last σ] at hx_σ
      rcases List.mem_append.mp hx_σ with h_drop | h_end
      · have h_σ_tail_ne : σ.support.tail ≠ [] := by
          intro h
          have : σ.support.tail.length = 0 := by rw [h]; rfl
          rw [List.length_tail, Walk.support_length] at this
          have h_σ_pos : 1 ≤ σ.length := Walk.length_pos_of_isBifurcation hb_σ
          omega
        rw [Walk.marg_support_cons_form σ,
            List.dropLast_cons_of_ne_nil h_σ_tail_ne] at h_drop
        rcases List.mem_cons.mp h_drop with h_eq | h_int
        · exact absurd h_eq hx_neq_a
        · exact h_int
      · simp at h_end; exact absurd h_end hx_neq_b
    -- x ∈ W₁ ∪ W₂ (by σ.InteriorIn), x ∉ W₁ → x ∈ W₂.
    rcases hint_σ x hx_int_σ with hW₁ | hW₂
    · exact absurd hW₁ hx_notW
    · exact hW₂
  · -- π : Walk (G.marg W₁) b a case.
    refine Or.inr ⟨π, hb_π, ?_⟩
    intro x hx
    have hx_supp : x ∈ π.support :=
      List.mem_of_mem_tail (List.dropLast_subset _ hx)
    have hx_neq_b : x ≠ b := by
      intro h_eq
      have hx_tail : x ∈ π.support.tail := List.dropLast_subset _ hx
      rw [h_eq] at hx_tail
      exact hb_π.2.1 hx_tail
    have hx_neq_a : x ≠ a := by
      intro h_eq
      have hx_dl_tail : x ∈ π.support.dropLast.tail := by
        rw [← list_tail_dropLast]; exact hx
      have hx_drop : x ∈ π.support.dropLast := List.mem_of_mem_tail hx_dl_tail
      rw [h_eq] at hx_drop
      exact hb_π.2.2.1 hx_drop
    have ⟨hx_σ, hx_notW⟩ := hsupp x hx_supp
    have hx_int_σ : x ∈ σ.support.tail.dropLast := by
      rw [Walk.marg_support_eq_dropLast_append_last σ] at hx_σ
      rcases List.mem_append.mp hx_σ with h_drop | h_end
      · have h_σ_tail_ne : σ.support.tail ≠ [] := by
          intro h
          have : σ.support.tail.length = 0 := by rw [h]; rfl
          rw [List.length_tail, Walk.support_length] at this
          have h_σ_pos : 1 ≤ σ.length := Walk.length_pos_of_isBifurcation hb_σ
          omega
        rw [Walk.marg_support_cons_form σ,
            List.dropLast_cons_of_ne_nil h_σ_tail_ne] at h_drop
        rcases List.mem_cons.mp h_drop with h_eq | h_int
        · exact absurd h_eq hx_neq_a
        · exact h_int
      · simp at h_end; exact absurd h_end hx_neq_b
    rcases hint_σ x hx_int_σ with hW₁ | hW₂
    · exact absurd hW₁ hx_notW
    · exact hW₂

/-- Bifurcation iff (L component): under the right endpoint constraints
and disjointness of `W₁, W₂`, the existence of a bifurcation in
`G.marginalize W₁` with interior in `W₂` (in either walk direction)
is equivalent to the existence of a bifurcation in `G` with interior
in `W₁ ∪ W₂` (in either walk direction). -/
lemma bifurcation_walk_iff_no_length (G : CDMG α)
    (W₁ W₂ : Set α) (hd : Disjoint W₁ W₂) {a b : α}
    (ha : a ∈ G.V \ (W₁ ∪ W₂)) (hb : b ∈ G.V \ (W₁ ∪ W₂))
    (hab : a ≠ b) :
    ((∃ π : Walk (G.marginalize W₁) a b, π.IsBifurcation ∧ π.InteriorIn W₂) ∨
     (∃ π : Walk (G.marginalize W₁) b a, π.IsBifurcation ∧ π.InteriorIn W₂))
    ↔
    ((∃ σ : Walk G a b, σ.IsBifurcation ∧ σ.InteriorIn (W₁ ∪ W₂)) ∨
     (∃ σ : Walk G b a, σ.IsBifurcation ∧ σ.InteriorIn (W₁ ∪ W₂))) := by
  constructor
  · -- (⇒): marg → G. Apply lift_bifurcation_walk on each disjunct.
    rintro (⟨π, hb_π, hint_π⟩ | ⟨π, hb_π, hint_π⟩)
    · exact lift_bifurcation_walk G W₁ W₂ hd ha hb π hb_π hint_π
    · exact (lift_bifurcation_walk G W₁ W₂ hd hb ha π hb_π hint_π).symm
  · -- (⇐): G → marg. Apply shrink_bifurcation_walk on each disjunct.
    rintro (⟨σ, hb_σ, hint_σ⟩ | ⟨σ, hb_σ, hint_σ⟩)
    · exact shrink_bifurcation_walk G W₁ W₂ hd ha hb σ hb_σ hint_σ
    · exact (shrink_bifurcation_walk G W₁ W₂ hd hb ha σ hb_σ hint_σ).symm

-- claim_3_17 (fusion)
-- title: MarginalizationsCommute -- fusion lemma
--
-- Iterating two *disjoint* marginalizations collapses to a single
-- marginalization on the union:
-- `(G^{\sm W₁})^{\sm W₂} = G^{\sm (W₁ ∪ W₂)}`. This is the central
-- content of the LN's triple equality; the commute form (below) is
-- an immediate corollary via `Set.union_comm`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 995 -- 1005):

\begin{claimmark}
\begin{Lem}[Marginalizations commute]\label{marginalizations-commute}
      Let $G=(J,V,E,L)$ be a CDMG and $W_1, W_2 \ins V$ two disjoint subsets of output nodes.
      Then we have:
      \[ \lp G^{\sm W_1} \rp^{\sm W_2} = \lp G^{\sm W_2} \rp^{\sm W_1} =  G^{\sm (W_1 \cup W_2)}. \]
\end{Lem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **No `W₁, W₂ ⊆ G.V` precondition -- this is a faithful
--   strengthening of the LN, not a divergence.** Mirrors the
--   no-precondition design of `marginalize`
--   (`Section3_2/Marginalization.lean` lines 258 -- 286, which cites
--   claim_3_17 by name as one of the two load-bearing motivating
--   tests that justified dropping the precondition; the verbatim
--   text there names "Iteration works unconditionally (claim_3_17)"
--   as its first reason). The LN's `W_i ⊆ V` clause is informal
--   scaffolding so that `G^{\sm W_i}` reads as "remove output nodes
--   from `G`" in prose; it is not load-bearing in the LN proof.
--   The equality holds component-wise on `(J, V, E, L)` for
--   arbitrary `W₁, W₂ : Set α` because vertices in `W \ G.V` are
--   never on any `Walk G _ _` (interior vertices of a walk of length
--   ≥ 1 force themselves into `G.J ∪ G.V` via `G.E_subset` /
--   `G.L_subset`, so `π.InteriorIn W` only sees the part of `W`
--   inside `G.J ∪ G.V`), hence none of `marginalize_J / V / E / L`
--   are affected by the "spurious" part of `W` outside `G.V`. The
--   outer call in `(G.marginalize W₁).marginalize W₂` would
--   otherwise need a hypothesis `W₂ ⊆ (G.marginalize W₁).V =
--   G.V \ W₁`; the LN proof tacitly assumes `W₂ ⊆ V` (the *base*
--   graph's output set) for *both* marginalization steps without
--   re-justifying it for the inner marginalization, which is
--   exactly the informal usage the no-precondition encoding
--   captures faithfully. Same choice `HardInterventionsCommute.lean`
--   makes for the analogous `hardInterventionOn_*` theorems, for
--   the same iteration-unblocking reason.
--
-- * **Disjointness `Disjoint W₁ W₂` is kept -- load-bearing for
--   both the LN statement and the LN walk-concatenation proof.**
--   The LN states `W_1, W_2` "disjoint" and its proof
--   (`graphs.tex` lines 1007 -- 1117) load-bears on it: a walk
--   through `W₁ ∪ W₂` is split, via disjointness, along
--   intermediate-vertex membership into the contribution from each
--   marginalization step (without disjointness the splitting is
--   ambiguous and the inductive identification of "walks with
--   interior in W₁ ∪ W₂" with the two-step composition breaks).
--   Under our fusion + commute split the *same* hypothesis `h`
--   feeds both: the fusion lemma uses `h` directly, and the
--   commute corollary feeds `h.symm` into the swapped-order
--   fusion call (`marginalize_marginalize G h.symm`). Using
--   mathlib's `Disjoint` from `Mathlib.Order.Disjoint`
--   (transitively imported via `Section3_2/Marginalization.lean`)
--   so that the symmetry call is just `h.symm`, with no manual
--   set-theoretic massaging.
--
-- * **Split the LN's chained equality into fusion + commute,
--   mirroring `HardInterventionsCommute.lean` precedent.** The LN
--   bundles `(G^{\sm W₁})^{\sm W₂} = (G^{\sm W₂})^{\sm W₁} =
--   G^{\sm (W₁ ∪ W₂)}` into one displayed equation, but the natural
--   Lean shape is two named lemmas: a *fusion* rewrite rule (this
--   theorem) and a *commute* corollary (`marginalize_comm` below).
--   This is the direct analogue of
--   `hardInterventionOn_hardInterventionOn` +
--   `hardInterventionOn_comm` for claim_3_11 (see
--   `HardInterventionsCommute.lean` lines 162 -- 184 and
--   286 -- 303 for the same split rationale, made there for the
--   same reasons). Fusion is what every downstream consumer
--   actually rewrites with -- the `graphs.tex` 984 / 1426
--   induction-on-`#W` arguments collapse iterated marginalizations
--   back to a single one via fusion, never via a chained-equality
--   pair; chapter 4+ latent-projection / hidden-variable
--   compression, do-calculus iteration, FCI / ICDF discovery, and
--   iSCM intervention iteration all reach for the fusion form.
--   The commute form is the rare-use corollary, needed only when
--   the downstream argument has fixed which `W_i` comes "first" and
--   wants to reorder without collapsing. An alternative we
--   considered and rejected was packaging the chained equality as
--   a single `⟨_, _⟩`-conjunction (or a triple equality via
--   `Eq.trans`); both would force every consumer to apply `.1` /
--   `.2` (or `.symm.trans`) at the call site, an extra projection
--   step that obscures the rewrite. Two separately-named lemmas is
--   the natural Mathlib shape (cf. `image_image` + `Function.comp`
--   style names; `mul_comm` / `add_comm` for the commute form).
/-- claim_3_17 fusion lemma: iterating two disjoint marginalizations
equals a single marginalization on the union,
`(G.marginalize W₁).marginalize W₂ = G.marginalize (W₁ ∪ W₂)`.
Mirrors the first half of the chained equality in the `\Lem` at
`lecture-notes/lecture_notes/graphs.tex` line 997
(`marginalizations-commute`). -/
theorem marginalize_marginalize (G : CDMG α) {W₁ W₂ : Set α}
    (h : Disjoint W₁ W₂) :
    (G.marginalize W₁).marginalize W₂ = G.marginalize (W₁ ∪ W₂) := by
  refine mk_eq_of_data ?_ ?_ ?_ ?_
  · -- J: both `(G.marg W₁).marg W₂.J = G.J` and `G.marg (W₁ ∪ W₂).J = G.J`.
    show ((G.marginalize W₁).marginalize W₂).J = (G.marginalize (W₁ ∪ W₂)).J
    rfl
  · -- V: `(G.V \ W₁) \ W₂ = G.V \ (W₁ ∪ W₂)` via `Set.diff_diff`.
    show ((G.marginalize W₁).marginalize W₂).V = (G.marginalize (W₁ ∪ W₂)).V
    simp only [CDMG.marginalize_V, Set.diff_diff]
  · -- E: walk-existential iff via `directed_walk_iff`.
    ext p
    simp only [CDMG.mem_marginalize_E, CDMG.marginalize_J, CDMG.marginalize_V,
               Set.diff_diff]
    constructor
    · rintro ⟨hp1, hp2, hex⟩
      exact ⟨hp1, hp2, (directed_walk_iff G W₁ W₂ hp1 hp2).mp hex⟩
    · rintro ⟨hp1, hp2, hex⟩
      exact ⟨hp1, hp2, (directed_walk_iff G W₁ W₂ hp1 hp2).mpr hex⟩
  · -- L: bifurcation existential + directed-walk negation clauses.
    -- Structure: unfold both sides via `mem_marginalize_L`; endpoint conditions
    -- match via `Set.diff_diff`; `p.1 ≠ p.2` is shared; the two
    -- `¬ ∃ directed walk` clauses follow from `directed_walk_iff_no_length`;
    -- the bifurcation `∨` requires interior-tracking bifurcation translators
    -- (analogue of `lift_directed_walk` / `shrink_directed_walk` for
    -- bifurcations) -- isolated below in `bifurcation_walk_iff_no_length`.
    ext p
    simp only [CDMG.mem_marginalize_L, CDMG.marginalize_V, Set.diff_diff]
    constructor
    · rintro ⟨hp1, hp2, hne, hnd12, hnd21, hbif⟩
      refine ⟨hp1, hp2, hne, ?_, ?_, ?_⟩
      · -- ¬ ∃ directed walk a → b in G: iff version, contradict via LHS.
        intro ⟨σ, hσ_dir, hσ_int⟩
        exact hnd12 ((directed_walk_iff_no_length G W₁ W₂ hp1 hp2 hne).mpr
                        ⟨σ, hσ_dir, hσ_int⟩)
      · -- ¬ ∃ directed walk b → a in G: similar with swapped endpoints.
        intro ⟨σ, hσ_dir, hσ_int⟩
        exact hnd21 ((directed_walk_iff_no_length G W₁ W₂ hp2 hp1 hne.symm).mpr
                        ⟨σ, hσ_dir, hσ_int⟩)
      · -- Bifurcation iff.
        exact (bifurcation_walk_iff_no_length G W₁ W₂ h hp1 hp2 hne).mp hbif
    · rintro ⟨hp1, hp2, hne, hnd12, hnd21, hbif⟩
      refine ⟨hp1, hp2, hne, ?_, ?_, ?_⟩
      · intro ⟨π, hπ_dir, hπ_int⟩
        exact hnd12 ((directed_walk_iff_no_length G W₁ W₂ hp1 hp2 hne).mp
                        ⟨π, hπ_dir, hπ_int⟩)
      · intro ⟨π, hπ_dir, hπ_int⟩
        exact hnd21 ((directed_walk_iff_no_length G W₁ W₂ hp2 hp1 hne.symm).mp
                        ⟨π, hπ_dir, hπ_int⟩)
      · exact (bifurcation_walk_iff_no_length G W₁ W₂ h hp1 hp2 hne).mpr hbif

-- claim_3_17 (commute corollary)
-- title: MarginalizationsCommute -- commute corollary
--
-- The order of two disjoint marginalizations does not matter:
-- `(G^{\sm W₁})^{\sm W₂} = (G^{\sm W₂})^{\sm W₁}`. One-line
-- corollary of the fusion lemma plus `Set.union_comm`.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Lem 995 -- 1005):

\begin{claimmark}
\begin{Lem}[Marginalizations commute]\label{marginalizations-commute}
      Let $G=(J,V,E,L)$ be a CDMG and $W_1, W_2 \ins V$ two disjoint subsets of output nodes.
      Then we have:
      \[ \lp G^{\sm W_1} \rp^{\sm W_2} = \lp G^{\sm W_2} \rp^{\sm W_1} =  G^{\sm (W_1 \cup W_2)}. \]
\end{Lem}
\end{claimmark}
-/
--
-- ## Design choice
--
-- * **No `W₁, W₂ ⊆ G.V` precondition** -- same reasoning as the
--   fusion lemma above. The no-precondition design of
--   `G.marginalize` (`Section3_2/Marginalization.lean` lines
--   258 -- 286) makes both this corollary and the fusion lemma
--   hold for arbitrary `W₁, W₂ : Set α`; the LN's `W_i ⊆ V` clause
--   is informal scaffolding, not load-bearing in the LN proof.
--   `verify_equivalence` confirmed this is a *faithful
--   strengthening* of the LN statement, not a divergence: the
--   four-component equality is unchanged on vertices that are
--   actually in `G.V`, and vertices in `W \ G.V` are never on any
--   walk so do not affect any of `marginalize_J / V / E / L`.
--
-- * **Disjointness `Disjoint W₁ W₂` is kept and reused on both
--   sides via symmetry.** Load-bearing in the LN statement and in
--   the LN walk-concatenation proof (see the fusion-lemma design
--   note above for the splitting-along-`W_i` argument). The same
--   hypothesis `h` drives both fusion calls in the proof below:
--   `marginalize_marginalize G h` collapses the LHS to
--   `G.marginalize (W₁ ∪ W₂)`, and `marginalize_marginalize G
--   h.symm` collapses the RHS to `G.marginalize (W₂ ∪ W₁)`.
--   Mathlib's `Disjoint` from `Mathlib.Order.Disjoint` has
--   `Disjoint.symm` built in, so we do not have to thread a
--   separate `Disjoint W₂ W₁` hypothesis through the API.
--
-- * **One-line proof from the fusion lemma.** Both sides collapse
--   via `marginalize_marginalize` to `G.marginalize (W₁ ∪ W₂)` and
--   `G.marginalize (W₂ ∪ W₁)` respectively; `Set.union_comm`
--   identifies the union arguments. The Lean proof is essentially
--   `rw [marginalize_marginalize G h,
--        marginalize_marginalize G h.symm, Set.union_comm]`.
--   This direct dependence on the fusion lemma is the reason the
--   two theorems live in the same file in this order (fusion
--   first, commute as corollary): keeping the corollary in the
--   same file makes the rewrite chain locally checkable and
--   matches `HardInterventionsCommute.lean`'s precedent
--   (`hardInterventionOn_comm` at lines 332 -- 343 there, whose
--   proof is the exact same three-rewrite recipe).
--
-- * **The third equality of the LN's triple, `(G^{\sm W₂})^{\sm W₁}
--   = G^{\sm (W₁ ∪ W₂)}`, is not a separate theorem.** It is
--   exactly `marginalize_marginalize G h.symm` followed by
--   `Set.union_comm` (or equivalently `marginalize_marginalize`
--   applied with `W₁` and `W₂` swapped); any consumer that wants
--   it can derive it in one step from the fusion lemma. Promoting
--   it to a named theorem would just be `marginalize_marginalize`
--   with the arguments swapped -- bloating the API without adding
--   expressive power.
--
-- * **Naming `marginalize_comm`.** Standard Mathlib `_comm` suffix
--   for commutativity-of-an-operator-style lemmas (`add_comm`,
--   `mul_comm`, `Set.union_comm`, `Function.comm`, ...). Pairs
--   naturally with the `marginalize_marginalize` fusion name
--   above; mirrors `hardInterventionOn_comm` of claim_3_11.
/-- claim_3_17 commute corollary: the order of two disjoint
marginalizations does not matter,
`(G.marginalize W₁).marginalize W₂ = (G.marginalize W₂).marginalize W₁`.
Mirrors the second half (`= (G^{\sm W₂})^{\sm W₁}`) of the chained
equality in the `\Lem` at `lecture-notes/lecture_notes/graphs.tex`
line 997 (`marginalizations-commute`). -/
theorem marginalize_comm (G : CDMG α) {W₁ W₂ : Set α}
    (h : Disjoint W₁ W₂) :
    (G.marginalize W₁).marginalize W₂
      = (G.marginalize W₂).marginalize W₁ := by
  -- Both sides collapse via `marginalize_marginalize` to `G.marginalize (W₁ ∪ W₂)`
  -- and `G.marginalize (W₂ ∪ W₁)` respectively; `Set.union_comm` identifies them.
  rw [marginalize_marginalize G h, marginalize_marginalize G h.symm,
      Set.union_comm]

end CDMG

end Causality
