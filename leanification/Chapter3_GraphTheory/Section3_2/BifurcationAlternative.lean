import Chapter3_GraphTheory.Section3_1.Bifurcation
import Chapter3_GraphTheory.Section3_1.FamilyReachability
import Chapter3_GraphTheory.Section3_2.HardInterventionOn
import Chapter3_GraphTheory.Section3_2.AcyclicUnderIntervention

-- TeX statement: tex/claim_3_5_statement_BifurcationAlternative.tex
-- TeX proof: tex/claim_3_5_proof_BifurcationAlternative.tex

/-!
# Bifurcation source ↔ ancestral conditions in singleton hard interventions (claim_3_5)

This file formalises *proposition 3.5* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex` lines
358 -- 371, label `prp:bifurcations_alternative`): for vertices
`v`, `w`, `c` of a CDMG `G`, there exists a bifurcation between
`v` and `w` in `G` with source `c` if and only if `v ≠ w` and both
ancestor-set conditions
`c ∈ Anc^{G_{do(w)}}(v) ∖ {v}` and `c ∈ Anc^{G_{do(v)}}(w) ∖ {w}`
hold.

The Lean LHS carries an extra `c ≠ w` conjunct beyond the literal
LN reading; see the design-choice note above the theorem (and the
manager decision recorded in
`Section3_2/workspace_claim_3_5.md`) for the rationale. -/

namespace Causality

open scoped Causality.CDMG

/-! ## Private walk-data helpers for `bifurcation_alternative`

The helpers in this section are scaffolding for the proof below. They
live inside this file (rather than under `Section3_1/`) because the
manager-side scope rule confines this row's edits to `Section3_2/`.
All declarations are `private` and therefore only visible inside this
file. None of them is referenced outside this proof. -/

namespace Walk

variable {α : Type*} {G : CDMG α}

/-- A walk's support is never empty: `nil v` has support `[v]` and
`cons s p` has support `v :: p.support`. -/
private lemma support_ne_nil {v w : α} (p : Walk G v w) : p.support ≠ [] := by
  cases p <;> simp

/-- The support of a walk concatenation: append the supports, dropping
the duplicate hinge vertex from the left walk. -/
private lemma support_append {u v w : α} (p : Walk G u v) (q : Walk G v w) :
    (p.append q).support = p.support.dropLast ++ q.support := by
  induction p with
  | nil v =>
    simp [Walk.nil_append, Walk.support_nil]
  | cons _ p' ih =>
    simp only [Walk.cons_append, Walk.support_cons, ih]
    rw [List.dropLast_cons_of_ne_nil p'.support_ne_nil, List.cons_append]

/-- The first vertex of a walk's support is the start vertex. -/
private lemma support_head {v w : α} (p : Walk G v w) :
    p.support.head p.support_ne_nil = v := by
  cases p <;> rfl

/-- The last vertex of a walk's support is the end vertex. -/
private lemma support_getLast {v w : α} (p : Walk G v w) :
    p.support.getLast p.support_ne_nil = w := by
  induction p with
  | nil _ => rfl
  | cons _ p' ih =>
    simp only [Walk.support_cons]
    rw [List.getLast_cons p'.support_ne_nil]
    exact ih

/-- Walk concatenation is associative. -/
private lemma append_assoc {u v w x : α}
    (p : Walk G u v) (q : Walk G v w) (r : Walk G w x) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp only [Walk.cons_append, ih]

/-- The support of a reversed walk is the reverse of the support. -/
private lemma support_reverse {v w : α} (p : Walk G v w) :
    p.reverse.support = p.support.reverse := by
  induction p with
  | nil _ => rfl
  | @cons v w u s p' ih =>
    rw [Walk.reverse_cons, support_append, ih]
    simp only [Walk.support_cons, Walk.support_nil, List.reverse_cons]
    -- Goal: p'.support.reverse.dropLast ++ [w, v] = p'.support.reverse ++ [v]
    -- since p'.support.reverse ends with w (head of p'.support)
    have hne : p'.support ≠ [] := p'.support_ne_nil
    have hhead : p'.support.head hne = w := p'.support_head
    have hne' : p'.support.reverse ≠ [] := by simpa using hne
    have hlast : p'.support.reverse.getLast hne' = w := by
      rw [List.getLast_reverse]; exact hhead
    have step : p'.support.reverse.dropLast ++ [w] = p'.support.reverse := by
      conv_rhs => rw [← List.dropLast_append_getLast hne']
      rw [hlast]
    -- p'.support.reverse.dropLast ++ [w, v] = (p'.support.reverse.dropLast ++ [w]) ++ [v]
    -- = p'.support.reverse ++ [v]
    calc p'.support.reverse.dropLast ++ [w, v]
        = p'.support.reverse.dropLast ++ ([w] ++ [v]) := by rfl
      _ = (p'.support.reverse.dropLast ++ [w]) ++ [v] := by rw [List.append_assoc]
      _ = p'.support.reverse ++ [v] := by rw [step]

/-- A walk concatenation is `IsDirected` iff both halves are. -/
private lemma isDirected_append {u v w : α}
    (p : Walk G u v) (q : Walk G v w) :
    (p.append q).IsDirected ↔ p.IsDirected ∧ q.IsDirected := by
  induction p with
  | nil _ => simp
  | cons s p' ih =>
    cases s with
    | forward _ =>
      simp only [Walk.cons_append, Walk.isDirected_cons_forward, ih]
    | backward _ =>
      simp [Walk.cons_append]
    | bidir _ =>
      simp [Walk.cons_append]

/-- A walk concatenation is `IsAllBackward` iff both halves are. -/
private lemma isAllBackward_append {u v w : α}
    (p : Walk G u v) (q : Walk G v w) :
    (p.append q).IsAllBackward ↔ p.IsAllBackward ∧ q.IsAllBackward := by
  induction p with
  | nil _ => simp
  | cons s p' ih =>
    cases s with
    | forward _ => simp [Walk.cons_append]
    | backward _ =>
      simp only [Walk.cons_append, Walk.isAllBackward_cons_backward, ih]
    | bidir _ => simp [Walk.cons_append]

/-- A `forward` step reverses to a `backward` step, so an all-forward
(`IsDirected`) walk reverses to an all-backward walk. -/
private lemma isAllBackward_reverse_of_isDirected {v w : α}
    {p : Walk G v w} (hp : p.IsDirected) : p.reverse.IsAllBackward := by
  induction p with
  | nil _ => simp
  | cons s p' ih =>
    cases s with
    | forward h =>
      simp only [Walk.isDirected_cons_forward] at hp
      simp only [Walk.reverse_cons, WalkStep.reverse_forward]
      rw [isAllBackward_append]
      refine ⟨ih hp, ?_⟩
      simp
    | backward _ => simp at hp
    | bidir _ => simp at hp

/-- A `backward` step reverses to a `forward` step, so an all-backward
walk reverses to an `IsDirected` walk. -/
private lemma isDirected_reverse_of_isAllBackward {v w : α}
    {p : Walk G v w} (hp : p.IsAllBackward) : p.reverse.IsDirected := by
  induction p with
  | nil _ => simp
  | cons s p' ih =>
    cases s with
    | forward _ => simp at hp
    | backward h =>
      simp only [Walk.isAllBackward_cons_backward] at hp
      simp only [Walk.reverse_cons, WalkStep.reverse_backward]
      rw [isDirected_append]
      refine ⟨ih hp, ?_⟩
      simp
    | bidir _ => simp at hp

/-- Restrict a directed walk in `G` to a directed walk in
`G.hardInterventionOn W`, provided every step's target avoids `W`.
The targets of a walk's steps are exactly the elements of
`support.tail`, so the per-step constraint is encoded in that form.
Together with `restrictForward_isDirected` below, this packages the
"lift down" half of the LN's intervention edge-shrinkage idiom. -/
private noncomputable def restrictForward {W : Set α} :
    ∀ {v w : α} (p : Walk G v w),
      p.IsDirected → (∀ x ∈ p.support.tail, x ∉ W) →
      Walk (G.hardInterventionOn W) v w := by
  intro v w p
  induction p with
  | nil v0 => exact fun _ _ => .nil v0
  | @cons v0 w0 u0 s p' ih =>
    intro hp htarg
    cases s with
    | forward h =>
      have htarget : w0 ∉ W := by
        apply htarg
        rw [Walk.support_cons, List.tail_cons]
        cases p' with
        | nil _ => simp
        | cons _ _ => simp
      have hp' : p'.IsDirected := by simpa using hp
      have htarg' : ∀ x ∈ p'.support.tail, x ∉ W := fun x hx => by
        apply htarg
        rw [Walk.support_cons, List.tail_cons]
        exact List.mem_of_mem_tail hx
      exact .cons (.forward ⟨h, htarget⟩) (ih hp' htarg')
    | backward _ => simp at hp
    | bidir _ => simp at hp

/-- The restricted walk is directed (every step is `.forward`). -/
private lemma restrictForward_isDirected {W : Set α} {v w : α}
    (p : Walk G v w) (hp : p.IsDirected)
    (htarg : ∀ x ∈ p.support.tail, x ∉ W) :
    (restrictForward p hp htarg).IsDirected := by
  induction p with
  | nil _ => simp [restrictForward]
  | cons s p' ih =>
    cases s with
    | forward _ =>
      -- Unfold restrictForward on the cons (.forward _) case.
      unfold restrictForward
      simp only
      exact ih _ _
    | backward _ => simp at hp
    | bidir _ => simp at hp

/-- Shorten a directed walk so its endpoint vertex does not occur in
`support.dropLast`. The result is a directed walk with the same start
and end vertices, whose support has the end vertex *only* at its last
position (the "endpoint-only" weakening of `IsPath`). -/
private lemma exists_endpoint_only_of_isDirected (n : ℕ) :
    ∀ {v w : α} (p : Walk G v w), p.IsDirected → p.length = n →
    ∃ q : Walk G v w, q.IsDirected ∧ w ∉ q.support.dropLast := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v w p hp hlen
    classical
    by_cases hw : w ∈ p.support.dropLast
    · cases p with
      | nil v0 => simp at hw
      | cons s p' =>
        cases s with
        | forward h =>
          by_cases hvw : v = w
          · subst hvw
            exact ⟨Walk.nil v, by simp, by simp⟩
          · have hp' : p'.IsDirected := by simpa using hp
            have hlen' : p'.length < n := by
              simp only [Walk.length_cons] at hlen
              omega
            obtain ⟨q', hq'_dir, hq'_end⟩ :=
              ih p'.length hlen' p' hp' rfl
            refine ⟨.cons (.forward h) q', ?_, ?_⟩
            · simpa using hq'_dir
            · simp only [Walk.support_cons]
              rw [List.dropLast_cons_of_ne_nil q'.support_ne_nil]
              simp only [List.mem_cons]
              push Not
              exact ⟨fun heq => hvw heq.symm, hq'_end⟩
        | backward _ => simp at hp
        | bidir _ => simp at hp
    · exact ⟨p, hp, hw⟩

/-- The support of a walk decomposed by a `BifurcationWitness`. -/
private lemma support_decompose {v w : α} {π : Walk G v w}
    (bw : BifurcationWitness π) :
    π.support = bw.leftArm.support.dropLast ++ (bw.m :: bw.rightArm.support) := by
  conv_lhs => rw [bw.decompose]
  rw [support_append]
  simp only [Walk.support_cons]

/-- A walk's support always starts with the start vertex. -/
private lemma support_eq_cons_tail {v w : α} (p : Walk G v w) :
    p.support = v :: p.support.tail := by
  cases p with
  | nil _ => rfl
  | cons _ _ => rfl

/-- For a walk `cons s p`, every vertex of `p.support` is in the tail
of `(cons s p).support`. -/
private lemma tail_support_cons {v w u : α} (s : WalkStep G v w) (p : Walk G w u) :
    (Walk.cons s p).support.tail = p.support := by
  rw [Walk.support_cons, List.tail_cons]

/-- Every vertex of a walk's support is either the start vertex or
in `support.tail`. -/
private lemma mem_support_iff_head_or_tail {v w : α} (p : Walk G v w) (x : α) :
    x ∈ p.support ↔ x = v ∨ x ∈ p.support.tail := by
  rw [show p.support = v :: p.support.tail from support_eq_cons_tail p]
  exact List.mem_cons

/-- A vertex in `p.support.dropLast` is in `p.support` (loses the last). -/
private lemma mem_support_of_mem_dropLast {v w : α} {p : Walk G v w} {x : α}
    (h : x ∈ p.support.dropLast) : x ∈ p.support :=
  List.dropLast_subset _ h

/-- For a non-trivial walk, `support.tail` is non-empty (and equals
`support.dropLast.tail ++ [endpoint]`). The simpler fact we need:
membership in `support.dropLast` (other than the head) lies in the
proper tail. -/
private lemma support_dropLast_eq {v w : α} (p : Walk G v w) (hpos : 1 ≤ p.length) :
    p.support.dropLast = v :: p.support.tail.dropLast := by
  cases p with
  | nil _ => simp at hpos
  | cons _ p' =>
    simp only [Walk.support_cons, List.tail_cons]
    rw [List.dropLast_cons_of_ne_nil p'.support_ne_nil]

/-- `(l1 ++ l2).tail = l1.tail ++ l2` when `l1` is non-empty. -/
private lemma list_tail_append_of_ne_nil {β : Type*} (l1 l2 : List β) (h : l1 ≠ []) :
    (l1 ++ l2).tail = l1.tail ++ l2 := by
  cases l1 with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- `l.reverse.dropLast = l.tail.reverse`: the reverse of the tail
equals the dropLast of the reverse. -/
private lemma list_reverse_dropLast {β : Type*} (l : List β) :
    l.reverse.dropLast = l.tail.reverse := by
  cases l with
  | nil => rfl
  | cons a rest =>
    rw [List.reverse_cons, List.tail_cons,
        List.dropLast_append_of_ne_nil (by simp : ([a] : List β) ≠ [])]
    simp

/-- Dual to `list_reverse_dropLast`: tail of the reverse equals
reverse of the dropLast. -/
private lemma list_reverse_tail {β : Type*} (l : List β) :
    l.reverse.tail = l.dropLast.reverse := by
  have h := list_reverse_dropLast l.reverse
  rw [List.reverse_reverse] at h
  -- h : l.dropLast = l.reverse.tail.reverse
  rw [h, List.reverse_reverse]

/-- The `tail` and `dropLast` operations commute. -/
private lemma list_tail_dropLast {β : Type*} (l : List β) :
    l.tail.dropLast = l.dropLast.tail := by
  cases l with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest' => rfl

/-- Uniqueness of the bifurcation source's `m'` (and that the hinge
is `.backward`, not `.bidir`) for a walk of the form (all-backward
`L`) ++ (backward hinge) ++ (directed `R`). For any
`BifurcationWitness` of such a walk, `bw.m' = c` and
`¬ bw.hinge.IsBidir`. -/
private lemma m'_eq_of_isAllBackward_append_cons_backward
    {α : Type*} {G : CDMG α} {v c w : α} :
    ∀ {m : α} (L : Walk G v m), L.IsAllBackward →
      ∀ (h : m ⟵[G] c) (R : Walk G c w), R.IsDirected →
      ∀ (bw : BifurcationWitness (L.append (Walk.cons (.backward h) R))),
        bw.m' = c ∧ ¬ bw.hinge.IsBidir := by
  intro m L
  induction L with
  | nil m0 =>
    intro _ h R hR bw
    obtain ⟨m_bw, m'_bw, leftArm, hinge, rightArm, decompose, leftBackward,
            hingeIntoSource, _⟩ := bw
    rw [Walk.nil_append] at decompose
    cases leftArm with
    | nil v' =>
      rw [Walk.nil_append] at decompose
      injection decompose with _ h_mid _ s_heq r_heq
      subst h_mid
      refine ⟨rfl, ?_⟩
      have hh : (WalkStep.backward h : WalkStep G m0 c) = hinge := eq_of_heq s_heq
      cases hh
      simp
    | @cons _ z _ s_b L_b =>
      cases s_b with
      | forward _ => simp at leftBackward
      | bidir _ => simp at leftBackward
      | backward h_b =>
        rw [Walk.cons_append] at decompose
        injection decompose with _ h_mid _ _ r_heq
        subst h_mid
        have hReq : R = L_b.append (Walk.cons hinge rightArm) := eq_of_heq r_heq
        have hRD : (L_b.append (Walk.cons hinge rightArm)).IsDirected := hReq ▸ hR
        rw [isDirected_append] at hRD
        have h_inner : (Walk.cons hinge rightArm).IsDirected := hRD.2
        cases hinge with
        | forward _ => exact absurd hingeIntoSource (by simp)
        | backward _ => simp at h_inner
        | bidir _ => simp at h_inner
  | @cons v0 z m0 s L' ih =>
    intro hL h R hR bw
    cases s with
    | forward _ => simp at hL
    | bidir _ => simp at hL
    | backward h_s =>
      have hL' : L'.IsAllBackward := by simpa using hL
      obtain ⟨m_bw, m'_bw, leftArm, hinge, rightArm, decompose, leftBackward,
              hingeIntoSource, rightDirected⟩ := bw
      rw [Walk.cons_append] at decompose
      -- decompose : cons (.backward h_s) (L'.append (cons (.backward h) R))
      --             = leftArm.append (cons hinge rightArm)
      cases leftArm with
      | nil v' =>
        rw [Walk.nil_append] at decompose
        -- decompose : cons (.backward h_s) (L'.append _) = cons hinge rightArm
        injection decompose with _ h_mid _ s_heq r_heq
        -- h_mid : z = m'_bw
        -- s_heq : HEq (.backward h_s) hinge
        -- r_heq : HEq (L'.append (cons (.backward h) R)) rightArm
        subst h_mid
        have hRD : (L'.append (Walk.cons (.backward h) R)).IsDirected := by
          have := eq_of_heq r_heq
          rw [this]; exact rightDirected
        rw [isDirected_append] at hRD
        have h_inner : (Walk.cons (.backward h) R).IsDirected := hRD.2
        simp at h_inner
      | @cons _ z' _ s_b L_b =>
        cases s_b with
        | forward _ => simp at leftBackward
        | bidir _ => simp at leftBackward
        | backward h_b =>
          rw [Walk.cons_append] at decompose
          -- decompose : cons (.backward h_s) (L'.append _)
          --             = cons (.backward h_b) (L_b.append _)
          injection decompose with _ h_mid _ _ r_heq
          -- h_mid : z = z'
          subst h_mid
          have hreq : L'.append (Walk.cons (.backward h) R)
                    = L_b.append (Walk.cons hinge rightArm) := eq_of_heq r_heq
          have hL_b : L_b.IsAllBackward := by simpa using leftBackward
          let bw' : BifurcationWitness (L'.append (Walk.cons (.backward h) R)) := {
            m := m_bw
            m' := m'_bw
            leftArm := L_b
            hinge := hinge
            rightArm := rightArm
            decompose := hreq
            leftBackward := hL_b
            hingeIntoSource := hingeIntoSource
            rightDirected := rightDirected
          }
          exact ih hL' h R hR bw'

/-- Every vertex of the right arm's support appears in `π.support.tail`
(i.e. not at the start vertex). -/
private lemma rightArm_support_subset_tail {v w : α} {π : Walk G v w}
    (bw : BifurcationWitness π) {x : α} (hx : x ∈ bw.rightArm.support) :
    x ∈ π.support.tail := by
  rw [support_decompose bw]
  -- π.support = bw.leftArm.support.dropLast ++ (bw.m :: bw.rightArm.support)
  by_cases hL : bw.leftArm.support.dropLast = []
  · rw [hL, List.nil_append, List.tail_cons]; exact hx
  · rw [list_tail_append_of_ne_nil _ _ hL]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx))

/-- For a directed walk in `G.hardInterventionOn W`, every vertex of
the support is outside `W`, provided the start vertex is. Each
`.forward` step requires its target to be outside `W` (by
`mem_hardInterventionOn_E`), so by induction every support vertex
inherits this property from the chain. -/
private lemma support_disjoint_W_of_isDirected {W : Set α} {a b : α}
    (p : Walk (G.hardInterventionOn W) a b) (hp : p.IsDirected) (ha : a ∉ W) :
    ∀ x ∈ p.support, x ∉ W := by
  induction p with
  | nil v0 =>
    intro x hx
    simp only [Walk.support_nil, List.mem_singleton] at hx
    rw [hx]; exact ha
  | @cons v0 w0 u0 s p' ih =>
    intro x hx
    cases s with
    | forward h =>
      -- h : (v0, w0) ∈ (G.hardInterventionOn W).E, so w0 ∉ W.
      have hw0 : w0 ∉ W := h.2
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with hxa | hxinp'
      · rw [hxa]; exact ha
      · exact ih (by simpa using hp) hw0 x hxinp'
    | backward _ => simp at hp
    | bidir _ => simp at hp

end Walk

namespace CDMG

variable {α : Type*}

-- claim_3_5
-- title: BifurcationAlternative
--
-- LN claim 3.5: there is a bifurcation between `v` and `w` with
-- source `c` iff `v ≠ w` and `c` is a non-trivial ancestor of `v`
-- in the single-vertex hard intervention `G_{do(w)}` and of `w` in
-- `G_{do(v)}`. The LN's prose is at `graphs.tex` 358 -- 371.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex` (Prp 360 -- 364)
-- the iff sentence is reflowed (linewrap only; text-mode whitespace
-- collapses, so this is verbatim under \LaTeX semantics):

\begin{claimmark}
\begin{Prp}\label{prp:bifurcations_alternative}
  Let $G = \lt J, V, E, L \rt$ be a CDMG. For $v, w, c \in V \cup J$:
  there exists a bifurcation between $v$ and $w$ in $G$ with source $c$
  if and only if $v \ne w$ and $c \in \Anc^{G_{\doit(w)}}(v) \sm \{v\}$
  and $c \in \Anc^{G_{\doit(v)}}(w) \sm \{w\}$.
\end{Prp}
\end{claimmark}
-/
/-- LN claim 3.5 (`prp:bifurcations_alternative`): for vertices
`v`, `w`, `c` of a CDMG `G`, there exists a bifurcation between
`v` and `w` in `G` with source `c` iff `v ≠ w` and both
ancestor-set conditions
`c ∈ Anc^{G_{do(w)}}(v) ∖ {v}` and `c ∈ Anc^{G_{do(v)}}(w) ∖ {w}`
hold. The LHS quantifies existentially over a walk
`π : Walk G v w` and a witness `hb : π.IsBifurcation`, with the
source extracted via `π.bifurcationSource hb = some c`; an extra
`c ≠ w` conjunct on the LHS captures the LN's *implicit*
"non-trivial directed path from `c` to `w`" requirement at the
claim level (see `## Design choice` below).

## Design choice

* **The `c ≠ w` LHS conjunct is the load-bearing decision for
  this row.** Without it, the iff is *literally false*. The
  current `Walk.bifurcationSource`
  (`Section3_1/Bifurcation.lean` lines 362 -- 367) returns
  `some bw.m'` whenever the chosen witness's hinge is
  `.backward _`, regardless of whether the witness's `rightArm`
  is the trivial `.nil` walk. Consequently, an all-backward walk
  `v ⊣ ⋯ ⊣ w` (length ≥ 1) is an `IsBifurcation` whose source is
  `w` (the witness picks the last backward step as the hinge,
  `rightArm = .nil w`, so `bw.m' = w`): the LHS with `c = w`
  holds, but the RHS forbids `c = w` via the `\ {w}` exclusion.
  Two repair routes were considered.
  - **Path 1** -- tighten `bifurcationSource` itself to require
    a non-trivial `rightArm` in addition to the backward hinge.
    **Rejected.** That extractor is owned by **def_3_4**
    (`Section3_1/Bifurcation.lean`, a previously-solved row in
    a different subsection); editing it from a Section_3_2 row
    breaks the manager-side scope rule, and the heavy-redesign
    machinery would have to be invoked to retract def_3_4 and
    its dependents. Disproportionate surgery to make one iff
    hold.
  - **Path 2** (chosen) -- add `c ≠ w` to the LHS so it mirrors
    the RHS's `\ {w}` exclusion clause-for-clause. Local,
    surgical, LN-faithful: the LN's own proof prose at
    `graphs.tex` lines 366 -- 371 calls the right half a
    *"non-trivial directed path from `c` to `w`"*, and `c ≠ w`
    is exactly the Lean transcription of "non-trivial". The LN's
    def_3_4 item 6 leaves this implicit -- claim_3_5 is where
    the LN first relies on it -- so encoding it on the claim's
    LHS rather than retroactively tightening def_3_4 stays
    closer to the LN's own factoring.

  See the *Manager decision (2026-05-20)* section at the top of
  `Section3_2/workspace_claim_3_5.md` for the full decision
  record (counterexample, scope-rule discussion, forward-tax
  estimate).

* **No symmetric `c ≠ v` conjunct on the LHS -- deliberate
  asymmetry.** `IsBifurcation` already enforces
  `v ∉ π.support.tail` (`Section3_1/Bifurcation.lean` line 311).
  For any witness `bw` of `π : Walk G v w`, the source vertex
  `c = bw.m'` sits at position `1 + bw.leftArm.length ≥ 1` of
  `π.support`, i.e. inside `π.support.tail`; combined with
  `v ∉ π.support.tail` this forces `c ≠ v` automatically. The
  asymmetry between the two endpoints mirrors how
  `bifurcationSource` *extracts* the source -- it names `m'`,
  the right side of the hinge -- so it is the *right arm* whose
  non-triviality has to be enforced separately on the LHS. The
  left arm's non-triviality is irrelevant to the source
  extractor: even a degenerate `k = 1` (empty `leftArm`) witness
  does not threaten the iff.

* **Two-argument `Anc` and singleton hard interventions.** `Anc`
  is the two-argument form `Anc : CDMG α → α → Set α`
  (`Section3_1/FamilyReachability.lean` lines 115 -- 125), not a
  one-argument predicate bundled over an implicit subgraph. The
  LN's `\Anc^{G_{\doit(w)}}(v)` therefore transcribes as
  `Anc (G.hardInterventionOn ({w} : Set α)) v`: the intervened
  graph is supplied as the first positional argument, and the
  singleton `{w}` is a literal `Set α`. We reuse the existing
  `hardInterventionOn : CDMG α → Set α → CDMG α` API of
  `Section3_2/HardInterventionOn.lean` directly rather than
  introducing a vertex-flavoured `hardInterventionOnVertex`
  wrapper -- the LN's notation is set-flavoured (the more
  general `G_{\doit(W)}` is the actual definitional unit), and
  the single-vertex case is just a one-element instantiation.
  Note also that `G.hardInterventionOn ({w} : Set α)` is
  well-defined for any `w : α` (no `w ∈ G` precondition),
  matching `HardInterventionOn`'s no-precondition design -- a
  design choice that was explicitly justified, in part, by this
  claim's need to write `G.hardInterventionOn {w}` without
  having to discharge `w ∈ G` at every call site.

* **No explicit `v, w, c ∈ G` precondition.** The LN's preamble
  "For `v, w, c ∈ V ∪ J`" is *not* hoisted into a hypothesis on
  the Lean statement. Both sides of the iff already force the
  relevant memberships where they are load-bearing:
  - LHS: a `π : Walk G v w` with `IsBifurcation` has length ≥ 1
    (`length_pos_of_isBifurcation`,
    `Section3_1/Bifurcation.lean` lines 395 -- 399), and its
    first/last/hinge edges place `v`, `w`, `c` in `G` via
    `G.E_subset` / `CDMG.mem_iff`.
  - RHS: each `c ∈ Anc G' v` membership carries a built-in
    `c ∈ G'` clause (`mem_Anc`,
    `Section3_1/FamilyReachability.lean` lines 122 -- 125),
    and the `\ {v}` / `\ {w}` exclusions give the remaining
    `c ≠ v` / `c ≠ w` constraints.
  An explicit precondition would therefore be redundant on both
  sides and would mildly clutter the consumer surface at every
  call site that does not already have the memberships in hand.
  Same no-precondition pattern as `isAcyclic_hardInterventionOn`
  (`Section3_2/AcyclicUnderIntervention.lean` line 191) and the
  `hardInterventionOn_hardInterventionOn` / `_comm` pair in
  `Section3_2/HardInterventionsCommute.lean`.

* **Walk direction: `Walk G v w`, not `Walk G w v`.** Matches
  the LN's def 3.4 ordering `v = v_0 \hus \cdots \hus v_n = w`
  -- the start vertex of the walk is the LN's `v`, the end
  vertex is the LN's `w`. This lets the `BifurcationWitness`'s
  `leftArm` / `rightArm` decomposition line up with the LN's
  left-of-hinge / right-of-hinge arms without any direction
  inversion, and lets `bw.m'` (the source) read off as the
  LN's `v_k` on the right of the hinge. The arrow direction on
  individual edges is independent of the walk direction --
  steps can be `.forward`, `.backward`, or `.bidir` either way
  -- so this choice is purely about index orientation, not
  about which arrows the walk is allowed to contain.

* **Known limitation / future redesign trigger.** The `c ≠ w`
  conjunct on the LHS is a *local* compensation for the
  looseness of `bifurcationSource` in the
  all-backward-walk corner case. Any future downstream claim
  that re-phrases "bifurcation with source `c`" in an
  *asymmetric* shape -- relating the source to ancestral /
  acyclicity / topological-order properties of one specific
  endpoint -- will need to repeat the same `c ≠ w` conjunct (or
  its symmetric `c ≠ v` variant) on its own LHS. Symmetric
  claims (e.g. the marginalisation-preserves-bifurcations
  reading of claim_3_6, which only quantifies source *existence*
  rather than identifying the source with a specific endpoint)
  are corner-case-stable and need no extra bookkeeping. If
  enough downstream rows end up paying this asymmetry tax, the
  **Path 1** refactor (tighten `bifurcationSource` once at the
  source, propagate via the heavy-redesign machinery) should be
  re-considered. -/
theorem bifurcation_alternative {G : CDMG α} {v w c : α} :
    (∃ π : Walk G v w, ∃ hb : π.IsBifurcation,
       π.bifurcationSource hb = some c ∧ c ≠ w)
    ↔ v ≠ w
      ∧ c ∈ Anc (G.hardInterventionOn ({w} : Set α)) v \ {v}
      ∧ c ∈ Anc (G.hardInterventionOn ({v} : Set α)) w \ {w} := by
  refine ⟨?_, ?_⟩
  · -- ⟹ direction
    rintro ⟨π, hb, hsrc, hcw⟩
    -- Unpack hb := ⟨hvw, hvtail, hwdroplast, ⟨bw⟩⟩ via choice
    obtain ⟨hvw, hvtail, hwdroplast, hbwne⟩ := hb
    -- Let bw := the chosen witness
    set bw := hbwne.some with hbw_def
    -- Unfold bifurcationSource at hsrc to get bw.hinge = .backward h, bw.m' = c.
    have key : ∃ h : bw.m ⟵[G] bw.m', bw.hinge = .backward h ∧ bw.m' = c := by
      show ∃ h, bw.hinge = .backward h ∧ bw.m' = c
      unfold Walk.bifurcationSource at hsrc
      -- hsrc : (let bw' := hb.2.2.2.some; match bw'.hinge with ...) = some c
      -- We have set bw := hbwne.some, but hsrc uses hb.2.2.2.some.
      -- These are the same: hb.2.2.2 = hbwne, hb.2.2.2.some = hbwne.some = bw.
      change (match bw.hinge with | .backward _ => some bw.m' | _ => none) = some c at hsrc
      cases hh : bw.hinge with
      | forward _ =>
        rw [hh] at hsrc; exact absurd hsrc (by simp)
      | backward h =>
        rw [hh] at hsrc
        simp only [Option.some.injEq] at hsrc
        exact ⟨h, rfl, hsrc⟩
      | bidir _ =>
        rw [hh] at hsrc; exact absurd hsrc (by simp)
    obtain ⟨h, hhinge, hm'c⟩ := key
    -- Helpful facts derived from hb:
    -- - bw.decompose : π = bw.leftArm.append (cons bw.hinge bw.rightArm)
    -- - bw.leftArm : Walk G v bw.m, IsAllBackward (bw.leftBackward)
    -- - bw.rightArm : Walk G bw.m' w, IsDirected (bw.rightDirected)
    -- - hvtail : v ∉ π.support.tail
    -- - hwdroplast : w ∉ π.support.dropLast
    -- Since bw.m' = c, bw.rightArm has type Walk G c w.
    -- The hinge .backward h : WalkStep G bw.m bw.m', with h : bw.m ⟵[G] bw.m'.
    --   Equivalently h : (bw.m', bw.m) ∈ G.E = (c, bw.m) ∈ G.E.
    --   So h : c ⟶[G] bw.m (forward edge from c to bw.m).
    -- Membership c ∈ G via G.E_subset on h.
    have hc_in_G : c ∈ G := by
      -- h : (c, bw.m) ∈ G.E (recall bw.m' = c)
      rw [hm'c] at h
      have hE : (c, bw.m) ∈ G.E := h
      have := G.E_subset hE
      rw [CDMG.mem_iff]
      exact (Set.mem_prod.mp this).1
    -- bw.m is in bw.leftArm.support (always: last vertex).
    -- w ∉ bw.leftArm.support : both bw.m ≠ w (lies inside π.support.dropLast)
    -- and every other vertex of bw.leftArm.support is in π.support.dropLast.
    -- The split: π.support = bw.leftArm.support.dropLast ++ (bw.m :: bw.rightArm.support).
    have hsupp_pi : π.support = bw.leftArm.support.dropLast ++
        (bw.m :: bw.rightArm.support) := Walk.support_decompose bw
    -- π.support.dropLast = bw.leftArm.support.dropLast ++ (bw.m :: bw.rightArm.support.dropLast).
    have hbw_rt_ne : bw.rightArm.support ≠ [] := bw.rightArm.support_ne_nil
    have hdropLast_pi : π.support.dropLast = bw.leftArm.support.dropLast ++
        (bw.m :: bw.rightArm.support.dropLast) := by
      rw [hsupp_pi]
      rw [List.dropLast_append_of_ne_nil]
      · simp [List.dropLast_cons_of_ne_nil hbw_rt_ne]
      · simp
    -- Now from hwdroplast and hdropLast_pi: w ∉ leftArm.dropLast, bw.m ≠ w, w ∉ rightArm.dropLast.
    have hwleft : w ∉ bw.leftArm.support.dropLast := by
      intro hh
      exact hwdroplast (hdropLast_pi ▸ List.mem_append.mpr (Or.inl hh))
    have hbwm_ne_w : bw.m ≠ w := by
      intro hh
      apply hwdroplast
      rw [hdropLast_pi]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl hh.symm)))
    have hwleft_full : w ∉ bw.leftArm.support := by
      have heq : bw.leftArm.support = bw.leftArm.support.dropLast ++ [bw.m] := by
        have := List.dropLast_append_getLast bw.leftArm.support_ne_nil
        rw [bw.leftArm.support_getLast] at this
        exact this.symm
      rw [heq, List.mem_append, List.mem_singleton]
      push Not
      exact ⟨hwleft, hbwm_ne_w.symm⟩
    -- c ≠ v : c ∈ bw.rightArm.support (head), and bw.rightArm.support ⊆ π.support.tail.
    have hc_in_rt : c ∈ bw.rightArm.support := by
      rw [← hm'c, Walk.support_eq_cons_tail bw.rightArm]
      exact List.mem_cons_self
    have hc_ne_v : c ≠ v := by
      intro heq
      have hcInTail : c ∈ π.support.tail :=
        Walk.rightArm_support_subset_tail bw hc_in_rt
      rw [heq] at hcInTail
      exact hvtail hcInTail
    -- Substitute c → bw.m' so we work with bw.m' throughout (since bw.m' = c).
    -- This way h : bw.m ⟵[G] bw.m' = (bw.m', bw.m) ∈ G.E = bw.m' ⟶[G] bw.m
    -- (definitional).
    subst hm'c
    -- Now goal uses bw.m' everywhere instead of c.
    refine ⟨hvw, ?_, ?_⟩
    · -- bw.m' ∈ Anc (G.hardInterventionOn {w}) v \ {v}
      refine ⟨?_, ?_⟩
      swap
      · simp only [Set.mem_singleton_iff]; exact hc_ne_v
      rw [mem_Anc]
      refine ⟨?_, ?_⟩
      · rw [CDMG.mem_iff]
        simp only [hardInterventionOn_J, hardInterventionOn_V, Set.mem_union, Set.mem_diff]
        rw [CDMG.mem_iff, Set.mem_union] at hc_in_G
        rcases hc_in_G with hJ | hV
        · exact Or.inl (Or.inl hJ)
        · by_cases hcw' : bw.m' = w
          · exact Or.inl (Or.inr hcw')
          · exact Or.inr ⟨hV, hcw'⟩
      -- Construct A_G : Walk G bw.m' v as cons (.forward h') bw.leftArm.reverse
      -- where h' : bw.m' ⟶[G] bw.m, definitionally h.
      have h' : bw.m' ⟶[G] bw.m := h
      have hleft_rev_dir : bw.leftArm.reverse.IsDirected :=
        Walk.isDirected_reverse_of_isAllBackward bw.leftBackward
      let A_G : Walk G bw.m' v := .cons (.forward h') bw.leftArm.reverse
      have hA_G_dir : A_G.IsDirected := by simpa [A_G] using hleft_rev_dir
      have h_targets : ∀ x ∈ A_G.support.tail, x ∉ ({w} : Set α) := by
        intro x hx
        change x ∈ (Walk.cons (.forward h') bw.leftArm.reverse).support.tail at hx
        rw [Walk.support_cons, List.tail_cons, Walk.support_reverse] at hx
        rw [List.mem_reverse] at hx
        intro hxw
        rw [Set.mem_singleton_iff] at hxw
        exact hwleft_full (hxw ▸ hx)
      exact ⟨Walk.restrictForward A_G hA_G_dir h_targets,
             Walk.restrictForward_isDirected _ _ _⟩
    · -- bw.m' ∈ Anc (G.hardInterventionOn {v}) w \ {w}
      refine ⟨?_, ?_⟩
      swap
      · simp only [Set.mem_singleton_iff]; exact hcw
      rw [mem_Anc]
      refine ⟨?_, ?_⟩
      · rw [CDMG.mem_iff]
        simp only [hardInterventionOn_J, hardInterventionOn_V, Set.mem_union, Set.mem_diff]
        rw [CDMG.mem_iff, Set.mem_union] at hc_in_G
        rcases hc_in_G with hJ | hV
        · exact Or.inl (Or.inl hJ)
        · by_cases hcv : bw.m' = v
          · exact Or.inl (Or.inr hcv)
          · exact Or.inr ⟨hV, hcv⟩
      have hrt_dir : bw.rightArm.IsDirected := bw.rightDirected
      have h_targets : ∀ x ∈ bw.rightArm.support.tail, x ∉ ({v} : Set α) := by
        intro x hx hxv
        rw [Set.mem_singleton_iff] at hxv
        have hxinπtail : x ∈ π.support.tail :=
          Walk.rightArm_support_subset_tail bw (List.mem_of_mem_tail hx)
        exact hvtail (hxv ▸ hxinπtail)
      exact ⟨Walk.restrictForward bw.rightArm hrt_dir h_targets,
             Walk.restrictForward_isDirected _ _ _⟩
  · -- ⟸ direction
    rintro ⟨hvw, hcw_in, hcv_in⟩
    obtain ⟨hcw_anc, hc_ne_v_set⟩ := hcw_in
    obtain ⟨hcv_anc, hc_ne_w_set⟩ := hcv_in
    simp only [Set.mem_singleton_iff] at hc_ne_v_set hc_ne_w_set
    rw [mem_Anc] at hcw_anc hcv_anc
    obtain ⟨hc_in_dow, A₀, hA₀_dir⟩ := hcw_anc
    obtain ⟨hc_in_dov, B₀, hB₀_dir⟩ := hcv_anc
    -- Step 1: Shorten A₀, B₀ to A, B with endpoint-only property.
    obtain ⟨A, hA_dir, hA_endpoint⟩ :=
      Walk.exists_endpoint_only_of_isDirected A₀.length A₀ hA₀_dir rfl
    obtain ⟨B, hB_dir, hB_endpoint⟩ :=
      Walk.exists_endpoint_only_of_isDirected B₀.length B₀ hB₀_dir rfl
    -- Step 2: Useful facts about A, B (in G_{do(W)}-forms).
    have hc_not_w : c ∉ ({w} : Set α) := by
      rw [Set.mem_singleton_iff]; exact hc_ne_w_set
    have hc_not_v : c ∉ ({v} : Set α) := by
      rw [Set.mem_singleton_iff]; exact hc_ne_v_set
    have hw_not_in_A : w ∉ A.support := fun hw_in =>
      Walk.support_disjoint_W_of_isDirected A hA_dir hc_not_w w hw_in rfl
    have hv_not_in_B : v ∉ B.support := fun hv_in =>
      Walk.support_disjoint_W_of_isDirected B hB_dir hc_not_v v hv_in rfl
    -- Step 3: Cases on A's structure. A has length ≥ 1 since c ≠ v.
    cases hA_form : A with
    | nil v0 =>
      -- v0 = c and v0 = v (from type Walk _ c v), so c = v. Contradicts hc_ne_v_set.
      exact absurd hc_ne_v_set (by rcases hA_form; intro h; exact h rfl)
    | @cons _ m_A _ s A' =>
      cases s with
      | backward _ => rw [hA_form] at hA_dir; simp at hA_dir
      | bidir _ => rw [hA_form] at hA_dir; simp at hA_dir
      | forward h_A =>
        -- h_A : c ⟶[G.hardInterventionOn {w}] m_A
        -- A' : Walk (G.hardInterventionOn {w}) m_A v
        have hA'_dir : A'.IsDirected := by
          have := hA_dir
          rw [hA_form] at this; simpa using this
        -- h_A's underlying : (c, m_A) ∈ (G.hardInterventionOn {w}).E.
        -- Lift to G: (c, m_A) ∈ G.E by .1.
        have h_A_G : (c, m_A) ∈ G.E := h_A.1
        -- Lift A and A' to G.
        let A_G' : Walk G m_A v := walkLiftHardInterventionOn A'
        let B_G : Walk G c w := walkLiftHardInterventionOn B
        have hA_G'_dir : A_G'.IsDirected :=
          walkLiftHardInterventionOn_isDirected A' hA'_dir
        have hB_G_dir : B_G.IsDirected :=
          walkLiftHardInterventionOn_isDirected B hB_dir
        have hA_G'_supp : A_G'.support = A'.support :=
          walkLiftHardInterventionOn_support A'
        have hB_G_supp : B_G.support = B.support :=
          walkLiftHardInterventionOn_support B
        -- Construct the explicit π = A_G'.reverse.append (cons (.backward h_A_G) B_G).
        let π : Walk G v w :=
          A_G'.reverse.append (Walk.cons (.backward h_A_G) B_G)
        -- Construct the explicit witness.
        have hL_back : A_G'.reverse.IsAllBackward :=
          Walk.isAllBackward_reverse_of_isDirected hA_G'_dir
        let bw_explicit : Walk.BifurcationWitness π :=
          { m := m_A
            m' := c
            leftArm := A_G'.reverse
            hinge := .backward h_A_G
            rightArm := B_G
            decompose := rfl
            leftBackward := hL_back
            hingeIntoSource := by simp
            rightDirected := hB_G_dir }
        -- Now show π.IsBifurcation.
        have hπ_supp : π.support = A_G'.support.reverse.dropLast
                                  ++ (m_A :: B_G.support) := by
          change (A_G'.reverse.append (Walk.cons (.backward h_A_G) B_G)).support = _
          rw [Walk.support_append, Walk.support_reverse, Walk.support_cons]
        have hA_supp : A.support = c :: A'.support := by
          rw [hA_form]; simp [Walk.support_cons]
        -- v ∉ A'.support.dropLast (derived from hA_endpoint).
        have hv_not_dropLast_A' : v ∉ A'.support.dropLast := by
          have := hA_endpoint
          rw [hA_supp, List.dropLast_cons_of_ne_nil A'.support_ne_nil] at this
          simp only [List.mem_cons, not_or] at this
          exact this.2
        have hv_not_dropLast_AG' : v ∉ A_G'.support.dropLast := by
          rw [hA_G'_supp]; exact hv_not_dropLast_A'
        have hv_not_in_B_G : v ∉ B_G.support := by
          rw [hB_G_supp]
          intro hv_in
          exact Walk.support_disjoint_W_of_isDirected B hB_dir hc_not_v v hv_in rfl
        -- v ∉ π.support.tail
        have hv_not_tail : v ∉ π.support.tail := by
          rw [hπ_supp]
          -- Case split on whether A_G'.support.reverse.dropLast is empty.
          by_cases hdL : A_G'.support.reverse.dropLast = []
          · rw [hdL, List.nil_append, List.tail_cons]
            -- Goal: v ∉ B_G.support. But we also need to handle that maybe m_A = v?
            -- Actually if dropLast is empty, A_G'.support.reverse has length ≤ 1.
            -- A_G'.support.reverse has same length as A_G'.support = A_G'.length + 1 ≥ 1.
            -- So A_G'.support.reverse has length 1, meaning A_G' = nil m_A and m_A = v.
            -- After tail_cons: the list is B_G.support. v ∉ B_G.support. ✓
            exact hv_not_in_B_G
          · rw [Walk.list_tail_append_of_ne_nil _ _ hdL]
            simp only [List.mem_append, List.mem_cons, not_or]
            refine ⟨?_, ?_, hv_not_in_B_G⟩
            · -- v ∉ A_G'.support.reverse.dropLast.tail
              -- Convert via list identities to membership in A_G'.support.dropLast.
              intro hv_in
              apply hv_not_dropLast_AG'
              -- A_G'.support.reverse.dropLast.tail
              --   = A_G'.support.tail.reverse.tail (by list_reverse_dropLast)
              --   = A_G'.support.tail.dropLast.reverse
              --       (by list_reverse_tail applied to support.tail)
              --   = A_G'.support.dropLast.tail.reverse (by list_tail_dropLast)
              rw [Walk.list_reverse_dropLast, Walk.list_reverse_tail,
                  Walk.list_tail_dropLast] at hv_in
              rw [List.mem_reverse] at hv_in
              exact List.mem_of_mem_tail hv_in
            · -- v ≠ m_A: when dropLast non-empty (length ≥ 1), m_A is at position 0.
              intro hvm
              apply hv_not_dropLast_AG'
              -- A_G'.length ≥ 1 follows from hdL (dropLast non-empty).
              have hpos : 1 ≤ A_G'.length := by
                by_contra hneg
                push Not at hneg
                apply hdL
                have : A_G'.support.reverse.dropLast.length = 0 := by
                  rw [List.length_dropLast, List.length_reverse, A_G'.support_length]
                  omega
                exact List.length_eq_zero_iff.mp this
              have hsupp_form : A_G'.support = m_A :: A_G'.support.tail :=
                Walk.support_eq_cons_tail _
              have htail_ne : A_G'.support.tail ≠ [] := by
                intro h
                rw [h] at hsupp_form
                have : A_G'.support.length = 1 := by rw [hsupp_form]; simp
                rw [A_G'.support_length] at this
                omega
              have h_mA_in : m_A ∈ A_G'.support.dropLast := by
                rw [hsupp_form, List.dropLast_cons_of_ne_nil htail_ne]
                exact List.mem_cons_self
              exact hvm.symm ▸ h_mA_in
        have hw_not_in_A : w ∉ A.support := fun hw_in =>
          Walk.support_disjoint_W_of_isDirected A hA_dir hc_not_w w hw_in rfl
        have hv_not_in_B : v ∉ B.support := fun hv_in =>
          Walk.support_disjoint_W_of_isDirected B hB_dir hc_not_v v hv_in rfl
        have hw_not_in_AG' : w ∉ A_G'.support := by
          rw [hA_G'_supp]
          intro hw_in
          have : w ∈ A.support := by rw [hA_supp]; exact List.mem_cons_of_mem _ hw_in
          exact hw_not_in_A this
        have hw_not_dropLast : w ∉ π.support.dropLast := by
          rw [hπ_supp]
          -- π.support.dropLast = A_G'.support.reverse.dropLast ++ (m_A :: B_G.support).dropLast.
          -- The (m_A :: B_G.support).dropLast = m_A :: B_G.support.dropLast
          -- (since B_G.support non-empty).
          rw [List.dropLast_append_of_ne_nil (by simp : (m_A :: B_G.support) ≠ [])]
          rw [List.dropLast_cons_of_ne_nil B_G.support_ne_nil]
          simp only [List.mem_append, List.mem_cons, not_or]
          refine ⟨?_, ?_, ?_⟩
          · intro hw_in
            apply hw_not_in_AG'
            have h1 : w ∈ A_G'.support.reverse := List.dropLast_subset _ hw_in
            exact List.mem_reverse.mp h1
          · intro hwm
            apply hw_not_in_AG'
            rw [hwm]
            -- m_A is the first vertex of A_G'.support
            cases A_G' with
            | nil _ => simp
            | cons _ _ => simp
          · -- w ∉ B_G.support.dropLast: from hB_endpoint (w ∉ B.support.dropLast)
            rw [hB_G_supp]
            exact hB_endpoint
        -- Now construct the BifurcationWitness and finish.
        have hb : π.IsBifurcation := ⟨hvw, hv_not_tail, hw_not_dropLast, ⟨bw_explicit⟩⟩
        refine ⟨π, hb, ?_, hc_ne_w_set⟩
        -- bifurcationSource π hb = some c.
        obtain ⟨hm'_eq, hh_not_bidir⟩ :=
          Walk.m'_eq_of_isAllBackward_append_cons_backward
            A_G'.reverse hL_back h_A_G B_G hB_G_dir hb.2.2.2.some
        have hinge_intoSource := (hb.2.2.2.some).hingeIntoSource
        cases hh : (hb.2.2.2.some).hinge with
        | forward _ =>
          rw [hh] at hinge_intoSource
          simp at hinge_intoSource
        | backward h' =>
          unfold Walk.bifurcationSource
          simp only [hh]
          exact congrArg some hm'_eq
        | bidir _ =>
          rw [hh] at hh_not_bidir
          simp at hh_not_bidir

end CDMG

end Causality
