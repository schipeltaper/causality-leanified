import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Filter
import Chapter3_GraphTheory.Section3_1.WalkPredicates
import Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks
import Chapter3_GraphTheory.Section3_3.LabelRoman

-- TeX statement: claim_3_23_statement_SigmaOpenPathWalk.tex
-- TeX proof:     claim_3_23_proof_SigmaOpenPathWalk.tex

/-!
# $\sigma$-open path / walk / walk-with-colliders-in-$C$ equivalence (claim_3_23)

This file formalises *claim 3.23* (the LN's Proposition
`prp:sigma_opens` / `\restateprpsigmaopens`) of the lecture
notes (Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`,
lines 1382 -- 1393): a `\begin{claimmark}` Proposition sitting
between def_3_18 ($i\sigma$-separation) and claim_3_24
(the consumer Remark that cites this proposition twice).

The LN block reads:

> Let $G = (J, V, E, L)$ be a CDMG. For $C \subseteq J \cup V$
> and $w_1, w_2 \in J \cup V$, the following are equivalent:
> 1. there exists a $C$-$\sigma$-open *path* between $w_1$ and
>    $w_2$ in $G$;
> 2. there exists a $C$-$\sigma$-open *walk* between $w_1$ and
>    $w_2$ in $G$;
> 3. there exists a $C$-$\sigma$-open *walk* between $w_1$ and
>    $w_2$ in $G$ such that all its colliders lie in $C$ (and
>    not just in $\Anc^G(C)$).

The statement itself encodes the LN's "the following are
equivalent" surface using Mathlib's `List.TFAE`, the canonical
Lean idiom for an $n$-way equivalence between numbered clauses.

This file formalises **the statement only**; the proof body is
`sorry`. The proof is the future Manager-B prover's job; the
LN's proof (`graphs.tex` lines 1655 -- 1673) discharges
`3 → 2` and `1 → 2` trivially ("paths are walks"), `2 → 3` by
expanding each $\Anc^G(C) \setminus C$ collider through a
directed-path-to-$C$-and-back insertion, and `2 → 1` by
*invoking `lem:replace_walk`*, the major lemma of claim_3_27
(title `LabelRoman`) which sits *later* in `data.json` than
this row. The prover will either reorder the dependency or
discharge the (more easily-proven) `1 → 2` / `3 → 2` halves
first.

## What this file contributes

A single `theorem`, `sigmaOpens_TFAE`, expressing the
three-way equivalence as `List.TFAE` of three existentials:

```
(G : CDMG α) (C : Set α) (w₁ w₂ : α) :
  List.TFAE
    [ (∃ π : Walk G w₁ w₂, π.IsPath ∧ π.IsSigmaOpen C),
      (∃ π : Walk G w₁ w₂, π.IsSigmaOpen C),
      (∃ π : Walk G w₁ w₂, π.IsSigmaOpen C ∧
         ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C) ]
```

The three list entries are direct one-to-one transliterations
of the LN's clauses 1, 2, 3. None of them are wrapped in a
named `def`; see the design block below for why inlining is
the deliberate choice.

The body is `sorry`. Per-pair extractions at the call site
read `((G.sigmaOpens_TFAE C w₁ w₂).out 0 1)` for the
path $\leftrightarrow$ walk equivalence (clauses 1 and 2) and
`.out 1 2` for the walk $\leftrightarrow$
walk-with-colliders-in-$C$ equivalence (clauses 2 and 3) --
exactly the two equivalences that claim_3_24's Remark cites
by name.

## Downstream usage

* **claim_3_24** (`graphs.tex` lines 1395 -- 1412) -- the
  Remark immediately following this proposition. It cites
  `prp:sigma_opens` *twice*:
    - once to rewrite `IsISigmaSeparated`'s
      universal-over-walks as a universal-over-paths
      ("$A \isPerp_G B \given C$ is equivalent to ... every
      *path* from a node in $A$ to a node in $J \cup B$ is
      $C$-$\sigma$-blocked"), which contraposes through
      `(sigmaOpens_TFAE _ _ _ _).out 0 1`; and
    - once to extract a shortest $C$-$\sigma$-open path / a
      shortest $C$-$\sigma$-open walk-with-colliders-in-$C$
      from a `IsNotISigmaSeparated` hypothesis, which uses
      `.out 0 1` and `.out 1 2` in sequence.
  Both extractions are first-class projections on a single
  TFAE theorem -- which is the principal ergonomic reason
  we picked the TFAE shape over two separate biconditionals
  (see the design block).
* **claim_3_25** ($i\sigma$-separation under marginalization,
  `graphs.tex` lines 1414 -- 1422) -- the LN's proof
  constructs $\sigma$-open walks on a marginalized graph
  from $\sigma$-open walks on the original, and then converts
  between path-existence and walk-existence at the boundary;
  consumes `(sigmaOpens_TFAE _ _ _ _).out 0 1`.
* **Chapter 4 (CBNs,
  `causal_bayesian_networks.tex`)** -- the Markov property
  for a CBN equates conditional independence in the joint
  distribution to graphical $i\sigma$-separation. Several
  statements of the CBN-Markov property and its corollaries
  are stated in terms of paths (rather than walks) because
  the path formulation is the one practitioners check; the
  equivalence here is the bridge.
* **Chapter 5 (do-calculus, `do-calculus.tex` +
  `proof-do-calculus.tex`)** -- the do-calculus rules cite
  $i\sigma$-separation premises; whenever a rule is applied
  by exhibiting a $\sigma$-open path, this proposition is
  the translation step.
* **Chapter 6 -- 7 (identification,
  `adjustment-criteria.tex` / `id-algorithm.tex`)** -- the
  backdoor / front-door / general adjustment criteria are
  most naturally stated as the *absence* of a $\sigma$-open
  path satisfying particular constraints; this proposition
  lets those statements ride on top of
  `IsISigmaSeparated`'s walk universal without re-deriving
  the path / walk equivalence in each criterion's proof.
* **Chapters 11 -- 16 (discovery,
  `causal_relations.tex` / `minimal_sep_sets.tex` /
  `fci.tex`)** -- FCI's skeleton-phase and orientation-phase
  reasoning operate on *paths*, because there are only
  finitely many of them in a finite graph (the LN's own
  pragmatic remark at `graphs.tex` line 1410: "in practice
  we usually check if every path is $C$-$\sigma$-blocked").
  This proposition lets the FCI-side path reasoning
  interoperate with the chapter-3 walk-based separation
  predicates.
* **Mirror in subsection 3.4** -- claim_3_30 (`graphs.tex`
  line 1745) explicitly cites "a similar result from
  Proposition \ref{prp:sigma_opens} holds for
  $id$-separation as well", i.e. the same three-way TFAE
  but with $d$-blocking in place of $\sigma$-blocking. The
  shape we pick here propagates to that future $id$-version.

## Style precedents

* `Chapter3_GraphTheory.Section3_3.SigmaSeparationSymmetric`
  (claim_3_22) -- the immediately preceding claim in this
  subsection. Same one-row claim-file pattern: module-level
  docstring with "What this file contributes" /
  "Downstream usage" / "Style precedents" sections;
  per-declaration `-- claim_*` comment header; LN block
  reproduced verbatim in a `/- ... -/` quote; design-choice
  block above the theorem; body `sorry` at the
  formalizer-worker stage. Stays in `namespace CDMG` so the
  theorem dot-projects on the CDMG argument
  (`G.sigmaOpens_TFAE`).
* `Chapter3_GraphTheory.Section3_3.ISigmaSeparation`
  (def_3_18) -- source of the surrounding
  $i\sigma$-separation surface; the per-`abbrev` design
  block at `IsSigmaSeparated` flags claim_3_23 / claim_3_24
  as principal consumers and the `Footnote rationale`
  paragraph in the module docstring is *why* the walk
  universals in `IsISigmaSeparated` are stated the way they
  are, which then licenses the existentials in *this* claim
  to be stated symmetrically across the three clauses.
* `Chapter3_GraphTheory.Section3_3.SigmaBlockedWalks`
  (def_3_17) -- source of `Walk.IsSigmaOpen`,
  `Walk.IsColliderAt`, `Walk.nodeAt` -- the three per-walk
  primitives this proposition's clauses inline.
* `Chapter3_GraphTheory.Section3_1.WalkPredicates`
  (def_3_4, item 5) -- source of `Walk.IsPath` (defined as
  `support.Nodup`), which clause 1 inlines alongside
  `IsSigmaOpen`.
* Mathlib `Mathlib.Data.List.TFAE` -- source of
  `List.TFAE`, the formal embodiment of the LN's "the
  following are equivalent" idiom. The `tfae_have` /
  `tfae_finish` tactics (in `Mathlib.Tactic.TFAE`, *not*
  imported here -- the future prover will import them) are
  the standard discharge mechanism for a TFAE goal and let
  the LN proof's "3 → 2 trivial", "1 → 2 trivial",
  "2 → 3 (collider-replacement)", "2 → 1 (`lem:replace_walk`)"
  structure be transcribed implication-by-implication into
  Lean tactics.

## Infrastructure note for the future prover

The LN's proof (`graphs.tex` lines 1655 -- 1673) opens with
`3 → 2` and `1 → 2` as trivial ("paths are walks"); these
two implications need only that a path is a special case of
a walk -- the existential witness in clauses 1 / 3 is
literally usable as the existential witness in clause 2
because `π.IsPath ∧ π.IsSigmaOpen C → π.IsSigmaOpen C` and
`(π.IsSigmaOpen C ∧ ∀ k, ...) → π.IsSigmaOpen C` are pure
projections.

The substantive directions are:

* **`2 → 3`** -- given a $C$-$\sigma$-open walk $\pi$, walk
  each collider $v_k \in \Anc^G(C) \setminus C$ on $\pi$
  *out* to $C$ via a directed path
  $v_k \tuh \cdots \tuh c_k \in C$ and back, replacing the
  collider with a longer sub-walk in which $v_k$ still
  appears as a collider but now sits *strictly inside* a
  $\Anc^G(C)$-witness with $c_k \in C$ on either side as a
  non-collider. Iterating over all such colliders produces a
  walk with every collider in $C$. The infrastructure needed
  is (i) the existence of the directed-path-to-$C$ witness
  ("a node in $\Anc^G(C)$ is the start of a directed walk to
  $C$"; this is the definitional content of
  `Section3_1.FamilyReachability.AncSet`'s reverse direction
  and is likely already available as a single-line lemma in
  that file or in `FamilyDirect`), and (ii) a walk-splicing
  /concatenation operation that preserves the per-position
  collider / non-collider / arrowhead structure
  (`Walk.append` from `Section3_1.Walks` is the foundation;
  the prover may need a `Walk.spliceAtPosition` helper that
  does not yet exist).
* **`2 → 1`** -- given a $C$-$\sigma$-open walk $\pi$ that
  is not yet a path, the LN's proof invokes
  `lem:replace_walk` (= claim_3_27, title `LabelRoman`):
  for any node $w$ appearing more than once on $\pi$, the
  subwalk between the first and last occurrences of $w$ can
  be replaced by a directed path within $\Sc^G(w)$,
  preserving $\sigma$-openness. The replacement strictly
  reduces the number of repeated nodes (by at least one),
  and iterating terminates with a $\sigma$-open *path*.
  **`lem:replace_walk` / claim_3_27 is currently
  unformalized and sits *later* in `data.json` than this
  row.** The prover has two options:
    1. **Reorder.** Move claim_3_27 ahead of claim_3_23 in
       the working sequence (the data.json's natural-order
       sequencing is not a hard dependency; reordering is
       the planner's call).
    2. **Push forward.** Prove `1 ↔ 2` and `2 ↔ 3` as
       far as possible without `lem:replace_walk`. Both
       directions of `1 ↔ 2` are immediate one-way
       (`1 → 2` is "paths are walks"; `2 → 1` needs
       `lem:replace_walk`), so this option only discharges
       the *trivial* halves. The TFAE proof would still
       need a `sorry` for the `2 → 1` arrow until
       claim_3_27 lands.

The `lem:replace_walk` dependency is also the reason the
workspace's `Critical dependency` section flagged this row
as a non-blocker for the *statement* phase but a real
question for the proof phase. This file is the statement;
the dependency is the prover's to navigate.

The infrastructure that *is* already in place:
`Walk.IsPath`, `Walk.IsSigmaOpen`, `Walk.IsColliderAt`,
`Walk.nodeAt`, `Walk.append`, `CDMG.AncSet`, plus the
chapter-3 `IsDirected` and `Sc^G` infrastructure (in
`Section3_1.FamilyReachability` /
`Section3_1.FamilyDistrict`) -- enough for the prover to
state every helper lemma the LN's proof relies on, given
`lem:replace_walk`.
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace CDMG

/-- Private helper used by `2 ⟹ 3` in `sigmaOpens_TFAE`: if
`v ∈ AncSet^G(C)` but `v ∉ C`, there is a *directed* walk `σ` from
`v` to some `c ∈ C` of positive length whose interior avoids `C`.
The witness is obtained by truncating any directed walk from `v`
to some `c₀ ∈ C` at the first interior position landing in `C`
(well-founded recursion on the walk length). -/
private theorem exists_directed_to_C_no_inner
    (G : CDMG α) (C : Set α) {v : α}
    (h_v_anc : v ∈ G.AncSet C) (h_v_not : v ∉ C) :
    ∃ (c : α) (σ : Walk G v c), c ∈ C ∧ σ.IsDirected ∧ 0 < σ.length ∧
      ∀ ℓ, 0 < ℓ → ℓ < σ.length → σ.nodeAt ℓ ∉ C := by
  classical
  rw [CDMG.mem_AncSet] at h_v_anc
  obtain ⟨c₀, h_c₀_in_C, h_v_in_Anc_c₀⟩ := h_v_anc
  obtain ⟨_, σ₀, h_σ₀_dir⟩ := h_v_in_Anc_c₀
  -- Strong induction on walk length; package as a universal statement.
  suffices h : ∀ n, ∀ (c : α) (σ : Walk G v c), σ.IsDirected → c ∈ C →
      σ.length ≤ n →
      ∃ (c' : α) (σ' : Walk G v c'), c' ∈ C ∧ σ'.IsDirected ∧ 0 < σ'.length ∧
        ∀ ℓ, 0 < ℓ → ℓ < σ'.length → σ'.nodeAt ℓ ∉ C from
    h σ₀.length c₀ σ₀ h_σ₀_dir h_c₀_in_C le_rfl
  intro n
  induction n with
  | zero =>
    intro c σ _h_dir h_c h_len
    -- Length-0 directed walk forces `v = c`, contradicting `v ∉ C ∧ c ∈ C`.
    exfalso
    have h_eq : σ.length = 0 := Nat.le_zero.mp h_len
    have h_v_eq_c : v = c := by
      have h0 : σ.nodeAt 0 = v := σ.nodeAt_zero
      have h1 : σ.nodeAt σ.length = c := σ.nodeAt_length
      rw [h_eq] at h1
      exact h0.symm.trans h1
    exact h_v_not (h_v_eq_c ▸ h_c)
  | succ n ih =>
    intro c σ h_dir h_c h_len
    by_cases h_inner : ∃ ℓ, 0 < ℓ ∧ ℓ < σ.length ∧ σ.nodeAt ℓ ∈ C
    · -- Some interior position is in `C`: recurse on the (shorter) prefix.
      obtain ⟨ℓ, h_ℓ_pos, h_ℓ_lt, h_ℓ_in_C⟩ := h_inner
      have h_ℓ_le : ℓ ≤ σ.length := le_of_lt h_ℓ_lt
      have h_pre_dir : (σ.prefix ℓ).IsDirected :=
        Walk.isDirected_prefix σ ℓ h_dir
      have h_pre_len : (σ.prefix ℓ).length = ℓ := Walk.length_prefix σ h_ℓ_le
      have h_pre_le_n : (σ.prefix ℓ).length ≤ n := by rw [h_pre_len]; omega
      -- σ.prefix ℓ : Walk G v (σ.nodeAt ℓ); ends in C via h_ℓ_in_C.
      exact ih (σ.nodeAt ℓ) (σ.prefix ℓ) h_pre_dir h_ℓ_in_C h_pre_le_n
    · -- No interior is in `C`; σ itself witnesses the claim.
      have h_σ_pos : 0 < σ.length := by
        rcases Nat.eq_zero_or_pos σ.length with h0 | h0
        · exfalso
          have h_v_eq_c : v = c := by
            have h_nz : σ.nodeAt 0 = v := σ.nodeAt_zero
            have h_nl : σ.nodeAt σ.length = c := σ.nodeAt_length
            rw [h0] at h_nl
            exact h_nz.symm.trans h_nl
          exact h_v_not (h_v_eq_c ▸ h_c)
        · exact h0
      refine ⟨c, σ, h_c, h_dir, h_σ_pos, ?_⟩
      intro ℓ h_ℓ_pos h_ℓ_lt h_ℓ_in_C
      exact h_inner ⟨ℓ, h_ℓ_pos, h_ℓ_lt, h_ℓ_in_C⟩

/-- The `2 ⟹ 3` arrow of `sigmaOpens_TFAE`, factored out as a private
lemma: from a `C`-σ-open walk `π : Walk G w₁ w₂`, construct a
`C`-σ-open walk whose every collider's vertex lies in `C`. The proof
follows the LN's collider-replacement argument: at every bad collider
`v_k` (vertex in `Anc^G(C) \ C`), splice a detour `σ ⧺ σ.reverse`
between positions `k` and `k`, where `σ` is a directed walk from
`v_k` to some `c ∈ C` with no interior in `C` (provided by
`exists_directed_to_C_no_inner`). The detour preserves σ-openness
(joints become non-colliders, interior of σ are right- or left-chain
non-colliders not in `C`, the turn-around vertex `c` is a new
collider but lies in `C`) and strictly decreases the bad-collider
count. -/
private theorem reduce_to_all_colliders_in_C
    (G : CDMG α) (C : Set α) (w₁ w₂ : α) (π₀ : Walk G w₁ w₂)
    (h_open₀ : π₀.IsSigmaOpen C) :
    ∃ π' : Walk G w₁ w₂, π'.IsSigmaOpen C ∧
      ∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ C := by
  classical
  -- The bad-collider count: how many positions `k ∈ {0,…,π.length}` are
  -- colliders on `π` whose vertex is *not* in `C`.
  let badN : ∀ {a b : α}, Walk G a b → ℕ := fun π =>
    ((Finset.range (π.length + 1)).filter
      (fun k => π.IsColliderAt k ∧ π.nodeAt k ∉ C)).card
  -- Helper: if `π.IsColliderAt k`, then `k ≤ π.length` (a collider needs the
  -- joint of two consecutive steps; out-of-range positions return False).
  have isColliderAt_le_length :
      ∀ {a b : α} (π : Walk G a b) (k : ℕ), π.IsColliderAt k → k ≤ π.length := by
    intro a b π
    induction π with
    | nil _ => intro k h; simp at h
    | cons s p ih =>
      intro k h_coll
      cases p with
      | nil _ => simp at h_coll
      | cons s' p' =>
        cases k with
        | zero => simp [Walk.length_cons]
        | succ k =>
          cases k with
          | zero => simp [Walk.length_cons]
          | succ k =>
            rw [Walk.isColliderAt_cons_cons_succ_succ] at h_coll
            have := ih (k + 1) h_coll
            simp only [Walk.length_cons] at this ⊢
            omega
  -- Strong induction on `n` with `badN π ≤ n`.
  suffices forall_n : ∀ (n : ℕ), ∀ (π : Walk G w₁ w₂), π.IsSigmaOpen C →
      badN π ≤ n →
      ∃ π' : Walk G w₁ w₂, π'.IsSigmaOpen C ∧
        ∀ k, π'.IsColliderAt k → π'.nodeAt k ∈ C from
    forall_n (badN π₀) π₀ h_open₀ le_rfl
  intro n
  induction n with
  | zero =>
    intro π h_open h_card
    -- badN π = 0 ⇒ filter is empty ⇒ every collider's node is in `C`.
    have h_card_zero : badN π = 0 := Nat.le_zero.mp h_card
    have h_filter_empty :
        (Finset.range (π.length + 1)).filter
            (fun k => π.IsColliderAt k ∧ π.nodeAt k ∉ C) = ∅ :=
      Finset.card_eq_zero.mp h_card_zero
    refine ⟨π, h_open, ?_⟩
    intro k h_coll
    by_contra h_not_in_C
    have hk_le : k ≤ π.length := isColliderAt_le_length π k h_coll
    have h_mem : k ∈ (Finset.range (π.length + 1)).filter
        (fun k' => π.IsColliderAt k' ∧ π.nodeAt k' ∉ C) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by omega), h_coll, h_not_in_C⟩
    rw [h_filter_empty] at h_mem
    exact Finset.notMem_empty _ h_mem
  | succ n ih =>
    intro π h_open h_card
    by_cases h_zero : badN π = 0
    · -- Same as the base case.
      have h_filter_empty :
          (Finset.range (π.length + 1)).filter
              (fun k => π.IsColliderAt k ∧ π.nodeAt k ∉ C) = ∅ :=
        Finset.card_eq_zero.mp h_zero
      refine ⟨π, h_open, ?_⟩
      intro k h_coll
      by_contra h_not_in_C
      have hk_le : k ≤ π.length := isColliderAt_le_length π k h_coll
      have h_mem : k ∈ (Finset.range (π.length + 1)).filter
          (fun k' => π.IsColliderAt k' ∧ π.nodeAt k' ∉ C) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (by omega), h_coll, h_not_in_C⟩
      rw [h_filter_empty] at h_mem
      exact Finset.notMem_empty _ h_mem
    · -- badN π ≥ 1: pick a bad collider, splice in a detour `σ ⧺ σ.reverse`.
      -- 1. Extract a bad collider position k.
      have h_nonempty :
          ((Finset.range (π.length + 1)).filter
              (fun k => π.IsColliderAt k ∧ π.nodeAt k ∉ C)).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero h_zero)
      obtain ⟨k, hk_mem⟩ := h_nonempty
      rw [Finset.mem_filter] at hk_mem
      obtain ⟨hk_range, h_coll_k, h_not_in_C_k⟩ := hk_mem
      have hk_le : k ≤ π.length := by
        have := Finset.mem_range.mp hk_range; omega
      have hk_lt : k < π.length :=
        Walk.isColliderAt_lt_length π h_coll_k
      have hk_pos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h_pos
        · exfalso; rw [h0] at h_coll_k
          exact (Walk.isNonColliderAt_zero π).2 h_coll_k
        · exact h_pos
      -- 2. Extract σ : v_k → c.
      have h_node_anc : π.nodeAt k ∈ G.AncSet C := h_open.1 k h_coll_k
      obtain ⟨c, σ, h_c_in_C, h_σ_dir, h_σ_pos, h_no_inner_C⟩ :=
        exists_directed_to_C_no_inner G C h_node_anc h_not_in_C_k
      -- 3. Construct σ_full and W.
      set σ_full : Walk G (π.nodeAt k) (π.nodeAt k) := σ.append σ.reverse
        with hσ_full_def
      set W : Walk G w₁ w₂ :=
        (π.prefix k).append (σ_full.append (π.suffix k)) with hW_def
      have h_σ_full_len : σ_full.length = σ.length + σ.length := by
        rw [hσ_full_def, Walk.length_append, Walk.length_reverse]
      have h_σ_full_pos : 0 < σ_full.length := by rw [h_σ_full_len]; omega
      have h_c_mem_G : c ∈ G := (Walk.endpoints_mem_G_of_pos σ h_σ_pos).2
      have h_c_in_AncSet : c ∈ G.AncSet C := by
        rw [CDMG.mem_AncSet]
        exact ⟨c, h_c_in_C, CDMG.self_mem_Anc h_c_mem_G⟩
      have h_pre_len : (π.prefix k).length = k := Walk.length_prefix π hk_le
      have h_suf_len : (π.suffix k).length = π.length - k := Walk.length_suffix π hk_le
      have h_W_len : W.length = k + σ_full.length + (π.length - k) := by
        rw [hW_def, Walk.length_append, Walk.length_append,
            h_pre_len, h_suf_len]
        omega
      -- 4. Decompose σ for joint analysis.
      obtain ⟨w_σ_first, s_σ_first, rest_σ_first, h_σ_eq⟩ :=
        Walk.walk_pos_eq_cons σ h_σ_pos
      have h_s_σ_first_fwd : s_σ_first.IsForward := by
        have h_dir' := h_σ_dir
        rw [h_σ_eq] at h_dir'
        cases s_σ_first with
        | forward _ => simp
        | backward _ => simp at h_dir'
        | bidir _ => simp at h_dir'
      -- σ_full's first step is s_σ_first.
      have h_σ_full_first :
          σ_full = Walk.cons s_σ_first (rest_σ_first.append σ.reverse) := by
        rw [hσ_full_def, h_σ_eq, Walk.cons_append]
      -- σ_full's last step is s_σ_first.reverse via the decomposition:
      --   σ_full = (cons s_σ_first (rest_σ_first ⧺ rest_σ_first.reverse))
      --              ⧺ (cons s_σ_first.reverse (nil _))
      have h_σ_full_last :
          σ_full = (Walk.cons s_σ_first
              (rest_σ_first.append rest_σ_first.reverse)).append
                (Walk.cons s_σ_first.reverse (Walk.nil (π.nodeAt k))) := by
        rw [hσ_full_def, h_σ_eq, Walk.reverse_cons]
        rw [Walk.cons_append, Walk.cons_append, Walk.append_assoc]
      -- Length of the prefix in the right-end decomposition above.
      have h_σ_full_pre_len :
          (Walk.cons s_σ_first
              (rest_σ_first.append rest_σ_first.reverse)).length =
            σ_full.length - 1 := by
        rw [Walk.length_cons, Walk.length_append, Walk.length_reverse]
        rw [h_σ_full_len]
        have h_rest_len : rest_σ_first.length = σ.length - 1 := by
          have h1 : σ.length = rest_σ_first.length + 1 := by
            rw [h_σ_eq, Walk.length_cons]
          omega
        omega
      -- s_σ_first.reverse is backward.
      have h_s_σ_first_rev_back : s_σ_first.reverse.IsBackward := by
        cases s_σ_first with
        | forward _ => simp
        | backward _ => simp at h_s_σ_first_fwd
        | bidir _ => simp at h_s_σ_first_fwd
      -- =========================================================
      -- Prove W.IsSigmaOpen C: per-position case analysis.
      -- =========================================================
      have hW_open : W.IsSigmaOpen C := by
        refine ⟨?_, ?_⟩
        · -- Clause 1: collider on W ⇒ node ∈ AncSet C.
          intro p h_coll_W
          have h_p_lt_W : p < W.length := Walk.isColliderAt_lt_length W h_coll_W
          rcases lt_or_ge p k with hp_lt_k | hp_ge_k
          · -- p < k: prefix region.
            rw [hW_def] at h_coll_W
            have h_π_coll :=
              (Walk.isColliderAt_splice_pre π σ_full hk_le hp_lt_k).mp h_coll_W
            rw [hW_def, Walk.nodeAt_splice_pre π σ_full hk_le (le_of_lt hp_lt_k)]
            exact h_open.1 p h_π_coll
          · rcases lt_or_ge p (k + σ_full.length) with hp_lt_mid | hp_ge_mid
            · -- k ≤ p < k + σ_full.length: middle/joints.
              rcases Nat.eq_or_lt_of_le hp_ge_k with hp_eq_k | hp_gt_k
              · -- p = k: left joint. NOT a collider, contradiction.
                exfalso
                subst hp_eq_k
                -- Decompose π.prefix k.
                have h_pre_pos : 1 ≤ (π.prefix k).length := by
                  rw [h_pre_len]; omega
                obtain ⟨w_pre, p_pre, s_left, h_pre_eq⟩ :=
                  Walk.walk_pos_eq_append_last (π.prefix k) h_pre_pos
                have h_p_pre_len : p_pre.length = k - 1 := by
                  have h1 : (π.prefix k).length = p_pre.length +
                      (Walk.cons s_left (Walk.nil (π.nodeAt k))).length := by
                    rw [h_pre_eq, Walk.length_append]
                  rw [h_pre_len] at h1
                  simp [Walk.length_cons, Walk.length_nil] at h1; omega
                -- Reassemble W to expose joint at k.
                set big_rest := (rest_σ_first.append σ.reverse).append (π.suffix k)
                  with hbig_def
                have hW_form :
                    W = p_pre.append
                      (Walk.cons s_left (Walk.cons s_σ_first big_rest)) := by
                  show (π.prefix k).append (σ_full.append (π.suffix k)) =
                    p_pre.append (Walk.cons s_left
                      (Walk.cons s_σ_first big_rest))
                  rw [h_pre_eq, h_σ_full_first]
                  rw [Walk.append_assoc, Walk.cons_append, Walk.nil_append,
                      Walk.cons_append]
                have h_at_k :
                    (p_pre.append (Walk.cons s_left
                      (Walk.cons s_σ_first big_rest))).IsColliderAt
                        (p_pre.length + 1) := by
                  rw [show p_pre.length + 1 = k from by omega, ← hW_form]
                  exact h_coll_W
                rw [Walk.isColliderAt_append_cons_cons_one] at h_at_k
                obtain ⟨_, h_src⟩ := h_at_k
                cases s_σ_first with
                | forward _ => simp at h_src
                | backward _ => simp at h_s_σ_first_fwd
                | bidir _ => simp at h_s_σ_first_fwd
              · -- k < p < k + σ_full.length: interior of σ_full.
                set p' := p - k with hp'_def
                have hp'_pos : 0 < p' := by omega
                have hp'_lt : p' < σ_full.length := by omega
                have hp_eq : k + p' = p := by omega
                have h_σ_full_coll : σ_full.IsColliderAt p' := by
                  rw [← hp_eq, hW_def] at h_coll_W
                  exact (Walk.isColliderAt_splice_mid π σ_full hk_le
                    hp'_pos hp'_lt).mp h_coll_W
                rcases lt_or_ge p' σ.length with hp'_lt_σ | hp'_ge_σ
                · -- p' < σ.length: σ.IsColliderAt p', contradicts σ.IsDirected.
                  exfalso
                  rw [hσ_full_def] at h_σ_full_coll
                  rw [Walk.isColliderAt_append_lt_length _ _ hp'_lt_σ]
                    at h_σ_full_coll
                  exact Walk.not_isColliderAt_of_isDirected σ p' h_σ_dir
                    h_σ_full_coll
                · rcases Nat.eq_or_lt_of_le hp'_ge_σ with hp'_eq_σ | hp'_gt_σ
                  · -- p' = σ.length: turn-around. Node = c ∈ AncSet C.
                    have h_σ_le_full : σ.length ≤ σ_full.length := by
                      rw [h_σ_full_len]; omega
                    rw [hW_def, ← hp_eq, ← hp'_eq_σ]
                    rw [Walk.nodeAt_splice_mid π σ_full hk_le h_σ_le_full]
                    rw [hσ_full_def, Walk.nodeAt_append_le σ σ.reverse le_rfl]
                    rw [Walk.nodeAt_length]
                    exact h_c_in_AncSet
                  · -- σ.length < p' < σ_full.length: interior of σ.reverse.
                    exfalso
                    have h_shift_pos : 0 < p' - σ.length := by omega
                    have h_p'_rw : p' = σ.length + (p' - σ.length) := by omega
                    rw [hσ_full_def, h_p'_rw,
                        Walk.isColliderAt_append_shift_pos σ σ.reverse
                          (p' - σ.length) h_shift_pos] at h_σ_full_coll
                    rw [Walk.isColliderAt_reverse_iff] at h_σ_full_coll
                    exact Walk.not_isColliderAt_of_isDirected σ _ h_σ_dir
                      h_σ_full_coll
            · rcases Nat.eq_or_lt_of_le hp_ge_mid with hp_eq_mid | hp_gt_mid
              · -- p = k + σ_full.length: right joint. NOT a collider.
                exfalso
                subst hp_eq_mid
                -- Decompose π.suffix k.
                have h_suf_pos : 1 ≤ (π.suffix k).length := by
                  rw [h_suf_len]; omega
                obtain ⟨w_suf, s_suf, rest_suf, h_suf_eq⟩ :=
                  Walk.walk_pos_eq_cons (π.suffix k) h_suf_pos
                -- W's structure exposing the right joint:
                -- W = ((π.prefix k).append (cons s_σ_first
                --       (rest_σ_first.append rest_σ_first.reverse))).append
                --     (cons s_σ_first.reverse (cons s_suf rest_suf))
                have hW_form :
                    W = ((π.prefix k).append (Walk.cons s_σ_first
                      (rest_σ_first.append rest_σ_first.reverse))).append
                      (Walk.cons s_σ_first.reverse
                        (Walk.cons s_suf rest_suf)) := by
                  show (π.prefix k).append (σ_full.append (π.suffix k)) = _
                  rw [h_σ_full_last, h_suf_eq, Walk.append_assoc,
                      ← Walk.append_assoc, Walk.cons_append, Walk.nil_append]
                -- Length of the left half.
                have h_left_len :
                    ((π.prefix k).append (Walk.cons s_σ_first
                      (rest_σ_first.append rest_σ_first.reverse))).length =
                      k + σ_full.length - 1 := by
                  rw [Walk.length_append, h_pre_len, h_σ_full_pre_len]
                  omega
                -- Apply the joint-collider lemma.
                rw [hW_form] at h_coll_W
                rw [show (k + σ_full.length : ℕ) =
                  ((π.prefix k).append (Walk.cons s_σ_first
                    (rest_σ_first.append rest_σ_first.reverse))).length + 1
                  from by rw [h_left_len]; omega] at h_coll_W
                rw [Walk.isColliderAt_append_cons_cons_one] at h_coll_W
                obtain ⟨h_target, _⟩ := h_coll_W
                cases s_σ_first with
                | forward _ => simp at h_target
                | backward _ => simp at h_s_σ_first_fwd
                | bidir _ => simp at h_s_σ_first_fwd
              · -- p > k + σ_full.length: suffix region.
                set p' := p - k - σ_full.length with hp'_def
                have hp'_pos : 0 < p' := by omega
                have hp_eq : k + σ_full.length + p' = p := by omega
                have h_π_coll : π.IsColliderAt (k + p') := by
                  rw [← hp_eq, hW_def] at h_coll_W
                  exact (Walk.isColliderAt_splice_suf π σ_full hk_le
                    hp'_pos).mp h_coll_W
                have h_bound : p' ≤ π.length - k := by
                  rw [h_W_len] at h_p_lt_W; omega
                rw [hW_def, ← hp_eq]
                rw [Walk.nodeAt_splice_suf π σ_full hk_le hk_le h_bound]
                exact h_open.1 (k + p') h_π_coll
        · -- Clause 2: blockable non-collider on W ⇒ node ∉ C.
          intro p h_block_W
          have h_noncoll_W : W.IsNonColliderAt p := h_block_W.1
          have h_p_le_W : p ≤ W.length := h_noncoll_W.1
          rcases lt_or_ge p k with hp_lt_k | hp_ge_k
          · -- p < k: transports from h_open.2.
            rw [hW_def, Walk.nodeAt_splice_pre π σ_full hk_le (le_of_lt hp_lt_k)]
            have h_π_block : π.IsBlockableNonColliderAt p := by
              refine ⟨⟨by omega, ?_⟩, ?_⟩
              · intro h_π_coll
                have : W.IsColliderAt p := by
                  rw [hW_def]
                  exact (Walk.isColliderAt_splice_pre π σ_full
                    hk_le hp_lt_k).mpr h_π_coll
                exact h_noncoll_W.2 this
              · intro h_π_unblock
                have : W.IsUnblockableNonColliderAt p := by
                  rw [hW_def]
                  exact (Walk.isUnblockableNonColliderAt_splice_pre π σ_full
                    hk_le hp_lt_k).mpr h_π_unblock
                exact h_block_W.2 this
            exact h_open.2 p h_π_block
          · rcases lt_or_ge p (k + σ_full.length) with hp_lt_mid | hp_ge_mid
            · rcases Nat.eq_or_lt_of_le hp_ge_k with hp_eq_k | hp_gt_k
              · -- p = k: node = v_k ∉ C.
                subst hp_eq_k
                rw [hW_def, Walk.nodeAt_splice_pre π σ_full hk_le (le_refl k)]
                exact h_not_in_C_k
              · -- k < p < k + σ_full.length: middle interior.
                set p' := p - k with hp'_def
                have hp'_pos : 0 < p' := by omega
                have hp'_lt : p' < σ_full.length := by omega
                have hp_eq : k + p' = p := by omega
                rw [hW_def, ← hp_eq]
                rw [Walk.nodeAt_splice_mid π σ_full hk_le (le_of_lt hp'_lt)]
                rcases lt_or_ge p' σ.length with hp'_lt_σ | hp'_ge_σ
                · -- p' < σ.length: σ_full.nodeAt p' = σ.nodeAt p' ∉ C.
                  rw [hσ_full_def, Walk.nodeAt_append_le σ σ.reverse
                    (le_of_lt hp'_lt_σ)]
                  exact h_no_inner_C p' hp'_pos hp'_lt_σ
                · rcases Nat.eq_or_lt_of_le hp'_ge_σ with hp'_eq_σ | hp'_gt_σ
                  · -- p' = σ.length: this position is a collider, contradiction.
                    exfalso
                    -- σ_full.IsColliderAt σ.length via the joint at the turn-around.
                    have h_σ_full_coll_at_σ : σ_full.IsColliderAt σ.length := by
                      -- Decompose σ = σ_pre_last.append (cons s_σ_last (nil c))
                      obtain ⟨w_σ_last, σ_pre_last, s_σ_last, h_σ_last_eq⟩ :=
                        Walk.walk_pos_eq_append_last σ h_σ_pos
                      have h_σ_pre_last_len : σ_pre_last.length = σ.length - 1 := by
                        have h1 : σ.length = σ_pre_last.length +
                            (Walk.cons s_σ_last (Walk.nil c)).length := by
                          rw [h_σ_last_eq, Walk.length_append]
                        simp [Walk.length_cons, Walk.length_nil] at h1; omega
                      -- s_σ_last is forward.
                      have h_s_σ_last_fwd : s_σ_last.IsForward := by
                        have h_dir' := h_σ_dir
                        rw [h_σ_last_eq] at h_dir'
                        have ⟨_, h_dir_tail⟩ := Walk.isDirected_split_append
                          σ_pre_last (Walk.cons s_σ_last (Walk.nil c)) h_dir'
                        cases s_σ_last with
                        | forward _ => simp
                        | backward _ => simp at h_dir_tail
                        | bidir _ => simp at h_dir_tail
                      -- σ.reverse = cons s_σ_last.reverse σ_pre_last.reverse.
                      have h_σ_rev_eq : σ.reverse =
                          Walk.cons s_σ_last.reverse σ_pre_last.reverse := by
                        rw [h_σ_last_eq, Walk.reverse_append, Walk.reverse_cons,
                            Walk.reverse_nil, Walk.nil_append, Walk.cons_append,
                            Walk.nil_append]
                      -- σ_full decomposition exposing the turn-around joint.
                      have h_σ_full_eq :
                          σ_full = σ_pre_last.append
                            (Walk.cons s_σ_last
                              (Walk.cons s_σ_last.reverse σ_pre_last.reverse)) := by
                        rw [hσ_full_def, h_σ_rev_eq, h_σ_last_eq,
                            Walk.append_assoc]
                        rfl
                      rw [h_σ_full_eq]
                      rw [show σ.length = σ_pre_last.length + 1 from by omega]
                      rw [Walk.isColliderAt_append_cons_cons_one]
                      refine ⟨?_, ?_⟩
                      · cases s_σ_last with
                        | forward _ => simp
                        | backward _ => simp at h_s_σ_last_fwd
                        | bidir _ => simp at h_s_σ_last_fwd
                      · cases s_σ_last with
                        | forward _ => simp [WalkStep.reverse]
                        | backward _ => simp at h_s_σ_last_fwd
                        | bidir _ => simp at h_s_σ_last_fwd
                    have h_p_eq : p = k + σ.length := by omega
                    have h_W_coll : W.IsColliderAt p := by
                      rw [h_p_eq, hW_def]
                      exact (Walk.isColliderAt_splice_mid π σ_full hk_le h_σ_pos
                        (by rw [h_σ_full_len]; omega)).mpr h_σ_full_coll_at_σ
                    exact h_noncoll_W.2 h_W_coll
                  · -- σ.length < p' < σ_full.length: σ_full.nodeAt p' on return leg.
                    rw [hσ_full_def]
                    have h_p'_rw : p' = σ.length + (p' - σ.length) := by omega
                    rw [h_p'_rw, Walk.nodeAt_append_add_left σ σ.reverse
                      (p' - σ.length)]
                    -- σ.reverse.nodeAt (p' - σ.length) = σ.nodeAt (σ.length - (p' - σ.length))
                    rw [Walk.nodeAt_reverse σ
                      (by omega : p' - σ.length ≤ σ.length)]
                    apply h_no_inner_C
                    · omega
                    · omega
            · rcases Nat.eq_or_lt_of_le hp_ge_mid with hp_eq_mid | hp_gt_mid
              · -- p = k + σ_full.length: node = v_k ∉ C.
                subst hp_eq_mid
                rw [hW_def, Walk.nodeAt_splice_mid π σ_full hk_le
                  (le_refl σ_full.length), Walk.nodeAt_length]
                exact h_not_in_C_k
              · -- p > k + σ_full.length: suffix region.
                set p' := p - k - σ_full.length with hp'_def
                have hp'_pos : 0 < p' := by omega
                have hp_eq : k + σ_full.length + p' = p := by omega
                have h_bound : p' ≤ π.length - k := by
                  rw [h_W_len] at h_p_le_W; omega
                rw [hW_def, ← hp_eq]
                rw [Walk.nodeAt_splice_suf π σ_full hk_le hk_le h_bound]
                have h_π_block : π.IsBlockableNonColliderAt (k + p') := by
                  refine ⟨⟨by omega, ?_⟩, ?_⟩
                  · intro h_π_coll
                    have h_W_coll : W.IsColliderAt p := by
                      rw [hW_def, ← hp_eq]
                      exact (Walk.isColliderAt_splice_suf π σ_full hk_le
                        hp'_pos).mpr h_π_coll
                    exact h_noncoll_W.2 h_W_coll
                  · intro h_π_unblock
                    have h_W_unblock : W.IsUnblockableNonColliderAt p := by
                      rw [hW_def, ← hp_eq]
                      exact (Walk.isUnblockableNonColliderAt_splice_suf π σ_full
                        hk_le hp'_pos).mpr h_π_unblock
                    exact h_block_W.2 h_W_unblock
                exact h_open.2 (k + p') h_π_block
      -- =========================================================
      -- Prove badN W ≤ n via strict-decrease counting.
      -- =========================================================
      have h_badN_lt : badN W ≤ n := by
        -- k is a bad collider position of π.
        have h_k_in_bad_π :
            k ∈ (Finset.range (π.length + 1)).filter
              (fun k' => π.IsColliderAt k' ∧ π.nodeAt k' ∉ C) := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_range.mpr (by omega), h_coll_k, h_not_in_C_k⟩
        -- Key helper: no bad collider on W in the middle region [k, k+σ_full.length].
        have h_no_bad_middle :
            ∀ p, k ≤ p → p ≤ k + σ_full.length →
              ¬ (W.IsColliderAt p ∧ W.nodeAt p ∉ C) := by
          intro p hp_ge hp_le ⟨h_coll, h_not_in⟩
          rcases Nat.eq_or_lt_of_le hp_ge with hp_eq_k | hp_gt_k
          · -- p = k: left joint, W not collider.
            subst hp_eq_k
            have h_pre_pos : 1 ≤ (π.prefix k).length := by
              rw [h_pre_len]; omega
            obtain ⟨w_pre, p_pre, s_left, h_pre_eq⟩ :=
              Walk.walk_pos_eq_append_last (π.prefix k) h_pre_pos
            have h_p_pre_len : p_pre.length = k - 1 := by
              have h1 : (π.prefix k).length = p_pre.length +
                  (Walk.cons s_left (Walk.nil (π.nodeAt k))).length := by
                rw [h_pre_eq, Walk.length_append]
              rw [h_pre_len] at h1
              simp [Walk.length_cons, Walk.length_nil] at h1; omega
            set big_rest := (rest_σ_first.append σ.reverse).append (π.suffix k)
            have hW_form :
                W = p_pre.append
                  (Walk.cons s_left (Walk.cons s_σ_first big_rest)) := by
              show (π.prefix k).append (σ_full.append (π.suffix k)) =
                p_pre.append (Walk.cons s_left
                  (Walk.cons s_σ_first big_rest))
              rw [h_pre_eq, h_σ_full_first]
              rw [Walk.append_assoc, Walk.cons_append, Walk.nil_append,
                  Walk.cons_append]
            have h_at_p :
                (p_pre.append (Walk.cons s_left
                  (Walk.cons s_σ_first big_rest))).IsColliderAt
                    (p_pre.length + 1) := by
              rw [show p_pre.length + 1 = k from by omega, ← hW_form]
              exact h_coll
            rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
            obtain ⟨_, h_src⟩ := h_at_p
            cases s_σ_first with
            | forward _ => simp at h_src
            | backward _ => simp at h_s_σ_first_fwd
            | bidir _ => simp at h_s_σ_first_fwd
          · -- k < p ≤ k + σ_full.length.
            set p' := p - k with hp'_def
            have hp'_pos : 0 < p' := by omega
            have hp_eq : k + p' = p := by omega
            rcases Nat.eq_or_lt_of_le hp_le with hp_eq_mid | hp_lt_mid
            · -- p = k + σ_full.length: right joint, W not collider.
              subst hp_eq_mid
              have h_suf_pos : 1 ≤ (π.suffix k).length := by
                rw [h_suf_len]; omega
              obtain ⟨w_suf, s_suf, rest_suf, h_suf_eq⟩ :=
                Walk.walk_pos_eq_cons (π.suffix k) h_suf_pos
              have hW_form :
                  W = ((π.prefix k).append (Walk.cons s_σ_first
                    (rest_σ_first.append rest_σ_first.reverse))).append
                    (Walk.cons s_σ_first.reverse
                      (Walk.cons s_suf rest_suf)) := by
                show (π.prefix k).append (σ_full.append (π.suffix k)) = _
                rw [h_σ_full_last, h_suf_eq, Walk.append_assoc,
                    ← Walk.append_assoc, Walk.cons_append, Walk.nil_append]
              have h_left_len :
                  ((π.prefix k).append (Walk.cons s_σ_first
                    (rest_σ_first.append rest_σ_first.reverse))).length =
                    k + σ_full.length - 1 := by
                rw [Walk.length_append, h_pre_len, h_σ_full_pre_len]
                omega
              rw [hW_form] at h_coll
              rw [show (k + σ_full.length : ℕ) =
                ((π.prefix k).append (Walk.cons s_σ_first
                  (rest_σ_first.append rest_σ_first.reverse))).length + 1
                from by rw [h_left_len]; omega] at h_coll
              rw [Walk.isColliderAt_append_cons_cons_one] at h_coll
              obtain ⟨h_target, _⟩ := h_coll
              cases s_σ_first with
              | forward _ => simp at h_target
              | backward _ => simp at h_s_σ_first_fwd
              | bidir _ => simp at h_s_σ_first_fwd
            · -- k < p < k + σ_full.length: middle interior.
              have hp'_lt : p' < σ_full.length := by omega
              rw [← hp_eq, hW_def] at h_coll
              have h_σ_full_coll :=
                (Walk.isColliderAt_splice_mid π σ_full hk_le hp'_pos
                  hp'_lt).mp h_coll
              rcases lt_or_ge p' σ.length with hp'_lt_σ | hp'_ge_σ
              · -- p' < σ.length: σ.IsColliderAt p', contradicts σ.IsDirected.
                rw [hσ_full_def] at h_σ_full_coll
                rw [Walk.isColliderAt_append_lt_length _ _ hp'_lt_σ]
                  at h_σ_full_coll
                exact Walk.not_isColliderAt_of_isDirected σ p' h_σ_dir
                  h_σ_full_coll
              · rcases Nat.eq_or_lt_of_le hp'_ge_σ with hp'_eq_σ | hp'_gt_σ
                · -- p' = σ.length: turn-around, node = c ∈ C contradicts ∉ C.
                  have h_node_eq : W.nodeAt p = c := by
                    rw [hW_def, ← hp_eq, ← hp'_eq_σ]
                    rw [Walk.nodeAt_splice_mid π σ_full hk_le
                      (by rw [h_σ_full_len]; omega : σ.length ≤ σ_full.length)]
                    rw [hσ_full_def, Walk.nodeAt_append_le σ σ.reverse le_rfl]
                    exact Walk.nodeAt_length σ
                  rw [h_node_eq] at h_not_in
                  exact h_not_in h_c_in_C
                · -- σ.length < p' < σ_full.length: σ.reverse interior.
                  have h_shift_pos : 0 < p' - σ.length := by omega
                  have h_p'_rw : p' = σ.length + (p' - σ.length) := by omega
                  rw [hσ_full_def, h_p'_rw,
                      Walk.isColliderAt_append_shift_pos σ σ.reverse
                        (p' - σ.length) h_shift_pos] at h_σ_full_coll
                  rw [Walk.isColliderAt_reverse_iff] at h_σ_full_coll
                  exact Walk.not_isColliderAt_of_isDirected σ _ h_σ_dir
                    h_σ_full_coll
        -- Define the injection from bad_W to bad_π.erase k.
        let f : ℕ → ℕ := fun p => if p < k then p else p - σ_full.length
        -- f maps bad_W into bad_π.erase k.
        have h_image_in :
            ∀ p ∈ ((Finset.range (W.length + 1)).filter
                (fun p' => W.IsColliderAt p' ∧ W.nodeAt p' ∉ C)),
              f p ∈ ((Finset.range (π.length + 1)).filter
                  (fun k' => π.IsColliderAt k' ∧ π.nodeAt k' ∉ C)).erase k := by
          intro p hp_mem
          rw [Finset.mem_filter] at hp_mem
          obtain ⟨hp_range, hp_coll, hp_not_in⟩ := hp_mem
          have hp_le_W : p ≤ W.length := by
            have := Finset.mem_range.mp hp_range; omega
          rcases lt_or_ge p k with hp_lt_k | hp_ge_k
          · -- p < k.
            simp only [f, if_pos hp_lt_k]
            rw [Finset.mem_erase, Finset.mem_filter]
            refine ⟨by omega, Finset.mem_range.mpr (by omega), ?_, ?_⟩
            · rw [hW_def] at hp_coll
              exact (Walk.isColliderAt_splice_pre π σ_full hk_le hp_lt_k).mp
                hp_coll
            · rw [hW_def, Walk.nodeAt_splice_pre π σ_full hk_le
                (le_of_lt hp_lt_k)] at hp_not_in
              exact hp_not_in
          · -- p ≥ k. Use h_no_bad_middle to derive p > k + σ_full.length.
            have hp_gt_mid : p > k + σ_full.length := by
              by_contra hp_not_gt
              push_neg at hp_not_gt
              exact h_no_bad_middle p hp_ge_k hp_not_gt ⟨hp_coll, hp_not_in⟩
            have hp_not_lt : ¬ p < k := by omega
            simp only [f, if_neg hp_not_lt]
            rw [Finset.mem_erase, Finset.mem_filter]
            set p' := p - k - σ_full.length with hp'_def
            have hp'_pos : 0 < p' := by omega
            have hp_eq : k + σ_full.length + p' = p := by omega
            have h_bound : p' ≤ π.length - k := by
              rw [h_W_len] at hp_le_W; omega
            have h_shift_eq : p - σ_full.length = k + p' := by omega
            rw [h_shift_eq]
            refine ⟨by omega, Finset.mem_range.mpr (by omega), ?_, ?_⟩
            · rw [← hp_eq, hW_def] at hp_coll
              exact (Walk.isColliderAt_splice_suf π σ_full hk_le hp'_pos).mp
                hp_coll
            · rw [← hp_eq, hW_def] at hp_not_in
              rw [Walk.nodeAt_splice_suf π σ_full hk_le hk_le h_bound] at hp_not_in
              exact hp_not_in
        -- f is injective on bad_W.
        have h_inj :
            Set.InjOn f ↑((Finset.range (W.length + 1)).filter
                (fun p' => W.IsColliderAt p' ∧ W.nodeAt p' ∉ C)) := by
          intro p₁ hp₁ p₂ hp₂ h_feq
          simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_range,
            Set.mem_setOf_eq] at hp₁ hp₂
          obtain ⟨hp₁_range, hp₁_coll, hp₁_not_in⟩ := hp₁
          obtain ⟨hp₂_range, hp₂_coll, hp₂_not_in⟩ := hp₂
          rcases lt_or_ge p₁ k with hp₁_lt | hp₁_ge
          · rcases lt_or_ge p₂ k with hp₂_lt | hp₂_ge
            · -- both < k.
              simp only [f, if_pos hp₁_lt, if_pos hp₂_lt] at h_feq
              exact h_feq
            · -- p₁ < k, p₂ ≥ k.
              exfalso
              have hp₂_gt_mid : p₂ > k + σ_full.length := by
                by_contra hp₂_not_gt
                push_neg at hp₂_not_gt
                exact h_no_bad_middle p₂ hp₂_ge hp₂_not_gt ⟨hp₂_coll, hp₂_not_in⟩
              have hp₂_not_lt : ¬ p₂ < k := by omega
              simp only [f, if_pos hp₁_lt, if_neg hp₂_not_lt] at h_feq
              omega
          · rcases lt_or_ge p₂ k with hp₂_lt | hp₂_ge
            · -- p₁ ≥ k, p₂ < k: symmetric.
              exfalso
              have hp₁_gt_mid : p₁ > k + σ_full.length := by
                by_contra hp₁_not_gt
                push_neg at hp₁_not_gt
                exact h_no_bad_middle p₁ hp₁_ge hp₁_not_gt ⟨hp₁_coll, hp₁_not_in⟩
              have hp₁_not_lt : ¬ p₁ < k := by omega
              simp only [f, if_neg hp₁_not_lt, if_pos hp₂_lt] at h_feq
              omega
            · -- both ≥ k.
              have hp₁_gt_mid : p₁ > k + σ_full.length := by
                by_contra hp₁_not_gt
                push_neg at hp₁_not_gt
                exact h_no_bad_middle p₁ hp₁_ge hp₁_not_gt ⟨hp₁_coll, hp₁_not_in⟩
              have hp₂_gt_mid : p₂ > k + σ_full.length := by
                by_contra hp₂_not_gt
                push_neg at hp₂_not_gt
                exact h_no_bad_middle p₂ hp₂_ge hp₂_not_gt ⟨hp₂_coll, hp₂_not_in⟩
              have hp₁_not_lt : ¬ p₁ < k := by omega
              have hp₂_not_lt : ¬ p₂ < k := by omega
              simp only [f, if_neg hp₁_not_lt, if_neg hp₂_not_lt] at h_feq
              omega
        -- Apply cardinality lemmas.
        have h_card_le :
            ((Finset.range (W.length + 1)).filter
                (fun p' => W.IsColliderAt p' ∧ W.nodeAt p' ∉ C)).card ≤
            (((Finset.range (π.length + 1)).filter
                (fun k' => π.IsColliderAt k' ∧ π.nodeAt k' ∉ C)).erase k).card :=
          Finset.card_le_card_of_injOn f h_image_in h_inj
        have h_erase_card :
            (((Finset.range (π.length + 1)).filter
                (fun k' => π.IsColliderAt k' ∧ π.nodeAt k' ∉ C)).erase k).card =
              ((Finset.range (π.length + 1)).filter
                (fun k' => π.IsColliderAt k' ∧ π.nodeAt k' ∉ C)).card - 1 :=
          Finset.card_erase_of_mem h_k_in_bad_π
        have h_badN_W_def : badN W = ((Finset.range (W.length + 1)).filter
            (fun p' => W.IsColliderAt p' ∧ W.nodeAt p' ∉ C)).card := rfl
        have h_badN_π_def : badN π = ((Finset.range (π.length + 1)).filter
            (fun k' => π.IsColliderAt k' ∧ π.nodeAt k' ∉ C)).card := rfl
        omega
      exact ih W hW_open h_badN_lt

-- claim_3_23
-- title: SigmaOpenPathWalk -- three-way TFAE between
-- $\sigma$-open path, $\sigma$-open walk, and $\sigma$-open
-- walk with all colliders in $C$
--
-- `G.sigmaOpens_TFAE C w₁ w₂` packages the LN's "the
-- following are equivalent" enumeration over three
-- $\sigma$-open-existence clauses into a single
-- `List.TFAE`. The clauses, in the LN's order:
--
--   1. there exists a $C$-$\sigma$-open *path* from $w_1$ to
--      $w_2$ in $G$;
--   2. there exists a $C$-$\sigma$-open *walk* from $w_1$ to
--      $w_2$ in $G$;
--   3. there exists a $C$-$\sigma$-open *walk* from $w_1$ to
--      $w_2$ in $G$ all of whose colliders lie in $C$ (i.e.
--      strictly in $C$, not merely in $\Anc^G(C)$).
--
-- All three propositions inline their per-walk content; no
-- intermediate "is a $\sigma$-open path" / "is a $\sigma$-open
-- walk with colliders in $C$" predicates are introduced (see
-- the design block).
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(claim_3_23, lines 1382 -- 1393):

  % claim_3_23
  \begin{claimmark}
  \begin{restatable}{Prp}{restateprpsigmaopens}\label{prp:sigma_opens}
    Let $G=(J,V,E,L)$ be a CDMG. For $C \subseteq J \cup V$, and
    $w_1, w_2 \in J \cup V$, the following are equivalent:
    \begin{enumerate}
        \item there exists a $C$-$\sigma$-open \emph{path}
          between $w_1$ and $w_2$ in $G$;
        \item there exists a $C$-$\sigma$-open \emph{walk}
          between $w_1$ and $w_2$ in $G$;
        \item there exists a $C$-$\sigma$-open \emph{walk}
          between $w_1$ and $w_2$ in $G$ such that all its
          colliders lie in $C$ (and not just in $\Anc^G(C)$).
    \end{enumerate}
  \end{restatable}
  \end{claimmark}
-/
--
-- ## Design choice
--
-- * **Status flag (post-`add_design_choice_comments`).** The
--   declaration below is **statement-only**: the body is
--   exactly `sorry`. `review_design` and `verify_equivalence`
--   both PASSed on the statement; the design-rationale
--   comments in this block are now filled in (this pass).
--   The *proof* is the next manager's job and is gated on
--   `lem:replace_walk` / claim_3_27 (`LabelRoman`) for the
--   `2 → 1` arrow -- see the module docstring's
--   "Infrastructure note for the future prover" section. A
--   reader pattern-matching on `solved=yes` for this row
--   should know: statement formalised, design recorded,
--   proof pending.
--
-- * **`List.TFAE` over three propositions, not a chain of
--   `Iff`s, not a conjunction of two `Iff`s, not two
--   separately-named biconditionals.** The LN's prose
--   "the following are equivalent" followed by a numbered
--   enumeration is *exactly* the mathematical idiom that
--   Mathlib's `List.TFAE` is built to formalise (cf.
--   `Mathlib.Data.List.TFAE`'s opening docstring: "The
--   Following Are Equivalent ... TFAE l means
--   `∀ x ∈ l, ∀ y ∈ l, x ↔ y`"). Three alternatives were
--   considered:
--     (A) a chain `(P₁ ↔ P₂) ↔ (P₂ ↔ P₃)` -- *not* the same
--         logical content as TFAE; the chained-`↔` form is
--         well-known *not* to associate the way mathematical
--         "the following are equivalent" prose does
--         (`Iff.trans` does not chain through a third `Iff`
--         in the obvious way). Ruled out as a transcription
--         error of the LN.
--     (B) two separately-named biconditionals,
--         e.g. `sigma_open_path_iff_walk` (= LN clauses
--         1 $\Leftrightarrow$ 2) and
--         `sigma_open_walk_iff_all_colliders_in_C`
--         (= LN clauses 2 $\Leftrightarrow$ 3). This mirrors
--         the LN proof's pivot structure (proves
--         `2 → 1`, `1 → 2`, `2 → 3`, `3 → 2`), and was the
--         tied-runner-up. Rejected because (i) it loses the
--         LN's "*the following are equivalent*" surface
--         (the LN names a single proposition, not two);
--         (ii) it forces a privileged-pivot reading
--         (clause 2 = the always-LHS of both bicons), which
--         the LN's flat enumeration does not endorse; and
--         (iii) downstream consumers cite the proposition
--         *by name* and by *clause number* -- not as two
--         distinct theorems. Concretely:
--           - claim_3_24's Remark (`graphs.tex` lines
--             1395 -- 1412) cites "by Proposition
--             \ref{prp:sigma_opens}" *twice*, once
--             projecting (1) $\Leftrightarrow$ (2) and once
--             projecting (2) $\Leftrightarrow$ (3) -- the
--             ergonomic move on a single-named TFAE is
--             `.out 0 1` and `.out 1 2`;
--           - claim_3_25's proof (`graphs.tex` line 1495)
--             cites "Proposition \ref{prp:sigma_opens}(3)"
--             literally by clause number to extract a walk
--             with colliders in $C$;
--           - claim_3_28's acyclification proof
--             (`graphs.tex` lines 2140, 2178) cites
--             "Proposition \ref{prp:sigma_opens}(3)" twice
--             (once for each direction of an equivalence),
--             again by clause number.
--         Every one of these consumers is a literal
--         transliteration of `(G.sigmaOpens_TFAE C w₁ w₂)
--         .out i j` with `i, j ∈ {0, 1, 2}`. Two separately-
--         named theorems would (a) force the consumer
--         pattern to choose *which* theorem name to invoke
--         per citation, and (b) silently lose the
--         clause-number labelling on which the LN's `(3)`-
--         style citations ride. The TFAE shape preserves
--         both.
--     (C) a single bundled `theorem sigmaOpens` returning a
--         conjunction `(P₁ ↔ P₂) ∧ (P₂ ↔ P₃)`. Equivalent
--         in content to TFAE for `n = 3`, but loses (i) the
--         "the following are equivalent" *surface*
--         (the conjunction-of-`Iff`s reads as "we have two
--         unrelated equivalences"), and (ii) the
--         `tfae_have` / `tfae_finish` tactic ecosystem that
--         lets the future prover discharge each implication
--         arrow in the LN's order without manually
--         assembling the `And.intro`. Rejected as a
--         strictly worse rendering of the same content.
--   `List.TFAE` is the LN-faithful choice: literally
--   "the following are equivalent", literally a list of the
--   three propositions, and *symmetric* across all three
--   clauses (no clause privileged as a pivot in the
--   *statement* -- the LN proof picks clause 2 as the
--   pivot, but the statement does not bake that in). The
--   `review_design` verifier downstream is the natural
--   place to sanity-check the choice; the workspace's plan
--   explicitly flagged this as the design decision deferred
--   to the formalizer, with `List.TFAE` as the manager's
--   weak prior. We confirm.
--
-- * **Clause order in the `List.TFAE` argument matches the
--   LN's enumeration literally (path / walk / walk-with-
--   colliders-in-$C$), with a 0-based offset on the
--   `.out` projection.** Mathlib's `List.TFAE` indexes into
--   its argument list starting at `0`; the LN's enumerated
--   clauses are 1-based. Concretely:
--     - LN clause (1) (path) = list index `0`;
--     - LN clause (2) (walk) = list index `1`;
--     - LN clause (3) (walk-colliders-in-$C$) = list index `2`.
--   So a downstream caller transliterating
--   "by Proposition \ref{prp:sigma_opens}(1) $\Leftrightarrow$
--   (2)" writes `(G.sigmaOpens_TFAE C w₁ w₂).out 0 1`;
--   "(2) $\Leftrightarrow$ (3)" is `.out 1 2`; and
--   "(1) $\Leftrightarrow$ (3)" is `.out 0 2`. The
--   alternative -- reordering the list as walk / path /
--   walk-colliders-in-$C$ to put the LN's "pivot" clause
--   first -- was rejected because it would break the
--   citation pattern: every downstream `\ref{prp:sigma_opens}
--   (3)` (e.g. `graphs.tex` lines 1495, 2140, 2178) would
--   silently project the *wrong* list entry. Keeping the
--   list literal-LN-order means the 0-based offset is the
--   *only* thing a reader has to remember, and the LN-clause
--   $\leftrightarrow$ Lean-index correspondence is a single
--   subtraction.
--
-- * **Each clause inlined as an `∃ π : Walk G w₁ w₂, ...`,
--   no named auxiliary predicates.** Three obvious helper
--   `def`s suggest themselves -- `IsSigmaOpenPath`,
--   `IsSigmaOpenWalk`, `IsSigmaOpenWalkAllCollidersIn` --
--   and were considered. Rejected because:
--     (i) the LN's clauses are already short, readable
--         compositions of *existing* predicates
--         (`Walk.IsPath`, `Walk.IsSigmaOpen`,
--         `Walk.IsColliderAt`, `Walk.nodeAt`); adding a
--         third layer would force downstream consumers to
--         unfold the wrapper before applying the existing
--         per-walk lemmas (claim_3_24's Remark in particular
--         needs to *negate* clause 1 into a universal-
--         over-paths to get the LN's "every path is
--         $\sigma$-blocked" phrasing -- the negation reads
--         cleanly off the inlined `∃ π, π.IsPath ∧ ...`
--         but would require a `simp`/`unfold` step against
--         a wrapper);
--     (ii) clause 3's "all colliders in $C$" predicate is a
--         *single-use* universal -- this is the *only*
--         place in chapters 3 -- 16 where the LN reasons
--         about it. A named `def` for a single-use predicate
--         pollutes the namespace and adds a layer of
--         indirection for no reuse gain;
--     (iii) the formalizer prompt explicitly directs
--         "do not introduce new definitions ... unless you
--         find a strong design-choice reason". No such
--         reason exists for any of the three.
--   If a downstream chapter ever wants the named wrapper
--   (e.g. chapter 16 reasoning about "the set of
--   $\sigma$-open paths"), it can introduce a local `def`
--   then -- *after* observing actual reuse.
--   Pointers to where the inlined predicates live, so a
--   reader of clause 1 / 3 does not have to grep:
--     - `Walk.IsPath` (clause 1) is `π.support.Nodup` -- a
--       one-line `def` at
--       `Section3_1/WalkPredicates.lean` line 466.
--     - `Walk.IsSigmaOpen` (clauses 1 / 2 / 3) is the
--       def_3_17 conjunction (collider / blockable / non-
--       unblockable conditions) at
--       `Section3_3/SigmaBlockedWalks.lean`.
--     - `Walk.IsColliderAt` (clause 3) is the position-
--       indexed collider predicate at
--       `Section3_3/CollidersAndNon.lean` line 189.
--     - `Walk.nodeAt` (clause 3) is the position-indexed
--       node accessor at
--       `Section3_3/SigmaBlockedWalks.lean` line 258.
--
-- * **Naming `sigmaOpens_TFAE`.** Three considerations
--   converge:
--     (i) the LN's LaTeX label is `prp:sigma_opens` /
--         macro `\restateprpsigmaopens`, which camelCases to
--         `sigmaOpens` -- matching the LN's name surface
--         literally;
--     (ii) Mathlib's TFAE-theorem convention adds a
--         `_TFAE` / `_tfae` suffix
--         (cf. `t1Space_TFAE`, `isLoop_tfae`,
--         `isColoop_tfae`) so the shape is recognisable in
--         the goal display and the consumer's `.out`
--         indexing reads as a TFAE projection;
--     (iii) downstream consumers cite the proposition by
--         the LN-name "Proposition \ref{prp:sigma_opens}";
--         keeping the LN name in the Lean identifier (with
--         the `_TFAE` suffix tagging the shape) makes the
--         citation chain obvious.
--   The capital-`TFAE` variant matches `t1Space_TFAE`
--   (Topology) over the lowercase `isLoop_tfae`
--   (Combinatorics) for no strong reason beyond
--   topology-side polish; either would work.
--
-- * **`G`-first, then `C`, then `w₁`, `w₂` -- explicit binders.**
--   `G : CDMG α` first matches every other `CDMG`-level
--   declaration (`G.IsISigmaSeparated`, `G.IsSigmaSeparated`,
--   `G.isSigmaSeparated_symm`, ...) and lets callers write
--   `G.sigmaOpens_TFAE C w₁ w₂` in dot-projection. `C` comes
--   second to match the LN prose order ("For
--   $C \subseteq J \cup V$, and $w_1, w_2 \in J \cup V$") and
--   the per-walk `IsSigmaOpen C` argument order. `w₁` and
--   `w₂` are explicit because no membership hypothesis pins
--   them down (compare `IsISigmaSeparated` where strict-
--   implicit `⦃v w⦄` are pinned by `v ∈ A` / `w ∈ G.J ∪ B`);
--   here the endpoints are part of the proposition's data,
--   not derivable from a hypothesis.
--
-- * **Subscript names `w₁ w₂`, not `v w` or `w₁' w₂'`.**
--   The LN uses $w_1, w_2$ explicitly; Lean's Unicode
--   subscripts render the LN notation literally
--   (`w₁` ↔ $w_1$, `w₂` ↔ $w_2$). Subscript binders are
--   precedented in `Section3_2` (e.g.
--   `Marginalization.lean` uses `v₁ v₂` elsewhere in the
--   chapter). Renaming to `v w` would diverge from the LN
--   surface at zero formal cost.
--
-- * **`w₁, w₂ ∈ G.J ∪ G.V` is a caller's side-condition,
--   not a type-level guard.** Same paradigm as
--   `IsSigmaBlocked` / `IsSigmaOpen` / `IsISigmaSeparated`:
--   the LN's preamble "$w_1, w_2 \in J \cup V$" is a
--   side-condition on the inputs, not a baked-in
--   restriction. The `verify_equivalence` verifier
--   explicitly endorsed *not* lifting it into a subtype.
--   There are two off-graph cases to track, and TFAE holds
--   vacuously in both:
--     - **Different off-graph endpoints
--       ($w_1 \neq w_2$).** No `Walk G w₁ w₂` inhabitant
--       exists -- every `WalkStep` constructor carries an
--       `EdgeOutOf` / `EdgeInto` / `L`-proof that pins both
--       endpoints into $G.J \cup G.V$, so the existential
--       in each clause is empty. All three propositions are
--       vacuously `False`; TFAE on three `False`s is `True`.
--     - **Same off-graph endpoint ($w_1 = w_2$, neither in
--       $G.J \cup G.V$).** The reflexive walk `Walk.nil`
--       (zero edges) inhabits `Walk G w₁ w₁` even for an
--       off-graph `w₁`. But `Walk.nil` has zero colliders
--       (vacuous over `IsColliderAt k`), is a path (its
--       support is a singleton, hence `Nodup`), and is
--       trivially $\sigma$-open (no positions to fail any
--       collider / non-collider check). It therefore
--       witnesses *all three* clauses simultaneously, and
--       TFAE again holds (this time with all three clauses
--       vacuously `True`).
--   Either way the statement is well-typed and logically
--   valid without the LN's preamble; the LN preamble does
--   no work at the statement level. Downstream consumers
--   that *use* the proposition non-vacuously will already
--   have $w_1, w_2 \in G.J \cup G.V$ in scope (e.g.
--   claim_3_24 gets it from `IsISigmaSeparated`'s `v ∈ A`
--   and `w ∈ G.J ∪ B` hypotheses).
--
-- * **`C : Set α`, not `{C : Set α // C ⊆ G.J ∪ G.V}`.**
--   Same convention as `IsSigmaBlocked` / `IsSigmaOpen` /
--   `IsISigmaSeparated`; see the design block on
--   `IsISigmaSeparated` (`ISigmaSeparation.lean` lines
--   206 -- 219). Carrying a subtype on every separation-
--   related signature pollutes downstream consumers for no
--   proof-ergonomic gain.
--
-- * **Clause 3's "all colliders in $C$" predicate uses
--   `π.nodeAt k ∈ C`, not `π.nodeAt k ∈ G.AncSet C`.** The
--   LN deliberately contrasts the two: "all its colliders
--   lie in $C$ (and not just in $\Anc^G(C)$)". Clause 2's
--   collider condition (from `IsSigmaOpen`) is
--   `π.nodeAt k ∈ G.AncSet C`; clause 3 *strengthens* it
--   to membership in $C$ itself. The strengthening is the
--   *only* difference between clauses 2 and 3 (both still
--   require `π.IsSigmaOpen C` overall, so the
--   blockable-non-collider condition is shared); we encode
--   that exactly. Wrapping clause 3 in a single
--   `π.IsSigmaOpen C ∧ (∀ k, π.IsColliderAt k → π.nodeAt k
--   ∈ C)` makes the relationship to clause 2 visible at the
--   surface -- clause 2 plus the extra collider tightening.
--
-- * **`∀ k, π.IsColliderAt k → π.nodeAt k ∈ C` is the
--   universal-implication rendering of the LN's "all its
--   colliders lie in $C$".** The natural-language phrase
--   "every collider $c$ on $\pi$ satisfies $c \in C$" is a
--   universal over collider positions; the Lean idiom for
--   "universal over a subset, gated by a predicate" is
--   `∀ k, IsColliderAt k → ...`, i.e. an implication-
--   guarded universal over all positions. Alternatives
--   (e.g. a `∀ k : {k // π.IsColliderAt k}` subtype-bound
--   universal, or quantifying over a `Fin π.length` with
--   an `IsColliderAt` guard) would force the consumer to
--   either coerce out of a subtype or unpack a `Fin` --
--   pure noise relative to the implication-guarded form.
--   The shape matches `IsSigmaOpen`'s clause-(i) exactly
--   (cf. `SigmaBlockedWalks.lean` line 427: the collider
--   conjunct of `IsSigmaOpen` is
--   `∀ k, π.IsColliderAt k → π.nodeAt k ∈ G.AncSet C`),
--   so clause 3 reads as "the same universal as `IsSigmaOpen`
--   but with $C$ in place of $\Anc^G(C)$" -- precisely the
--   LN's "all its colliders lie in $C$ (and not just in
--   $\Anc^G(C)$)" contrast at the surface. `IsColliderAt`
--   itself is the position-indexed predicate from
--   `Section3_3/CollidersAndNon.lean` line 189; `nodeAt`
--   is the position-indexed node accessor from
--   `Section3_3/SigmaBlockedWalks.lean` line 258. The
--   `k : ℕ` is gated by `IsColliderAt k` (which returns
--   `False` at out-of-range positions, see the position-
--   indexing convention in `SigmaBlockedWalks.lean`'s
--   module docstring), so the quantifier is correctly
--   restricted to actual collider positions on $\pi$
--   without needing a `Fin` bound.
--
-- * **Body is exactly `sorry`.** Per the formalizer-worker
--   prompt (`scaffold/claude_prompts/row_workers/`
--   `formalize_claim_in_lean.md`): "Body is exactly one
--   `sorry` per declaration. Do not attempt the proof here
--   -- that's `prove_claim_in_lean`, which runs *after* the
--   tex proof has been written and verified." The future
--   prover will pivot through `lem:replace_walk` (=
--   claim_3_27) for the `2 → 1` arrow; see the module
--   docstring's "Infrastructure note for the future
--   prover" section.
--
-- ## Downstream consequences
--
-- * **claim_3_24** (Remark, `graphs.tex` lines 1395 -- 1412):
--   the principal consumer. Cites this proposition twice:
--   once via `.out 0 1` to bridge between path-existence
--   and walk-existence (rewriting `IsISigmaSeparated`'s
--   walk universal as a path universal), and once via
--   `.out 1 2` to bridge between walk-existence and
--   walk-with-colliders-in-$C$-existence (extracting a
--   stronger witness from a `IsNotISigmaSeparated`
--   hypothesis). Both extractions are first-class
--   projections on `sigmaOpens_TFAE`.
-- * **claim_3_25** ($i\sigma$-separation under
--   marginalization, `graphs.tex` lines 1414 -- 1422): the
--   LN proof translates between walks on $G$ and walks on
--   $G^{\setminus D}$; some of its steps are cleaner stated
--   on paths, so `.out 0 1` is the bridge.
-- * **Chapter 4+ Markov-property theorems**: whenever
--   "every path from $A$ to $J \cup B$ is $\sigma$-blocked"
--   shows up (e.g. CBN-Markov consequences stated for
--   practitioners), the equivalence here is the bridge to
--   the walk-based `IsISigmaSeparated`.
-- * **Chapter 5 -- 7 (do-calculus / identification)**: rule
--   premises and adjustment criteria are most ergonomic
--   in the *path* formulation; theorems are proved in the
--   *walk* formulation. The TFAE bridges between the two.
-- * **Chapters 11 -- 16 (discovery, FCI / ICDF)**: path-based
--   separation tests live inside FCI's main loop; this
--   bridge is invoked at every test.
-- * **Mirror in subsection 3.4** (claim_3_30, `graphs.tex`
--   line 1745): "a similar result from Proposition
--   \ref{prp:sigma_opens} holds for $id$-separation as
--   well", i.e. the $d$-blocking version. Picking the
--   TFAE shape here propagates verbatim to the future
--   `dOpens_TFAE`.
--
-- ## Constraints / known limitations
--
-- * **The proof body is `sorry`** -- this row is at the
--   formalizer stage. Manager B's prover will fill it,
--   navigating the `lem:replace_walk` / claim_3_27
--   dependency (see the module docstring's "Infrastructure
--   note for the future prover" section). Until the proof
--   lands, every downstream consumer is also gated on
--   `sorry` -- a single point of unsoundness, easy to
--   audit, easy to discharge in one place.
-- * **`w₁, w₂ ∈ G.J ∪ G.V` is a caller's side-condition,
--   not a type-level guard.** Stating
--   `G.sigmaOpens_TFAE C w₁ w₂` with $w_1 \notin G.J \cup
--   G.V$ is *not a type error* -- it just makes all three
--   list entries vacuously `False`, hence TFAE is `True`.
--   Callers that rely on the proposition's content need
--   $w_1, w_2 \in G.J \cup G.V$ in scope (which they will,
--   if they got here via `IsISigmaSeparated`'s membership
--   hypotheses).
-- * **No `Decidable` instance.** Like `IsISigmaSeparated`
--   and the rest of the LN's separation predicates, the
--   propositions here are classical-existential over
--   walks (which form an infinite type for general
--   graphs); we provide no decidability infrastructure.
--   Finite-graph specialisations may be added downstream
--   when chapters 11 -- 16's FCI implementation needs them.
-- * **The `tfae_have` / `tfae_finish` tactics are not yet
--   imported here**, only `Mathlib.Data.List.TFAE` (the
--   type and its API). The future prover will pull
--   `Mathlib.Tactic.TFAE` into this file (or whichever
--   file Lake routes the proof through) -- a small import
--   pinned by the proof's pivot through `tfae_have`.

/-- claim_3_23 (`SigmaOpenPathWalk`,
LN `\restateprpsigmaopens` / `prp:sigma_opens`): for a CDMG
$G$, a conditioning set $C \subseteq J \cup V$, and two
nodes $w_1, w_2 \in J \cup V$, the following three
propositions are equivalent:
1. there exists a $C$-$\sigma$-open *path* from $w_1$ to
   $w_2$ in $G$;
2. there exists a $C$-$\sigma$-open *walk* from $w_1$ to
   $w_2$ in $G$;
3. there exists a $C$-$\sigma$-open *walk* from $w_1$ to
   $w_2$ in $G$ all of whose colliders lie in $C$ (not just
   in $\Anc^G(C)$).
Packaged as a `List.TFAE`; pairwise extractions are
`(G.sigmaOpens_TFAE C w₁ w₂).out i j` for `i, j ∈ {0, 1, 2}`.

The proof body is `sorry`; the LN's proof pivots through
clause 2 and uses `lem:replace_walk` (= claim_3_27,
`LabelRoman`) for the `2 → 1` direction, see this file's
module docstring's "Infrastructure note for the future
prover". -/
theorem sigmaOpens_TFAE (G : CDMG α) (C : Set α) (w₁ w₂ : α) :
    List.TFAE
      [ (∃ π : Walk G w₁ w₂, π.IsPath ∧ π.IsSigmaOpen C),
        (∃ π : Walk G w₁ w₂, π.IsSigmaOpen C),
        (∃ π : Walk G w₁ w₂, π.IsSigmaOpen C ∧
          ∀ k, π.IsColliderAt k → π.nodeAt k ∈ C) ] := by
  classical
  -- 3 → 2 and 1 → 2: trivial (drop a conjunct from the clause-3 / clause-1 witness).
  tfae_have h₃₂ : 3 → 2 := fun ⟨π, hOpen, _⟩ => ⟨π, hOpen⟩
  tfae_have h₁₂ : 1 → 2 := fun ⟨π, _, hOpen⟩ => ⟨π, hOpen⟩
  -- 2 → 1: induction on `π.length`. When `π` is not a path, find a duplicated
  -- position `p < q ≤ π.length` (so `π.nodeAt p = π.nodeAt q`); apply
  -- `replace_walk` to get `σ : Walk G (π.nodeAt p) (π.nodeAt q)`. Since `σ` is
  -- a *path* with equal endpoints, it must be `Walk.nil _` (length 0), so the
  -- spliced walk is strictly shorter.
  tfae_have h₂₁ : 2 → 1 := by
    rintro ⟨π₀, h_open₀⟩
    -- Strong induction package on `π.length`.
    suffices h : ∀ n, ∀ (π : Walk G w₁ w₂), π.IsSigmaOpen C →
        π.length ≤ n →
        ∃ π' : Walk G w₁ w₂, π'.IsPath ∧ π'.IsSigmaOpen C from
      h π₀.length π₀ h_open₀ le_rfl
    intro n
    induction n with
    | zero =>
      intro π h_open h_len
      have h_len_eq : π.length = 0 := Nat.le_zero.mp h_len
      cases π with
      | nil _ =>
        refine ⟨Walk.nil _, ?_, h_open⟩
        simp [Walk.IsPath]
      | cons _ _ =>
        simp [Walk.length_cons] at h_len_eq
    | succ n ih =>
      intro π h_open h_len
      by_cases h_path : π.IsPath
      · exact ⟨π, h_path, h_open⟩
      · -- Non-path: extract a duplicate position pair.
        obtain ⟨p, q, hpq, hq, heq⟩ :=
          Walk.exists_dup_positions_of_not_isPath π h_path
        have hp_le : p ≤ π.length := le_trans (le_of_lt hpq) hq
        -- Both `π.nodeAt p` and `π.nodeAt q` lie in `G`: π is non-trivial since
        -- `0 ≤ p < q ≤ π.length` forces `π.length ≥ 1`.
        have h_π_pos : 0 < π.length := by omega
        have h_node_q_mem : π.nodeAt q ∈ G := by
          rcases lt_or_eq_of_le hq with hlt | heq2
          · exact Walk.nodeAt_mem_G_of_lt_length π hlt
          · -- q = π.length: node at length is the destination, in `G` via endpoints.
            rw [heq2, Walk.nodeAt_length]
            exact (Walk.endpoints_mem_G_of_pos π h_π_pos).2
        -- v_p = v_q ∈ G, hence v_p ∈ Sc^G(v_q) by self-reflexivity.
        have h_sc : π.nodeAt p ∈ G.Sc (π.nodeAt q) := by
          rw [heq]; exact CDMG.self_mem_Sc h_node_q_mem
        -- Apply `replace_walk`.
        obtain ⟨σ, h_splice_open, _h_dir_or_rev, _h_inSc, h_σ_path⟩ :=
          Walk.replace_walk π C h_open hpq hq h_sc
        -- σ : Walk G (π.nodeAt p) (π.nodeAt q). Since `π.nodeAt p = π.nodeAt q`
        -- (by `heq`) and `σ.IsPath`, σ must have length 0.
        have h_σ_len_zero : σ.length = 0 := by
          by_contra h_ne
          have h_σ_pos : 1 ≤ σ.length := Nat.one_le_iff_ne_zero.mpr h_ne
          have h_supp_len : σ.support.length = σ.length + 1 := Walk.support_length σ
          have h_idx_zero : (0 : ℕ) < σ.support.length := by rw [h_supp_len]; omega
          have h_idx_last : σ.length < σ.support.length := by rw [h_supp_len]; omega
          have h_first : σ.support[0]'h_idx_zero = π.nodeAt p := by
            rw [Walk.support_getElem_eq_nodeAt σ h_idx_zero, Walk.nodeAt_zero]
          have h_last : σ.support[σ.length]'h_idx_last = π.nodeAt q := by
            rw [Walk.support_getElem_eq_nodeAt σ h_idx_last, Walk.nodeAt_length]
          have h_eq_supp :
              σ.support[0]'h_idx_zero = σ.support[σ.length]'h_idx_last := by
            rw [h_first, h_last, heq]
          have h_nodup : σ.support.Nodup := h_σ_path
          have : (0 : ℕ) = σ.length :=
            (List.Nodup.getElem_inj_iff h_nodup).mp h_eq_supp
          omega
        -- The spliced walk has length `p + 0 + (π.length - q) < π.length`.
        set π' : Walk G w₁ w₂ :=
          (π.prefix p).append (σ.append (π.suffix q)) with hπ'_def
        have h_π'_len : π'.length < π.length := by
          have h_pre_len : (π.prefix p).length = p := Walk.length_prefix π hp_le
          have h_suf_len : (π.suffix q).length = π.length - q := Walk.length_suffix π hq
          have h_app_len :
              (σ.append (π.suffix q)).length = σ.length + (π.length - q) := by
            rw [Walk.length_append, h_suf_len]
          have : π'.length = p + (σ.length + (π.length - q)) := by
            rw [hπ'_def, Walk.length_append, h_pre_len, h_app_len]
          rw [this, h_σ_len_zero]
          omega
        have h_π'_le_n : π'.length ≤ n := by omega
        exact ih π' h_splice_open h_π'_le_n
  -- 2 → 3: induction on the number of "bad" collider positions (positions
  -- with `IsColliderAt` whose node is *not* in `C`). At each step, pick a
  -- bad collider `v_k`, find a directed walk `σ : v_k → c ∈ C` with no
  -- interior in `C`, and splice in `σ ⧺ σ.reverse` between positions `k`
  -- and `k`. The new walk has strictly fewer bad colliders.
  tfae_have h₂₃ : 2 → 3 := by
    rintro ⟨π₀, h_open₀⟩
    exact reduce_to_all_colliders_in_C G C w₁ w₂ π₀ h_open₀
  tfae_finish

end CDMG

end Causality
