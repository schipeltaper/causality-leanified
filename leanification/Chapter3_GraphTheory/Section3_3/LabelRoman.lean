import Chapter3_GraphTheory.Section3_3.WalkPrefixSuffix
import Chapter3_GraphTheory.Section3_3.LabelRomanHelpers

/-!
# claim_3_27 -- `lem:replace_walk` -- Walk replacement preserves σ-openness

This file formalises *claim 3_27* of the lecture notes
(Forré & Mooij, `lecture-notes/lecture_notes/graphs.tex`,
lines 1620 -- 1652): given a $C$-$\sigma$-open walk
$\pi = (v_0 \sus \cdots \sus v_n)$ in a CDMG $G$ and two
positions $i < j$ with $v_i \in \Sc^G(v_j)$, there exists a
walk $\sigma$ from $v_i$ to $v_j$ -- directed in one of the
two orientations -- entirely within $\Sc^G(v_j)$ whose splice
into $\pi$ (replacing the subwalk between positions $i$ and
$j$) is still $C$-$\sigma$-open.

The Lean statement packages the LN's two cases (i) and (ii)
into a single existential whose witness $\sigma$ is either
directed (LN case (i): $v_i \tuh \cdots \tuh v_j$) or has a
directed reverse (LN case (ii): $v_i \hut \cdots \hut v_j$).
The spliced walk is expressed concretely as
`(π.prefix i).append (σ.append (π.suffix j))`, composing the
`Walk.prefix` / `Walk.suffix` primitives from
`WalkPrefixSuffix.lean` (step 1 of this row's plan) with the
existing `Walk.append`. The LN's "shortest directed path"
qualifier unbundles into two qualitative properties --
(a) every $\sigma$ vertex lies in $\Sc^G(v_j)$ and (b) the
path has no repeats (`σ.IsPath`) -- both retained as
separate conjuncts of the existential; only the
*quantitative* length-minimisation is dropped. The path
conjunct is load-bearing for the only live consumer,
claim_3_23's $2 \Rightarrow 1$ direction, which counts
repeated nodes on a $\sigma$-open walk and needs the count
to strictly drop under replacement. See the per-declaration
design block below for the full rationale (existential vs.
constructive splice, prefix/suffix vs. dedicated `splice`,
disjunction packing of LN cases, the
(a)+(b)-without-minimisation reading of "shortest", and
the `≤ σ.length` interval unifying endpoints and interior).

This file holds only the statement (with `sorry` body) at the
present step; the helper lemmas L1 -- L7 and the proof come
in subsequent steps of the row's plan
(`workspace_claim_3_27.md`, §4).
-/

namespace Causality

open scoped Causality.CDMG

variable {α : Type*}

namespace Walk

variable {G : CDMG α}

-- REFACTOR-BLOCK-ORIGINAL-BEGIN: replace_walk
-- claim_3_27
-- title: LabelRoman -- replacing an Sc-bounded subwalk of a
-- σ-open walk yields a σ-open walk
--
-- ## LN reference
--
-- `lem:replace_walk`, `lecture-notes/lecture_notes/graphs.tex`
-- lines 1620 -- 1652.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(claim_3_27, lines 1620 -- 1630):

  Let $G = (J, V, E, L)$ be a CDMG, $C \subseteq V \cup J$ and
  $\pi = \lp v_0 \sus \cdots \sus v_n \rp$ a $C$-$\sigma$-open
  walk in $G$. Suppose $v_i \in \Sc^G(v_j)$ for some
  $i, j \in \{0, \dots, n\}$ with $i < j$. If we then replace
  the subwalk $v_i \sus \cdots \sus v_j$ of $\pi$ by
    (i)  a shortest directed path $v_i \tuh \cdots \tuh v_j$ in
         $G$ if $j = n$ or if $v_j \tuh v_{j+1}$ on $\pi$, or
    (ii) a shortest directed path $v_i \hut \cdots \hut v_j$ in
         $G$ otherwise,
  then this new subwalk is entirely within $\Sc^G(v_j)$ and
  the modified walk $\pi'$ is still $C$-$\sigma$-open.
-/
--
-- ## Statement (informal)
--
-- Given a $C$-$\sigma$-open walk $\pi$ on $G$ and two
-- positions $i < j$ with $v_i \in \Sc^G(v_j)$, *there exists*
-- a walk $\sigma$ from $v_i$ to $v_j$ such that:
--   (1) splicing $\sigma$ into $\pi$ in place of the subwalk
--       between positions $i$ and $j$ yields a walk that is
--       still $C$-$\sigma$-open;
--   (2) $\sigma$ is either directed ($v_i \tuh \cdots \tuh
--       v_j$, LN case (i)) or its reverse is directed
--       ($v_i \hut \cdots \hut v_j$, LN case (ii));
--   (3) every vertex on $\sigma$ -- endpoints and interior --
--       lies in $\Sc^G(v_j)$; and
--   (4) $\sigma$ is a *path* (no repeated vertices).
-- Properties (3) and (4) together are the two qualitative
-- consequences of the LN's "shortest directed path"
-- qualifier; (1), (2) and the existence claim itself are
-- the LN's own conclusion.
--
-- ## Design choices
--
-- * **Existential conclusion, not a function returning a
--   specific witness walk.** The LN says "if we replace ... then
--   ... is $\sigma$-open", which reads as: *there exists* a
--   replacement subwalk with the desired properties. We expose
--   this directly as `∃ σ : Walk G (π.nodeAt i) (π.nodeAt j), ...`
--   with the four relevant properties bundled as conjuncts
--   ($\sigma$-openness of the splice, directedness of $\sigma$ in
--   one orientation, SCC-membership of every $\sigma$ vertex,
--   path-ness of $\sigma$). The alternative -- packaging the same
--   data as a function `replace_walk : ... → Walk G v₀ vₙ` whose
--   output is a definite spliced walk -- was rejected because the
--   *only* live consumer (claim_3_23's $2 \Rightarrow 1$
--   direction, LN lines 1666 -- 1672) needs to **destructure** the
--   resulting splice into its three constituent pieces (`π.prefix
--   i`, $\sigma$, `π.suffix j`) and reason about repetition counts
--   on each segment separately. A function returning an opaque
--   `Walk G v₀ vₙ` would force every consumer to either re-derive
--   the splice structure or compute with a specific witness
--   (which is brittle: the witness's exact shape depends on
--   which case (i) or (ii) fires, which the consumer should not
--   have to know). The existential keeps the splice *structurally
--   visible* in the conclusion, while still letting the consumer
--   abstract over which $\sigma$ was produced. See
--   `workspace_claim_3_27.md` §1, "Statement shape -- DECISION",
--   paragraph 1 for the original discussion.
--
-- * **Spliced walk via `prefix` / `suffix` / `append`, not a
--   dedicated `Walk.splice` operator.** The expression
--   `(π.prefix i).append (σ.append (π.suffix j))` reads
--   exactly as the LN's "$\pi$ with the subwalk between $v_i$
--   and $v_j$ replaced by $\sigma$": the prefix of $\pi$ up
--   to position $i$, then $\sigma$, then the suffix of $\pi$
--   from position $j$ onwards. A dedicated `Walk.splice π i j
--   σ` operator would add a layer of indirection that
--   consumers would immediately unfold to the same three-way
--   append; the prefix/suffix spelling is identical and ties
--   directly into the existing `*_append_*` per-position
--   lemmas in `SigmaBlockedReversal.lean`
--   (`isColliderAt_append_lt_length`,
--   `isUnblockableNonColliderAt_append_cons_cons_one`, etc.).
--   See `workspace_claim_3_27.md` §1, paragraph 3 for the
--   rationale.
--
-- * **Right-associated bracketing `(π.prefix i).append
--   (σ.append (π.suffix j))`, not the left-associated
--   `((π.prefix i).append σ).append (π.suffix j)`.** Both
--   spellings denote the same walk modulo `append_assoc`
--   (`SigmaBlockedReversal.lean` line 120), but they expose
--   different two-pair structures to the existing `*_append_*`
--   API, which is stated for a single split point
--   `p₁.append p₂`. With right-association the two joints of the
--   three-way splice land cleanly as: the *outer* joint at
--   position `i` is between `p₁ = π.prefix i` and `p₂ =
--   σ.append (π.suffix j)`; the *inner* joint at the
--   $\sigma$-end is between `p₁ = σ` and `p₂ = π.suffix j`,
--   *inside* the outer `p₂`. Each joint then matches the
--   existing single-split lemmas (`isColliderAt_append_*`,
--   `isUnblockableNonColliderAt_append_*`) by descending the
--   structural pair `(p₁, p₂)` once, without re-deriving the
--   inner split. Left-association would force the inner-joint
--   reasoning to dig through the *first* argument of the outer
--   append -- which `Walk.append`'s recursion in
--   `Section3_1/Walks.lean` recurses on -- a strictly longer
--   structural descent. Consumers may convert between the two
--   forms by `append_assoc` if needed.
--
-- * **`σ.IsDirected ∨ σ.reverse.IsDirected` packs LN cases
--   (i) and (ii) into one existential.** The LN distinguishes
--   the two replacement orientations by the local pattern of
--   $\pi$ at position $j$: case (i) (forward $v_i \tuh \cdots
--   \tuh v_j$) when $j = n$ or $v_j \tuh v_{j+1}$ on $\pi$,
--   case (ii) (backward $v_i \hut \cdots \hut v_j$) otherwise.
--   The disjunction is the propositional packing of this
--   two-way case split into a single existential. Consumers
--   never branch on (i) vs. (ii) -- they just take whichever
--   orientation the witness provides; the case split lives
--   inside the proof, not at the interface. Splitting
--   `replace_walk` into two separate theorems
--   (`replace_walk_forward`, `replace_walk_backward`) was
--   considered and rejected for two reasons. (1) Every
--   downstream call would either have to invoke both and
--   `rcases`-merge, or duplicate the LN's case-discriminating
--   logic (`j = n ∨ v_j \tuh v_{j+1}` vs. otherwise) at the
--   call site. (2) The *cut-point* `(i, j)` is shared between
--   the two cases -- it's a single decision the consumer made
--   before invoking the lemma -- so the case (i) / (ii) split
--   is an internal implementation detail of *how* the splice
--   is produced, not a different *kind* of splice. Bundling
--   into one theorem keeps the cut-point well-defined at the
--   interface and hides the implementation detail. The same
--   reasoning is why the hypothesis `h_sc : π.nodeAt i ∈ G.Sc
--   (π.nodeAt j)` is not duplicated either: it's the
--   precondition that *both* cases share.
--
-- * **"Shortest" is unbundled into two qualitative
--   conjuncts.** The LN's "shortest directed path" qualifier
--   delivers *two* properties simultaneously: (a) every
--   intermediate vertex lies in $\Sc^G(v_j)$ (a
--   longer-than-necessary directed walk inside $\Sc^G(v_j)$
--   could in principle loop, but every node on such a loop
--   is still in $\Sc^G(v_j)$), and (b) the path has no
--   repeats (`σ.IsPath`). We drop the *quantitative*
--   minimisation ("shortest" as length-minimising --
--   incidental to every downstream use, and costly to
--   formalise as a min-over-walks well-founded construction
--   with no other consumer in this chapter) but **retain
--   both qualitative properties separately**: (a) as the
--   third conjunct
--   `∀ k, k ≤ σ.length → σ.nodeAt k ∈ G.Sc (π.nodeAt j)`,
--   which is exactly what the LN's proof uses "shortest" to
--   establish on the SCC side (see LN line 1635: "all nodes
--   in between lie in the same strongly connected component
--   $\Sc^G(v_i)$"); and (b) as the fourth conjunct
--   `σ.IsPath`. The path-ness is *load-bearing* for the
--   only live consumer (claim_3_23's $2 \Rightarrow 1$
--   direction, LN lines 1666 -- 1672), which counts repeated
--   nodes on a $\sigma$-open walk and needs the count to
--   *strictly* drop under replacement: without
--   `σ.IsPath`, the witness could be a closed walk
--   (e.g. `v_i \tuh x \tuh v_i \tuh x \tuh v_j` with every
--   step forward and every node in $\Sc^G(v_j)$) that
--   reintroduces repeats and so leaves the count unchanged
--   or worse. The degenerate $v_i = v_j$ case is even
--   sharper: with `IsPath`, the witness *must* be
--   `Walk.nil _` and the $[i, j]$ segment is genuinely
--   collapsed; without it, the witness can be a non-trivial
--   closed walk and $v_j$ stays multiply-occurring.
--   Proof-cost note: producing the path-witness is
--   uniformly *cheaper* than any other "shortest" notion,
--   because loop-erasure of a directed walk is still
--   directed and still inside $\Sc^G(v_j)$ (loop-erasure
--   only deletes support members, never adds), so the
--   helper L2 (`directed_walk_in_Sc`) composes with a
--   standard loop-erasure step to yield a directed-and-path
--   witness with all-in-`Sc` membership preserved. See
--   `workspace_claim_3_27.md` §1, paragraph 1 (to be
--   updated by the manager once this revision lands) for
--   the original "shortest is dropped" framing that this
--   bullet supersedes.
--
-- * **The SCC-membership universal is gated by `k ≤ σ.length`,
--   covering both endpoints and the interior.** At `k = 0` we
--   have $\sigma.\text{nodeAt}\,0 = v_i \in \Sc^G(v_j)$ by
--   `h_sc`; at `k = σ.length` we have
--   $\sigma.\text{nodeAt}\,\sigma.\text{length} = v_j$ which
--   is in $\Sc^G(v_j)$ by `self_mem_Sc`; in between, the LN's
--   "all nodes in between lie in the same SCC" gives the
--   interior. Phrasing the universal over the whole closed
--   interval `[0, σ.length]` lets consumers index any position
--   on the spliced middle uniformly, and matches the LN's
--   prose ("this new subwalk is *entirely* within
--   $\Sc^G(v_j)$") which makes no endpoint/interior
--   distinction.
--
-- * **`namespace Walk` placement, not `namespace CDMG`.**
--   Matches the convention of claim_3_21
--   (`UnblockableNonCollidersOpen.lean`) and the per-walk
--   predicates in this section: the theorem is *about* a walk,
--   so it lives under `Causality.Walk`. Callers may reach for
--   it via `π.replace_walk C h_open hij hj h_sc`
--   (dot-projection on the walk, with the walk-first /
--   conditioning-set-second argument order matching
--   `π.IsSigmaOpen C` and the rest of the chapter's per-walk
--   API). The planner's workspace draft
--   (`workspace_claim_3_27.md` §1) suggested `namespace CDMG`
--   to dot-project on `G`; we chose `Walk` instead because
--   `G` is implicit in this signature and so does not actually
--   dot-project, while `π` is explicit and does. Verified
--   against the chapter's argument-order convention (`π`
--   first, `C` second; same as `Walk.IsSigmaOpen π C` in
--   `SigmaBlockedWalks.lean` and
--   `isSigmaBlocked_iff_not_isSigmaOpen π C` in
--   `SigmaBlockedReversal.lean`).
--
-- * **`C : Set α`, not a subtype of `J ∪ V`.** Same convention
--   as `IsSigmaOpen` itself (`SigmaBlockedWalks.lean`):
--   `AncSet G C` silently ignores members outside the graph,
--   so the LN's "$C \subseteq V \cup J$" precondition is
--   propagated by callers as a side hypothesis, not encoded
--   at the type level.
--
-- * **Bound `hj : j ≤ π.length` only; `i`'s bound comes from
--   `hij : i < j`.** The LN's "$i, j \in \{0, \dots, n\}$
--   with $i < j$" gives $i < j \le n = \pi.\text{length}$, so
--   the single `hj` is sufficient. `nodeAt` is total
--   (junk-OK), so both `π.nodeAt i` and `π.nodeAt j` are
--   well-typed unconditionally; the bound is needed for the
--   semantic side (e.g. `prefix_length` / `suffix_length` lift
--   `π.prefix i` and `π.suffix j` to their non-junk
--   characterisations).

/-- claim_3_27 (`lem:replace_walk`): given a $C$-$\sigma$-open
walk `π` in a CDMG `G` and two positions `i < j` on `π` with
`π.nodeAt i ∈ Sc^G(π.nodeAt j)`, there exists a walk `σ` from
`π.nodeAt i` to `π.nodeAt j` such that splicing `σ` into `π`
in place of the subwalk between positions `i` and `j` yields a
walk that is (1) still $C$-$\sigma$-open, (2) either directed
or has a directed reverse (packing LN cases (i) and (ii) into
a single existential), (3) entirely within
$\Sc^G(\pi.\text{nodeAt}\,j)$ at every position, and (4) a
path (no repeated vertices) -- the two qualitative
consequences of the LN's "shortest directed path" qualifier,
both retained as separate conjuncts. -/
theorem replace_walk
    {G : CDMG α} {v₀ vₙ : α} (π : Walk G v₀ vₙ) (C : Set α)
    (h_open : π.IsSigmaOpen C)
    {i j : ℕ} (hij : i < j) (hj : j ≤ π.length)
    (h_sc : π.nodeAt i ∈ G.Sc (π.nodeAt j)) :
    ∃ σ : Walk G (π.nodeAt i) (π.nodeAt j),
      ((π.prefix i).append (σ.append (π.suffix j))).IsSigmaOpen C
      ∧ (σ.IsDirected ∨ σ.reverse.IsDirected)
      ∧ (∀ k, k ≤ σ.length → σ.nodeAt k ∈ G.Sc (π.nodeAt j))
      ∧ σ.IsPath := by
  classical
  -- Notational shortcuts for the cut-point vertices.
  set vᵢ : α := π.nodeAt i with hvᵢ_def
  set vⱼ : α := π.nodeAt j with hvⱼ_def
  -- vᵢ ∈ G follows from h_sc.1 (it lives in Anc^G(vⱼ) which has a `∈ G` conjunct).
  have h_vi_mem : vᵢ ∈ G := h_sc.1.1
  -- vⱼ ∈ G: from `h_sc.2 : vᵢ ∈ Desc^G(vⱼ)` extract the directed walk vⱼ → vᵢ; if
  -- it is non-trivial, vⱼ is the source of a step (in G via E_subset/L_subset).
  -- If it is the trivial walk, vᵢ = vⱼ, so vⱼ ∈ G via h_vi_mem.
  have h_vj_mem : vⱼ ∈ G := by
    obtain ⟨_, π_back, _⟩ := h_sc.2
    by_cases hlen : 1 ≤ π_back.length
    · obtain ⟨_, s, _, _⟩ := Walk.walk_pos_eq_cons π_back hlen
      exact s.source_mem_G
    · -- π_back has length 0, so its endpoints coincide: vⱼ = vᵢ.
      push_neg at hlen
      have h_len_zero : π_back.length = 0 := Nat.lt_one_iff.mp hlen
      have h1 : π_back.nodeAt 0 = vⱼ := π_back.nodeAt_zero
      have h2 : π_back.nodeAt π_back.length = vᵢ := π_back.nodeAt_length
      rw [h_len_zero] at h2
      have h_eq : vⱼ = vᵢ := h1 ▸ h2
      rw [h_eq]; exact h_vi_mem
  have h_vj_in_Sc_vj : vⱼ ∈ G.Sc vⱼ := CDMG.self_mem_Sc h_vj_mem
  -- The length-i prefix of π exists and lies in `Walk G v₀ vᵢ`.
  -- The length-(π.length - j) suffix lies in `Walk G vⱼ vₙ`.
  have hi_le : i ≤ π.length := le_trans (le_of_lt hij) hj
  -- Bounds on π's positions / lengths we will reuse.
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π hi_le
  have h_suf_len : (π.suffix j).length = π.length - j := Walk.length_suffix π hj
  -- Two key sub-helpers for σ-openness arguments
  -- on the spliced walk.  We'll write them as `have`-block lemmas
  -- after constructing σ, since they depend on σ's properties.

  -- ============================================================
  -- Top-level case split based on the local pattern at position j on π.
  -- ============================================================
  -- Case (ii) trigger: ∃ a first-step of (π.suffix j) with source-arrowhead.
  by_cases h_case_ii : ∃ (a : α) (s_j : WalkStep G (π.nodeAt j) a)
      (rest_j : Walk G a vₙ),
      π.suffix j = Walk.cons s_j rest_j ∧ s_j.HasArrowheadAtSource
  · -- ============================================================
    -- LN case (ii): step at j on π is backward or bidir.
    -- σ is built from h_sc.2 (Desc^G(vⱼ)), loop-erased, then reversed.
    -- ============================================================
    -- Extract case (ii)'s step structure.
    obtain ⟨a_j, s_j, rest_j, h_suf_eq, h_s_j_arrowhead⟩ := h_case_ii
    -- Extract directed walk π_dir : Walk G vⱼ vᵢ from h_sc.2.
    obtain ⟨π_dir, h_πdir_dir⟩ := h_sc.2.2
    -- Loop-erase to get a directed path σ₀ : Walk G vⱼ vᵢ.
    obtain ⟨σ₀, hσ₀_dir, hσ₀_path⟩ :=
      Walk.exists_path_of_directed π_dir h_πdir_dir
    -- σ = σ₀.reverse : Walk G vᵢ vⱼ.
    set σ : Walk G vᵢ vⱼ := σ₀.reverse with hσ_def
    -- (2) σ.reverse is directed:
    have hσ_rev_dir : σ.reverse.IsDirected := by
      rw [hσ_def, Walk.reverse_reverse]
      exact hσ₀_dir
    -- (4) σ.IsPath: σ₀ is a path, so its reverse is too.
    have hσ_path : σ.IsPath := by
      rw [hσ_def, Walk.isPath_reverse_iff]; exact hσ₀_path
    -- (3) σ's nodes ∈ G.Sc vⱼ.
    -- σ.nodeAt k = σ₀.reverse.nodeAt k = σ₀.nodeAt (σ₀.length - k).
    -- σ₀ : Walk G vⱼ vᵢ directed. With vⱼ ∈ G.Sc vᵢ (from Sc-symm), every node of σ₀ ∈ Sc^G(vᵢ).
    -- And Sc^G(vᵢ) = Sc^G(vⱼ) by Sc-equivalence.
    have h_sc_symm : vⱼ ∈ G.Sc vᵢ := Walk.mem_Sc_symm h_sc
    have hσ₀_inSc_vi : ∀ m, m ≤ σ₀.length → σ₀.nodeAt m ∈ G.Sc vᵢ :=
      Walk.directed_walk_in_Sc σ₀ hσ₀_dir h_sc_symm
    have hσ_inSc : ∀ k, k ≤ σ.length → σ.nodeAt k ∈ G.Sc vⱼ := by
      intro k hk
      -- σ.length = σ₀.length (length_reverse)
      have hσ_len_eq : σ.length = σ₀.length := by
        rw [hσ_def, Walk.length_reverse]
      -- σ.nodeAt k = σ₀.nodeAt (σ₀.length - k).
      have h_node : σ.nodeAt k = σ₀.nodeAt (σ₀.length - k) := by
        rw [hσ_def]
        exact Walk.nodeAt_reverse σ₀ (by rw [hσ_def] at hk; rw [Walk.length_reverse] at hk; exact hk)
      rw [h_node]
      -- σ₀.nodeAt (σ₀.length - k) ∈ Sc^G(vᵢ).
      have h_in_vi : σ₀.nodeAt (σ₀.length - k) ∈ G.Sc vᵢ := by
        apply hσ₀_inSc_vi
        omega
      -- Sc-trans: ∈ Sc(vᵢ) AND vᵢ ∈ Sc(vⱼ) (from h_sc) → ∈ Sc(vⱼ).
      -- Use the Sc-equivalence via mem_Sc_trans (need to define) or via the
      -- explicit chain.
      refine ⟨?_, ?_⟩
      · -- node ∈ Anc^G(vⱼ): use node ∈ Anc^G(vᵢ) and vᵢ ∈ Anc^G(vⱼ).
        obtain ⟨h_mem, ⟨p_to_vi, hp_to_vi⟩⟩ := h_in_vi.1
        obtain ⟨_, ⟨p_vi_vj, hp_vi_vj⟩⟩ := h_sc.1
        exact ⟨h_mem, ⟨p_to_vi.append p_vi_vj,
          Walk.isDirected_append _ _ hp_to_vi hp_vi_vj⟩⟩
      · -- node ∈ Desc^G(vⱼ): use vⱼ → vᵢ (from h_sc.2) and vᵢ → node (from h_in_vi.2).
        obtain ⟨_, ⟨p_vj_vi, hp_vj_vi⟩⟩ := h_sc.2
        obtain ⟨h_mem, ⟨p_vi_to_node, hp_vi_to_node⟩⟩ := h_in_vi.2
        exact ⟨h_mem, ⟨p_vj_vi.append p_vi_to_node,
          Walk.isDirected_append _ _ hp_vj_vi hp_vi_to_node⟩⟩
    refine ⟨σ, ?_, Or.inr hσ_rev_dir, hσ_inSc, hσ_path⟩
    -- Disjunct (1): σ-openness of the spliced walk W in case (ii).
    -- σ.reverse.IsDirected, so each step of σ is `backward`.  This makes interior joints
    -- left-chain non-colliders (unblockable inside Sc^G(vⱼ)) and the right joint at j
    -- unconditionally a left-chain non-collider (sole strict-outgoing into Sc^G(vⱼ)).
    -- The left joint at i splits into sub-cases (ii.a) (backward s_left_πi) and (ii.b)
    -- (forward/bidir s_left_πi); (ii.b) is the only sub-case where v_i becomes a collider
    -- on W and we discharge via the first-collider induction on π.
    -- Also relevant: π's first step of `π.suffix j` (= s_j) has source-arrowhead.
    refine ⟨?_, ?_⟩
    · -- ===== (1.coll)  W.IsColliderAt k → W.nodeAt k ∈ G.AncSet C =====
      intro k h_coll
      rcases lt_or_ge k i with h_k_lt_i | h_k_ge_i
      · -- k < i: transport via splice_pre.
        have h_πColl :=
          (Walk.isColliderAt_splice_pre π σ hi_le h_k_lt_i).mp h_coll
        rw [Walk.nodeAt_splice_pre π σ hi_le (le_of_lt h_k_lt_i)]
        exact h_open.1 k h_πColl
      · -- k ≥ i.
        rcases lt_or_ge k (i + σ.length) with h_k_lt_mid | h_k_ge_mid
        · -- i ≤ k < i + σ.length.
          rcases Nat.eq_or_lt_of_le h_k_ge_i with h_k_eq_i | h_k_gt_i
          · -- k = i: outer joint.  Sub-case (ii.a) or (ii.b) based on s_left_πi.
            subst h_k_eq_i
            -- For collider clause: (ii.a) backward s_left_πi: NOT collider, exfalso.
            -- (ii.b) forward/bidir s_left_πi: collider possible; v_i ∈ AncSet(C) via induction.
            -- Reduce W.nodeAt i = π.nodeAt i.
            rw [Walk.nodeAt_splice_pre π σ hi_le (le_refl i)]
            -- Goal: π.nodeAt i ∈ G.AncSet C.
            -- Case on i = 0 (W endpoint, can't be collider) vs i ≥ 1.
            by_cases hi_zero : i = 0
            · -- i = 0: position 0 of W is not a collider (endpoint).
              subst hi_zero
              exfalso
              exact (Walk.isNonColliderAt_zero _).2 h_coll
            · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
              have h_pre_i_pos : 1 ≤ (π.prefix i).length := by rw [h_pre_len]; omega
              obtain ⟨w_pre_i, p_pre_i, s_left_πi, h_pre_i_eq⟩ :=
                Walk.walk_pos_eq_append_last (π.prefix i) h_pre_i_pos
              have h_p_pre_i_len : p_pre_i.length = i - 1 := by
                have h1 : (π.prefix i).length = p_pre_i.length +
                    (Walk.cons s_left_πi (Walk.nil (π.nodeAt i))).length := by
                  rw [h_pre_i_eq, Walk.length_append]
                rw [h_pre_len] at h1
                simp [Walk.length_cons, Walk.length_nil] at h1
                omega
              have h_pos_form_i : (p_pre_i.length + 1 : ℕ) = i := by omega
              -- The right side of the joint at v_i on W: first step of σ.append (π.suffix j).
              -- In both σ.length ≥ 1 and σ.length = 0 cases, the right step has source-arrowhead:
              --   σ.length ≥ 1: σ's first step is backward (source-arrowhead).
              --   σ.length = 0: π.suffix j's first step is s_j (source-arrowhead from h_s_j_arrowhead).
              have h_app_pos : 1 ≤ (σ.append (π.suffix j)).length := by
                rw [Walk.length_append]
                have h_suf_pos : 1 ≤ (π.suffix j).length := by
                  rw [h_suf_eq, Walk.length_cons]; omega
                omega
              obtain ⟨w_app, s_app, rest_app, h_app_eq⟩ :=
                Walk.walk_pos_eq_cons _ h_app_pos
              -- s_app has source π.nodeAt i and source-arrowhead.  Use the dual helper.
              have h_suf_has_src : ∀ (a' : α) (s' : WalkStep G (π.nodeAt j) a')
                  (rest' : Walk G a' vₙ),
                  π.suffix j = Walk.cons s' rest' → s'.HasArrowheadAtSource := by
                intro a' s' rest' h_eq'
                rw [h_suf_eq] at h_eq'
                obtain ⟨h_av, h_sa, _⟩ := Walk.cons.inj h_eq'
                subst h_av
                have h_s_eq : s_j = s' := eq_of_heq h_sa
                rw [← h_s_eq]
                exact h_s_j_arrowhead
              have h_s_app_src : s_app.HasArrowheadAtSource :=
                Walk.first_step_has_source_of_reverseDirected_append σ (π.suffix j) _ s_app
                  rest_app hσ_rev_dir h_app_eq h_suf_has_src
              -- Now we have h_s_app_src : s_app.HasArrowheadAtSource.
              -- Build structural form of W at position i.
              have hW_form_i :
                  (π.prefix i).append (σ.append (π.suffix j)) =
                    p_pre_i.append (Walk.cons s_left_πi
                      (Walk.cons s_app rest_app)) := by
                rw [h_pre_i_eq, h_app_eq, Walk.append_assoc,
                  Walk.cons_append, Walk.nil_append]
              -- W.IsColliderAt i ↔ s_left_πi.HasArrowheadAtTarget ∧ s_app.HasArrowheadAtSource.
              have h_coll_at_i :
                  ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt i := h_coll
              rw [hW_form_i] at h_coll_at_i
              have h_at_p : (p_pre_i.append (Walk.cons s_left_πi
                  (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                convert h_coll_at_i using 2
              rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
              obtain ⟨h_left_arr, _h_right_arr⟩ := h_at_p
              -- (ii.a) backward s_left_πi is excluded here since backward has
              -- HasArrowheadAtTarget = False, contradicting h_left_arr.  Only (ii.b)
              -- (= forward / bidir s_left_πi) remains.  Use the first-collider induction.
              have hj_lt_π : j < π.length := by
                have hh : 1 ≤ (π.suffix j).length := by rw [h_suf_eq, Walk.length_cons]; omega
                rw [Walk.length_suffix π hj] at hh
                omega
              -- Build the helper's left-arrowhead hypothesis using π = π.prefix i ⧺ π.suffix i.
              have h_πfull : π = (π.prefix i).append (π.suffix i) :=
                (Walk.prefix_append_suffix π hi_le).symm
              have h_helper_left :
                  ∃ (wim1 wi : α) (p_pre : Walk G v₀ wim1) (s_left : WalkStep G wim1 wi)
                      (rest : Walk G wi vₙ),
                    π = p_pre.append (Walk.cons s_left rest) ∧
                    wi = π.nodeAt i ∧
                    p_pre.length = i - 1 ∧
                    s_left.HasArrowheadAtTarget := by
                refine ⟨w_pre_i, π.nodeAt i, p_pre_i, s_left_πi, π.suffix i, ?_, rfl,
                  h_p_pre_i_len, h_left_arr⟩
                have h_pre_alt :
                    (π.prefix i).append (π.suffix i) =
                      (p_pre_i.append (Walk.cons s_left_πi (Walk.nil _))).append (π.suffix i) := by
                  rw [h_pre_i_eq]
                have h_reassoc :
                    (p_pre_i.append (Walk.cons s_left_πi (Walk.nil (π.nodeAt i)))).append
                        (π.suffix i) =
                      p_pre_i.append (Walk.cons s_left_πi (π.suffix i)) := by
                  rw [Walk.append_assoc, Walk.cons_append, Walk.nil_append]
                exact h_πfull.trans (h_pre_alt.trans h_reassoc)
              -- Build the helper's right-arrowhead hypothesis.
              have h_πfull_j : π = (π.prefix j).append (π.suffix j) :=
                (Walk.prefix_append_suffix π hj).symm
              have h_pre_j_len : (π.prefix j).length = j := Walk.length_prefix π hj
              have h_helper_right :
                  ∃ (wjp1 wj : α) (s_right : WalkStep G wj wjp1) (p_pre_j : Walk G v₀ wj)
                      (rest_j : Walk G wjp1 vₙ),
                    π = p_pre_j.append (Walk.cons s_right rest_j) ∧
                    wj = π.nodeAt (i + (j - i)) ∧
                    p_pre_j.length = i + (j - i) ∧
                    s_right.HasArrowheadAtSource := by
                refine ⟨a_j, π.nodeAt j, s_j, π.prefix j, rest_j, ?_, ?_, ?_, h_s_j_arrowhead⟩
                · rw [h_suf_eq] at h_πfull_j; exact h_πfull_j
                · congr 1; omega
                · rw [h_pre_j_len]; omega
              have hi_n_lt : i + (j - i) < π.length := by
                have : i + (j - i) = j := by omega
                rw [this]; exact hj_lt_π
              have h_n_pos : 0 < j - i := by omega
              obtain ⟨k, _h_k_ge, _h_k_le, h_πColl, h_anc⟩ :=
                Walk.exists_collider_with_anc π (j - i) h_n_pos hi_pos hi_n_lt
                  h_helper_left h_helper_right
              exact CDMG.ancSet_of_anc_ancSet h_anc (h_open.1 k h_πColl)
          · -- i < k < i + σ.length: σ interior.  σ.reverse.IsDirected, so no collider.
            exfalso
            set k' := k - i with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_lt : k' < σ.length := by omega
            have h_eq : i + k' = k := by omega
            rw [← h_eq] at h_coll
            have h_σColl :=
              (Walk.isColliderAt_splice_mid π σ hi_le h_k'_pos h_k'_lt).mp h_coll
            exact Walk.not_isColliderAt_of_isReverseDirected σ k' hσ_rev_dir h_σColl
        · rcases Nat.eq_or_lt_of_le h_k_ge_mid with h_k_eq_mid | h_k_gt_mid
          · -- k = i + σ.length: right joint (case ii) when σ.length ≥ 1; collapsed joint when σ.length = 0.
            subst h_k_eq_mid
            by_cases hσ_pos : 1 ≤ σ.length
            · -- σ.length ≥ 1: NOT a collider since σ's last step is backward.
              exfalso
              -- Decompose σ's last step.
              obtain ⟨w_last_σ, σ_pre, s_last_σ, hσ_last_eq⟩ :=
                Walk.walk_pos_eq_append_last σ hσ_pos
              -- s_last_σ : WalkStep G w_last_σ vⱼ.
              have hσ_pre_len : σ_pre.length = σ.length - 1 := by
                have h_eq : σ.length = σ_pre.length + 1 := by
                  conv_lhs => rw [hσ_last_eq]
                  rw [Walk.length_append, Walk.length_cons, Walk.length_nil]
                omega
              -- s_last_σ is backward (σ.reverse.IsDirected).
              have h_s_last_σ_bw : s_last_σ.IsBackward := by
                rw [hσ_last_eq] at hσ_rev_dir
                rw [Walk.reverse_append, Walk.reverse_cons, Walk.reverse_nil,
                  Walk.nil_append] at hσ_rev_dir
                -- hσ_rev_dir : (cons s_last_σ.reverse σ_pre.reverse).IsDirected
                cases s_last_σ with
                | forward _ => simp at hσ_rev_dir
                | backward _ => simp
                | bidir _ => simp at hσ_rev_dir
              -- W = ((π.prefix i).append σ_pre).append (cons s_last_σ (π.suffix j))
              have hW_form_inner :
                  (π.prefix i).append (σ.append (π.suffix j)) =
                    ((π.prefix i).append σ_pre).append
                      (Walk.cons s_last_σ (π.suffix j)) := by
                rw [hσ_last_eq, Walk.append_assoc, Walk.append_assoc, Walk.cons_append,
                  Walk.nil_append]
              have hpos_inner : ((π.prefix i).append σ_pre).length + 1 = i + σ.length := by
                rw [Walk.length_append, h_pre_len, hσ_pre_len]; omega
              -- Now use `not_isColliderAt_append_cons_at_left_length`'s dual reasoning:
              -- s_last_σ has no target-arrowhead (backward), so the joint is NOT a collider.
              -- We need a separate helper or inline it.
              rw [hW_form_inner] at h_coll
              -- h_coll : (((π.prefix i).append σ_pre).append (cons s_last_σ (π.suffix j))).IsColliderAt (i + σ.length).
              rw [show (i + σ.length : ℕ) = ((π.prefix i).append σ_pre).length + 1 from
                hpos_inner.symm] at h_coll
              -- Decompose π.suffix j to expose s_j.
              rw [h_suf_eq] at h_coll
              -- h_coll : (((π.prefix i).append σ_pre).append (cons s_last_σ (cons s_j rest_j))).IsColliderAt
              --           (((π.prefix i).append σ_pre).length + 1).
              rw [Walk.isColliderAt_append_cons_cons_one] at h_coll
              -- h_coll : s_last_σ.HasArrowheadAtTarget ∧ s_j.HasArrowheadAtSource
              -- s_last_σ backward has HasArrowheadAtTarget = False, contradiction.
              cases s_last_σ with
              | forward _ => simp at h_s_last_σ_bw
              | backward _ => simp at h_coll
              | bidir _ => simp at h_s_last_σ_bw
            · -- σ.length = 0: joint collapses with outer joint.  Same (ii.a)/(ii.b) analysis.
              push_neg at hσ_pos
              have hσ_zero : σ.length = 0 := Nat.lt_one_iff.mp hσ_pos
              -- W's position i + σ.length = i.  W.nodeAt (i + σ.length) reduces to π.nodeAt i.
              rw [Walk.nodeAt_splice_mid π σ hi_le (le_refl σ.length), Walk.nodeAt_length]
              have h_vi_eq_vj : π.nodeAt i = π.nodeAt j :=
                Walk.source_eq_target_of_length_zero σ hσ_zero
              rw [← h_vi_eq_vj]
              -- Goal: π.nodeAt i ∈ G.AncSet C.  Use the (ii.b) collider induction.
              by_cases hi_zero : i = 0
              · subst hi_zero
                -- i = 0: W's position 0 is an endpoint (not a collider).  Exfalso.
                exfalso
                have h_eq : (0 : ℕ) + σ.length = 0 := by rw [hσ_zero]
                rw [h_eq] at h_coll
                exact (Walk.isNonColliderAt_zero _).2 h_coll
              · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
                have h_pre_i_pos : 1 ≤ (π.prefix i).length := by rw [h_pre_len]; omega
                obtain ⟨w_pre_i, p_pre_i, s_left_πi, h_pre_i_eq⟩ :=
                  Walk.walk_pos_eq_append_last (π.prefix i) h_pre_i_pos
                have h_p_pre_i_len : p_pre_i.length = i - 1 := by
                  have h1 : (π.prefix i).length = p_pre_i.length +
                      (Walk.cons s_left_πi (Walk.nil (π.nodeAt i))).length := by
                    rw [h_pre_i_eq, Walk.length_append]
                  rw [h_pre_len] at h1
                  simp [Walk.length_cons, Walk.length_nil] at h1
                  omega
                have h_pos_form_i : (p_pre_i.length + 1 : ℕ) = i := by omega
                have h_app_pos : 1 ≤ (σ.append (π.suffix j)).length := by
                  rw [Walk.length_append]
                  have h_suf_pos : 1 ≤ (π.suffix j).length := by
                    rw [h_suf_eq, Walk.length_cons]; omega
                  omega
                obtain ⟨w_app, s_app, rest_app, h_app_eq⟩ :=
                  Walk.walk_pos_eq_cons _ h_app_pos
                have h_suf_has_src : ∀ (a' : α) (s' : WalkStep G (π.nodeAt j) a')
                    (rest' : Walk G a' vₙ),
                    π.suffix j = Walk.cons s' rest' → s'.HasArrowheadAtSource := by
                  intro a' s' rest' h_eq'
                  rw [h_suf_eq] at h_eq'
                  obtain ⟨h_av, h_sa, _⟩ := Walk.cons.inj h_eq'
                  subst h_av
                  have h_s_eq : s_j = s' := eq_of_heq h_sa
                  rw [← h_s_eq]
                  exact h_s_j_arrowhead
                have h_s_app_src : s_app.HasArrowheadAtSource :=
                  Walk.first_step_has_source_of_reverseDirected_append σ (π.suffix j) _ s_app
                    rest_app hσ_rev_dir h_app_eq h_suf_has_src
                have hW_form_i :
                    (π.prefix i).append (σ.append (π.suffix j)) =
                      p_pre_i.append (Walk.cons s_left_πi
                        (Walk.cons s_app rest_app)) := by
                  rw [h_pre_i_eq, h_app_eq, Walk.append_assoc,
                    Walk.cons_append, Walk.nil_append]
                have h_coll_i : ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt i := by
                  have h_eq : (i + σ.length : ℕ) = i := by omega
                  rw [h_eq] at h_coll
                  exact h_coll
                rw [hW_form_i] at h_coll_i
                have h_at_p : (p_pre_i.append (Walk.cons s_left_πi
                    (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                  convert h_coll_i using 2
                rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                obtain ⟨h_left_arr, _h_right_arr⟩ := h_at_p
                have hj_lt_π : j < π.length := by
                  have hh : 1 ≤ (π.suffix j).length := by rw [h_suf_eq, Walk.length_cons]; omega
                  rw [Walk.length_suffix π hj] at hh
                  omega
                have h_πfull : π = (π.prefix i).append (π.suffix i) :=
                  (Walk.prefix_append_suffix π hi_le).symm
                have h_helper_left :
                    ∃ (wim1 wi : α) (p_pre : Walk G v₀ wim1) (s_left : WalkStep G wim1 wi)
                        (rest : Walk G wi vₙ),
                      π = p_pre.append (Walk.cons s_left rest) ∧
                      wi = π.nodeAt i ∧
                      p_pre.length = i - 1 ∧
                      s_left.HasArrowheadAtTarget := by
                  refine ⟨w_pre_i, π.nodeAt i, p_pre_i, s_left_πi, π.suffix i, ?_, rfl,
                    h_p_pre_i_len, h_left_arr⟩
                  have h_pre_alt :
                      (π.prefix i).append (π.suffix i) =
                        (p_pre_i.append (Walk.cons s_left_πi (Walk.nil _))).append (π.suffix i) := by
                    rw [h_pre_i_eq]
                  have h_reassoc :
                      (p_pre_i.append (Walk.cons s_left_πi (Walk.nil (π.nodeAt i)))).append
                          (π.suffix i) =
                        p_pre_i.append (Walk.cons s_left_πi (π.suffix i)) := by
                    rw [Walk.append_assoc, Walk.cons_append, Walk.nil_append]
                  exact h_πfull.trans (h_pre_alt.trans h_reassoc)
                have h_πfull_j : π = (π.prefix j).append (π.suffix j) :=
                  (Walk.prefix_append_suffix π hj).symm
                have h_pre_j_len : (π.prefix j).length = j := Walk.length_prefix π hj
                have h_helper_right :
                    ∃ (wjp1 wj : α) (s_right : WalkStep G wj wjp1) (p_pre_j : Walk G v₀ wj)
                        (rest_j : Walk G wjp1 vₙ),
                      π = p_pre_j.append (Walk.cons s_right rest_j) ∧
                      wj = π.nodeAt (i + (j - i)) ∧
                      p_pre_j.length = i + (j - i) ∧
                      s_right.HasArrowheadAtSource := by
                  refine ⟨a_j, π.nodeAt j, s_j, π.prefix j, rest_j, ?_, ?_, ?_, h_s_j_arrowhead⟩
                  · rw [h_suf_eq] at h_πfull_j; exact h_πfull_j
                  · congr 1; omega
                  · rw [h_pre_j_len]; omega
                have hi_n_lt : i + (j - i) < π.length := by
                  have : i + (j - i) = j := by omega
                  rw [this]; exact hj_lt_π
                have h_n_pos : 0 < j - i := by omega
                obtain ⟨k, _h_k_ge, _h_k_le, h_πColl, h_anc⟩ :=
                  Walk.exists_collider_with_anc π (j - i) h_n_pos hi_pos hi_n_lt
                  h_helper_left h_helper_right
                exact CDMG.ancSet_of_anc_ancSet h_anc (h_open.1 k h_πColl)
          · -- k > i + σ.length: in suffix part.  Transport via splice_suf.
            have hWlen : ((π.prefix i).append (σ.append (π.suffix j))).length =
                i + σ.length + (π.length - j) := by
              rw [Walk.length_append, h_pre_len, Walk.length_append, h_suf_len, Nat.add_assoc]
            have hk_lt_Wlen : k < ((π.prefix i).append (σ.append (π.suffix j))).length :=
              Walk.isColliderAt_lt_length _ h_coll
            rw [hWlen] at hk_lt_Wlen
            set k' := k - (i + σ.length) with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_le : k' ≤ π.length - j := by omega
            have h_eq : i + σ.length + k' = k := by omega
            rw [← h_eq] at h_coll
            have h_πColl :=
              (Walk.isColliderAt_splice_suf π σ hi_le h_k'_pos).mp h_coll
            rw [← h_eq, Walk.nodeAt_splice_suf π σ hi_le hj h_k'_le]
            exact h_open.1 (j + k') h_πColl
    · -- ===== (1.blkNC) W.IsBlockableNonColliderAt k → W.nodeAt k ∉ C =====
      intro k h_blkNC
      rcases lt_or_ge k i with h_k_lt_i | h_k_ge_i
      · -- k < i: blockable transports to π via splice_pre.
        have h_πNC : π.IsNonColliderAt k := by
          refine ⟨le_trans (le_of_lt h_k_lt_i) hi_le, ?_⟩
          intro h_πColl
          exact h_blkNC.1.2
            ((Walk.isColliderAt_splice_pre π σ hi_le h_k_lt_i).mpr h_πColl)
        have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt k := by
          intro h_πUnblk
          apply h_blkNC.2
          exact (Walk.isUnblockableNonColliderAt_splice_pre π σ hi_le h_k_lt_i).mpr h_πUnblk
        rw [Walk.nodeAt_splice_pre π σ hi_le (le_of_lt h_k_lt_i)]
        exact h_open.2 k ⟨h_πNC, h_πNotUnblk⟩
      · rcases lt_or_ge k (i + σ.length) with h_k_lt_mid | h_k_ge_mid
        · rcases Nat.eq_or_lt_of_le h_k_ge_i with h_k_eq_i | h_k_gt_i
          · -- k = i: outer joint in case (ii).
            -- Sub-cases (ii.a) and (ii.b) based on s_left_πi.
            subst h_k_eq_i
            rw [Walk.nodeAt_splice_pre π σ hi_le (le_refl i)]
            -- Goal: π.nodeAt i ∉ C.
            by_cases hi_zero : i = 0
            · -- i = 0: endpoint.
              subst hi_zero
              exact h_open.2 0 (Walk.isBlockableNonColliderAt_zero π)
            · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
              -- Extract π's step at i-1 (= last step of π.prefix i).
              have h_pre_i_pos : 1 ≤ (π.prefix i).length := by rw [h_pre_len]; omega
              obtain ⟨w_pre_i, p_pre_i, s_left_πi, h_pre_i_eq⟩ :=
                Walk.walk_pos_eq_append_last (π.prefix i) h_pre_i_pos
              have h_p_pre_i_len : p_pre_i.length = i - 1 := by
                have h1 : (π.prefix i).length = p_pre_i.length +
                    (Walk.cons s_left_πi (Walk.nil (π.nodeAt i))).length := by
                  rw [h_pre_i_eq, Walk.length_append]
                rw [h_pre_len] at h1
                simp [Walk.length_cons, Walk.length_nil] at h1
                omega
              have h_pos_form_i : (p_pre_i.length + 1 : ℕ) = i := by omega
              -- Extract first step of σ.append (π.suffix j) as s_app with source-arrowhead.
              have h_app_pos : 1 ≤ (σ.append (π.suffix j)).length := by
                rw [Walk.length_append]
                have h_suf_pos : 1 ≤ (π.suffix j).length := by
                  rw [h_suf_eq, Walk.length_cons]; omega
                omega
              obtain ⟨w_app, s_app, rest_app, h_app_eq⟩ :=
                Walk.walk_pos_eq_cons _ h_app_pos
              have h_suf_has_src : ∀ (a' : α) (s' : WalkStep G (π.nodeAt j) a')
                  (rest' : Walk G a' vₙ),
                  π.suffix j = Walk.cons s' rest' → s'.HasArrowheadAtSource := by
                intro a' s' rest' h_eq'
                rw [h_suf_eq] at h_eq'
                obtain ⟨h_av, h_sa, _⟩ := Walk.cons.inj h_eq'
                subst h_av
                have h_s_eq : s_j = s' := eq_of_heq h_sa
                rw [← h_s_eq]
                exact h_s_j_arrowhead
              have h_s_app_src : s_app.HasArrowheadAtSource :=
                Walk.first_step_has_source_of_reverseDirected_append σ (π.suffix j) _ s_app
                  rest_app hσ_rev_dir h_app_eq h_suf_has_src
              -- Structural form of W at position i.
              have hW_form_i :
                  (π.prefix i).append (σ.append (π.suffix j)) =
                    p_pre_i.append (Walk.cons s_left_πi
                      (Walk.cons s_app rest_app)) := by
                rw [h_pre_i_eq, h_app_eq, Walk.append_assoc,
                  Walk.cons_append, Walk.nil_append]
              -- Case on s_left_πi: backward (ii.a) vs forward/bidir (ii.b).
              cases s_left_πi with
              | forward h_fwd_πi =>
                -- (ii.b): forward s_left has target-arrowhead.  Combined with s_app source-arrowhead,
                -- W.IsColliderAt i.  But h_blkNC.1.2 says ¬ W.IsColliderAt i.  Exfalso.
                exfalso
                apply h_blkNC.1.2
                have h_at_p : (p_pre_i.append (Walk.cons (WalkStep.forward h_fwd_πi)
                    (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                  rw [Walk.isColliderAt_append_cons_cons_one]; exact ⟨by simp, h_s_app_src⟩
                have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt
                    (p_pre_i.length + 1) := by
                  rw [hW_form_i]; exact h_at_p
                convert h_at_W using 2; omega
              | backward h_bw_πi =>
                -- (ii.a): backward s_left.  Joint is non-collider; analyze.
                by_cases h_left_sc : w_pre_i ∈ G.Sc (π.nodeAt i)
                · -- Joint is unblockable.  Exfalso.
                  exfalso
                  apply h_blkNC.2
                  have h_joint : (WalkStep.backward h_bw_πi).IsUnblockableJoint s_app := by
                    refine ⟨?_, ?_, ?_⟩
                    · intro ⟨h_tgt, _⟩; simp at h_tgt
                    · intro _; exact h_left_sc
                    · intro h_fwd
                      cases s_app with
                      | forward _ => simp at h_s_app_src
                      | backward _ => simp at h_fwd
                      | bidir _ => simp at h_fwd
                  have h_at_p :
                      (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                          (Walk.cons s_app rest_app))).IsUnblockableNonColliderAt
                        (p_pre_i.length + 1) :=
                    (Walk.isUnblockableNonColliderAt_append_cons_cons_one p_pre_i
                      (WalkStep.backward h_bw_πi) s_app rest_app).mpr h_joint
                  have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                      (p_pre_i.length + 1) := by
                    rw [hW_form_i]; exact h_at_p
                  convert h_at_W using 2; omega
                · -- Joint not unblockable.  Transport from π at i.
                  -- π's step at i.
                  have hi_lt_π : i < π.length := lt_of_lt_of_le hij hj
                  have h_suf_i_pos : 1 ≤ (π.suffix i).length := by
                    rw [Walk.length_suffix π (le_of_lt hi_lt_π)]; omega
                  obtain ⟨_, s_right_πi, rest_πi, h_suf_i_eq⟩ :=
                    Walk.walk_pos_eq_cons (π.suffix i) h_suf_i_pos
                  have h_alt_eq :
                      (π.prefix i).append (π.suffix i) =
                        p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                          (Walk.cons s_right_πi rest_πi)) := by
                    rw [h_pre_i_eq, h_suf_i_eq, Walk.append_assoc,
                      Walk.cons_append, Walk.nil_append]
                  have hπ_form : π = p_pre_i.append
                      (Walk.cons (WalkStep.backward h_bw_πi)
                        (Walk.cons s_right_πi rest_πi)) := by
                    rw [← h_alt_eq]
                    exact (Walk.prefix_append_suffix π (le_of_lt hi_lt_π)).symm
                  have h_πNC : π.IsNonColliderAt i := by
                    refine ⟨le_of_lt hi_lt_π, ?_⟩
                    intro h_πColl
                    rw [hπ_form] at h_πColl
                    have h_at_p :
                        (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                            (Walk.cons s_right_πi rest_πi))).IsColliderAt
                          (p_pre_i.length + 1) := by
                      convert h_πColl using 2
                    rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                    simp at h_at_p
                  have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt i := by
                    intro h_πUnblk
                    rw [hπ_form] at h_πUnblk
                    have h_at_p :
                        (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                            (Walk.cons s_right_πi rest_πi))).IsUnblockableNonColliderAt
                          (p_pre_i.length + 1) := by
                      convert h_πUnblk using 2
                    rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                    apply h_left_sc
                    exact h_at_p.2.1 (by simp [WalkStep.IsBackward])
                  exact h_open.2 i ⟨h_πNC, h_πNotUnblk⟩
              | bidir h_bd_πi =>
                -- (ii.b): bidir s_left has target-arrowhead.  Same as forward case.
                exfalso
                apply h_blkNC.1.2
                have h_at_p : (p_pre_i.append (Walk.cons (WalkStep.bidir h_bd_πi)
                    (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                  rw [Walk.isColliderAt_append_cons_cons_one]; exact ⟨by simp, h_s_app_src⟩
                have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt
                    (p_pre_i.length + 1) := by
                  rw [hW_form_i]; exact h_at_p
                convert h_at_W using 2; omega
          · -- i < k < i + σ.length: σ interior.  Unblockable via reverseDirected.
            exfalso
            set k' := k - i with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_lt : k' < σ.length := by omega
            have h_eq : i + k' = k := by omega
            apply h_blkNC.2
            rw [← h_eq]
            rw [Walk.isUnblockableNonColliderAt_splice_mid π σ hi_le h_k'_pos h_k'_lt]
            exact Walk.isUnblockableNonColliderAt_interior_of_reverseDirected_in_Sc σ
              hσ_rev_dir hσ_inSc k' h_k'_pos h_k'_lt
        · rcases Nat.eq_or_lt_of_le h_k_ge_mid with h_k_eq_mid | h_k_gt_mid
          · -- k = i + σ.length: right joint (σ.length ≥ 1) OR collapsed joint (σ.length = 0).
            subst h_k_eq_mid
            by_cases hσ_pos : 1 ≤ σ.length
            · -- σ.length ≥ 1: unblockable left-chain joint.  exfalso.
              exfalso
              obtain ⟨w_last_σ, σ_pre, s_last_σ, hσ_last_eq⟩ :=
                Walk.walk_pos_eq_append_last σ hσ_pos
              have hσ_pre_len : σ_pre.length = σ.length - 1 := by
                have h_eq : σ.length = σ_pre.length + 1 := by
                  conv_lhs => rw [hσ_last_eq]
                  rw [Walk.length_append, Walk.length_cons, Walk.length_nil]
                omega
              have h_s_last_σ_bw : s_last_σ.IsBackward := by
                rw [hσ_last_eq] at hσ_rev_dir
                rw [Walk.reverse_append, Walk.reverse_cons, Walk.reverse_nil,
                  Walk.nil_append] at hσ_rev_dir
                cases s_last_σ with
                | forward _ => simp at hσ_rev_dir
                | backward _ => simp
                | bidir _ => simp at hσ_rev_dir
              have h_w_last_σ_sc : w_last_σ ∈ G.Sc (π.nodeAt j) := by
                have h_σ_pre_len_le : σ_pre.length ≤ σ.length := by omega
                have h_in : σ.nodeAt σ_pre.length ∈ G.Sc (π.nodeAt j) :=
                  hσ_inSc σ_pre.length h_σ_pre_len_le
                have h_node_eq : σ.nodeAt σ_pre.length = w_last_σ := by
                  rw [hσ_last_eq]
                  rw [Walk.nodeAt_append_le _ _ (le_refl _)]
                  exact Walk.nodeAt_length _
                rw [h_node_eq] at h_in
                exact h_in
              -- W = ((π.prefix i).append σ_pre).append (cons s_last_σ (cons s_j rest_j))
              have hW_form_inner :
                  (π.prefix i).append (σ.append (π.suffix j)) =
                    ((π.prefix i).append σ_pre).append
                      (Walk.cons s_last_σ (Walk.cons s_j rest_j)) := by
                rw [hσ_last_eq, h_suf_eq, Walk.append_assoc, Walk.append_assoc,
                  Walk.cons_append, Walk.nil_append]
              have hpos_inner : ((π.prefix i).append σ_pre).length + 1 = i + σ.length := by
                rw [Walk.length_append, h_pre_len, hσ_pre_len]; omega
              apply h_blkNC.2
              rw [hW_form_inner]
              rw [show (i + σ.length : ℕ) = ((π.prefix i).append σ_pre).length + 1 from
                hpos_inner.symm]
              rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one]
              refine ⟨?_, ?_, ?_⟩
              · -- ¬ collider: s_last_σ backward has HasArrowheadAtTarget = False.
                intro ⟨h_tgt, _⟩
                cases s_last_σ with
                | forward _ => simp at h_s_last_σ_bw
                | backward _ => simp at h_tgt
                | bidir _ => simp at h_s_last_σ_bw
              · -- s_last_σ.IsBackward → w_last_σ ∈ Sc^G(π.nodeAt j).
                intro _; exact h_w_last_σ_sc
              · -- s_j.IsForward → ...: s_j has source-arrowhead, NOT forward.  Vacuous.
                intro h_fwd
                cases s_j with
                | forward _ => simp at h_s_j_arrowhead
                | backward _ => simp at h_fwd
                | bidir _ => simp at h_fwd
            · -- σ.length = 0: joint collapses with outer joint.  Same (ii.a)/(ii.b) analysis.
              push_neg at hσ_pos
              have hσ_zero : σ.length = 0 := Nat.lt_one_iff.mp hσ_pos
              -- Goal: W.nodeAt (i + σ.length) ∉ C.  Reduce to π.nodeAt i ∉ C.
              rw [Walk.nodeAt_splice_mid π σ hi_le (le_refl σ.length), Walk.nodeAt_length]
              have h_vi_eq_vj : π.nodeAt i = π.nodeAt j :=
                Walk.source_eq_target_of_length_zero σ hσ_zero
              rw [← h_vi_eq_vj]
              -- Goal: π.nodeAt i ∉ C.
              by_cases hi_zero : i = 0
              · subst hi_zero
                exact h_open.2 0 (Walk.isBlockableNonColliderAt_zero π)
              · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
                have h_pre_i_pos : 1 ≤ (π.prefix i).length := by rw [h_pre_len]; omega
                obtain ⟨w_pre_i, p_pre_i, s_left_πi, h_pre_i_eq⟩ :=
                  Walk.walk_pos_eq_append_last (π.prefix i) h_pre_i_pos
                have h_p_pre_i_len : p_pre_i.length = i - 1 := by
                  have h1 : (π.prefix i).length = p_pre_i.length +
                      (Walk.cons s_left_πi (Walk.nil (π.nodeAt i))).length := by
                    rw [h_pre_i_eq, Walk.length_append]
                  rw [h_pre_len] at h1
                  simp [Walk.length_cons, Walk.length_nil] at h1
                  omega
                have h_pos_form_i : (p_pre_i.length + 1 : ℕ) = i := by omega
                have h_app_pos : 1 ≤ (σ.append (π.suffix j)).length := by
                  rw [Walk.length_append]
                  have h_suf_pos : 1 ≤ (π.suffix j).length := by
                    rw [h_suf_eq, Walk.length_cons]; omega
                  omega
                obtain ⟨w_app, s_app, rest_app, h_app_eq⟩ :=
                  Walk.walk_pos_eq_cons _ h_app_pos
                have h_suf_has_src : ∀ (a' : α) (s' : WalkStep G (π.nodeAt j) a')
                    (rest' : Walk G a' vₙ),
                    π.suffix j = Walk.cons s' rest' → s'.HasArrowheadAtSource := by
                  intro a' s' rest' h_eq'
                  rw [h_suf_eq] at h_eq'
                  obtain ⟨h_av, h_sa, _⟩ := Walk.cons.inj h_eq'
                  subst h_av
                  have h_s_eq : s_j = s' := eq_of_heq h_sa
                  rw [← h_s_eq]
                  exact h_s_j_arrowhead
                have h_s_app_src : s_app.HasArrowheadAtSource :=
                  Walk.first_step_has_source_of_reverseDirected_append σ (π.suffix j) _ s_app
                    rest_app hσ_rev_dir h_app_eq h_suf_has_src
                have hW_form_i :
                    (π.prefix i).append (σ.append (π.suffix j)) =
                      p_pre_i.append (Walk.cons s_left_πi
                        (Walk.cons s_app rest_app)) := by
                  rw [h_pre_i_eq, h_app_eq, Walk.append_assoc,
                    Walk.cons_append, Walk.nil_append]
                -- Case on s_left_πi.
                cases s_left_πi with
                | forward h_fwd_πi =>
                  -- (ii.b): collider on W, ¬ collider in h_blkNC fails. Exfalso.
                  exfalso
                  apply h_blkNC.1.2
                  have h_at_p : (p_pre_i.append (Walk.cons (WalkStep.forward h_fwd_πi)
                      (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                    rw [Walk.isColliderAt_append_cons_cons_one]; exact ⟨by simp, h_s_app_src⟩
                  have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt
                      (p_pre_i.length + 1) := by
                    rw [hW_form_i]; exact h_at_p
                  have h_pos_eq : (i + σ.length : ℕ) = p_pre_i.length + 1 := by omega
                  exact h_pos_eq.symm ▸ h_at_W
                | backward h_bw_πi =>
                  -- (ii.a): non-collider on W.  Sub-case on v_{i-1} ∈ Sc^G(v_i).
                  by_cases h_left_sc : w_pre_i ∈ G.Sc (π.nodeAt i)
                  · -- Unblockable → exfalso.
                    exfalso
                    apply h_blkNC.2
                    have h_joint : (WalkStep.backward h_bw_πi).IsUnblockableJoint s_app := by
                      refine ⟨?_, ?_, ?_⟩
                      · intro ⟨h_tgt, _⟩; simp at h_tgt
                      · intro _; exact h_left_sc
                      · intro h_fwd
                        cases s_app with
                        | forward _ => simp at h_s_app_src
                        | backward _ => simp at h_fwd
                        | bidir _ => simp at h_fwd
                    have h_at_p :
                        (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                            (Walk.cons s_app rest_app))).IsUnblockableNonColliderAt
                          (p_pre_i.length + 1) :=
                      (Walk.isUnblockableNonColliderAt_append_cons_cons_one p_pre_i
                        (WalkStep.backward h_bw_πi) s_app rest_app).mpr h_joint
                    have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                        (p_pre_i.length + 1) := by
                      rw [hW_form_i]; exact h_at_p
                    have h_pos_eq : (i + σ.length : ℕ) = p_pre_i.length + 1 := by omega
                    exact h_pos_eq.symm ▸ h_at_W
                  · -- Joint not unblockable.  Transport from π at i.
                    have hi_lt_π : i < π.length := lt_of_lt_of_le hij hj
                    have h_suf_i_pos : 1 ≤ (π.suffix i).length := by
                      rw [Walk.length_suffix π (le_of_lt hi_lt_π)]; omega
                    obtain ⟨_, s_right_πi, rest_πi, h_suf_i_eq⟩ :=
                      Walk.walk_pos_eq_cons (π.suffix i) h_suf_i_pos
                    have h_alt_eq :
                        (π.prefix i).append (π.suffix i) =
                          p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                            (Walk.cons s_right_πi rest_πi)) := by
                      rw [h_pre_i_eq, h_suf_i_eq, Walk.append_assoc,
                        Walk.cons_append, Walk.nil_append]
                    have hπ_form : π = p_pre_i.append
                        (Walk.cons (WalkStep.backward h_bw_πi)
                          (Walk.cons s_right_πi rest_πi)) := by
                      rw [← h_alt_eq]
                      exact (Walk.prefix_append_suffix π (le_of_lt hi_lt_π)).symm
                    have h_πNC : π.IsNonColliderAt i := by
                      refine ⟨le_of_lt hi_lt_π, ?_⟩
                      intro h_πColl
                      rw [hπ_form] at h_πColl
                      have h_at_p :
                          (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                              (Walk.cons s_right_πi rest_πi))).IsColliderAt
                            (p_pre_i.length + 1) := by
                        convert h_πColl using 2
                      rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                      simp at h_at_p
                    have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt i := by
                      intro h_πUnblk
                      rw [hπ_form] at h_πUnblk
                      have h_at_p :
                          (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                              (Walk.cons s_right_πi rest_πi))).IsUnblockableNonColliderAt
                            (p_pre_i.length + 1) := by
                        convert h_πUnblk using 2
                      rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                      apply h_left_sc
                      exact h_at_p.2.1 (by simp [WalkStep.IsBackward])
                    exact h_open.2 i ⟨h_πNC, h_πNotUnblk⟩
                | bidir h_bd_πi =>
                  -- (ii.b): collider on W (bidir has target-arrowhead). Exfalso.
                  exfalso
                  apply h_blkNC.1.2
                  have h_at_p : (p_pre_i.append (Walk.cons (WalkStep.bidir h_bd_πi)
                      (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                    rw [Walk.isColliderAt_append_cons_cons_one]; exact ⟨by simp, h_s_app_src⟩
                  have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt
                      (p_pre_i.length + 1) := by
                    rw [hW_form_i]; exact h_at_p
                  have h_pos_eq : (i + σ.length : ℕ) = p_pre_i.length + 1 := by omega
                  exact h_pos_eq.symm ▸ h_at_W
          · -- k > i + σ.length: transport via splice_suf.
            have hWlen : ((π.prefix i).append (σ.append (π.suffix j))).length =
                i + σ.length + (π.length - j) := by
              rw [Walk.length_append, h_pre_len, Walk.length_append, h_suf_len, Nat.add_assoc]
            have hk_le_Wlen : k ≤ ((π.prefix i).append (σ.append (π.suffix j))).length :=
              h_blkNC.1.1
            rw [hWlen] at hk_le_Wlen
            set k' := k - (i + σ.length) with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_le : k' ≤ π.length - j := by omega
            have h_eq : i + σ.length + k' = k := by omega
            have h_jk'_le : j + k' ≤ π.length := by omega
            have h_πNC : π.IsNonColliderAt (j + k') := by
              refine ⟨h_jk'_le, ?_⟩
              intro h_πColl
              apply h_blkNC.1.2
              rw [← h_eq]
              exact (Walk.isColliderAt_splice_suf π σ hi_le h_k'_pos).mpr h_πColl
            have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt (j + k') := by
              intro h_πUnblk
              apply h_blkNC.2
              rw [← h_eq]
              exact (Walk.isUnblockableNonColliderAt_splice_suf
                π σ hi_le h_k'_pos).mpr h_πUnblk
            rw [← h_eq, Walk.nodeAt_splice_suf π σ hi_le hj h_k'_le]
            exact h_open.2 (j + k') ⟨h_πNC, h_πNotUnblk⟩
  · -- ============================================================
    -- LN case (i): j = π.length OR step at j is forward.
    -- σ is built from h_sc.1.
    -- ============================================================
    -- "No first step of π.suffix j has source-arrowhead":
    have h_suf_no_src : ∀ (a : α) (s : WalkStep G (π.nodeAt j) a)
        (rest : Walk G a vₙ), π.suffix j = Walk.cons s rest →
          ¬ s.HasArrowheadAtSource := by
      intro a s rest h_eq h_src
      exact h_case_ii ⟨a, s, rest, h_eq, h_src⟩
    -- Extract directed walk π_dir : Walk G vᵢ vⱼ from h_sc.1
    obtain ⟨π_dir, h_πdir_dir⟩ := h_sc.1.2
    -- Loop-erase to get a directed path σ
    obtain ⟨σ, hσ_dir, hσ_path⟩ :=
      Walk.exists_path_of_directed π_dir h_πdir_dir
    -- Verify disjunct (3): every position on σ lies in Sc^G(vⱼ).
    have hσ_inSc : ∀ k, k ≤ σ.length → σ.nodeAt k ∈ G.Sc vⱼ :=
      Walk.directed_walk_in_Sc σ hσ_dir h_sc
    refine ⟨σ, ?_, Or.inl hσ_dir, hσ_inSc, hσ_path⟩
    -- All that remains is disjunct (1): σ-openness of the spliced walk.
    refine ⟨?_, ?_⟩
    · -- ===== (1.coll)  W.IsColliderAt k → W.nodeAt k ∈ G.AncSet C =====
      intro k h_coll
      rcases lt_or_ge k i with h_k_lt_i | h_k_ge_i
      · -- k < i: transport via splice_pre.
        have h_πColl :=
          (Walk.isColliderAt_splice_pre π σ hi_le h_k_lt_i).mp h_coll
        rw [Walk.nodeAt_splice_pre π σ hi_le (le_of_lt h_k_lt_i)]
        exact h_open.1 k h_πColl
      · -- k ≥ i.
        rcases lt_or_ge k (i + σ.length) with h_k_lt_mid | h_k_ge_mid
        · -- i ≤ k < i + σ.length.
          rcases Nat.eq_or_lt_of_le h_k_ge_i with h_k_eq_i | h_k_gt_i
          · -- k = i: outer joint.  No collider in case (i).
            exfalso
            subst h_k_eq_i
            by_cases hp2_pos : 1 ≤ (σ.append (π.suffix j)).length
            · obtain ⟨_, s, p₂', hp_eq⟩ := Walk.walk_pos_eq_cons _ hp2_pos
              -- The first step of σ.append (π.suffix j) has no source-arrowhead.
              have h_no_src : ¬ s.HasArrowheadAtSource :=
                Walk.first_step_no_source_of_directed_append σ (π.suffix j) _ s p₂'
                  hσ_dir hp_eq h_suf_no_src
              rw [hp_eq] at h_coll
              have h_coll' :
                  ((π.prefix i).append (Walk.cons s p₂')).IsColliderAt
                    (π.prefix i).length := by
                rw [h_pre_len]; exact h_coll
              exact Walk.not_isColliderAt_append_cons_at_left_length
                (π.prefix i) s p₂' h_no_src h_coll'
            · push_neg at hp2_pos
              have hp2_zero : (σ.append (π.suffix j)).length = 0 :=
                Nat.lt_one_iff.mp hp2_pos
              have hWlen : ((π.prefix i).append (σ.append (π.suffix j))).length = i := by
                rw [Walk.length_append, h_pre_len, hp2_zero]; omega
              apply (Walk.isNonColliderAt_length _).2
              rw [hWlen]
              exact h_coll
          · -- i < k < i + σ.length: interior of σ.
            -- W.IsColliderAt k = σ.IsColliderAt (k - i) by splice_mid.
            -- σ.IsColliderAt = False (directed).
            exfalso
            set k' := k - i with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_lt : k' < σ.length := by omega
            have h_eq : i + k' = k := by omega
            rw [← h_eq] at h_coll
            have h_σColl :=
              (Walk.isColliderAt_splice_mid π σ hi_le h_k'_pos h_k'_lt).mp h_coll
            exact Walk.not_isColliderAt_of_isDirected σ k' hσ_dir h_σColl
        · -- k ≥ i + σ.length.
          rcases Nat.eq_or_lt_of_le h_k_ge_mid with h_k_eq_mid | h_k_gt_mid
          · -- k = i + σ.length: inner joint (or endpoint when j = π.length).
            -- Use append_assoc to rewrite W as ((π.prefix i).append σ).append (π.suffix j).
            -- Position k is then ((π.prefix i).append σ).length, the boundary.
            exfalso
            subst h_k_eq_mid
            -- W = (π.prefix i).append (σ.append (π.suffix j))
            --   = ((π.prefix i).append σ).append (π.suffix j) by append_assoc.
            have hW_assoc :
                (π.prefix i).append (σ.append (π.suffix j)) =
                  ((π.prefix i).append σ).append (π.suffix j) :=
              (Walk.append_assoc _ _ _).symm
            rw [hW_assoc] at h_coll
            -- Now h_coll : (((π.prefix i).append σ).append (π.suffix j)).IsColliderAt (i + σ.length).
            -- Case-on π.suffix j: either cons or nil.
            by_cases hsuf_pos : 1 ≤ (π.suffix j).length
            · -- π.suffix j has a first step. Decompose.
              obtain ⟨_, s, p₂', hsuf_eq⟩ :=
                Walk.walk_pos_eq_cons (π.suffix j) hsuf_pos
              -- First step has no source-arrowhead (by h_suf_no_src).
              have h_no_src : ¬ s.HasArrowheadAtSource :=
                h_suf_no_src _ s p₂' hsuf_eq
              rw [hsuf_eq] at h_coll
              -- h_coll : (((π.prefix i).append σ).append (cons s p₂')).IsColliderAt (i + σ.length).
              have h_len_app : ((π.prefix i).append σ).length = i + σ.length := by
                rw [Walk.length_append, h_pre_len]
              have h_coll' :
                  (((π.prefix i).append σ).append (Walk.cons s p₂')).IsColliderAt
                    ((π.prefix i).append σ).length := by
                rw [h_len_app]; exact h_coll
              exact Walk.not_isColliderAt_append_cons_at_left_length
                ((π.prefix i).append σ) s p₂' h_no_src h_coll'
            · -- π.suffix j has length 0.
              push_neg at hsuf_pos
              have hsuf_zero : (π.suffix j).length = 0 := Nat.lt_one_iff.mp hsuf_pos
              -- Position i + σ.length on W is the endpoint of W.
              have hWlen :
                  (((π.prefix i).append σ).append (π.suffix j)).length =
                    i + σ.length := by
                rw [Walk.length_append, Walk.length_append, h_pre_len, hsuf_zero]; omega
              apply (Walk.isNonColliderAt_length _).2
              rw [hWlen]
              exact h_coll
          · -- k > i + σ.length: in suffix part. Transport.
            have hWlen : ((π.prefix i).append (σ.append (π.suffix j))).length =
                i + σ.length + (π.length - j) := by
              rw [Walk.length_append, h_pre_len, Walk.length_append, h_suf_len, Nat.add_assoc]
            have hk_lt_Wlen : k < ((π.prefix i).append (σ.append (π.suffix j))).length := by
              exact Walk.isColliderAt_lt_length _ h_coll
            rw [hWlen] at hk_lt_Wlen
            set k' := k - (i + σ.length) with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_le : k' ≤ π.length - j := by omega
            have h_eq : i + σ.length + k' = k := by omega
            rw [← h_eq] at h_coll
            have h_πColl :=
              (Walk.isColliderAt_splice_suf π σ hi_le h_k'_pos).mp h_coll
            rw [← h_eq]
            rw [Walk.nodeAt_splice_suf π σ hi_le hj h_k'_le]
            exact h_open.1 (j + k') h_πColl
    · -- ===== (1.blkNC) W.IsBlockableNonColliderAt k → W.nodeAt k ∉ C =====
      intro k h_blkNC
      rcases lt_or_ge k i with h_k_lt_i | h_k_ge_i
      · -- k < i: blockable transports to π.
        have h_πNC : π.IsNonColliderAt k := by
          refine ⟨le_trans (le_of_lt h_k_lt_i) hi_le, ?_⟩
          intro h_πColl
          exact h_blkNC.1.2
            ((Walk.isColliderAt_splice_pre π σ hi_le h_k_lt_i).mpr h_πColl)
        have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt k := by
          intro h_πUnblk
          apply h_blkNC.2
          exact (Walk.isUnblockableNonColliderAt_splice_pre π σ hi_le h_k_lt_i).mpr h_πUnblk
        rw [Walk.nodeAt_splice_pre π σ hi_le (le_of_lt h_k_lt_i)]
        exact h_open.2 k ⟨h_πNC, h_πNotUnblk⟩
      · -- k ≥ i.
        rcases lt_or_ge k (i + σ.length) with h_k_lt_mid | h_k_ge_mid
        · rcases Nat.eq_or_lt_of_le h_k_ge_i with h_k_eq_i | h_k_gt_i
          · -- k = i: outer joint blockable analysis.
            subst h_k_eq_i
            -- Goal: W.nodeAt i ∉ C.  Reduce W.nodeAt i to π.nodeAt i.
            rw [Walk.nodeAt_splice_pre π σ hi_le (le_refl i)]
            -- Now goal: π.nodeAt i ∉ C.
            -- Case on i = 0 (endpoint) vs i ≥ 1.
            by_cases hi_zero : i = 0
            · subst hi_zero
              exact h_open.2 0 (Walk.isBlockableNonColliderAt_zero π)
            · -- i ≥ 1.
              have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
              -- Extract π's step at i-1: the last step of π.prefix i.
              have h_pre_pos : 1 ≤ (π.prefix i).length := by rw [h_pre_len]; omega
              obtain ⟨w_pre, p_pre, s_left, h_pre_eq⟩ :=
                Walk.walk_pos_eq_append_last (π.prefix i) h_pre_pos
              -- p_pre.length = i - 1.
              have h_p_pre_len : p_pre.length = i - 1 := by
                have h1 : (π.prefix i).length =
                    p_pre.length + (Walk.cons s_left (Walk.nil (π.nodeAt i))).length := by
                  rw [h_pre_eq, Walk.length_append]
                rw [h_pre_len] at h1
                simp [Walk.length_cons, Walk.length_nil] at h1
                omega
              -- Case on σ.append (π.suffix j) length.
              by_cases hp2_pos : 1 ≤ (σ.append (π.suffix j)).length
              · -- σ.append (π.suffix j) is a cons.
                obtain ⟨w_r, s_right, p_rest, hp_eq⟩ :=
                  Walk.walk_pos_eq_cons _ hp2_pos
                -- W = p_pre ⧺ cons s_left (cons s_right p_rest) (after rewriting).
                have hW_form : ((π.prefix i).append (σ.append (π.suffix j))) =
                    p_pre.append (Walk.cons s_left (Walk.cons s_right p_rest)) := by
                  rw [h_pre_eq, hp_eq, Walk.append_assoc]
                  rw [Walk.cons_append, Walk.nil_append]
                -- s_right has no source-arrowhead (case (i)).
                have h_s_right_no_src : ¬ s_right.HasArrowheadAtSource :=
                  Walk.first_step_no_source_of_directed_append σ (π.suffix j) _ s_right p_rest
                    hσ_dir hp_eq h_suf_no_src
                -- The joint condition: if (2) and (3) hold, joint is unblockable on W,
                -- contradicting h_blkNC.2.  Otherwise, derive π.IsBlockableNonColliderAt i
                -- (or j when σ.length = 0).
                -- s_right is forward (no source-arrowhead).
                have h_s_right_fwd : s_right.IsForward := by
                  cases s_right with
                  | forward _ => simp
                  | backward _ => simp at h_s_right_no_src
                  | bidir _ => simp at h_s_right_no_src
                -- Position-on-W shift identity.
                have h_pos_form : (p_pre.length + 1 : ℕ) = i := by omega
                -- W is unblockable at (p_pre.length + 1) iff s_left.IsUnblockableJoint s_right.
                -- We avoid rewriting i in the iff (since s_left's type mentions vᵢ = π.nodeAt i).
                have h_unblk_iff :
                    ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                      (p_pre.length + 1) ↔ s_left.IsUnblockableJoint s_right := by
                  rw [hW_form]
                  exact Walk.isUnblockableNonColliderAt_append_cons_cons_one
                    p_pre s_left s_right p_rest
                -- ¬ Unblockable joint:
                have h_no_unblk : ¬ s_left.IsUnblockableJoint s_right := by
                  intro h_joint
                  have h_at_p : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                      (p_pre.length + 1) := h_unblk_iff.mpr h_joint
                  apply h_blkNC.2
                  convert h_at_p using 2
                  exact h_pos_form.symm
                -- Unpacking ¬ IsUnblockableJoint: since ¬ collider holds, either
                -- (s_left.IsBackward ∧ source ∉ Sc) or (s_right.IsForward ∧ target ∉ Sc).
                -- We split via classical reasoning.
                -- Show what target(s_right) and source(s_left) are.
                -- For target ∈ Sc^G(vᵢ): determined by σ.length.
                by_cases h_target_sc : w_r ∈ G.Sc (π.nodeAt i)
                · -- target ∈ Sc^G(vᵢ): (3) holds.  So (2) must fail.
                  -- (2) fails: s_left.IsBackward ∧ source ∉ Sc^G(vᵢ).
                  -- s_left's type is WalkStep G w_pre (π.nodeAt i).
                  by_cases h_source_sc : w_pre ∈ G.Sc (π.nodeAt i)
                  · -- (2) vacuous or holds. Combined with (3), joint unblockable. Contradiction.
                    exfalso
                    apply h_no_unblk
                    refine ⟨?_, ?_, ?_⟩
                    · intro ⟨_, hsrc⟩; exact h_s_right_no_src hsrc
                    · intro _; exact h_source_sc
                    · intro _; exact h_target_sc
                  · -- s_left.IsBackward must hold (since (2) fails requires backward).
                    -- And source ∉ Sc.
                    -- So s_left is backward, and v_{i-1} ∉ Sc.
                    -- This means on π at position i, the joint is (s_left=backward, π's step at i).
                    -- v_i on π is non-collider (s_left no target-arrowhead) AND blockable
                    -- (outgoing to v_{i-1} ∉ Sc). v_i ∉ C.
                    -- To verify s_left is backward, we examine its constructor.
                    cases s_left with
                    | forward h_e =>
                      -- s_left forward: target-arrowhead True, source-arrowhead False.
                      -- (2) is vacuous (IsBackward = False). But h_source_sc says source ∉ Sc.
                      -- Need: joint condition (2) to be the failure point.
                      -- Hmm, with s_left forward, (2) is vacuous → no contribution to ¬ unblockable.
                      -- (3) holds → joint unblockable → contradict h_no_unblk.
                      exfalso
                      apply h_no_unblk
                      refine ⟨?_, ?_, ?_⟩
                      · intro ⟨_, hsrc⟩; exact h_s_right_no_src hsrc
                      · intro h_back; simp at h_back
                      · intro _; exact h_target_sc
                    | backward h_e =>
                      -- s_left backward: source ∉ Sc^G(vᵢ).
                      -- On π at i: blockable.  Construct π.IsBlockableNonColliderAt i.
                      have hi_lt_π : i < π.length := lt_of_lt_of_le hij hj
                      have h_suf_i_pos : 1 ≤ (π.suffix i).length := by
                        rw [Walk.length_suffix π (le_of_lt hi_lt_π)]; omega
                      obtain ⟨_, s_right_π, rest_π, h_suf_i_eq⟩ :=
                        Walk.walk_pos_eq_cons (π.suffix i) h_suf_i_pos
                      -- Establish π in the structural form, via two-step Eq.trans:
                      --   π = (π.prefix i).append (π.suffix i)
                      --     = (p_pre ⧺ cons s_left (nil _)) ⧺ (cons s_right_π rest_π)
                      --     = p_pre ⧺ cons s_left (cons s_right_π rest_π).
                      have h_alt_eq :
                          (π.prefix i).append (π.suffix i) =
                            p_pre.append (Walk.cons (WalkStep.backward h_e)
                              (Walk.cons s_right_π rest_π)) := by
                        rw [h_pre_eq, h_suf_i_eq, Walk.append_assoc,
                          Walk.cons_append, Walk.nil_append]
                      have hπ_form : π = p_pre.append
                          (Walk.cons (WalkStep.backward h_e)
                            (Walk.cons s_right_π rest_π)) := by
                        rw [← h_alt_eq]
                        exact (Walk.prefix_append_suffix π (le_of_lt hi_lt_π)).symm
                      -- π is non-collider at i: s_left has no target-arrowhead.
                      have h_πNC : π.IsNonColliderAt i := by
                        refine ⟨le_of_lt hi_lt_π, ?_⟩
                        intro h_πColl
                        rw [hπ_form] at h_πColl
                        have h_at_p :
                            (p_pre.append (Walk.cons (WalkStep.backward h_e)
                                (Walk.cons s_right_π rest_π))).IsColliderAt
                              (p_pre.length + 1) := by
                          convert h_πColl using 2
                        rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                        simp at h_at_p
                      -- π is not unblockable at i: (2) fails (source = w_pre ∉ Sc).
                      have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt i := by
                        intro h_πUnblk
                        rw [hπ_form] at h_πUnblk
                        have h_at_p :
                            (p_pre.append (Walk.cons (WalkStep.backward h_e)
                                (Walk.cons s_right_π rest_π))).IsUnblockableNonColliderAt
                              (p_pre.length + 1) := by
                          convert h_πUnblk using 2
                        rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                        -- h_at_p : (backward h_e).IsUnblockableJoint s_right_π.
                        -- This requires (2): source (= w_pre) ∈ Sc^G(target = vᵢ).
                        -- But h_source_sc says ¬ (w_pre ∈ G.Sc vᵢ).
                        apply h_source_sc
                        exact h_at_p.2.1 (by simp [WalkStep.IsBackward])
                      exact h_open.2 i ⟨h_πNC, h_πNotUnblk⟩
                    | bidir h_e =>
                      -- s_left bidir: source-arrowhead True (in particular target-arrowhead True).
                      -- (2) vacuous. (3) holds → joint unblockable → contradict.
                      exfalso
                      apply h_no_unblk
                      refine ⟨?_, ?_, ?_⟩
                      · intro ⟨_, hsrc⟩; exact h_s_right_no_src hsrc
                      · intro h_back; simp at h_back
                      · intro _; exact h_target_sc
                · -- target ∉ Sc^G(vᵢ): (3) fails.
                  -- We claim σ.length = 0 (otherwise target = σ.nodeAt 1 ∈ Sc, contradiction).
                  by_cases hσ_pos : 1 ≤ σ.length
                  · -- σ.length ≥ 1: σ's first step is forward, target = σ.nodeAt 1.
                    -- Show target ∈ Sc^G(vⱼ) = Sc^G(vᵢ), contradicting h_target_sc.
                    exfalso
                    apply h_target_sc
                    obtain ⟨_, sσ, σrest, hσ_eq⟩ := Walk.walk_pos_eq_cons σ hσ_pos
                    have hp_eq' : σ.append (π.suffix j) =
                        Walk.cons sσ (σrest.append (π.suffix j)) := by
                      rw [hσ_eq, Walk.cons_append]
                    rw [hp_eq'] at hp_eq
                    obtain ⟨h_w_eq, _, _⟩ := Walk.cons.inj hp_eq
                    have h_sc_node1 : σ.nodeAt 1 ∈ G.Sc vⱼ :=
                      hσ_inSc 1 (by omega)
                    have h_node1_eq : σ.nodeAt 1 = w_r := by
                      rw [hσ_eq]
                      change σrest.nodeAt 0 = w_r
                      rw [Walk.nodeAt_zero]
                      exact h_w_eq
                    rw [h_node1_eq] at h_sc_node1
                    -- Now w_r ∈ G.Sc vⱼ.  Convert to w_r ∈ G.Sc vᵢ via Sc-equivalence.
                    obtain ⟨h_anc, h_desc⟩ := h_sc_node1
                    refine ⟨?_, ?_⟩
                    · obtain ⟨h_wr_mem, ⟨p_wr_vj, hp_wr_vj⟩⟩ := h_anc
                      obtain ⟨_, ⟨p_vj_vi, hp_vj_vi⟩⟩ := h_sc.2
                      exact ⟨h_wr_mem, ⟨p_wr_vj.append p_vj_vi,
                        Walk.isDirected_append _ _ hp_wr_vj hp_vj_vi⟩⟩
                    · obtain ⟨_, ⟨p_vi_vj, hp_vi_vj⟩⟩ := h_sc.1
                      obtain ⟨h_wr_mem, ⟨p_vj_wr, hp_vj_wr⟩⟩ := h_desc
                      exact ⟨h_wr_mem, ⟨p_vi_vj.append p_vj_wr,
                        Walk.isDirected_append _ _ hp_vi_vj hp_vj_wr⟩⟩
                  · -- σ.length = 0: σ = nil; vᵢ = vⱼ.  Transport from π's σ-openness at j.
                    push_neg at hσ_pos
                    have hσ_zero : σ.length = 0 := Nat.lt_one_iff.mp hσ_pos
                    have h_vi_eq_vj : π.nodeAt i = π.nodeAt j :=
                      Walk.source_eq_target_of_length_zero σ hσ_zero
                    -- Show j < π.length.
                    have hj_lt_π : j < π.length := by
                      rcases lt_or_eq_of_le hj with hj_lt | hj_eq
                      · exact hj_lt
                      · exfalso
                        have h_suf_z : (π.suffix j).length = 0 := by
                          rw [h_suf_len]; omega
                        have : (σ.append (π.suffix j)).length = 0 := by
                          rw [Walk.length_append, hσ_zero, h_suf_z]
                        omega
                    -- Extract π's step at j-1 and at j.
                    have h_pre_j_pos : 1 ≤ (π.prefix j).length := by
                      rw [Walk.length_prefix π hj]; omega
                    obtain ⟨w_pre_j, p_pre_j, s_left_πj, h_pre_j_eq⟩ :=
                      Walk.walk_pos_eq_append_last (π.prefix j) h_pre_j_pos
                    have h_suf_j_pos : 1 ≤ (π.suffix j).length := by
                      rw [h_suf_len]; omega
                    obtain ⟨mid_πj, s_right_πj, rest_πj, h_suf_j_eq⟩ :=
                      Walk.walk_pos_eq_cons (π.suffix j) h_suf_j_pos
                    -- s_right_πj has no source-arrowhead (case (i)).
                    have h_no_src_πj : ¬ s_right_πj.HasArrowheadAtSource :=
                      h_suf_no_src _ s_right_πj rest_πj h_suf_j_eq
                    have h_s_right_πj_fwd : s_right_πj.IsForward := by
                      cases s_right_πj with
                      | forward _ => simp
                      | backward _ => simp at h_no_src_πj
                      | bidir _ => simp at h_no_src_πj
                    -- mid_πj = π.nodeAt (j + 1) (via nodeAt of π.suffix j at 1).
                    have h_mid_eq : mid_πj = π.nodeAt (j + 1) := by
                      have h1 : (π.suffix j).nodeAt 1 = π.nodeAt (j + 1) :=
                        Walk.nodeAt_suffix π (by rw [h_suf_len] at h_suf_j_pos; omega)
                      have h2 : (π.suffix j).nodeAt 1 = mid_πj := by
                        rw [h_suf_j_eq]
                        change rest_πj.nodeAt 0 = mid_πj
                        rw [Walk.nodeAt_zero]
                      exact h2.symm.trans h1
                    -- w_r = π.nodeAt (j+1).  Via nodeAt computation.
                    have h_w_r_eq : w_r = π.nodeAt (j + 1) := by
                      -- (σ.append (π.suffix j)).nodeAt 1 = w_r (from hp_eq).
                      have h1 : (σ.append (π.suffix j)).nodeAt 1 = w_r := by
                        rw [hp_eq]
                        change p_rest.nodeAt 0 = w_r
                        rw [Walk.nodeAt_zero]
                      -- (σ.append (π.suffix j)).nodeAt 1 = π.nodeAt (j+1) when σ.length = 0.
                      have h2 : (σ.append (π.suffix j)).nodeAt 1 = π.nodeAt (j + 1) := by
                        have h_at_σl : (σ.append (π.suffix j)).nodeAt (σ.length + 1) =
                            (π.suffix j).nodeAt 1 :=
                          Walk.nodeAt_append_add_left σ (π.suffix j) 1
                        rw [hσ_zero, Nat.zero_add] at h_at_σl
                        rw [h_at_σl]
                        exact Walk.nodeAt_suffix π (by rw [h_suf_len] at h_suf_j_pos; omega)
                      exact h1.symm.trans h2
                    -- Now build π.IsBlockableNonColliderAt j.
                    have h_p_pre_j_len : p_pre_j.length = j - 1 := by
                      have h1 : (π.prefix j).length =
                          p_pre_j.length +
                            (Walk.cons s_left_πj (Walk.nil (π.nodeAt j))).length := by
                        rw [h_pre_j_eq, Walk.length_append]
                      rw [Walk.length_prefix π hj] at h1
                      simp [Walk.length_cons, Walk.length_nil] at h1
                      omega
                    have h_pos_form_j : (p_pre_j.length + 1 : ℕ) = j := by omega
                    have h_alt_eq_j :
                        (π.prefix j).append (π.suffix j) =
                          p_pre_j.append
                            (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj)) := by
                      rw [h_pre_j_eq, h_suf_j_eq, Walk.append_assoc,
                        Walk.cons_append, Walk.nil_append]
                    have hπ_form_j : π = p_pre_j.append
                        (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj)) := by
                      rw [← h_alt_eq_j]
                      exact (Walk.prefix_append_suffix π hj).symm
                    have h_πNC_j : π.IsNonColliderAt j := by
                      refine ⟨le_of_lt hj_lt_π, ?_⟩
                      intro h_πColl
                      rw [hπ_form_j] at h_πColl
                      have h_at_p :
                          (p_pre_j.append
                            (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj))).IsColliderAt
                            (p_pre_j.length + 1) := by
                        convert h_πColl using 2
                      rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                      exact h_no_src_πj h_at_p.2
                    have h_πNotUnblk_j : ¬ π.IsUnblockableNonColliderAt j := by
                      intro h_πUnblk
                      rw [hπ_form_j] at h_πUnblk
                      have h_at_p :
                          (p_pre_j.append
                            (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj))).IsUnblockableNonColliderAt
                            (p_pre_j.length + 1) := by
                        convert h_πUnblk using 2
                      rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                      -- h_at_p : s_left_πj.IsUnblockableJoint s_right_πj.
                      -- Use (3): target(s_right_πj) ∈ Sc^G(π.nodeAt j).
                      -- target(s_right_πj) = π.nodeAt (j+1) (defeq).
                      have h_target_in_Sc : π.nodeAt (j+1) ∈ G.Sc (π.nodeAt j) := by
                        have h_at_target := h_at_p.2.2 h_s_right_πj_fwd
                        -- h_at_target : mid_πj ∈ G.Sc (π.nodeAt j).
                        -- mid_πj = π.nodeAt (j+1) by h_mid_eq.
                        rw [← h_mid_eq]
                        exact h_at_target
                      apply h_target_sc
                      rw [h_w_r_eq, h_vi_eq_vj]
                      exact h_target_in_Sc
                    rw [h_vi_eq_vj]
                    exact h_open.2 j ⟨h_πNC_j, h_πNotUnblk_j⟩
              · -- σ.append (π.suffix j) has length 0: σ.length = 0 AND j = π.length.
                push_neg at hp2_pos
                have hp2_zero : (σ.append (π.suffix j)).length = 0 := Nat.lt_one_iff.mp hp2_pos
                -- W has length i + 0 = i. Position i is endpoint of W.
                -- vᵢ = vⱼ = vₙ. Use π's σ-openness at endpoint π.length.
                -- σ.length + (π.length - j) = 0 → σ.length = 0 ∧ j = π.length.
                have h_σ_zero : σ.length = 0 := by
                  rw [Walk.length_append] at hp2_zero
                  omega
                have h_j_eq : j = π.length := by
                  rw [Walk.length_append, h_suf_len] at hp2_zero
                  omega
                -- π.nodeAt i = π.nodeAt j (since vᵢ = vⱼ from σ.length = 0).
                -- And j = π.length so vⱼ = vₙ.
                have h_vi_eq_vj : π.nodeAt i = π.nodeAt j := by
                  have := Walk.source_eq_target_of_length_zero σ h_σ_zero
                  exact this
                have h_vj_eq_vn : π.nodeAt j = vₙ := by
                  rw [h_j_eq, Walk.nodeAt_length]
                rw [h_vi_eq_vj, h_vj_eq_vn]
                -- Goal: vₙ ∉ C.
                have := h_open.2 π.length (Walk.isBlockableNonColliderAt_length π)
                rw [Walk.nodeAt_length] at this
                exact this
          · -- i < k < i + σ.length: interior of σ.  σ is directed so all interior
            -- joints are unblockable (Walk.isUnblockableNonColliderAt_interior_of_directed_in_Sc).
            exfalso
            set k' := k - i with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_lt : k' < σ.length := by omega
            have h_eq : i + k' = k := by omega
            apply h_blkNC.2
            rw [← h_eq]
            rw [Walk.isUnblockableNonColliderAt_splice_mid π σ hi_le h_k'_pos h_k'_lt]
            exact Walk.isUnblockableNonColliderAt_interior_of_directed_in_Sc σ
              hσ_dir hσ_inSc k' h_k'_pos h_k'_lt
        · rcases Nat.eq_or_lt_of_le h_k_ge_mid with h_k_eq_mid | h_k_gt_mid
          · -- k = i + σ.length: inner joint blockable analysis.
            subst h_k_eq_mid
            -- Reduce W.nodeAt (i + σ.length) to vⱼ.
            -- nodeAt_splice_mid with k' = σ.length: W.nodeAt (i + σ.length) = σ.nodeAt σ.length = vⱼ.
            rw [Walk.nodeAt_splice_mid π σ hi_le (le_refl σ.length), Walk.nodeAt_length]
            -- Goal: vⱼ ∉ C.
            -- Case on whether π.nodeAt (j+1) ∈ Sc^G(vⱼ).
            -- Also need: j < π.length (when σ.length doesn't fill W).
            have h_W_len_eq : ((π.prefix i).append (σ.append (π.suffix j))).length =
                i + σ.length + (π.length - j) := by
              rw [Walk.length_append, h_pre_len, Walk.length_append, h_suf_len, Nat.add_assoc]
            -- Bounds: from blockable, i + σ.length ≤ W.length, hence π.length - j ≥ 0
            -- (always true).  We need to know if j = π.length (then W's right side
            -- is empty and position i + σ.length is endpoint) or j < π.length.
            by_cases hj_eq_π : j = π.length
            · -- j = π.length: right side of W is empty.  Position i + σ.length is endpoint.
              -- vⱼ = vₙ.
              rw [show π.nodeAt j = vₙ from by rw [hj_eq_π, Walk.nodeAt_length]]
              have := h_open.2 π.length (Walk.isBlockableNonColliderAt_length π)
              rw [Walk.nodeAt_length] at this
              exact this
            · -- j < π.length.
              have hj_lt_π : j < π.length := lt_of_le_of_ne hj hj_eq_π
              -- Extract π's step at j.
              have h_suf_j_pos : 1 ≤ (π.suffix j).length := by
                rw [h_suf_len]; omega
              obtain ⟨mid_πj, s_right_πj, rest_πj, h_suf_j_eq⟩ :=
                Walk.walk_pos_eq_cons (π.suffix j) h_suf_j_pos
              -- s_right_πj is forward (case (i) via h_suf_no_src).
              have h_no_src_πj : ¬ s_right_πj.HasArrowheadAtSource :=
                h_suf_no_src _ s_right_πj rest_πj h_suf_j_eq
              have h_s_right_πj_fwd : s_right_πj.IsForward := by
                cases s_right_πj with
                | forward _ => simp
                | backward _ => simp at h_no_src_πj
                | bidir _ => simp at h_no_src_πj
              -- mid_πj = π.nodeAt (j+1).
              have h_mid_eq : mid_πj = π.nodeAt (j + 1) := by
                have h1 : (π.suffix j).nodeAt 1 = π.nodeAt (j + 1) :=
                  Walk.nodeAt_suffix π (by rw [h_suf_len] at h_suf_j_pos; omega)
                have h2 : (π.suffix j).nodeAt 1 = mid_πj := by
                  rw [h_suf_j_eq]
                  change rest_πj.nodeAt 0 = mid_πj
                  rw [Walk.nodeAt_zero]
                exact h2.symm.trans h1
              -- Case on whether the joint's right-target is in Sc.
              by_cases h_target_sc : π.nodeAt (j + 1) ∈ G.Sc (π.nodeAt j)
              · -- Joint is unblockable on W (when σ.length ≥ 1).
                -- For σ.length = 0, we drop to a direct argument (no exfalso).
                by_cases hσ_pos : 1 ≤ σ.length
                · -- σ.length ≥ 1: σ ends with last step (forward).
                  exfalso
                  apply h_blkNC.2
                  -- Decompose σ via walk_pos_eq_append_last.
                  obtain ⟨w_last_σ, σ_pre, s_last_σ, hσ_last_eq⟩ :=
                    Walk.walk_pos_eq_append_last σ hσ_pos
                  -- s_last_σ : WalkStep G w_last_σ (π.nodeAt j).
                  -- σ.length = σ_pre.length + 1.
                  have hσ_pre_len : σ_pre.length = σ.length - 1 := by
                    have h_eq : σ.length = σ_pre.length + 1 := by
                      conv_lhs => rw [hσ_last_eq]
                      rw [Walk.length_append, Walk.length_cons, Walk.length_nil]
                    omega
                  -- σ_pre.nodeAt σ_pre.length = w_last_σ (target of σ_pre = source of s_last_σ).
                  -- And σ.nodeAt (σ.length - 1) = w_last_σ (source of last step).
                  -- We have hσ_inSc, so σ.nodeAt (σ_pre.length) = σ.nodeAt (σ.length - 1) ∈ Sc^G(vⱼ).
                  -- Hence w_last_σ ∈ Sc^G(vⱼ).
                  have h_w_last_σ_sc : w_last_σ ∈ G.Sc (π.nodeAt j) := by
                    have h_σ_pre_len_le : σ_pre.length ≤ σ.length := by omega
                    have h_in : σ.nodeAt σ_pre.length ∈ G.Sc (π.nodeAt j) :=
                      hσ_inSc σ_pre.length h_σ_pre_len_le
                    -- σ.nodeAt σ_pre.length = w_last_σ (the source of s_last_σ).
                    have h_node_eq : σ.nodeAt σ_pre.length = w_last_σ := by
                      rw [hσ_last_eq]
                      -- (σ_pre.append (cons s_last_σ (nil vⱼ))).nodeAt σ_pre.length =
                      --   σ_pre.nodeAt σ_pre.length = w_last_σ (the target of σ_pre).
                      rw [Walk.nodeAt_append_le _ _ (le_refl _)]
                      exact Walk.nodeAt_length _
                    rw [h_node_eq] at h_in
                    exact h_in
                  -- s_last_σ is forward (σ.IsDirected).
                  have h_s_last_σ_fwd : s_last_σ.IsForward := by
                    have h_σ_dir' : (σ_pre.append (Walk.cons s_last_σ
                        (Walk.nil (π.nodeAt j)))).IsDirected := by
                      rw [← hσ_last_eq]; exact hσ_dir
                    -- The last step is forward via the split-append directedness helper.
                    obtain ⟨_, h_last_dir⟩ := Walk.isDirected_split_append σ_pre _ h_σ_dir'
                    -- h_last_dir : (cons s_last_σ (nil _)).IsDirected.
                    cases s_last_σ with
                    | forward _ => simp
                    | backward _ => simp at h_last_dir
                    | bidir _ => simp at h_last_dir
                  -- Now express W = ((π.prefix i).append σ_pre).append (cons s_last_σ
                  --   (cons s_right_πj rest_πj)) and apply joint lemma.
                  have hW_form_inner :
                      (π.prefix i).append (σ.append (π.suffix j)) =
                        ((π.prefix i).append σ_pre).append
                          (Walk.cons s_last_σ (Walk.cons s_right_πj rest_πj)) := by
                    rw [hσ_last_eq, h_suf_j_eq, Walk.append_assoc, Walk.append_assoc,
                      Walk.cons_append, Walk.nil_append]
                  have hpos_inner : ((π.prefix i).append σ_pre).length + 1 = i + σ.length := by
                    rw [Walk.length_append, h_pre_len, hσ_pre_len]; omega
                  -- Apply isUnblockableNonColliderAt_append_cons_cons_one.
                  rw [hW_form_inner]
                  have h_at_p :
                      (((π.prefix i).append σ_pre).append
                        (Walk.cons s_last_σ (Walk.cons s_right_πj rest_πj))).IsUnblockableNonColliderAt
                          (((π.prefix i).append σ_pre).length + 1) ↔
                        s_last_σ.IsUnblockableJoint s_right_πj :=
                    Walk.isUnblockableNonColliderAt_append_cons_cons_one
                      ((π.prefix i).append σ_pre) s_last_σ s_right_πj rest_πj
                  -- Convert position.
                  have h_at_p' :
                      (((π.prefix i).append σ_pre).append
                        (Walk.cons s_last_σ (Walk.cons s_right_πj rest_πj))).IsUnblockableNonColliderAt
                          (i + σ.length) ↔
                        s_last_σ.IsUnblockableJoint s_right_πj := by
                    rw [← hpos_inner]; exact h_at_p
                  rw [h_at_p']
                  -- Build IsUnblockableJoint: forward-forward, with target ∈ Sc^G(vⱼ).
                  refine ⟨?_, ?_, ?_⟩
                  · -- ¬ collider: s_right_πj forward → no source-arrowhead.
                    intro ⟨_, h_src⟩; exact h_no_src_πj h_src
                  · -- s_last_σ.IsBackward → ...: s_last_σ forward, vacuous.
                    intro h_back
                    cases s_last_σ with
                    | forward _ => simp at h_back
                    | backward _ => simp at h_s_last_σ_fwd
                    | bidir _ => simp at h_s_last_σ_fwd
                  · -- s_right_πj.IsForward → mid_πj ∈ Sc^G(π.nodeAt j).
                    intro _
                    rw [h_mid_eq]
                    exact h_target_sc
                · -- σ.length = 0: σ = nil, merged joint = outer joint.
                  -- Goal: π.nodeAt j ∉ C.
                  push_neg at hσ_pos
                  have hσ_zero : σ.length = 0 := Nat.lt_one_iff.mp hσ_pos
                  have h_vi_eq_vj : π.nodeAt i = π.nodeAt j :=
                    Walk.source_eq_target_of_length_zero σ hσ_zero
                  rw [← h_vi_eq_vj]
                  -- Goal: π.nodeAt i ∉ C.
                  by_cases hi_zero : i = 0
                  · -- i = 0: transport from h_open.2 0.
                    subst hi_zero
                    exact h_open.2 0 (Walk.isBlockableNonColliderAt_zero π)
                  · -- i ≥ 1: case-on π's step at i-1.
                    have h_i_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
                    have h_pre_i_pos : 1 ≤ (π.prefix i).length := by
                      rw [h_pre_len]; omega
                    obtain ⟨w_pre_i, p_pre_i, s_left_πi, h_pre_i_eq⟩ :=
                      Walk.walk_pos_eq_append_last (π.prefix i) h_pre_i_pos
                    have h_p_pre_i_len : p_pre_i.length = i - 1 := by
                      have h1 : (π.prefix i).length =
                          p_pre_i.length +
                            (Walk.cons s_left_πi (Walk.nil (π.nodeAt i))).length := by
                        rw [h_pre_i_eq, Walk.length_append]
                      rw [h_pre_len] at h1
                      simp [Walk.length_cons, Walk.length_nil] at h1
                      omega
                    have h_pos_form_i : (p_pre_i.length + 1 : ℕ) = i := by omega
                    -- Decompose σ.append (π.suffix j) directly (its source is π.nodeAt i).
                    have h_app_pos : 1 ≤ (σ.append (π.suffix j)).length := by
                      rw [Walk.length_append, hσ_zero, Nat.zero_add]
                      exact h_suf_j_pos
                    obtain ⟨w_app, s_app, rest_app, h_app_eq⟩ :=
                      Walk.walk_pos_eq_cons (σ.append (π.suffix j)) h_app_pos
                    -- s_app has source π.nodeAt i and no source-arrowhead.
                    have h_no_src_app : ¬ s_app.HasArrowheadAtSource :=
                      Walk.first_step_no_source_of_directed_append σ (π.suffix j) _ s_app rest_app
                        hσ_dir h_app_eq h_suf_no_src
                    -- Show w_app = π.nodeAt (j + 1).
                    have h_w_app_eq : w_app = π.nodeAt (j + 1) := by
                      have h1 : (σ.append (π.suffix j)).nodeAt 1 = w_app := by
                        rw [h_app_eq]
                        change rest_app.nodeAt 0 = w_app
                        rw [Walk.nodeAt_zero]
                      have h2 : (σ.append (π.suffix j)).nodeAt 1 = π.nodeAt (j + 1) := by
                        have h_app_add_left := Walk.nodeAt_append_add_left σ (π.suffix j) 1
                        rw [hσ_zero, Nat.zero_add] at h_app_add_left
                        rw [h_app_add_left]
                        exact Walk.nodeAt_suffix π (by rw [h_suf_len] at h_suf_j_pos; omega)
                      exact h1.symm.trans h2
                    -- w_app ∈ G.Sc (π.nodeAt i).
                    have h_w_app_sc : w_app ∈ G.Sc (π.nodeAt i) := by
                      rw [h_w_app_eq, h_vi_eq_vj]
                      exact h_target_sc
                    -- Structural form of W: p_pre_i ⧺ cons s_left_πi (cons s_app rest_app).
                    have hW_form_zero :
                        (π.prefix i).append (σ.append (π.suffix j)) =
                          p_pre_i.append (Walk.cons s_left_πi
                            (Walk.cons s_app rest_app)) := by
                      rw [h_pre_i_eq, h_app_eq, Walk.append_assoc,
                        Walk.cons_append, Walk.nil_append]
                    -- Case-split on s_left_πi.
                    cases s_left_πi with
                    | forward h_fwd_πi =>
                      -- (2) vacuous; (3) holds via h_w_app_sc.  Unblockable.  exfalso.
                      exfalso
                      have h_joint : (WalkStep.forward h_fwd_πi).IsUnblockableJoint s_app := by
                        refine ⟨?_, ?_, ?_⟩
                        · intro ⟨_, h_src⟩; exact h_no_src_app h_src
                        · intro h_back; simp at h_back
                        · intro _; exact h_w_app_sc
                      have h_at_p :
                          (p_pre_i.append (Walk.cons (WalkStep.forward h_fwd_πi)
                              (Walk.cons s_app rest_app))).IsUnblockableNonColliderAt
                            (p_pre_i.length + 1) :=
                        (Walk.isUnblockableNonColliderAt_append_cons_cons_one
                          p_pre_i (WalkStep.forward h_fwd_πi) s_app rest_app).mpr h_joint
                      have h_at_p_W : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                          (p_pre_i.length + 1) := by
                        rw [hW_form_zero]
                        exact h_at_p
                      apply h_blkNC.2
                      convert h_at_p_W using 1
                      omega
                    | backward h_bw_πi =>
                      by_cases h_left_sc : w_pre_i ∈ G.Sc (π.nodeAt i)
                      · -- (2) holds, (3) holds.  Unblockable.  exfalso.
                        exfalso
                        have h_joint : (WalkStep.backward h_bw_πi).IsUnblockableJoint s_app := by
                          refine ⟨?_, ?_, ?_⟩
                          · intro ⟨h_tgt, _⟩; simp at h_tgt
                          · intro _; exact h_left_sc
                          · intro _; exact h_w_app_sc
                        have h_at_p :
                            (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                                (Walk.cons s_app rest_app))).IsUnblockableNonColliderAt
                              (p_pre_i.length + 1) :=
                          (Walk.isUnblockableNonColliderAt_append_cons_cons_one
                            p_pre_i (WalkStep.backward h_bw_πi) s_app rest_app).mpr h_joint
                        have h_at_p_W : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                            (p_pre_i.length + 1) := by
                          rw [hW_form_zero]
                          exact h_at_p
                        apply h_blkNC.2
                        convert h_at_p_W using 1
                        omega
                      · -- (2) fails.  Transport from π at i.
                        -- π = p_pre_i ⧺ cons (backward h_bw_πi) (cons s_right_πi rest_πi)
                        -- where s_right_πi is π's step at i.
                        have h_suf_i_pos : 1 ≤ (π.suffix i).length := by
                          rw [Walk.length_suffix π hi_le]
                          have : i < π.length := lt_of_lt_of_le hij hj
                          omega
                        obtain ⟨_, s_right_πi, rest_πi, h_suf_i_eq⟩ :=
                          Walk.walk_pos_eq_cons (π.suffix i) h_suf_i_pos
                        have h_alt_eq_i :
                            (π.prefix i).append (π.suffix i) =
                              p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                                (Walk.cons s_right_πi rest_πi)) := by
                          rw [h_pre_i_eq, h_suf_i_eq, Walk.append_assoc,
                            Walk.cons_append, Walk.nil_append]
                        have hπ_form_i : π = p_pre_i.append
                            (Walk.cons (WalkStep.backward h_bw_πi)
                              (Walk.cons s_right_πi rest_πi)) := by
                          rw [← h_alt_eq_i]
                          exact (Walk.prefix_append_suffix π hi_le).symm
                        have hi_le_π : i ≤ π.length := hi_le
                        have h_πNC_i : π.IsNonColliderAt i := by
                          refine ⟨hi_le_π, ?_⟩
                          intro h_πColl
                          rw [hπ_form_i] at h_πColl
                          have h_at_p :
                              (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                                (Walk.cons s_right_πi rest_πi))).IsColliderAt
                                (p_pre_i.length + 1) := by
                            convert h_πColl using 2
                          rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                          simp at h_at_p
                        have h_πNotUnblk_i : ¬ π.IsUnblockableNonColliderAt i := by
                          intro h_πUnblk
                          rw [hπ_form_i] at h_πUnblk
                          have h_at_p :
                              (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                                (Walk.cons s_right_πi rest_πi))).IsUnblockableNonColliderAt
                                (p_pre_i.length + 1) := by
                            convert h_πUnblk using 2
                          rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                          apply h_left_sc
                          exact h_at_p.2.1 (by simp [WalkStep.IsBackward])
                        exact h_open.2 i ⟨h_πNC_i, h_πNotUnblk_i⟩
                    | bidir h_bd_πi =>
                      -- Bidir: (2) vacuous (IsBackward False), (3) holds.  Unblockable.
                      exfalso
                      have h_joint : (WalkStep.bidir h_bd_πi).IsUnblockableJoint s_app := by
                        refine ⟨?_, ?_, ?_⟩
                        · intro ⟨_, h_src⟩; exact h_no_src_app h_src
                        · intro h_back; simp at h_back
                        · intro _; exact h_w_app_sc
                      have h_at_p :
                          (p_pre_i.append (Walk.cons (WalkStep.bidir h_bd_πi)
                              (Walk.cons s_app rest_app))).IsUnblockableNonColliderAt
                            (p_pre_i.length + 1) :=
                        (Walk.isUnblockableNonColliderAt_append_cons_cons_one
                          p_pre_i (WalkStep.bidir h_bd_πi) s_app rest_app).mpr h_joint
                      have h_at_p_W : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                          (p_pre_i.length + 1) := by
                        rw [hW_form_zero]
                        exact h_at_p
                      apply h_blkNC.2
                      convert h_at_p_W using 1
                      omega
              · -- target ∉ Sc^G(vⱼ): joint blockable on W.  Transport from π at j.
                -- π's right edge at j is forward + target ∉ Sc.  π is blockable at j.
                -- Build π.IsBlockableNonColliderAt j and apply h_open.2 j.
                -- Need π's step at j-1.
                have h_pre_j_pos : 1 ≤ (π.prefix j).length := by
                  rw [Walk.length_prefix π hj]; omega
                obtain ⟨w_pre_j, p_pre_j, s_left_πj, h_pre_j_eq⟩ :=
                  Walk.walk_pos_eq_append_last (π.prefix j) h_pre_j_pos
                have h_p_pre_j_len : p_pre_j.length = j - 1 := by
                  have h1 : (π.prefix j).length = p_pre_j.length +
                      (Walk.cons s_left_πj (Walk.nil (π.nodeAt j))).length := by
                    rw [h_pre_j_eq, Walk.length_append]
                  rw [Walk.length_prefix π hj] at h1
                  simp [Walk.length_cons, Walk.length_nil] at h1
                  omega
                have h_pos_form_j : (p_pre_j.length + 1 : ℕ) = j := by omega
                have h_alt_eq_j :
                    (π.prefix j).append (π.suffix j) =
                      p_pre_j.append
                        (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj)) := by
                  rw [h_pre_j_eq, h_suf_j_eq, Walk.append_assoc,
                    Walk.cons_append, Walk.nil_append]
                have hπ_form_j : π = p_pre_j.append
                    (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj)) := by
                  rw [← h_alt_eq_j]
                  exact (Walk.prefix_append_suffix π hj).symm
                have h_πNC_j : π.IsNonColliderAt j := by
                  refine ⟨le_of_lt hj_lt_π, ?_⟩
                  intro h_πColl
                  rw [hπ_form_j] at h_πColl
                  have h_at_p :
                      (p_pre_j.append
                        (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj))).IsColliderAt
                        (p_pre_j.length + 1) := by
                    convert h_πColl using 2
                  rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                  exact h_no_src_πj h_at_p.2
                have h_πNotUnblk_j : ¬ π.IsUnblockableNonColliderAt j := by
                  intro h_πUnblk
                  rw [hπ_form_j] at h_πUnblk
                  have h_at_p :
                      (p_pre_j.append
                        (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj))).IsUnblockableNonColliderAt
                        (p_pre_j.length + 1) := by
                    convert h_πUnblk using 2
                  rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                  apply h_target_sc
                  rw [← h_mid_eq]
                  exact h_at_p.2.2 h_s_right_πj_fwd
                exact h_open.2 j ⟨h_πNC_j, h_πNotUnblk_j⟩
          · -- k > i + σ.length: transport via splice_suf.
            have hWlen : ((π.prefix i).append (σ.append (π.suffix j))).length =
                i + σ.length + (π.length - j) := by
              rw [Walk.length_append, h_pre_len, Walk.length_append, h_suf_len, Nat.add_assoc]
            -- Bound k ≤ W.length:
            -- Position k must satisfy k ≤ W.length for blockable to be informative.
            -- (IsBlockableNonColliderAt requires k ≤ length via IsNonColliderAt.)
            have hk_le_Wlen : k ≤ ((π.prefix i).append (σ.append (π.suffix j))).length :=
              h_blkNC.1.1
            rw [hWlen] at hk_le_Wlen
            set k' := k - (i + σ.length) with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_le : k' ≤ π.length - j := by omega
            have h_eq : i + σ.length + k' = k := by omega
            have h_jk'_le : j + k' ≤ π.length := by omega
            have h_πNC : π.IsNonColliderAt (j + k') := by
              refine ⟨h_jk'_le, ?_⟩
              intro h_πColl
              apply h_blkNC.1.2
              rw [← h_eq]
              exact (Walk.isColliderAt_splice_suf π σ hi_le h_k'_pos).mpr h_πColl
            have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt (j + k') := by
              intro h_πUnblk
              apply h_blkNC.2
              rw [← h_eq]
              exact (Walk.isUnblockableNonColliderAt_splice_suf
                π σ hi_le h_k'_pos).mpr h_πUnblk
            rw [← h_eq, Walk.nodeAt_splice_suf π σ hi_le hj h_k'_le]
            exact h_open.2 (j + k') ⟨h_πNC, h_πNotUnblk⟩
-- REFACTOR-BLOCK-ORIGINAL-END: replace_walk

-- REFACTOR-BLOCK-REPLACEMENT-BEGIN: replace_walk (was: refactor_replace_walk)

/-! ## Refactor (`claim_3_2_no_finite`) replacement.

The refactor `claim_3_2_no_finite` removes the `[Finite α]` instance
hypothesis from `claim_3_2`'s `isAcyclic_iff_hasTopologicalOrder`. This
row's `replace_walk` proof does NOT reference that API (verified by
grep across all three Section3_3 files), so the refactor is a *no-op*
at the statement / API level for this row -- the replacement below has
the *same* signature and the *same* proof body as the ORIGINAL block
above; only the identifier changes from `replace_walk` to
`refactor_replace_walk` so the cleanup script can rename it back at
Phase 7. See the ORIGINAL block above for the full design-choice
rationale; we do not duplicate that prose here. -/

-- claim_3_27
-- title: LabelRoman -- replacing an Sc-bounded subwalk of a
-- σ-open walk yields a σ-open walk
--
-- ## LN reference
--
-- `lem:replace_walk`, `lecture-notes/lecture_notes/graphs.tex`
-- lines 1620 -- 1652.
/-
Verbatim from `lecture-notes/lecture_notes/graphs.tex`
(claim_3_27, lines 1620 -- 1630):

  Let $G = (J, V, E, L)$ be a CDMG, $C \subseteq V \cup J$ and
  $\pi = \lp v_0 \sus \cdots \sus v_n \rp$ a $C$-$\sigma$-open
  walk in $G$. Suppose $v_i \in \Sc^G(v_j)$ for some
  $i, j \in \{0, \dots, n\}$ with $i < j$. If we then replace
  the subwalk $v_i \sus \cdots \sus v_j$ of $\pi$ by
    (i)  a shortest directed path $v_i \tuh \cdots \tuh v_j$ in
         $G$ if $j = n$ or if $v_j \tuh v_{j+1}$ on $\pi$, or
    (ii) a shortest directed path $v_i \hut \cdots \hut v_j$ in
         $G$ otherwise,
  then this new subwalk is entirely within $\Sc^G(v_j)$ and
  the modified walk $\pi'$ is still $C$-$\sigma$-open.
-/
--
-- ## Statement (informal)
--
-- Given a $C$-$\sigma$-open walk $\pi$ on $G$ and two
-- positions $i < j$ with $v_i \in \Sc^G(v_j)$, *there exists*
-- a walk $\sigma$ from $v_i$ to $v_j$ such that:
--   (1) splicing $\sigma$ into $\pi$ in place of the subwalk
--       between positions $i$ and $j$ yields a walk that is
--       still $C$-$\sigma$-open;
--   (2) $\sigma$ is either directed ($v_i \tuh \cdots \tuh
--       v_j$, LN case (i)) or its reverse is directed
--       ($v_i \hut \cdots \hut v_j$, LN case (ii));
--   (3) every vertex on $\sigma$ -- endpoints and interior --
--       lies in $\Sc^G(v_j)$; and
--   (4) $\sigma$ is a *path* (no repeated vertices).
-- Properties (3) and (4) together are the two qualitative
-- consequences of the LN's "shortest directed path"
-- qualifier; (1), (2) and the existence claim itself are
-- the LN's own conclusion.
--
-- ## Design choices
--
-- * **Existential conclusion, not a function returning a
--   specific witness walk.** The LN says "if we replace ... then
--   ... is $\sigma$-open", which reads as: *there exists* a
--   replacement subwalk with the desired properties. We expose
--   this directly as `∃ σ : Walk G (π.nodeAt i) (π.nodeAt j), ...`
--   with the four relevant properties bundled as conjuncts
--   ($\sigma$-openness of the splice, directedness of $\sigma$ in
--   one orientation, SCC-membership of every $\sigma$ vertex,
--   path-ness of $\sigma$). The alternative -- packaging the same
--   data as a function `replace_walk : ... → Walk G v₀ vₙ` whose
--   output is a definite spliced walk -- was rejected because the
--   *only* live consumer (claim_3_23's $2 \Rightarrow 1$
--   direction, LN lines 1666 -- 1672) needs to **destructure** the
--   resulting splice into its three constituent pieces (`π.prefix
--   i`, $\sigma$, `π.suffix j`) and reason about repetition counts
--   on each segment separately. A function returning an opaque
--   `Walk G v₀ vₙ` would force every consumer to either re-derive
--   the splice structure or compute with a specific witness
--   (which is brittle: the witness's exact shape depends on
--   which case (i) or (ii) fires, which the consumer should not
--   have to know). The existential keeps the splice *structurally
--   visible* in the conclusion, while still letting the consumer
--   abstract over which $\sigma$ was produced. See
--   `workspace_claim_3_27.md` §1, "Statement shape -- DECISION",
--   paragraph 1 for the original discussion.
--
-- * **Spliced walk via `prefix` / `suffix` / `append`, not a
--   dedicated `Walk.splice` operator.** The expression
--   `(π.prefix i).append (σ.append (π.suffix j))` reads
--   exactly as the LN's "$\pi$ with the subwalk between $v_i$
--   and $v_j$ replaced by $\sigma$": the prefix of $\pi$ up
--   to position $i$, then $\sigma$, then the suffix of $\pi$
--   from position $j$ onwards. A dedicated `Walk.splice π i j
--   σ` operator would add a layer of indirection that
--   consumers would immediately unfold to the same three-way
--   append; the prefix/suffix spelling is identical and ties
--   directly into the existing `*_append_*` per-position
--   lemmas in `SigmaBlockedReversal.lean`
--   (`isColliderAt_append_lt_length`,
--   `isUnblockableNonColliderAt_append_cons_cons_one`, etc.).
--   See `workspace_claim_3_27.md` §1, paragraph 3 for the
--   rationale.
--
-- * **Right-associated bracketing `(π.prefix i).append
--   (σ.append (π.suffix j))`, not the left-associated
--   `((π.prefix i).append σ).append (π.suffix j)`.** Both
--   spellings denote the same walk modulo `append_assoc`
--   (`SigmaBlockedReversal.lean` line 120), but they expose
--   different two-pair structures to the existing `*_append_*`
--   API, which is stated for a single split point
--   `p₁.append p₂`. With right-association the two joints of the
--   three-way splice land cleanly as: the *outer* joint at
--   position `i` is between `p₁ = π.prefix i` and `p₂ =
--   σ.append (π.suffix j)`; the *inner* joint at the
--   $\sigma$-end is between `p₁ = σ` and `p₂ = π.suffix j`,
--   *inside* the outer `p₂`. Each joint then matches the
--   existing single-split lemmas (`isColliderAt_append_*`,
--   `isUnblockableNonColliderAt_append_*`) by descending the
--   structural pair `(p₁, p₂)` once, without re-deriving the
--   inner split. Left-association would force the inner-joint
--   reasoning to dig through the *first* argument of the outer
--   append -- which `Walk.append`'s recursion in
--   `Section3_1/Walks.lean` recurses on -- a strictly longer
--   structural descent. Consumers may convert between the two
--   forms by `append_assoc` if needed.
--
-- * **`σ.IsDirected ∨ σ.reverse.IsDirected` packs LN cases
--   (i) and (ii) into one existential.** The LN distinguishes
--   the two replacement orientations by the local pattern of
--   $\pi$ at position $j$: case (i) (forward $v_i \tuh \cdots
--   \tuh v_j$) when $j = n$ or $v_j \tuh v_{j+1}$ on $\pi$,
--   case (ii) (backward $v_i \hut \cdots \hut v_j$) otherwise.
--   The disjunction is the propositional packing of this
--   two-way case split into a single existential. Consumers
--   never branch on (i) vs. (ii) -- they just take whichever
--   orientation the witness provides; the case split lives
--   inside the proof, not at the interface. Splitting
--   `replace_walk` into two separate theorems
--   (`replace_walk_forward`, `replace_walk_backward`) was
--   considered and rejected for two reasons. (1) Every
--   downstream call would either have to invoke both and
--   `rcases`-merge, or duplicate the LN's case-discriminating
--   logic (`j = n ∨ v_j \tuh v_{j+1}` vs. otherwise) at the
--   call site. (2) The *cut-point* `(i, j)` is shared between
--   the two cases -- it's a single decision the consumer made
--   before invoking the lemma -- so the case (i) / (ii) split
--   is an internal implementation detail of *how* the splice
--   is produced, not a different *kind* of splice. Bundling
--   into one theorem keeps the cut-point well-defined at the
--   interface and hides the implementation detail. The same
--   reasoning is why the hypothesis `h_sc : π.nodeAt i ∈ G.Sc
--   (π.nodeAt j)` is not duplicated either: it's the
--   precondition that *both* cases share.
--
-- * **"Shortest" is unbundled into two qualitative
--   conjuncts.** The LN's "shortest directed path" qualifier
--   delivers *two* properties simultaneously: (a) every
--   intermediate vertex lies in $\Sc^G(v_j)$ (a
--   longer-than-necessary directed walk inside $\Sc^G(v_j)$
--   could in principle loop, but every node on such a loop
--   is still in $\Sc^G(v_j)$), and (b) the path has no
--   repeats (`σ.IsPath`). We drop the *quantitative*
--   minimisation ("shortest" as length-minimising --
--   incidental to every downstream use, and costly to
--   formalise as a min-over-walks well-founded construction
--   with no other consumer in this chapter) but **retain
--   both qualitative properties separately**: (a) as the
--   third conjunct
--   `∀ k, k ≤ σ.length → σ.nodeAt k ∈ G.Sc (π.nodeAt j)`,
--   which is exactly what the LN's proof uses "shortest" to
--   establish on the SCC side (see LN line 1635: "all nodes
--   in between lie in the same strongly connected component
--   $\Sc^G(v_i)$"); and (b) as the fourth conjunct
--   `σ.IsPath`. The path-ness is *load-bearing* for the
--   only live consumer (claim_3_23's $2 \Rightarrow 1$
--   direction, LN lines 1666 -- 1672), which counts repeated
--   nodes on a $\sigma$-open walk and needs the count to
--   *strictly* drop under replacement: without
--   `σ.IsPath`, the witness could be a closed walk
--   (e.g. `v_i \tuh x \tuh v_i \tuh x \tuh v_j` with every
--   step forward and every node in $\Sc^G(v_j)$) that
--   reintroduces repeats and so leaves the count unchanged
--   or worse. The degenerate $v_i = v_j$ case is even
--   sharper: with `IsPath`, the witness *must* be
--   `Walk.nil _` and the $[i, j]$ segment is genuinely
--   collapsed; without it, the witness can be a non-trivial
--   closed walk and $v_j$ stays multiply-occurring.
--   Proof-cost note: producing the path-witness is
--   uniformly *cheaper* than any other "shortest" notion,
--   because loop-erasure of a directed walk is still
--   directed and still inside $\Sc^G(v_j)$ (loop-erasure
--   only deletes support members, never adds), so the
--   helper L2 (`directed_walk_in_Sc`) composes with a
--   standard loop-erasure step to yield a directed-and-path
--   witness with all-in-`Sc` membership preserved. See
--   `workspace_claim_3_27.md` §1, paragraph 1 (to be
--   updated by the manager once this revision lands) for
--   the original "shortest is dropped" framing that this
--   bullet supersedes.
--
-- * **The SCC-membership universal is gated by `k ≤ σ.length`,
--   covering both endpoints and the interior.** At `k = 0` we
--   have $\sigma.\text{nodeAt}\,0 = v_i \in \Sc^G(v_j)$ by
--   `h_sc`; at `k = σ.length` we have
--   $\sigma.\text{nodeAt}\,\sigma.\text{length} = v_j$ which
--   is in $\Sc^G(v_j)$ by `self_mem_Sc`; in between, the LN's
--   "all nodes in between lie in the same SCC" gives the
--   interior. Phrasing the universal over the whole closed
--   interval `[0, σ.length]` lets consumers index any position
--   on the spliced middle uniformly, and matches the LN's
--   prose ("this new subwalk is *entirely* within
--   $\Sc^G(v_j)$") which makes no endpoint/interior
--   distinction.
--
-- * **`namespace Walk` placement, not `namespace CDMG`.**
--   Matches the convention of claim_3_21
--   (`UnblockableNonCollidersOpen.lean`) and the per-walk
--   predicates in this section: the theorem is *about* a walk,
--   so it lives under `Causality.Walk`. Callers may reach for
--   it via `π.replace_walk C h_open hij hj h_sc`
--   (dot-projection on the walk, with the walk-first /
--   conditioning-set-second argument order matching
--   `π.IsSigmaOpen C` and the rest of the chapter's per-walk
--   API). The planner's workspace draft
--   (`workspace_claim_3_27.md` §1) suggested `namespace CDMG`
--   to dot-project on `G`; we chose `Walk` instead because
--   `G` is implicit in this signature and so does not actually
--   dot-project, while `π` is explicit and does. Verified
--   against the chapter's argument-order convention (`π`
--   first, `C` second; same as `Walk.IsSigmaOpen π C` in
--   `SigmaBlockedWalks.lean` and
--   `isSigmaBlocked_iff_not_isSigmaOpen π C` in
--   `SigmaBlockedReversal.lean`).
--
-- * **`C : Set α`, not a subtype of `J ∪ V`.** Same convention
--   as `IsSigmaOpen` itself (`SigmaBlockedWalks.lean`):
--   `AncSet G C` silently ignores members outside the graph,
--   so the LN's "$C \subseteq V \cup J$" precondition is
--   propagated by callers as a side hypothesis, not encoded
--   at the type level.
--
-- * **Bound `hj : j ≤ π.length` only; `i`'s bound comes from
--   `hij : i < j`.** The LN's "$i, j \in \{0, \dots, n\}$
--   with $i < j$" gives $i < j \le n = \pi.\text{length}$, so
--   the single `hj` is sufficient. `nodeAt` is total
--   (junk-OK), so both `π.nodeAt i` and `π.nodeAt j` are
--   well-typed unconditionally; the bound is needed for the
--   semantic side (e.g. `prefix_length` / `suffix_length` lift
--   `π.prefix i` and `π.suffix j` to their non-junk
--   characterisations).

/-- claim_3_27 (`lem:replace_walk`): given a $C$-$\sigma$-open
walk `π` in a CDMG `G` and two positions `i < j` on `π` with
`π.nodeAt i ∈ Sc^G(π.nodeAt j)`, there exists a walk `σ` from
`π.nodeAt i` to `π.nodeAt j` such that splicing `σ` into `π`
in place of the subwalk between positions `i` and `j` yields a
walk that is (1) still $C$-$\sigma$-open, (2) either directed
or has a directed reverse (packing LN cases (i) and (ii) into
a single existential), (3) entirely within
$\Sc^G(\pi.\text{nodeAt}\,j)$ at every position, and (4) a
path (no repeated vertices) -- the two qualitative
consequences of the LN's "shortest directed path" qualifier,
both retained as separate conjuncts. -/
theorem refactor_replace_walk
    {G : CDMG α} {v₀ vₙ : α} (π : Walk G v₀ vₙ) (C : Set α)
    (h_open : π.IsSigmaOpen C)
    {i j : ℕ} (hij : i < j) (hj : j ≤ π.length)
    (h_sc : π.nodeAt i ∈ G.Sc (π.nodeAt j)) :
    ∃ σ : Walk G (π.nodeAt i) (π.nodeAt j),
      ((π.prefix i).append (σ.append (π.suffix j))).IsSigmaOpen C
      ∧ (σ.IsDirected ∨ σ.reverse.IsDirected)
      ∧ (∀ k, k ≤ σ.length → σ.nodeAt k ∈ G.Sc (π.nodeAt j))
      ∧ σ.IsPath := by
  classical
  -- Notational shortcuts for the cut-point vertices.
  set vᵢ : α := π.nodeAt i with hvᵢ_def
  set vⱼ : α := π.nodeAt j with hvⱼ_def
  -- vᵢ ∈ G follows from h_sc.1 (it lives in Anc^G(vⱼ) which has a `∈ G` conjunct).
  have h_vi_mem : vᵢ ∈ G := h_sc.1.1
  -- vⱼ ∈ G: from `h_sc.2 : vᵢ ∈ Desc^G(vⱼ)` extract the directed walk vⱼ → vᵢ; if
  -- it is non-trivial, vⱼ is the source of a step (in G via E_subset/L_subset).
  -- If it is the trivial walk, vᵢ = vⱼ, so vⱼ ∈ G via h_vi_mem.
  have h_vj_mem : vⱼ ∈ G := by
    obtain ⟨_, π_back, _⟩ := h_sc.2
    by_cases hlen : 1 ≤ π_back.length
    · obtain ⟨_, s, _, _⟩ := Walk.walk_pos_eq_cons π_back hlen
      exact s.source_mem_G
    · -- π_back has length 0, so its endpoints coincide: vⱼ = vᵢ.
      push_neg at hlen
      have h_len_zero : π_back.length = 0 := Nat.lt_one_iff.mp hlen
      have h1 : π_back.nodeAt 0 = vⱼ := π_back.nodeAt_zero
      have h2 : π_back.nodeAt π_back.length = vᵢ := π_back.nodeAt_length
      rw [h_len_zero] at h2
      have h_eq : vⱼ = vᵢ := h1 ▸ h2
      rw [h_eq]; exact h_vi_mem
  have h_vj_in_Sc_vj : vⱼ ∈ G.Sc vⱼ := CDMG.self_mem_Sc h_vj_mem
  -- The length-i prefix of π exists and lies in `Walk G v₀ vᵢ`.
  -- The length-(π.length - j) suffix lies in `Walk G vⱼ vₙ`.
  have hi_le : i ≤ π.length := le_trans (le_of_lt hij) hj
  -- Bounds on π's positions / lengths we will reuse.
  have h_pre_len : (π.prefix i).length = i := Walk.length_prefix π hi_le
  have h_suf_len : (π.suffix j).length = π.length - j := Walk.length_suffix π hj
  -- Two key sub-helpers for σ-openness arguments
  -- on the spliced walk.  We'll write them as `have`-block lemmas
  -- after constructing σ, since they depend on σ's properties.

  -- ============================================================
  -- Top-level case split based on the local pattern at position j on π.
  -- ============================================================
  -- Case (ii) trigger: ∃ a first-step of (π.suffix j) with source-arrowhead.
  by_cases h_case_ii : ∃ (a : α) (s_j : WalkStep G (π.nodeAt j) a)
      (rest_j : Walk G a vₙ),
      π.suffix j = Walk.cons s_j rest_j ∧ s_j.HasArrowheadAtSource
  · -- ============================================================
    -- LN case (ii): step at j on π is backward or bidir.
    -- σ is built from h_sc.2 (Desc^G(vⱼ)), loop-erased, then reversed.
    -- ============================================================
    -- Extract case (ii)'s step structure.
    obtain ⟨a_j, s_j, rest_j, h_suf_eq, h_s_j_arrowhead⟩ := h_case_ii
    -- Extract directed walk π_dir : Walk G vⱼ vᵢ from h_sc.2.
    obtain ⟨π_dir, h_πdir_dir⟩ := h_sc.2.2
    -- Loop-erase to get a directed path σ₀ : Walk G vⱼ vᵢ.
    obtain ⟨σ₀, hσ₀_dir, hσ₀_path⟩ :=
      Walk.exists_path_of_directed π_dir h_πdir_dir
    -- σ = σ₀.reverse : Walk G vᵢ vⱼ.
    set σ : Walk G vᵢ vⱼ := σ₀.reverse with hσ_def
    -- (2) σ.reverse is directed:
    have hσ_rev_dir : σ.reverse.IsDirected := by
      rw [hσ_def, Walk.reverse_reverse]
      exact hσ₀_dir
    -- (4) σ.IsPath: σ₀ is a path, so its reverse is too.
    have hσ_path : σ.IsPath := by
      rw [hσ_def, Walk.isPath_reverse_iff]; exact hσ₀_path
    -- (3) σ's nodes ∈ G.Sc vⱼ.
    -- σ.nodeAt k = σ₀.reverse.nodeAt k = σ₀.nodeAt (σ₀.length - k).
    -- σ₀ : Walk G vⱼ vᵢ directed. With vⱼ ∈ G.Sc vᵢ (from Sc-symm), every node of σ₀ ∈ Sc^G(vᵢ).
    -- And Sc^G(vᵢ) = Sc^G(vⱼ) by Sc-equivalence.
    have h_sc_symm : vⱼ ∈ G.Sc vᵢ := Walk.mem_Sc_symm h_sc
    have hσ₀_inSc_vi : ∀ m, m ≤ σ₀.length → σ₀.nodeAt m ∈ G.Sc vᵢ :=
      Walk.directed_walk_in_Sc σ₀ hσ₀_dir h_sc_symm
    have hσ_inSc : ∀ k, k ≤ σ.length → σ.nodeAt k ∈ G.Sc vⱼ := by
      intro k hk
      -- σ.length = σ₀.length (length_reverse)
      have hσ_len_eq : σ.length = σ₀.length := by
        rw [hσ_def, Walk.length_reverse]
      -- σ.nodeAt k = σ₀.nodeAt (σ₀.length - k).
      have h_node : σ.nodeAt k = σ₀.nodeAt (σ₀.length - k) := by
        rw [hσ_def]
        exact Walk.nodeAt_reverse σ₀ (by rw [hσ_def] at hk; rw [Walk.length_reverse] at hk; exact hk)
      rw [h_node]
      -- σ₀.nodeAt (σ₀.length - k) ∈ Sc^G(vᵢ).
      have h_in_vi : σ₀.nodeAt (σ₀.length - k) ∈ G.Sc vᵢ := by
        apply hσ₀_inSc_vi
        omega
      -- Sc-trans: ∈ Sc(vᵢ) AND vᵢ ∈ Sc(vⱼ) (from h_sc) → ∈ Sc(vⱼ).
      -- Use the Sc-equivalence via mem_Sc_trans (need to define) or via the
      -- explicit chain.
      refine ⟨?_, ?_⟩
      · -- node ∈ Anc^G(vⱼ): use node ∈ Anc^G(vᵢ) and vᵢ ∈ Anc^G(vⱼ).
        obtain ⟨h_mem, ⟨p_to_vi, hp_to_vi⟩⟩ := h_in_vi.1
        obtain ⟨_, ⟨p_vi_vj, hp_vi_vj⟩⟩ := h_sc.1
        exact ⟨h_mem, ⟨p_to_vi.append p_vi_vj,
          Walk.isDirected_append _ _ hp_to_vi hp_vi_vj⟩⟩
      · -- node ∈ Desc^G(vⱼ): use vⱼ → vᵢ (from h_sc.2) and vᵢ → node (from h_in_vi.2).
        obtain ⟨_, ⟨p_vj_vi, hp_vj_vi⟩⟩ := h_sc.2
        obtain ⟨h_mem, ⟨p_vi_to_node, hp_vi_to_node⟩⟩ := h_in_vi.2
        exact ⟨h_mem, ⟨p_vj_vi.append p_vi_to_node,
          Walk.isDirected_append _ _ hp_vj_vi hp_vi_to_node⟩⟩
    refine ⟨σ, ?_, Or.inr hσ_rev_dir, hσ_inSc, hσ_path⟩
    -- Disjunct (1): σ-openness of the spliced walk W in case (ii).
    -- σ.reverse.IsDirected, so each step of σ is `backward`.  This makes interior joints
    -- left-chain non-colliders (unblockable inside Sc^G(vⱼ)) and the right joint at j
    -- unconditionally a left-chain non-collider (sole strict-outgoing into Sc^G(vⱼ)).
    -- The left joint at i splits into sub-cases (ii.a) (backward s_left_πi) and (ii.b)
    -- (forward/bidir s_left_πi); (ii.b) is the only sub-case where v_i becomes a collider
    -- on W and we discharge via the first-collider induction on π.
    -- Also relevant: π's first step of `π.suffix j` (= s_j) has source-arrowhead.
    refine ⟨?_, ?_⟩
    · -- ===== (1.coll)  W.IsColliderAt k → W.nodeAt k ∈ G.AncSet C =====
      intro k h_coll
      rcases lt_or_ge k i with h_k_lt_i | h_k_ge_i
      · -- k < i: transport via splice_pre.
        have h_πColl :=
          (Walk.isColliderAt_splice_pre π σ hi_le h_k_lt_i).mp h_coll
        rw [Walk.nodeAt_splice_pre π σ hi_le (le_of_lt h_k_lt_i)]
        exact h_open.1 k h_πColl
      · -- k ≥ i.
        rcases lt_or_ge k (i + σ.length) with h_k_lt_mid | h_k_ge_mid
        · -- i ≤ k < i + σ.length.
          rcases Nat.eq_or_lt_of_le h_k_ge_i with h_k_eq_i | h_k_gt_i
          · -- k = i: outer joint.  Sub-case (ii.a) or (ii.b) based on s_left_πi.
            subst h_k_eq_i
            -- For collider clause: (ii.a) backward s_left_πi: NOT collider, exfalso.
            -- (ii.b) forward/bidir s_left_πi: collider possible; v_i ∈ AncSet(C) via induction.
            -- Reduce W.nodeAt i = π.nodeAt i.
            rw [Walk.nodeAt_splice_pre π σ hi_le (le_refl i)]
            -- Goal: π.nodeAt i ∈ G.AncSet C.
            -- Case on i = 0 (W endpoint, can't be collider) vs i ≥ 1.
            by_cases hi_zero : i = 0
            · -- i = 0: position 0 of W is not a collider (endpoint).
              subst hi_zero
              exfalso
              exact (Walk.isNonColliderAt_zero _).2 h_coll
            · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
              have h_pre_i_pos : 1 ≤ (π.prefix i).length := by rw [h_pre_len]; omega
              obtain ⟨w_pre_i, p_pre_i, s_left_πi, h_pre_i_eq⟩ :=
                Walk.walk_pos_eq_append_last (π.prefix i) h_pre_i_pos
              have h_p_pre_i_len : p_pre_i.length = i - 1 := by
                have h1 : (π.prefix i).length = p_pre_i.length +
                    (Walk.cons s_left_πi (Walk.nil (π.nodeAt i))).length := by
                  rw [h_pre_i_eq, Walk.length_append]
                rw [h_pre_len] at h1
                simp [Walk.length_cons, Walk.length_nil] at h1
                omega
              have h_pos_form_i : (p_pre_i.length + 1 : ℕ) = i := by omega
              -- The right side of the joint at v_i on W: first step of σ.append (π.suffix j).
              -- In both σ.length ≥ 1 and σ.length = 0 cases, the right step has source-arrowhead:
              --   σ.length ≥ 1: σ's first step is backward (source-arrowhead).
              --   σ.length = 0: π.suffix j's first step is s_j (source-arrowhead from h_s_j_arrowhead).
              have h_app_pos : 1 ≤ (σ.append (π.suffix j)).length := by
                rw [Walk.length_append]
                have h_suf_pos : 1 ≤ (π.suffix j).length := by
                  rw [h_suf_eq, Walk.length_cons]; omega
                omega
              obtain ⟨w_app, s_app, rest_app, h_app_eq⟩ :=
                Walk.walk_pos_eq_cons _ h_app_pos
              -- s_app has source π.nodeAt i and source-arrowhead.  Use the dual helper.
              have h_suf_has_src : ∀ (a' : α) (s' : WalkStep G (π.nodeAt j) a')
                  (rest' : Walk G a' vₙ),
                  π.suffix j = Walk.cons s' rest' → s'.HasArrowheadAtSource := by
                intro a' s' rest' h_eq'
                rw [h_suf_eq] at h_eq'
                obtain ⟨h_av, h_sa, _⟩ := Walk.cons.inj h_eq'
                subst h_av
                have h_s_eq : s_j = s' := eq_of_heq h_sa
                rw [← h_s_eq]
                exact h_s_j_arrowhead
              have h_s_app_src : s_app.HasArrowheadAtSource :=
                Walk.first_step_has_source_of_reverseDirected_append σ (π.suffix j) _ s_app
                  rest_app hσ_rev_dir h_app_eq h_suf_has_src
              -- Now we have h_s_app_src : s_app.HasArrowheadAtSource.
              -- Build structural form of W at position i.
              have hW_form_i :
                  (π.prefix i).append (σ.append (π.suffix j)) =
                    p_pre_i.append (Walk.cons s_left_πi
                      (Walk.cons s_app rest_app)) := by
                rw [h_pre_i_eq, h_app_eq, Walk.append_assoc,
                  Walk.cons_append, Walk.nil_append]
              -- W.IsColliderAt i ↔ s_left_πi.HasArrowheadAtTarget ∧ s_app.HasArrowheadAtSource.
              have h_coll_at_i :
                  ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt i := h_coll
              rw [hW_form_i] at h_coll_at_i
              have h_at_p : (p_pre_i.append (Walk.cons s_left_πi
                  (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                convert h_coll_at_i using 2
              rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
              obtain ⟨h_left_arr, _h_right_arr⟩ := h_at_p
              -- (ii.a) backward s_left_πi is excluded here since backward has
              -- HasArrowheadAtTarget = False, contradicting h_left_arr.  Only (ii.b)
              -- (= forward / bidir s_left_πi) remains.  Use the first-collider induction.
              have hj_lt_π : j < π.length := by
                have hh : 1 ≤ (π.suffix j).length := by rw [h_suf_eq, Walk.length_cons]; omega
                rw [Walk.length_suffix π hj] at hh
                omega
              -- Build the helper's left-arrowhead hypothesis using π = π.prefix i ⧺ π.suffix i.
              have h_πfull : π = (π.prefix i).append (π.suffix i) :=
                (Walk.prefix_append_suffix π hi_le).symm
              have h_helper_left :
                  ∃ (wim1 wi : α) (p_pre : Walk G v₀ wim1) (s_left : WalkStep G wim1 wi)
                      (rest : Walk G wi vₙ),
                    π = p_pre.append (Walk.cons s_left rest) ∧
                    wi = π.nodeAt i ∧
                    p_pre.length = i - 1 ∧
                    s_left.HasArrowheadAtTarget := by
                refine ⟨w_pre_i, π.nodeAt i, p_pre_i, s_left_πi, π.suffix i, ?_, rfl,
                  h_p_pre_i_len, h_left_arr⟩
                have h_pre_alt :
                    (π.prefix i).append (π.suffix i) =
                      (p_pre_i.append (Walk.cons s_left_πi (Walk.nil _))).append (π.suffix i) := by
                  rw [h_pre_i_eq]
                have h_reassoc :
                    (p_pre_i.append (Walk.cons s_left_πi (Walk.nil (π.nodeAt i)))).append
                        (π.suffix i) =
                      p_pre_i.append (Walk.cons s_left_πi (π.suffix i)) := by
                  rw [Walk.append_assoc, Walk.cons_append, Walk.nil_append]
                exact h_πfull.trans (h_pre_alt.trans h_reassoc)
              -- Build the helper's right-arrowhead hypothesis.
              have h_πfull_j : π = (π.prefix j).append (π.suffix j) :=
                (Walk.prefix_append_suffix π hj).symm
              have h_pre_j_len : (π.prefix j).length = j := Walk.length_prefix π hj
              have h_helper_right :
                  ∃ (wjp1 wj : α) (s_right : WalkStep G wj wjp1) (p_pre_j : Walk G v₀ wj)
                      (rest_j : Walk G wjp1 vₙ),
                    π = p_pre_j.append (Walk.cons s_right rest_j) ∧
                    wj = π.nodeAt (i + (j - i)) ∧
                    p_pre_j.length = i + (j - i) ∧
                    s_right.HasArrowheadAtSource := by
                refine ⟨a_j, π.nodeAt j, s_j, π.prefix j, rest_j, ?_, ?_, ?_, h_s_j_arrowhead⟩
                · rw [h_suf_eq] at h_πfull_j; exact h_πfull_j
                · congr 1; omega
                · rw [h_pre_j_len]; omega
              have hi_n_lt : i + (j - i) < π.length := by
                have : i + (j - i) = j := by omega
                rw [this]; exact hj_lt_π
              have h_n_pos : 0 < j - i := by omega
              obtain ⟨k, _h_k_ge, _h_k_le, h_πColl, h_anc⟩ :=
                Walk.exists_collider_with_anc π (j - i) h_n_pos hi_pos hi_n_lt
                  h_helper_left h_helper_right
              exact CDMG.ancSet_of_anc_ancSet h_anc (h_open.1 k h_πColl)
          · -- i < k < i + σ.length: σ interior.  σ.reverse.IsDirected, so no collider.
            exfalso
            set k' := k - i with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_lt : k' < σ.length := by omega
            have h_eq : i + k' = k := by omega
            rw [← h_eq] at h_coll
            have h_σColl :=
              (Walk.isColliderAt_splice_mid π σ hi_le h_k'_pos h_k'_lt).mp h_coll
            exact Walk.not_isColliderAt_of_isReverseDirected σ k' hσ_rev_dir h_σColl
        · rcases Nat.eq_or_lt_of_le h_k_ge_mid with h_k_eq_mid | h_k_gt_mid
          · -- k = i + σ.length: right joint (case ii) when σ.length ≥ 1; collapsed joint when σ.length = 0.
            subst h_k_eq_mid
            by_cases hσ_pos : 1 ≤ σ.length
            · -- σ.length ≥ 1: NOT a collider since σ's last step is backward.
              exfalso
              -- Decompose σ's last step.
              obtain ⟨w_last_σ, σ_pre, s_last_σ, hσ_last_eq⟩ :=
                Walk.walk_pos_eq_append_last σ hσ_pos
              -- s_last_σ : WalkStep G w_last_σ vⱼ.
              have hσ_pre_len : σ_pre.length = σ.length - 1 := by
                have h_eq : σ.length = σ_pre.length + 1 := by
                  conv_lhs => rw [hσ_last_eq]
                  rw [Walk.length_append, Walk.length_cons, Walk.length_nil]
                omega
              -- s_last_σ is backward (σ.reverse.IsDirected).
              have h_s_last_σ_bw : s_last_σ.IsBackward := by
                rw [hσ_last_eq] at hσ_rev_dir
                rw [Walk.reverse_append, Walk.reverse_cons, Walk.reverse_nil,
                  Walk.nil_append] at hσ_rev_dir
                -- hσ_rev_dir : (cons s_last_σ.reverse σ_pre.reverse).IsDirected
                cases s_last_σ with
                | forward _ => simp at hσ_rev_dir
                | backward _ => simp
                | bidir _ => simp at hσ_rev_dir
              -- W = ((π.prefix i).append σ_pre).append (cons s_last_σ (π.suffix j))
              have hW_form_inner :
                  (π.prefix i).append (σ.append (π.suffix j)) =
                    ((π.prefix i).append σ_pre).append
                      (Walk.cons s_last_σ (π.suffix j)) := by
                rw [hσ_last_eq, Walk.append_assoc, Walk.append_assoc, Walk.cons_append,
                  Walk.nil_append]
              have hpos_inner : ((π.prefix i).append σ_pre).length + 1 = i + σ.length := by
                rw [Walk.length_append, h_pre_len, hσ_pre_len]; omega
              -- Now use `not_isColliderAt_append_cons_at_left_length`'s dual reasoning:
              -- s_last_σ has no target-arrowhead (backward), so the joint is NOT a collider.
              -- We need a separate helper or inline it.
              rw [hW_form_inner] at h_coll
              -- h_coll : (((π.prefix i).append σ_pre).append (cons s_last_σ (π.suffix j))).IsColliderAt (i + σ.length).
              rw [show (i + σ.length : ℕ) = ((π.prefix i).append σ_pre).length + 1 from
                hpos_inner.symm] at h_coll
              -- Decompose π.suffix j to expose s_j.
              rw [h_suf_eq] at h_coll
              -- h_coll : (((π.prefix i).append σ_pre).append (cons s_last_σ (cons s_j rest_j))).IsColliderAt
              --           (((π.prefix i).append σ_pre).length + 1).
              rw [Walk.isColliderAt_append_cons_cons_one] at h_coll
              -- h_coll : s_last_σ.HasArrowheadAtTarget ∧ s_j.HasArrowheadAtSource
              -- s_last_σ backward has HasArrowheadAtTarget = False, contradiction.
              cases s_last_σ with
              | forward _ => simp at h_s_last_σ_bw
              | backward _ => simp at h_coll
              | bidir _ => simp at h_s_last_σ_bw
            · -- σ.length = 0: joint collapses with outer joint.  Same (ii.a)/(ii.b) analysis.
              push_neg at hσ_pos
              have hσ_zero : σ.length = 0 := Nat.lt_one_iff.mp hσ_pos
              -- W's position i + σ.length = i.  W.nodeAt (i + σ.length) reduces to π.nodeAt i.
              rw [Walk.nodeAt_splice_mid π σ hi_le (le_refl σ.length), Walk.nodeAt_length]
              have h_vi_eq_vj : π.nodeAt i = π.nodeAt j :=
                Walk.source_eq_target_of_length_zero σ hσ_zero
              rw [← h_vi_eq_vj]
              -- Goal: π.nodeAt i ∈ G.AncSet C.  Use the (ii.b) collider induction.
              by_cases hi_zero : i = 0
              · subst hi_zero
                -- i = 0: W's position 0 is an endpoint (not a collider).  Exfalso.
                exfalso
                have h_eq : (0 : ℕ) + σ.length = 0 := by rw [hσ_zero]
                rw [h_eq] at h_coll
                exact (Walk.isNonColliderAt_zero _).2 h_coll
              · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
                have h_pre_i_pos : 1 ≤ (π.prefix i).length := by rw [h_pre_len]; omega
                obtain ⟨w_pre_i, p_pre_i, s_left_πi, h_pre_i_eq⟩ :=
                  Walk.walk_pos_eq_append_last (π.prefix i) h_pre_i_pos
                have h_p_pre_i_len : p_pre_i.length = i - 1 := by
                  have h1 : (π.prefix i).length = p_pre_i.length +
                      (Walk.cons s_left_πi (Walk.nil (π.nodeAt i))).length := by
                    rw [h_pre_i_eq, Walk.length_append]
                  rw [h_pre_len] at h1
                  simp [Walk.length_cons, Walk.length_nil] at h1
                  omega
                have h_pos_form_i : (p_pre_i.length + 1 : ℕ) = i := by omega
                have h_app_pos : 1 ≤ (σ.append (π.suffix j)).length := by
                  rw [Walk.length_append]
                  have h_suf_pos : 1 ≤ (π.suffix j).length := by
                    rw [h_suf_eq, Walk.length_cons]; omega
                  omega
                obtain ⟨w_app, s_app, rest_app, h_app_eq⟩ :=
                  Walk.walk_pos_eq_cons _ h_app_pos
                have h_suf_has_src : ∀ (a' : α) (s' : WalkStep G (π.nodeAt j) a')
                    (rest' : Walk G a' vₙ),
                    π.suffix j = Walk.cons s' rest' → s'.HasArrowheadAtSource := by
                  intro a' s' rest' h_eq'
                  rw [h_suf_eq] at h_eq'
                  obtain ⟨h_av, h_sa, _⟩ := Walk.cons.inj h_eq'
                  subst h_av
                  have h_s_eq : s_j = s' := eq_of_heq h_sa
                  rw [← h_s_eq]
                  exact h_s_j_arrowhead
                have h_s_app_src : s_app.HasArrowheadAtSource :=
                  Walk.first_step_has_source_of_reverseDirected_append σ (π.suffix j) _ s_app
                    rest_app hσ_rev_dir h_app_eq h_suf_has_src
                have hW_form_i :
                    (π.prefix i).append (σ.append (π.suffix j)) =
                      p_pre_i.append (Walk.cons s_left_πi
                        (Walk.cons s_app rest_app)) := by
                  rw [h_pre_i_eq, h_app_eq, Walk.append_assoc,
                    Walk.cons_append, Walk.nil_append]
                have h_coll_i : ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt i := by
                  have h_eq : (i + σ.length : ℕ) = i := by omega
                  rw [h_eq] at h_coll
                  exact h_coll
                rw [hW_form_i] at h_coll_i
                have h_at_p : (p_pre_i.append (Walk.cons s_left_πi
                    (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                  convert h_coll_i using 2
                rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                obtain ⟨h_left_arr, _h_right_arr⟩ := h_at_p
                have hj_lt_π : j < π.length := by
                  have hh : 1 ≤ (π.suffix j).length := by rw [h_suf_eq, Walk.length_cons]; omega
                  rw [Walk.length_suffix π hj] at hh
                  omega
                have h_πfull : π = (π.prefix i).append (π.suffix i) :=
                  (Walk.prefix_append_suffix π hi_le).symm
                have h_helper_left :
                    ∃ (wim1 wi : α) (p_pre : Walk G v₀ wim1) (s_left : WalkStep G wim1 wi)
                        (rest : Walk G wi vₙ),
                      π = p_pre.append (Walk.cons s_left rest) ∧
                      wi = π.nodeAt i ∧
                      p_pre.length = i - 1 ∧
                      s_left.HasArrowheadAtTarget := by
                  refine ⟨w_pre_i, π.nodeAt i, p_pre_i, s_left_πi, π.suffix i, ?_, rfl,
                    h_p_pre_i_len, h_left_arr⟩
                  have h_pre_alt :
                      (π.prefix i).append (π.suffix i) =
                        (p_pre_i.append (Walk.cons s_left_πi (Walk.nil _))).append (π.suffix i) := by
                    rw [h_pre_i_eq]
                  have h_reassoc :
                      (p_pre_i.append (Walk.cons s_left_πi (Walk.nil (π.nodeAt i)))).append
                          (π.suffix i) =
                        p_pre_i.append (Walk.cons s_left_πi (π.suffix i)) := by
                    rw [Walk.append_assoc, Walk.cons_append, Walk.nil_append]
                  exact h_πfull.trans (h_pre_alt.trans h_reassoc)
                have h_πfull_j : π = (π.prefix j).append (π.suffix j) :=
                  (Walk.prefix_append_suffix π hj).symm
                have h_pre_j_len : (π.prefix j).length = j := Walk.length_prefix π hj
                have h_helper_right :
                    ∃ (wjp1 wj : α) (s_right : WalkStep G wj wjp1) (p_pre_j : Walk G v₀ wj)
                        (rest_j : Walk G wjp1 vₙ),
                      π = p_pre_j.append (Walk.cons s_right rest_j) ∧
                      wj = π.nodeAt (i + (j - i)) ∧
                      p_pre_j.length = i + (j - i) ∧
                      s_right.HasArrowheadAtSource := by
                  refine ⟨a_j, π.nodeAt j, s_j, π.prefix j, rest_j, ?_, ?_, ?_, h_s_j_arrowhead⟩
                  · rw [h_suf_eq] at h_πfull_j; exact h_πfull_j
                  · congr 1; omega
                  · rw [h_pre_j_len]; omega
                have hi_n_lt : i + (j - i) < π.length := by
                  have : i + (j - i) = j := by omega
                  rw [this]; exact hj_lt_π
                have h_n_pos : 0 < j - i := by omega
                obtain ⟨k, _h_k_ge, _h_k_le, h_πColl, h_anc⟩ :=
                  Walk.exists_collider_with_anc π (j - i) h_n_pos hi_pos hi_n_lt
                  h_helper_left h_helper_right
                exact CDMG.ancSet_of_anc_ancSet h_anc (h_open.1 k h_πColl)
          · -- k > i + σ.length: in suffix part.  Transport via splice_suf.
            have hWlen : ((π.prefix i).append (σ.append (π.suffix j))).length =
                i + σ.length + (π.length - j) := by
              rw [Walk.length_append, h_pre_len, Walk.length_append, h_suf_len, Nat.add_assoc]
            have hk_lt_Wlen : k < ((π.prefix i).append (σ.append (π.suffix j))).length :=
              Walk.isColliderAt_lt_length _ h_coll
            rw [hWlen] at hk_lt_Wlen
            set k' := k - (i + σ.length) with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_le : k' ≤ π.length - j := by omega
            have h_eq : i + σ.length + k' = k := by omega
            rw [← h_eq] at h_coll
            have h_πColl :=
              (Walk.isColliderAt_splice_suf π σ hi_le h_k'_pos).mp h_coll
            rw [← h_eq, Walk.nodeAt_splice_suf π σ hi_le hj h_k'_le]
            exact h_open.1 (j + k') h_πColl
    · -- ===== (1.blkNC) W.IsBlockableNonColliderAt k → W.nodeAt k ∉ C =====
      intro k h_blkNC
      rcases lt_or_ge k i with h_k_lt_i | h_k_ge_i
      · -- k < i: blockable transports to π via splice_pre.
        have h_πNC : π.IsNonColliderAt k := by
          refine ⟨le_trans (le_of_lt h_k_lt_i) hi_le, ?_⟩
          intro h_πColl
          exact h_blkNC.1.2
            ((Walk.isColliderAt_splice_pre π σ hi_le h_k_lt_i).mpr h_πColl)
        have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt k := by
          intro h_πUnblk
          apply h_blkNC.2
          exact (Walk.isUnblockableNonColliderAt_splice_pre π σ hi_le h_k_lt_i).mpr h_πUnblk
        rw [Walk.nodeAt_splice_pre π σ hi_le (le_of_lt h_k_lt_i)]
        exact h_open.2 k ⟨h_πNC, h_πNotUnblk⟩
      · rcases lt_or_ge k (i + σ.length) with h_k_lt_mid | h_k_ge_mid
        · rcases Nat.eq_or_lt_of_le h_k_ge_i with h_k_eq_i | h_k_gt_i
          · -- k = i: outer joint in case (ii).
            -- Sub-cases (ii.a) and (ii.b) based on s_left_πi.
            subst h_k_eq_i
            rw [Walk.nodeAt_splice_pre π σ hi_le (le_refl i)]
            -- Goal: π.nodeAt i ∉ C.
            by_cases hi_zero : i = 0
            · -- i = 0: endpoint.
              subst hi_zero
              exact h_open.2 0 (Walk.isBlockableNonColliderAt_zero π)
            · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
              -- Extract π's step at i-1 (= last step of π.prefix i).
              have h_pre_i_pos : 1 ≤ (π.prefix i).length := by rw [h_pre_len]; omega
              obtain ⟨w_pre_i, p_pre_i, s_left_πi, h_pre_i_eq⟩ :=
                Walk.walk_pos_eq_append_last (π.prefix i) h_pre_i_pos
              have h_p_pre_i_len : p_pre_i.length = i - 1 := by
                have h1 : (π.prefix i).length = p_pre_i.length +
                    (Walk.cons s_left_πi (Walk.nil (π.nodeAt i))).length := by
                  rw [h_pre_i_eq, Walk.length_append]
                rw [h_pre_len] at h1
                simp [Walk.length_cons, Walk.length_nil] at h1
                omega
              have h_pos_form_i : (p_pre_i.length + 1 : ℕ) = i := by omega
              -- Extract first step of σ.append (π.suffix j) as s_app with source-arrowhead.
              have h_app_pos : 1 ≤ (σ.append (π.suffix j)).length := by
                rw [Walk.length_append]
                have h_suf_pos : 1 ≤ (π.suffix j).length := by
                  rw [h_suf_eq, Walk.length_cons]; omega
                omega
              obtain ⟨w_app, s_app, rest_app, h_app_eq⟩ :=
                Walk.walk_pos_eq_cons _ h_app_pos
              have h_suf_has_src : ∀ (a' : α) (s' : WalkStep G (π.nodeAt j) a')
                  (rest' : Walk G a' vₙ),
                  π.suffix j = Walk.cons s' rest' → s'.HasArrowheadAtSource := by
                intro a' s' rest' h_eq'
                rw [h_suf_eq] at h_eq'
                obtain ⟨h_av, h_sa, _⟩ := Walk.cons.inj h_eq'
                subst h_av
                have h_s_eq : s_j = s' := eq_of_heq h_sa
                rw [← h_s_eq]
                exact h_s_j_arrowhead
              have h_s_app_src : s_app.HasArrowheadAtSource :=
                Walk.first_step_has_source_of_reverseDirected_append σ (π.suffix j) _ s_app
                  rest_app hσ_rev_dir h_app_eq h_suf_has_src
              -- Structural form of W at position i.
              have hW_form_i :
                  (π.prefix i).append (σ.append (π.suffix j)) =
                    p_pre_i.append (Walk.cons s_left_πi
                      (Walk.cons s_app rest_app)) := by
                rw [h_pre_i_eq, h_app_eq, Walk.append_assoc,
                  Walk.cons_append, Walk.nil_append]
              -- Case on s_left_πi: backward (ii.a) vs forward/bidir (ii.b).
              cases s_left_πi with
              | forward h_fwd_πi =>
                -- (ii.b): forward s_left has target-arrowhead.  Combined with s_app source-arrowhead,
                -- W.IsColliderAt i.  But h_blkNC.1.2 says ¬ W.IsColliderAt i.  Exfalso.
                exfalso
                apply h_blkNC.1.2
                have h_at_p : (p_pre_i.append (Walk.cons (WalkStep.forward h_fwd_πi)
                    (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                  rw [Walk.isColliderAt_append_cons_cons_one]; exact ⟨by simp, h_s_app_src⟩
                have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt
                    (p_pre_i.length + 1) := by
                  rw [hW_form_i]; exact h_at_p
                convert h_at_W using 2; omega
              | backward h_bw_πi =>
                -- (ii.a): backward s_left.  Joint is non-collider; analyze.
                by_cases h_left_sc : w_pre_i ∈ G.Sc (π.nodeAt i)
                · -- Joint is unblockable.  Exfalso.
                  exfalso
                  apply h_blkNC.2
                  have h_joint : (WalkStep.backward h_bw_πi).IsUnblockableJoint s_app := by
                    refine ⟨?_, ?_, ?_⟩
                    · intro ⟨h_tgt, _⟩; simp at h_tgt
                    · intro _; exact h_left_sc
                    · intro h_fwd
                      cases s_app with
                      | forward _ => simp at h_s_app_src
                      | backward _ => simp at h_fwd
                      | bidir _ => simp at h_fwd
                  have h_at_p :
                      (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                          (Walk.cons s_app rest_app))).IsUnblockableNonColliderAt
                        (p_pre_i.length + 1) :=
                    (Walk.isUnblockableNonColliderAt_append_cons_cons_one p_pre_i
                      (WalkStep.backward h_bw_πi) s_app rest_app).mpr h_joint
                  have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                      (p_pre_i.length + 1) := by
                    rw [hW_form_i]; exact h_at_p
                  convert h_at_W using 2; omega
                · -- Joint not unblockable.  Transport from π at i.
                  -- π's step at i.
                  have hi_lt_π : i < π.length := lt_of_lt_of_le hij hj
                  have h_suf_i_pos : 1 ≤ (π.suffix i).length := by
                    rw [Walk.length_suffix π (le_of_lt hi_lt_π)]; omega
                  obtain ⟨_, s_right_πi, rest_πi, h_suf_i_eq⟩ :=
                    Walk.walk_pos_eq_cons (π.suffix i) h_suf_i_pos
                  have h_alt_eq :
                      (π.prefix i).append (π.suffix i) =
                        p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                          (Walk.cons s_right_πi rest_πi)) := by
                    rw [h_pre_i_eq, h_suf_i_eq, Walk.append_assoc,
                      Walk.cons_append, Walk.nil_append]
                  have hπ_form : π = p_pre_i.append
                      (Walk.cons (WalkStep.backward h_bw_πi)
                        (Walk.cons s_right_πi rest_πi)) := by
                    rw [← h_alt_eq]
                    exact (Walk.prefix_append_suffix π (le_of_lt hi_lt_π)).symm
                  have h_πNC : π.IsNonColliderAt i := by
                    refine ⟨le_of_lt hi_lt_π, ?_⟩
                    intro h_πColl
                    rw [hπ_form] at h_πColl
                    have h_at_p :
                        (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                            (Walk.cons s_right_πi rest_πi))).IsColliderAt
                          (p_pre_i.length + 1) := by
                      convert h_πColl using 2
                    rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                    simp at h_at_p
                  have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt i := by
                    intro h_πUnblk
                    rw [hπ_form] at h_πUnblk
                    have h_at_p :
                        (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                            (Walk.cons s_right_πi rest_πi))).IsUnblockableNonColliderAt
                          (p_pre_i.length + 1) := by
                      convert h_πUnblk using 2
                    rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                    apply h_left_sc
                    exact h_at_p.2.1 (by simp [WalkStep.IsBackward])
                  exact h_open.2 i ⟨h_πNC, h_πNotUnblk⟩
              | bidir h_bd_πi =>
                -- (ii.b): bidir s_left has target-arrowhead.  Same as forward case.
                exfalso
                apply h_blkNC.1.2
                have h_at_p : (p_pre_i.append (Walk.cons (WalkStep.bidir h_bd_πi)
                    (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                  rw [Walk.isColliderAt_append_cons_cons_one]; exact ⟨by simp, h_s_app_src⟩
                have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt
                    (p_pre_i.length + 1) := by
                  rw [hW_form_i]; exact h_at_p
                convert h_at_W using 2; omega
          · -- i < k < i + σ.length: σ interior.  Unblockable via reverseDirected.
            exfalso
            set k' := k - i with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_lt : k' < σ.length := by omega
            have h_eq : i + k' = k := by omega
            apply h_blkNC.2
            rw [← h_eq]
            rw [Walk.isUnblockableNonColliderAt_splice_mid π σ hi_le h_k'_pos h_k'_lt]
            exact Walk.isUnblockableNonColliderAt_interior_of_reverseDirected_in_Sc σ
              hσ_rev_dir hσ_inSc k' h_k'_pos h_k'_lt
        · rcases Nat.eq_or_lt_of_le h_k_ge_mid with h_k_eq_mid | h_k_gt_mid
          · -- k = i + σ.length: right joint (σ.length ≥ 1) OR collapsed joint (σ.length = 0).
            subst h_k_eq_mid
            by_cases hσ_pos : 1 ≤ σ.length
            · -- σ.length ≥ 1: unblockable left-chain joint.  exfalso.
              exfalso
              obtain ⟨w_last_σ, σ_pre, s_last_σ, hσ_last_eq⟩ :=
                Walk.walk_pos_eq_append_last σ hσ_pos
              have hσ_pre_len : σ_pre.length = σ.length - 1 := by
                have h_eq : σ.length = σ_pre.length + 1 := by
                  conv_lhs => rw [hσ_last_eq]
                  rw [Walk.length_append, Walk.length_cons, Walk.length_nil]
                omega
              have h_s_last_σ_bw : s_last_σ.IsBackward := by
                rw [hσ_last_eq] at hσ_rev_dir
                rw [Walk.reverse_append, Walk.reverse_cons, Walk.reverse_nil,
                  Walk.nil_append] at hσ_rev_dir
                cases s_last_σ with
                | forward _ => simp at hσ_rev_dir
                | backward _ => simp
                | bidir _ => simp at hσ_rev_dir
              have h_w_last_σ_sc : w_last_σ ∈ G.Sc (π.nodeAt j) := by
                have h_σ_pre_len_le : σ_pre.length ≤ σ.length := by omega
                have h_in : σ.nodeAt σ_pre.length ∈ G.Sc (π.nodeAt j) :=
                  hσ_inSc σ_pre.length h_σ_pre_len_le
                have h_node_eq : σ.nodeAt σ_pre.length = w_last_σ := by
                  rw [hσ_last_eq]
                  rw [Walk.nodeAt_append_le _ _ (le_refl _)]
                  exact Walk.nodeAt_length _
                rw [h_node_eq] at h_in
                exact h_in
              -- W = ((π.prefix i).append σ_pre).append (cons s_last_σ (cons s_j rest_j))
              have hW_form_inner :
                  (π.prefix i).append (σ.append (π.suffix j)) =
                    ((π.prefix i).append σ_pre).append
                      (Walk.cons s_last_σ (Walk.cons s_j rest_j)) := by
                rw [hσ_last_eq, h_suf_eq, Walk.append_assoc, Walk.append_assoc,
                  Walk.cons_append, Walk.nil_append]
              have hpos_inner : ((π.prefix i).append σ_pre).length + 1 = i + σ.length := by
                rw [Walk.length_append, h_pre_len, hσ_pre_len]; omega
              apply h_blkNC.2
              rw [hW_form_inner]
              rw [show (i + σ.length : ℕ) = ((π.prefix i).append σ_pre).length + 1 from
                hpos_inner.symm]
              rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one]
              refine ⟨?_, ?_, ?_⟩
              · -- ¬ collider: s_last_σ backward has HasArrowheadAtTarget = False.
                intro ⟨h_tgt, _⟩
                cases s_last_σ with
                | forward _ => simp at h_s_last_σ_bw
                | backward _ => simp at h_tgt
                | bidir _ => simp at h_s_last_σ_bw
              · -- s_last_σ.IsBackward → w_last_σ ∈ Sc^G(π.nodeAt j).
                intro _; exact h_w_last_σ_sc
              · -- s_j.IsForward → ...: s_j has source-arrowhead, NOT forward.  Vacuous.
                intro h_fwd
                cases s_j with
                | forward _ => simp at h_s_j_arrowhead
                | backward _ => simp at h_fwd
                | bidir _ => simp at h_fwd
            · -- σ.length = 0: joint collapses with outer joint.  Same (ii.a)/(ii.b) analysis.
              push_neg at hσ_pos
              have hσ_zero : σ.length = 0 := Nat.lt_one_iff.mp hσ_pos
              -- Goal: W.nodeAt (i + σ.length) ∉ C.  Reduce to π.nodeAt i ∉ C.
              rw [Walk.nodeAt_splice_mid π σ hi_le (le_refl σ.length), Walk.nodeAt_length]
              have h_vi_eq_vj : π.nodeAt i = π.nodeAt j :=
                Walk.source_eq_target_of_length_zero σ hσ_zero
              rw [← h_vi_eq_vj]
              -- Goal: π.nodeAt i ∉ C.
              by_cases hi_zero : i = 0
              · subst hi_zero
                exact h_open.2 0 (Walk.isBlockableNonColliderAt_zero π)
              · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
                have h_pre_i_pos : 1 ≤ (π.prefix i).length := by rw [h_pre_len]; omega
                obtain ⟨w_pre_i, p_pre_i, s_left_πi, h_pre_i_eq⟩ :=
                  Walk.walk_pos_eq_append_last (π.prefix i) h_pre_i_pos
                have h_p_pre_i_len : p_pre_i.length = i - 1 := by
                  have h1 : (π.prefix i).length = p_pre_i.length +
                      (Walk.cons s_left_πi (Walk.nil (π.nodeAt i))).length := by
                    rw [h_pre_i_eq, Walk.length_append]
                  rw [h_pre_len] at h1
                  simp [Walk.length_cons, Walk.length_nil] at h1
                  omega
                have h_pos_form_i : (p_pre_i.length + 1 : ℕ) = i := by omega
                have h_app_pos : 1 ≤ (σ.append (π.suffix j)).length := by
                  rw [Walk.length_append]
                  have h_suf_pos : 1 ≤ (π.suffix j).length := by
                    rw [h_suf_eq, Walk.length_cons]; omega
                  omega
                obtain ⟨w_app, s_app, rest_app, h_app_eq⟩ :=
                  Walk.walk_pos_eq_cons _ h_app_pos
                have h_suf_has_src : ∀ (a' : α) (s' : WalkStep G (π.nodeAt j) a')
                    (rest' : Walk G a' vₙ),
                    π.suffix j = Walk.cons s' rest' → s'.HasArrowheadAtSource := by
                  intro a' s' rest' h_eq'
                  rw [h_suf_eq] at h_eq'
                  obtain ⟨h_av, h_sa, _⟩ := Walk.cons.inj h_eq'
                  subst h_av
                  have h_s_eq : s_j = s' := eq_of_heq h_sa
                  rw [← h_s_eq]
                  exact h_s_j_arrowhead
                have h_s_app_src : s_app.HasArrowheadAtSource :=
                  Walk.first_step_has_source_of_reverseDirected_append σ (π.suffix j) _ s_app
                    rest_app hσ_rev_dir h_app_eq h_suf_has_src
                have hW_form_i :
                    (π.prefix i).append (σ.append (π.suffix j)) =
                      p_pre_i.append (Walk.cons s_left_πi
                        (Walk.cons s_app rest_app)) := by
                  rw [h_pre_i_eq, h_app_eq, Walk.append_assoc,
                    Walk.cons_append, Walk.nil_append]
                -- Case on s_left_πi.
                cases s_left_πi with
                | forward h_fwd_πi =>
                  -- (ii.b): collider on W, ¬ collider in h_blkNC fails. Exfalso.
                  exfalso
                  apply h_blkNC.1.2
                  have h_at_p : (p_pre_i.append (Walk.cons (WalkStep.forward h_fwd_πi)
                      (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                    rw [Walk.isColliderAt_append_cons_cons_one]; exact ⟨by simp, h_s_app_src⟩
                  have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt
                      (p_pre_i.length + 1) := by
                    rw [hW_form_i]; exact h_at_p
                  have h_pos_eq : (i + σ.length : ℕ) = p_pre_i.length + 1 := by omega
                  exact h_pos_eq.symm ▸ h_at_W
                | backward h_bw_πi =>
                  -- (ii.a): non-collider on W.  Sub-case on v_{i-1} ∈ Sc^G(v_i).
                  by_cases h_left_sc : w_pre_i ∈ G.Sc (π.nodeAt i)
                  · -- Unblockable → exfalso.
                    exfalso
                    apply h_blkNC.2
                    have h_joint : (WalkStep.backward h_bw_πi).IsUnblockableJoint s_app := by
                      refine ⟨?_, ?_, ?_⟩
                      · intro ⟨h_tgt, _⟩; simp at h_tgt
                      · intro _; exact h_left_sc
                      · intro h_fwd
                        cases s_app with
                        | forward _ => simp at h_s_app_src
                        | backward _ => simp at h_fwd
                        | bidir _ => simp at h_fwd
                    have h_at_p :
                        (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                            (Walk.cons s_app rest_app))).IsUnblockableNonColliderAt
                          (p_pre_i.length + 1) :=
                      (Walk.isUnblockableNonColliderAt_append_cons_cons_one p_pre_i
                        (WalkStep.backward h_bw_πi) s_app rest_app).mpr h_joint
                    have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                        (p_pre_i.length + 1) := by
                      rw [hW_form_i]; exact h_at_p
                    have h_pos_eq : (i + σ.length : ℕ) = p_pre_i.length + 1 := by omega
                    exact h_pos_eq.symm ▸ h_at_W
                  · -- Joint not unblockable.  Transport from π at i.
                    have hi_lt_π : i < π.length := lt_of_lt_of_le hij hj
                    have h_suf_i_pos : 1 ≤ (π.suffix i).length := by
                      rw [Walk.length_suffix π (le_of_lt hi_lt_π)]; omega
                    obtain ⟨_, s_right_πi, rest_πi, h_suf_i_eq⟩ :=
                      Walk.walk_pos_eq_cons (π.suffix i) h_suf_i_pos
                    have h_alt_eq :
                        (π.prefix i).append (π.suffix i) =
                          p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                            (Walk.cons s_right_πi rest_πi)) := by
                      rw [h_pre_i_eq, h_suf_i_eq, Walk.append_assoc,
                        Walk.cons_append, Walk.nil_append]
                    have hπ_form : π = p_pre_i.append
                        (Walk.cons (WalkStep.backward h_bw_πi)
                          (Walk.cons s_right_πi rest_πi)) := by
                      rw [← h_alt_eq]
                      exact (Walk.prefix_append_suffix π (le_of_lt hi_lt_π)).symm
                    have h_πNC : π.IsNonColliderAt i := by
                      refine ⟨le_of_lt hi_lt_π, ?_⟩
                      intro h_πColl
                      rw [hπ_form] at h_πColl
                      have h_at_p :
                          (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                              (Walk.cons s_right_πi rest_πi))).IsColliderAt
                            (p_pre_i.length + 1) := by
                        convert h_πColl using 2
                      rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                      simp at h_at_p
                    have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt i := by
                      intro h_πUnblk
                      rw [hπ_form] at h_πUnblk
                      have h_at_p :
                          (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                              (Walk.cons s_right_πi rest_πi))).IsUnblockableNonColliderAt
                            (p_pre_i.length + 1) := by
                        convert h_πUnblk using 2
                      rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                      apply h_left_sc
                      exact h_at_p.2.1 (by simp [WalkStep.IsBackward])
                    exact h_open.2 i ⟨h_πNC, h_πNotUnblk⟩
                | bidir h_bd_πi =>
                  -- (ii.b): collider on W (bidir has target-arrowhead). Exfalso.
                  exfalso
                  apply h_blkNC.1.2
                  have h_at_p : (p_pre_i.append (Walk.cons (WalkStep.bidir h_bd_πi)
                      (Walk.cons s_app rest_app))).IsColliderAt (p_pre_i.length + 1) := by
                    rw [Walk.isColliderAt_append_cons_cons_one]; exact ⟨by simp, h_s_app_src⟩
                  have h_at_W : ((π.prefix i).append (σ.append (π.suffix j))).IsColliderAt
                      (p_pre_i.length + 1) := by
                    rw [hW_form_i]; exact h_at_p
                  have h_pos_eq : (i + σ.length : ℕ) = p_pre_i.length + 1 := by omega
                  exact h_pos_eq.symm ▸ h_at_W
          · -- k > i + σ.length: transport via splice_suf.
            have hWlen : ((π.prefix i).append (σ.append (π.suffix j))).length =
                i + σ.length + (π.length - j) := by
              rw [Walk.length_append, h_pre_len, Walk.length_append, h_suf_len, Nat.add_assoc]
            have hk_le_Wlen : k ≤ ((π.prefix i).append (σ.append (π.suffix j))).length :=
              h_blkNC.1.1
            rw [hWlen] at hk_le_Wlen
            set k' := k - (i + σ.length) with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_le : k' ≤ π.length - j := by omega
            have h_eq : i + σ.length + k' = k := by omega
            have h_jk'_le : j + k' ≤ π.length := by omega
            have h_πNC : π.IsNonColliderAt (j + k') := by
              refine ⟨h_jk'_le, ?_⟩
              intro h_πColl
              apply h_blkNC.1.2
              rw [← h_eq]
              exact (Walk.isColliderAt_splice_suf π σ hi_le h_k'_pos).mpr h_πColl
            have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt (j + k') := by
              intro h_πUnblk
              apply h_blkNC.2
              rw [← h_eq]
              exact (Walk.isUnblockableNonColliderAt_splice_suf
                π σ hi_le h_k'_pos).mpr h_πUnblk
            rw [← h_eq, Walk.nodeAt_splice_suf π σ hi_le hj h_k'_le]
            exact h_open.2 (j + k') ⟨h_πNC, h_πNotUnblk⟩
  · -- ============================================================
    -- LN case (i): j = π.length OR step at j is forward.
    -- σ is built from h_sc.1.
    -- ============================================================
    -- "No first step of π.suffix j has source-arrowhead":
    have h_suf_no_src : ∀ (a : α) (s : WalkStep G (π.nodeAt j) a)
        (rest : Walk G a vₙ), π.suffix j = Walk.cons s rest →
          ¬ s.HasArrowheadAtSource := by
      intro a s rest h_eq h_src
      exact h_case_ii ⟨a, s, rest, h_eq, h_src⟩
    -- Extract directed walk π_dir : Walk G vᵢ vⱼ from h_sc.1
    obtain ⟨π_dir, h_πdir_dir⟩ := h_sc.1.2
    -- Loop-erase to get a directed path σ
    obtain ⟨σ, hσ_dir, hσ_path⟩ :=
      Walk.exists_path_of_directed π_dir h_πdir_dir
    -- Verify disjunct (3): every position on σ lies in Sc^G(vⱼ).
    have hσ_inSc : ∀ k, k ≤ σ.length → σ.nodeAt k ∈ G.Sc vⱼ :=
      Walk.directed_walk_in_Sc σ hσ_dir h_sc
    refine ⟨σ, ?_, Or.inl hσ_dir, hσ_inSc, hσ_path⟩
    -- All that remains is disjunct (1): σ-openness of the spliced walk.
    refine ⟨?_, ?_⟩
    · -- ===== (1.coll)  W.IsColliderAt k → W.nodeAt k ∈ G.AncSet C =====
      intro k h_coll
      rcases lt_or_ge k i with h_k_lt_i | h_k_ge_i
      · -- k < i: transport via splice_pre.
        have h_πColl :=
          (Walk.isColliderAt_splice_pre π σ hi_le h_k_lt_i).mp h_coll
        rw [Walk.nodeAt_splice_pre π σ hi_le (le_of_lt h_k_lt_i)]
        exact h_open.1 k h_πColl
      · -- k ≥ i.
        rcases lt_or_ge k (i + σ.length) with h_k_lt_mid | h_k_ge_mid
        · -- i ≤ k < i + σ.length.
          rcases Nat.eq_or_lt_of_le h_k_ge_i with h_k_eq_i | h_k_gt_i
          · -- k = i: outer joint.  No collider in case (i).
            exfalso
            subst h_k_eq_i
            by_cases hp2_pos : 1 ≤ (σ.append (π.suffix j)).length
            · obtain ⟨_, s, p₂', hp_eq⟩ := Walk.walk_pos_eq_cons _ hp2_pos
              -- The first step of σ.append (π.suffix j) has no source-arrowhead.
              have h_no_src : ¬ s.HasArrowheadAtSource :=
                Walk.first_step_no_source_of_directed_append σ (π.suffix j) _ s p₂'
                  hσ_dir hp_eq h_suf_no_src
              rw [hp_eq] at h_coll
              have h_coll' :
                  ((π.prefix i).append (Walk.cons s p₂')).IsColliderAt
                    (π.prefix i).length := by
                rw [h_pre_len]; exact h_coll
              exact Walk.not_isColliderAt_append_cons_at_left_length
                (π.prefix i) s p₂' h_no_src h_coll'
            · push_neg at hp2_pos
              have hp2_zero : (σ.append (π.suffix j)).length = 0 :=
                Nat.lt_one_iff.mp hp2_pos
              have hWlen : ((π.prefix i).append (σ.append (π.suffix j))).length = i := by
                rw [Walk.length_append, h_pre_len, hp2_zero]; omega
              apply (Walk.isNonColliderAt_length _).2
              rw [hWlen]
              exact h_coll
          · -- i < k < i + σ.length: interior of σ.
            -- W.IsColliderAt k = σ.IsColliderAt (k - i) by splice_mid.
            -- σ.IsColliderAt = False (directed).
            exfalso
            set k' := k - i with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_lt : k' < σ.length := by omega
            have h_eq : i + k' = k := by omega
            rw [← h_eq] at h_coll
            have h_σColl :=
              (Walk.isColliderAt_splice_mid π σ hi_le h_k'_pos h_k'_lt).mp h_coll
            exact Walk.not_isColliderAt_of_isDirected σ k' hσ_dir h_σColl
        · -- k ≥ i + σ.length.
          rcases Nat.eq_or_lt_of_le h_k_ge_mid with h_k_eq_mid | h_k_gt_mid
          · -- k = i + σ.length: inner joint (or endpoint when j = π.length).
            -- Use append_assoc to rewrite W as ((π.prefix i).append σ).append (π.suffix j).
            -- Position k is then ((π.prefix i).append σ).length, the boundary.
            exfalso
            subst h_k_eq_mid
            -- W = (π.prefix i).append (σ.append (π.suffix j))
            --   = ((π.prefix i).append σ).append (π.suffix j) by append_assoc.
            have hW_assoc :
                (π.prefix i).append (σ.append (π.suffix j)) =
                  ((π.prefix i).append σ).append (π.suffix j) :=
              (Walk.append_assoc _ _ _).symm
            rw [hW_assoc] at h_coll
            -- Now h_coll : (((π.prefix i).append σ).append (π.suffix j)).IsColliderAt (i + σ.length).
            -- Case-on π.suffix j: either cons or nil.
            by_cases hsuf_pos : 1 ≤ (π.suffix j).length
            · -- π.suffix j has a first step. Decompose.
              obtain ⟨_, s, p₂', hsuf_eq⟩ :=
                Walk.walk_pos_eq_cons (π.suffix j) hsuf_pos
              -- First step has no source-arrowhead (by h_suf_no_src).
              have h_no_src : ¬ s.HasArrowheadAtSource :=
                h_suf_no_src _ s p₂' hsuf_eq
              rw [hsuf_eq] at h_coll
              -- h_coll : (((π.prefix i).append σ).append (cons s p₂')).IsColliderAt (i + σ.length).
              have h_len_app : ((π.prefix i).append σ).length = i + σ.length := by
                rw [Walk.length_append, h_pre_len]
              have h_coll' :
                  (((π.prefix i).append σ).append (Walk.cons s p₂')).IsColliderAt
                    ((π.prefix i).append σ).length := by
                rw [h_len_app]; exact h_coll
              exact Walk.not_isColliderAt_append_cons_at_left_length
                ((π.prefix i).append σ) s p₂' h_no_src h_coll'
            · -- π.suffix j has length 0.
              push_neg at hsuf_pos
              have hsuf_zero : (π.suffix j).length = 0 := Nat.lt_one_iff.mp hsuf_pos
              -- Position i + σ.length on W is the endpoint of W.
              have hWlen :
                  (((π.prefix i).append σ).append (π.suffix j)).length =
                    i + σ.length := by
                rw [Walk.length_append, Walk.length_append, h_pre_len, hsuf_zero]; omega
              apply (Walk.isNonColliderAt_length _).2
              rw [hWlen]
              exact h_coll
          · -- k > i + σ.length: in suffix part. Transport.
            have hWlen : ((π.prefix i).append (σ.append (π.suffix j))).length =
                i + σ.length + (π.length - j) := by
              rw [Walk.length_append, h_pre_len, Walk.length_append, h_suf_len, Nat.add_assoc]
            have hk_lt_Wlen : k < ((π.prefix i).append (σ.append (π.suffix j))).length := by
              exact Walk.isColliderAt_lt_length _ h_coll
            rw [hWlen] at hk_lt_Wlen
            set k' := k - (i + σ.length) with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_le : k' ≤ π.length - j := by omega
            have h_eq : i + σ.length + k' = k := by omega
            rw [← h_eq] at h_coll
            have h_πColl :=
              (Walk.isColliderAt_splice_suf π σ hi_le h_k'_pos).mp h_coll
            rw [← h_eq]
            rw [Walk.nodeAt_splice_suf π σ hi_le hj h_k'_le]
            exact h_open.1 (j + k') h_πColl
    · -- ===== (1.blkNC) W.IsBlockableNonColliderAt k → W.nodeAt k ∉ C =====
      intro k h_blkNC
      rcases lt_or_ge k i with h_k_lt_i | h_k_ge_i
      · -- k < i: blockable transports to π.
        have h_πNC : π.IsNonColliderAt k := by
          refine ⟨le_trans (le_of_lt h_k_lt_i) hi_le, ?_⟩
          intro h_πColl
          exact h_blkNC.1.2
            ((Walk.isColliderAt_splice_pre π σ hi_le h_k_lt_i).mpr h_πColl)
        have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt k := by
          intro h_πUnblk
          apply h_blkNC.2
          exact (Walk.isUnblockableNonColliderAt_splice_pre π σ hi_le h_k_lt_i).mpr h_πUnblk
        rw [Walk.nodeAt_splice_pre π σ hi_le (le_of_lt h_k_lt_i)]
        exact h_open.2 k ⟨h_πNC, h_πNotUnblk⟩
      · -- k ≥ i.
        rcases lt_or_ge k (i + σ.length) with h_k_lt_mid | h_k_ge_mid
        · rcases Nat.eq_or_lt_of_le h_k_ge_i with h_k_eq_i | h_k_gt_i
          · -- k = i: outer joint blockable analysis.
            subst h_k_eq_i
            -- Goal: W.nodeAt i ∉ C.  Reduce W.nodeAt i to π.nodeAt i.
            rw [Walk.nodeAt_splice_pre π σ hi_le (le_refl i)]
            -- Now goal: π.nodeAt i ∉ C.
            -- Case on i = 0 (endpoint) vs i ≥ 1.
            by_cases hi_zero : i = 0
            · subst hi_zero
              exact h_open.2 0 (Walk.isBlockableNonColliderAt_zero π)
            · -- i ≥ 1.
              have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
              -- Extract π's step at i-1: the last step of π.prefix i.
              have h_pre_pos : 1 ≤ (π.prefix i).length := by rw [h_pre_len]; omega
              obtain ⟨w_pre, p_pre, s_left, h_pre_eq⟩ :=
                Walk.walk_pos_eq_append_last (π.prefix i) h_pre_pos
              -- p_pre.length = i - 1.
              have h_p_pre_len : p_pre.length = i - 1 := by
                have h1 : (π.prefix i).length =
                    p_pre.length + (Walk.cons s_left (Walk.nil (π.nodeAt i))).length := by
                  rw [h_pre_eq, Walk.length_append]
                rw [h_pre_len] at h1
                simp [Walk.length_cons, Walk.length_nil] at h1
                omega
              -- Case on σ.append (π.suffix j) length.
              by_cases hp2_pos : 1 ≤ (σ.append (π.suffix j)).length
              · -- σ.append (π.suffix j) is a cons.
                obtain ⟨w_r, s_right, p_rest, hp_eq⟩ :=
                  Walk.walk_pos_eq_cons _ hp2_pos
                -- W = p_pre ⧺ cons s_left (cons s_right p_rest) (after rewriting).
                have hW_form : ((π.prefix i).append (σ.append (π.suffix j))) =
                    p_pre.append (Walk.cons s_left (Walk.cons s_right p_rest)) := by
                  rw [h_pre_eq, hp_eq, Walk.append_assoc]
                  rw [Walk.cons_append, Walk.nil_append]
                -- s_right has no source-arrowhead (case (i)).
                have h_s_right_no_src : ¬ s_right.HasArrowheadAtSource :=
                  Walk.first_step_no_source_of_directed_append σ (π.suffix j) _ s_right p_rest
                    hσ_dir hp_eq h_suf_no_src
                -- The joint condition: if (2) and (3) hold, joint is unblockable on W,
                -- contradicting h_blkNC.2.  Otherwise, derive π.IsBlockableNonColliderAt i
                -- (or j when σ.length = 0).
                -- s_right is forward (no source-arrowhead).
                have h_s_right_fwd : s_right.IsForward := by
                  cases s_right with
                  | forward _ => simp
                  | backward _ => simp at h_s_right_no_src
                  | bidir _ => simp at h_s_right_no_src
                -- Position-on-W shift identity.
                have h_pos_form : (p_pre.length + 1 : ℕ) = i := by omega
                -- W is unblockable at (p_pre.length + 1) iff s_left.IsUnblockableJoint s_right.
                -- We avoid rewriting i in the iff (since s_left's type mentions vᵢ = π.nodeAt i).
                have h_unblk_iff :
                    ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                      (p_pre.length + 1) ↔ s_left.IsUnblockableJoint s_right := by
                  rw [hW_form]
                  exact Walk.isUnblockableNonColliderAt_append_cons_cons_one
                    p_pre s_left s_right p_rest
                -- ¬ Unblockable joint:
                have h_no_unblk : ¬ s_left.IsUnblockableJoint s_right := by
                  intro h_joint
                  have h_at_p : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                      (p_pre.length + 1) := h_unblk_iff.mpr h_joint
                  apply h_blkNC.2
                  convert h_at_p using 2
                  exact h_pos_form.symm
                -- Unpacking ¬ IsUnblockableJoint: since ¬ collider holds, either
                -- (s_left.IsBackward ∧ source ∉ Sc) or (s_right.IsForward ∧ target ∉ Sc).
                -- We split via classical reasoning.
                -- Show what target(s_right) and source(s_left) are.
                -- For target ∈ Sc^G(vᵢ): determined by σ.length.
                by_cases h_target_sc : w_r ∈ G.Sc (π.nodeAt i)
                · -- target ∈ Sc^G(vᵢ): (3) holds.  So (2) must fail.
                  -- (2) fails: s_left.IsBackward ∧ source ∉ Sc^G(vᵢ).
                  -- s_left's type is WalkStep G w_pre (π.nodeAt i).
                  by_cases h_source_sc : w_pre ∈ G.Sc (π.nodeAt i)
                  · -- (2) vacuous or holds. Combined with (3), joint unblockable. Contradiction.
                    exfalso
                    apply h_no_unblk
                    refine ⟨?_, ?_, ?_⟩
                    · intro ⟨_, hsrc⟩; exact h_s_right_no_src hsrc
                    · intro _; exact h_source_sc
                    · intro _; exact h_target_sc
                  · -- s_left.IsBackward must hold (since (2) fails requires backward).
                    -- And source ∉ Sc.
                    -- So s_left is backward, and v_{i-1} ∉ Sc.
                    -- This means on π at position i, the joint is (s_left=backward, π's step at i).
                    -- v_i on π is non-collider (s_left no target-arrowhead) AND blockable
                    -- (outgoing to v_{i-1} ∉ Sc). v_i ∉ C.
                    -- To verify s_left is backward, we examine its constructor.
                    cases s_left with
                    | forward h_e =>
                      -- s_left forward: target-arrowhead True, source-arrowhead False.
                      -- (2) is vacuous (IsBackward = False). But h_source_sc says source ∉ Sc.
                      -- Need: joint condition (2) to be the failure point.
                      -- Hmm, with s_left forward, (2) is vacuous → no contribution to ¬ unblockable.
                      -- (3) holds → joint unblockable → contradict h_no_unblk.
                      exfalso
                      apply h_no_unblk
                      refine ⟨?_, ?_, ?_⟩
                      · intro ⟨_, hsrc⟩; exact h_s_right_no_src hsrc
                      · intro h_back; simp at h_back
                      · intro _; exact h_target_sc
                    | backward h_e =>
                      -- s_left backward: source ∉ Sc^G(vᵢ).
                      -- On π at i: blockable.  Construct π.IsBlockableNonColliderAt i.
                      have hi_lt_π : i < π.length := lt_of_lt_of_le hij hj
                      have h_suf_i_pos : 1 ≤ (π.suffix i).length := by
                        rw [Walk.length_suffix π (le_of_lt hi_lt_π)]; omega
                      obtain ⟨_, s_right_π, rest_π, h_suf_i_eq⟩ :=
                        Walk.walk_pos_eq_cons (π.suffix i) h_suf_i_pos
                      -- Establish π in the structural form, via two-step Eq.trans:
                      --   π = (π.prefix i).append (π.suffix i)
                      --     = (p_pre ⧺ cons s_left (nil _)) ⧺ (cons s_right_π rest_π)
                      --     = p_pre ⧺ cons s_left (cons s_right_π rest_π).
                      have h_alt_eq :
                          (π.prefix i).append (π.suffix i) =
                            p_pre.append (Walk.cons (WalkStep.backward h_e)
                              (Walk.cons s_right_π rest_π)) := by
                        rw [h_pre_eq, h_suf_i_eq, Walk.append_assoc,
                          Walk.cons_append, Walk.nil_append]
                      have hπ_form : π = p_pre.append
                          (Walk.cons (WalkStep.backward h_e)
                            (Walk.cons s_right_π rest_π)) := by
                        rw [← h_alt_eq]
                        exact (Walk.prefix_append_suffix π (le_of_lt hi_lt_π)).symm
                      -- π is non-collider at i: s_left has no target-arrowhead.
                      have h_πNC : π.IsNonColliderAt i := by
                        refine ⟨le_of_lt hi_lt_π, ?_⟩
                        intro h_πColl
                        rw [hπ_form] at h_πColl
                        have h_at_p :
                            (p_pre.append (Walk.cons (WalkStep.backward h_e)
                                (Walk.cons s_right_π rest_π))).IsColliderAt
                              (p_pre.length + 1) := by
                          convert h_πColl using 2
                        rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                        simp at h_at_p
                      -- π is not unblockable at i: (2) fails (source = w_pre ∉ Sc).
                      have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt i := by
                        intro h_πUnblk
                        rw [hπ_form] at h_πUnblk
                        have h_at_p :
                            (p_pre.append (Walk.cons (WalkStep.backward h_e)
                                (Walk.cons s_right_π rest_π))).IsUnblockableNonColliderAt
                              (p_pre.length + 1) := by
                          convert h_πUnblk using 2
                        rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                        -- h_at_p : (backward h_e).IsUnblockableJoint s_right_π.
                        -- This requires (2): source (= w_pre) ∈ Sc^G(target = vᵢ).
                        -- But h_source_sc says ¬ (w_pre ∈ G.Sc vᵢ).
                        apply h_source_sc
                        exact h_at_p.2.1 (by simp [WalkStep.IsBackward])
                      exact h_open.2 i ⟨h_πNC, h_πNotUnblk⟩
                    | bidir h_e =>
                      -- s_left bidir: source-arrowhead True (in particular target-arrowhead True).
                      -- (2) vacuous. (3) holds → joint unblockable → contradict.
                      exfalso
                      apply h_no_unblk
                      refine ⟨?_, ?_, ?_⟩
                      · intro ⟨_, hsrc⟩; exact h_s_right_no_src hsrc
                      · intro h_back; simp at h_back
                      · intro _; exact h_target_sc
                · -- target ∉ Sc^G(vᵢ): (3) fails.
                  -- We claim σ.length = 0 (otherwise target = σ.nodeAt 1 ∈ Sc, contradiction).
                  by_cases hσ_pos : 1 ≤ σ.length
                  · -- σ.length ≥ 1: σ's first step is forward, target = σ.nodeAt 1.
                    -- Show target ∈ Sc^G(vⱼ) = Sc^G(vᵢ), contradicting h_target_sc.
                    exfalso
                    apply h_target_sc
                    obtain ⟨_, sσ, σrest, hσ_eq⟩ := Walk.walk_pos_eq_cons σ hσ_pos
                    have hp_eq' : σ.append (π.suffix j) =
                        Walk.cons sσ (σrest.append (π.suffix j)) := by
                      rw [hσ_eq, Walk.cons_append]
                    rw [hp_eq'] at hp_eq
                    obtain ⟨h_w_eq, _, _⟩ := Walk.cons.inj hp_eq
                    have h_sc_node1 : σ.nodeAt 1 ∈ G.Sc vⱼ :=
                      hσ_inSc 1 (by omega)
                    have h_node1_eq : σ.nodeAt 1 = w_r := by
                      rw [hσ_eq]
                      change σrest.nodeAt 0 = w_r
                      rw [Walk.nodeAt_zero]
                      exact h_w_eq
                    rw [h_node1_eq] at h_sc_node1
                    -- Now w_r ∈ G.Sc vⱼ.  Convert to w_r ∈ G.Sc vᵢ via Sc-equivalence.
                    obtain ⟨h_anc, h_desc⟩ := h_sc_node1
                    refine ⟨?_, ?_⟩
                    · obtain ⟨h_wr_mem, ⟨p_wr_vj, hp_wr_vj⟩⟩ := h_anc
                      obtain ⟨_, ⟨p_vj_vi, hp_vj_vi⟩⟩ := h_sc.2
                      exact ⟨h_wr_mem, ⟨p_wr_vj.append p_vj_vi,
                        Walk.isDirected_append _ _ hp_wr_vj hp_vj_vi⟩⟩
                    · obtain ⟨_, ⟨p_vi_vj, hp_vi_vj⟩⟩ := h_sc.1
                      obtain ⟨h_wr_mem, ⟨p_vj_wr, hp_vj_wr⟩⟩ := h_desc
                      exact ⟨h_wr_mem, ⟨p_vi_vj.append p_vj_wr,
                        Walk.isDirected_append _ _ hp_vi_vj hp_vj_wr⟩⟩
                  · -- σ.length = 0: σ = nil; vᵢ = vⱼ.  Transport from π's σ-openness at j.
                    push_neg at hσ_pos
                    have hσ_zero : σ.length = 0 := Nat.lt_one_iff.mp hσ_pos
                    have h_vi_eq_vj : π.nodeAt i = π.nodeAt j :=
                      Walk.source_eq_target_of_length_zero σ hσ_zero
                    -- Show j < π.length.
                    have hj_lt_π : j < π.length := by
                      rcases lt_or_eq_of_le hj with hj_lt | hj_eq
                      · exact hj_lt
                      · exfalso
                        have h_suf_z : (π.suffix j).length = 0 := by
                          rw [h_suf_len]; omega
                        have : (σ.append (π.suffix j)).length = 0 := by
                          rw [Walk.length_append, hσ_zero, h_suf_z]
                        omega
                    -- Extract π's step at j-1 and at j.
                    have h_pre_j_pos : 1 ≤ (π.prefix j).length := by
                      rw [Walk.length_prefix π hj]; omega
                    obtain ⟨w_pre_j, p_pre_j, s_left_πj, h_pre_j_eq⟩ :=
                      Walk.walk_pos_eq_append_last (π.prefix j) h_pre_j_pos
                    have h_suf_j_pos : 1 ≤ (π.suffix j).length := by
                      rw [h_suf_len]; omega
                    obtain ⟨mid_πj, s_right_πj, rest_πj, h_suf_j_eq⟩ :=
                      Walk.walk_pos_eq_cons (π.suffix j) h_suf_j_pos
                    -- s_right_πj has no source-arrowhead (case (i)).
                    have h_no_src_πj : ¬ s_right_πj.HasArrowheadAtSource :=
                      h_suf_no_src _ s_right_πj rest_πj h_suf_j_eq
                    have h_s_right_πj_fwd : s_right_πj.IsForward := by
                      cases s_right_πj with
                      | forward _ => simp
                      | backward _ => simp at h_no_src_πj
                      | bidir _ => simp at h_no_src_πj
                    -- mid_πj = π.nodeAt (j + 1) (via nodeAt of π.suffix j at 1).
                    have h_mid_eq : mid_πj = π.nodeAt (j + 1) := by
                      have h1 : (π.suffix j).nodeAt 1 = π.nodeAt (j + 1) :=
                        Walk.nodeAt_suffix π (by rw [h_suf_len] at h_suf_j_pos; omega)
                      have h2 : (π.suffix j).nodeAt 1 = mid_πj := by
                        rw [h_suf_j_eq]
                        change rest_πj.nodeAt 0 = mid_πj
                        rw [Walk.nodeAt_zero]
                      exact h2.symm.trans h1
                    -- w_r = π.nodeAt (j+1).  Via nodeAt computation.
                    have h_w_r_eq : w_r = π.nodeAt (j + 1) := by
                      -- (σ.append (π.suffix j)).nodeAt 1 = w_r (from hp_eq).
                      have h1 : (σ.append (π.suffix j)).nodeAt 1 = w_r := by
                        rw [hp_eq]
                        change p_rest.nodeAt 0 = w_r
                        rw [Walk.nodeAt_zero]
                      -- (σ.append (π.suffix j)).nodeAt 1 = π.nodeAt (j+1) when σ.length = 0.
                      have h2 : (σ.append (π.suffix j)).nodeAt 1 = π.nodeAt (j + 1) := by
                        have h_at_σl : (σ.append (π.suffix j)).nodeAt (σ.length + 1) =
                            (π.suffix j).nodeAt 1 :=
                          Walk.nodeAt_append_add_left σ (π.suffix j) 1
                        rw [hσ_zero, Nat.zero_add] at h_at_σl
                        rw [h_at_σl]
                        exact Walk.nodeAt_suffix π (by rw [h_suf_len] at h_suf_j_pos; omega)
                      exact h1.symm.trans h2
                    -- Now build π.IsBlockableNonColliderAt j.
                    have h_p_pre_j_len : p_pre_j.length = j - 1 := by
                      have h1 : (π.prefix j).length =
                          p_pre_j.length +
                            (Walk.cons s_left_πj (Walk.nil (π.nodeAt j))).length := by
                        rw [h_pre_j_eq, Walk.length_append]
                      rw [Walk.length_prefix π hj] at h1
                      simp [Walk.length_cons, Walk.length_nil] at h1
                      omega
                    have h_pos_form_j : (p_pre_j.length + 1 : ℕ) = j := by omega
                    have h_alt_eq_j :
                        (π.prefix j).append (π.suffix j) =
                          p_pre_j.append
                            (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj)) := by
                      rw [h_pre_j_eq, h_suf_j_eq, Walk.append_assoc,
                        Walk.cons_append, Walk.nil_append]
                    have hπ_form_j : π = p_pre_j.append
                        (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj)) := by
                      rw [← h_alt_eq_j]
                      exact (Walk.prefix_append_suffix π hj).symm
                    have h_πNC_j : π.IsNonColliderAt j := by
                      refine ⟨le_of_lt hj_lt_π, ?_⟩
                      intro h_πColl
                      rw [hπ_form_j] at h_πColl
                      have h_at_p :
                          (p_pre_j.append
                            (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj))).IsColliderAt
                            (p_pre_j.length + 1) := by
                        convert h_πColl using 2
                      rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                      exact h_no_src_πj h_at_p.2
                    have h_πNotUnblk_j : ¬ π.IsUnblockableNonColliderAt j := by
                      intro h_πUnblk
                      rw [hπ_form_j] at h_πUnblk
                      have h_at_p :
                          (p_pre_j.append
                            (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj))).IsUnblockableNonColliderAt
                            (p_pre_j.length + 1) := by
                        convert h_πUnblk using 2
                      rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                      -- h_at_p : s_left_πj.IsUnblockableJoint s_right_πj.
                      -- Use (3): target(s_right_πj) ∈ Sc^G(π.nodeAt j).
                      -- target(s_right_πj) = π.nodeAt (j+1) (defeq).
                      have h_target_in_Sc : π.nodeAt (j+1) ∈ G.Sc (π.nodeAt j) := by
                        have h_at_target := h_at_p.2.2 h_s_right_πj_fwd
                        -- h_at_target : mid_πj ∈ G.Sc (π.nodeAt j).
                        -- mid_πj = π.nodeAt (j+1) by h_mid_eq.
                        rw [← h_mid_eq]
                        exact h_at_target
                      apply h_target_sc
                      rw [h_w_r_eq, h_vi_eq_vj]
                      exact h_target_in_Sc
                    rw [h_vi_eq_vj]
                    exact h_open.2 j ⟨h_πNC_j, h_πNotUnblk_j⟩
              · -- σ.append (π.suffix j) has length 0: σ.length = 0 AND j = π.length.
                push_neg at hp2_pos
                have hp2_zero : (σ.append (π.suffix j)).length = 0 := Nat.lt_one_iff.mp hp2_pos
                -- W has length i + 0 = i. Position i is endpoint of W.
                -- vᵢ = vⱼ = vₙ. Use π's σ-openness at endpoint π.length.
                -- σ.length + (π.length - j) = 0 → σ.length = 0 ∧ j = π.length.
                have h_σ_zero : σ.length = 0 := by
                  rw [Walk.length_append] at hp2_zero
                  omega
                have h_j_eq : j = π.length := by
                  rw [Walk.length_append, h_suf_len] at hp2_zero
                  omega
                -- π.nodeAt i = π.nodeAt j (since vᵢ = vⱼ from σ.length = 0).
                -- And j = π.length so vⱼ = vₙ.
                have h_vi_eq_vj : π.nodeAt i = π.nodeAt j := by
                  have := Walk.source_eq_target_of_length_zero σ h_σ_zero
                  exact this
                have h_vj_eq_vn : π.nodeAt j = vₙ := by
                  rw [h_j_eq, Walk.nodeAt_length]
                rw [h_vi_eq_vj, h_vj_eq_vn]
                -- Goal: vₙ ∉ C.
                have := h_open.2 π.length (Walk.isBlockableNonColliderAt_length π)
                rw [Walk.nodeAt_length] at this
                exact this
          · -- i < k < i + σ.length: interior of σ.  σ is directed so all interior
            -- joints are unblockable (Walk.isUnblockableNonColliderAt_interior_of_directed_in_Sc).
            exfalso
            set k' := k - i with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_lt : k' < σ.length := by omega
            have h_eq : i + k' = k := by omega
            apply h_blkNC.2
            rw [← h_eq]
            rw [Walk.isUnblockableNonColliderAt_splice_mid π σ hi_le h_k'_pos h_k'_lt]
            exact Walk.isUnblockableNonColliderAt_interior_of_directed_in_Sc σ
              hσ_dir hσ_inSc k' h_k'_pos h_k'_lt
        · rcases Nat.eq_or_lt_of_le h_k_ge_mid with h_k_eq_mid | h_k_gt_mid
          · -- k = i + σ.length: inner joint blockable analysis.
            subst h_k_eq_mid
            -- Reduce W.nodeAt (i + σ.length) to vⱼ.
            -- nodeAt_splice_mid with k' = σ.length: W.nodeAt (i + σ.length) = σ.nodeAt σ.length = vⱼ.
            rw [Walk.nodeAt_splice_mid π σ hi_le (le_refl σ.length), Walk.nodeAt_length]
            -- Goal: vⱼ ∉ C.
            -- Case on whether π.nodeAt (j+1) ∈ Sc^G(vⱼ).
            -- Also need: j < π.length (when σ.length doesn't fill W).
            have h_W_len_eq : ((π.prefix i).append (σ.append (π.suffix j))).length =
                i + σ.length + (π.length - j) := by
              rw [Walk.length_append, h_pre_len, Walk.length_append, h_suf_len, Nat.add_assoc]
            -- Bounds: from blockable, i + σ.length ≤ W.length, hence π.length - j ≥ 0
            -- (always true).  We need to know if j = π.length (then W's right side
            -- is empty and position i + σ.length is endpoint) or j < π.length.
            by_cases hj_eq_π : j = π.length
            · -- j = π.length: right side of W is empty.  Position i + σ.length is endpoint.
              -- vⱼ = vₙ.
              rw [show π.nodeAt j = vₙ from by rw [hj_eq_π, Walk.nodeAt_length]]
              have := h_open.2 π.length (Walk.isBlockableNonColliderAt_length π)
              rw [Walk.nodeAt_length] at this
              exact this
            · -- j < π.length.
              have hj_lt_π : j < π.length := lt_of_le_of_ne hj hj_eq_π
              -- Extract π's step at j.
              have h_suf_j_pos : 1 ≤ (π.suffix j).length := by
                rw [h_suf_len]; omega
              obtain ⟨mid_πj, s_right_πj, rest_πj, h_suf_j_eq⟩ :=
                Walk.walk_pos_eq_cons (π.suffix j) h_suf_j_pos
              -- s_right_πj is forward (case (i) via h_suf_no_src).
              have h_no_src_πj : ¬ s_right_πj.HasArrowheadAtSource :=
                h_suf_no_src _ s_right_πj rest_πj h_suf_j_eq
              have h_s_right_πj_fwd : s_right_πj.IsForward := by
                cases s_right_πj with
                | forward _ => simp
                | backward _ => simp at h_no_src_πj
                | bidir _ => simp at h_no_src_πj
              -- mid_πj = π.nodeAt (j+1).
              have h_mid_eq : mid_πj = π.nodeAt (j + 1) := by
                have h1 : (π.suffix j).nodeAt 1 = π.nodeAt (j + 1) :=
                  Walk.nodeAt_suffix π (by rw [h_suf_len] at h_suf_j_pos; omega)
                have h2 : (π.suffix j).nodeAt 1 = mid_πj := by
                  rw [h_suf_j_eq]
                  change rest_πj.nodeAt 0 = mid_πj
                  rw [Walk.nodeAt_zero]
                exact h2.symm.trans h1
              -- Case on whether the joint's right-target is in Sc.
              by_cases h_target_sc : π.nodeAt (j + 1) ∈ G.Sc (π.nodeAt j)
              · -- Joint is unblockable on W (when σ.length ≥ 1).
                -- For σ.length = 0, we drop to a direct argument (no exfalso).
                by_cases hσ_pos : 1 ≤ σ.length
                · -- σ.length ≥ 1: σ ends with last step (forward).
                  exfalso
                  apply h_blkNC.2
                  -- Decompose σ via walk_pos_eq_append_last.
                  obtain ⟨w_last_σ, σ_pre, s_last_σ, hσ_last_eq⟩ :=
                    Walk.walk_pos_eq_append_last σ hσ_pos
                  -- s_last_σ : WalkStep G w_last_σ (π.nodeAt j).
                  -- σ.length = σ_pre.length + 1.
                  have hσ_pre_len : σ_pre.length = σ.length - 1 := by
                    have h_eq : σ.length = σ_pre.length + 1 := by
                      conv_lhs => rw [hσ_last_eq]
                      rw [Walk.length_append, Walk.length_cons, Walk.length_nil]
                    omega
                  -- σ_pre.nodeAt σ_pre.length = w_last_σ (target of σ_pre = source of s_last_σ).
                  -- And σ.nodeAt (σ.length - 1) = w_last_σ (source of last step).
                  -- We have hσ_inSc, so σ.nodeAt (σ_pre.length) = σ.nodeAt (σ.length - 1) ∈ Sc^G(vⱼ).
                  -- Hence w_last_σ ∈ Sc^G(vⱼ).
                  have h_w_last_σ_sc : w_last_σ ∈ G.Sc (π.nodeAt j) := by
                    have h_σ_pre_len_le : σ_pre.length ≤ σ.length := by omega
                    have h_in : σ.nodeAt σ_pre.length ∈ G.Sc (π.nodeAt j) :=
                      hσ_inSc σ_pre.length h_σ_pre_len_le
                    -- σ.nodeAt σ_pre.length = w_last_σ (the source of s_last_σ).
                    have h_node_eq : σ.nodeAt σ_pre.length = w_last_σ := by
                      rw [hσ_last_eq]
                      -- (σ_pre.append (cons s_last_σ (nil vⱼ))).nodeAt σ_pre.length =
                      --   σ_pre.nodeAt σ_pre.length = w_last_σ (the target of σ_pre).
                      rw [Walk.nodeAt_append_le _ _ (le_refl _)]
                      exact Walk.nodeAt_length _
                    rw [h_node_eq] at h_in
                    exact h_in
                  -- s_last_σ is forward (σ.IsDirected).
                  have h_s_last_σ_fwd : s_last_σ.IsForward := by
                    have h_σ_dir' : (σ_pre.append (Walk.cons s_last_σ
                        (Walk.nil (π.nodeAt j)))).IsDirected := by
                      rw [← hσ_last_eq]; exact hσ_dir
                    -- The last step is forward via the split-append directedness helper.
                    obtain ⟨_, h_last_dir⟩ := Walk.isDirected_split_append σ_pre _ h_σ_dir'
                    -- h_last_dir : (cons s_last_σ (nil _)).IsDirected.
                    cases s_last_σ with
                    | forward _ => simp
                    | backward _ => simp at h_last_dir
                    | bidir _ => simp at h_last_dir
                  -- Now express W = ((π.prefix i).append σ_pre).append (cons s_last_σ
                  --   (cons s_right_πj rest_πj)) and apply joint lemma.
                  have hW_form_inner :
                      (π.prefix i).append (σ.append (π.suffix j)) =
                        ((π.prefix i).append σ_pre).append
                          (Walk.cons s_last_σ (Walk.cons s_right_πj rest_πj)) := by
                    rw [hσ_last_eq, h_suf_j_eq, Walk.append_assoc, Walk.append_assoc,
                      Walk.cons_append, Walk.nil_append]
                  have hpos_inner : ((π.prefix i).append σ_pre).length + 1 = i + σ.length := by
                    rw [Walk.length_append, h_pre_len, hσ_pre_len]; omega
                  -- Apply isUnblockableNonColliderAt_append_cons_cons_one.
                  rw [hW_form_inner]
                  have h_at_p :
                      (((π.prefix i).append σ_pre).append
                        (Walk.cons s_last_σ (Walk.cons s_right_πj rest_πj))).IsUnblockableNonColliderAt
                          (((π.prefix i).append σ_pre).length + 1) ↔
                        s_last_σ.IsUnblockableJoint s_right_πj :=
                    Walk.isUnblockableNonColliderAt_append_cons_cons_one
                      ((π.prefix i).append σ_pre) s_last_σ s_right_πj rest_πj
                  -- Convert position.
                  have h_at_p' :
                      (((π.prefix i).append σ_pre).append
                        (Walk.cons s_last_σ (Walk.cons s_right_πj rest_πj))).IsUnblockableNonColliderAt
                          (i + σ.length) ↔
                        s_last_σ.IsUnblockableJoint s_right_πj := by
                    rw [← hpos_inner]; exact h_at_p
                  rw [h_at_p']
                  -- Build IsUnblockableJoint: forward-forward, with target ∈ Sc^G(vⱼ).
                  refine ⟨?_, ?_, ?_⟩
                  · -- ¬ collider: s_right_πj forward → no source-arrowhead.
                    intro ⟨_, h_src⟩; exact h_no_src_πj h_src
                  · -- s_last_σ.IsBackward → ...: s_last_σ forward, vacuous.
                    intro h_back
                    cases s_last_σ with
                    | forward _ => simp at h_back
                    | backward _ => simp at h_s_last_σ_fwd
                    | bidir _ => simp at h_s_last_σ_fwd
                  · -- s_right_πj.IsForward → mid_πj ∈ Sc^G(π.nodeAt j).
                    intro _
                    rw [h_mid_eq]
                    exact h_target_sc
                · -- σ.length = 0: σ = nil, merged joint = outer joint.
                  -- Goal: π.nodeAt j ∉ C.
                  push_neg at hσ_pos
                  have hσ_zero : σ.length = 0 := Nat.lt_one_iff.mp hσ_pos
                  have h_vi_eq_vj : π.nodeAt i = π.nodeAt j :=
                    Walk.source_eq_target_of_length_zero σ hσ_zero
                  rw [← h_vi_eq_vj]
                  -- Goal: π.nodeAt i ∉ C.
                  by_cases hi_zero : i = 0
                  · -- i = 0: transport from h_open.2 0.
                    subst hi_zero
                    exact h_open.2 0 (Walk.isBlockableNonColliderAt_zero π)
                  · -- i ≥ 1: case-on π's step at i-1.
                    have h_i_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
                    have h_pre_i_pos : 1 ≤ (π.prefix i).length := by
                      rw [h_pre_len]; omega
                    obtain ⟨w_pre_i, p_pre_i, s_left_πi, h_pre_i_eq⟩ :=
                      Walk.walk_pos_eq_append_last (π.prefix i) h_pre_i_pos
                    have h_p_pre_i_len : p_pre_i.length = i - 1 := by
                      have h1 : (π.prefix i).length =
                          p_pre_i.length +
                            (Walk.cons s_left_πi (Walk.nil (π.nodeAt i))).length := by
                        rw [h_pre_i_eq, Walk.length_append]
                      rw [h_pre_len] at h1
                      simp [Walk.length_cons, Walk.length_nil] at h1
                      omega
                    have h_pos_form_i : (p_pre_i.length + 1 : ℕ) = i := by omega
                    -- Decompose σ.append (π.suffix j) directly (its source is π.nodeAt i).
                    have h_app_pos : 1 ≤ (σ.append (π.suffix j)).length := by
                      rw [Walk.length_append, hσ_zero, Nat.zero_add]
                      exact h_suf_j_pos
                    obtain ⟨w_app, s_app, rest_app, h_app_eq⟩ :=
                      Walk.walk_pos_eq_cons (σ.append (π.suffix j)) h_app_pos
                    -- s_app has source π.nodeAt i and no source-arrowhead.
                    have h_no_src_app : ¬ s_app.HasArrowheadAtSource :=
                      Walk.first_step_no_source_of_directed_append σ (π.suffix j) _ s_app rest_app
                        hσ_dir h_app_eq h_suf_no_src
                    -- Show w_app = π.nodeAt (j + 1).
                    have h_w_app_eq : w_app = π.nodeAt (j + 1) := by
                      have h1 : (σ.append (π.suffix j)).nodeAt 1 = w_app := by
                        rw [h_app_eq]
                        change rest_app.nodeAt 0 = w_app
                        rw [Walk.nodeAt_zero]
                      have h2 : (σ.append (π.suffix j)).nodeAt 1 = π.nodeAt (j + 1) := by
                        have h_app_add_left := Walk.nodeAt_append_add_left σ (π.suffix j) 1
                        rw [hσ_zero, Nat.zero_add] at h_app_add_left
                        rw [h_app_add_left]
                        exact Walk.nodeAt_suffix π (by rw [h_suf_len] at h_suf_j_pos; omega)
                      exact h1.symm.trans h2
                    -- w_app ∈ G.Sc (π.nodeAt i).
                    have h_w_app_sc : w_app ∈ G.Sc (π.nodeAt i) := by
                      rw [h_w_app_eq, h_vi_eq_vj]
                      exact h_target_sc
                    -- Structural form of W: p_pre_i ⧺ cons s_left_πi (cons s_app rest_app).
                    have hW_form_zero :
                        (π.prefix i).append (σ.append (π.suffix j)) =
                          p_pre_i.append (Walk.cons s_left_πi
                            (Walk.cons s_app rest_app)) := by
                      rw [h_pre_i_eq, h_app_eq, Walk.append_assoc,
                        Walk.cons_append, Walk.nil_append]
                    -- Case-split on s_left_πi.
                    cases s_left_πi with
                    | forward h_fwd_πi =>
                      -- (2) vacuous; (3) holds via h_w_app_sc.  Unblockable.  exfalso.
                      exfalso
                      have h_joint : (WalkStep.forward h_fwd_πi).IsUnblockableJoint s_app := by
                        refine ⟨?_, ?_, ?_⟩
                        · intro ⟨_, h_src⟩; exact h_no_src_app h_src
                        · intro h_back; simp at h_back
                        · intro _; exact h_w_app_sc
                      have h_at_p :
                          (p_pre_i.append (Walk.cons (WalkStep.forward h_fwd_πi)
                              (Walk.cons s_app rest_app))).IsUnblockableNonColliderAt
                            (p_pre_i.length + 1) :=
                        (Walk.isUnblockableNonColliderAt_append_cons_cons_one
                          p_pre_i (WalkStep.forward h_fwd_πi) s_app rest_app).mpr h_joint
                      have h_at_p_W : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                          (p_pre_i.length + 1) := by
                        rw [hW_form_zero]
                        exact h_at_p
                      apply h_blkNC.2
                      convert h_at_p_W using 1
                      omega
                    | backward h_bw_πi =>
                      by_cases h_left_sc : w_pre_i ∈ G.Sc (π.nodeAt i)
                      · -- (2) holds, (3) holds.  Unblockable.  exfalso.
                        exfalso
                        have h_joint : (WalkStep.backward h_bw_πi).IsUnblockableJoint s_app := by
                          refine ⟨?_, ?_, ?_⟩
                          · intro ⟨h_tgt, _⟩; simp at h_tgt
                          · intro _; exact h_left_sc
                          · intro _; exact h_w_app_sc
                        have h_at_p :
                            (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                                (Walk.cons s_app rest_app))).IsUnblockableNonColliderAt
                              (p_pre_i.length + 1) :=
                          (Walk.isUnblockableNonColliderAt_append_cons_cons_one
                            p_pre_i (WalkStep.backward h_bw_πi) s_app rest_app).mpr h_joint
                        have h_at_p_W : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                            (p_pre_i.length + 1) := by
                          rw [hW_form_zero]
                          exact h_at_p
                        apply h_blkNC.2
                        convert h_at_p_W using 1
                        omega
                      · -- (2) fails.  Transport from π at i.
                        -- π = p_pre_i ⧺ cons (backward h_bw_πi) (cons s_right_πi rest_πi)
                        -- where s_right_πi is π's step at i.
                        have h_suf_i_pos : 1 ≤ (π.suffix i).length := by
                          rw [Walk.length_suffix π hi_le]
                          have : i < π.length := lt_of_lt_of_le hij hj
                          omega
                        obtain ⟨_, s_right_πi, rest_πi, h_suf_i_eq⟩ :=
                          Walk.walk_pos_eq_cons (π.suffix i) h_suf_i_pos
                        have h_alt_eq_i :
                            (π.prefix i).append (π.suffix i) =
                              p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                                (Walk.cons s_right_πi rest_πi)) := by
                          rw [h_pre_i_eq, h_suf_i_eq, Walk.append_assoc,
                            Walk.cons_append, Walk.nil_append]
                        have hπ_form_i : π = p_pre_i.append
                            (Walk.cons (WalkStep.backward h_bw_πi)
                              (Walk.cons s_right_πi rest_πi)) := by
                          rw [← h_alt_eq_i]
                          exact (Walk.prefix_append_suffix π hi_le).symm
                        have hi_le_π : i ≤ π.length := hi_le
                        have h_πNC_i : π.IsNonColliderAt i := by
                          refine ⟨hi_le_π, ?_⟩
                          intro h_πColl
                          rw [hπ_form_i] at h_πColl
                          have h_at_p :
                              (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                                (Walk.cons s_right_πi rest_πi))).IsColliderAt
                                (p_pre_i.length + 1) := by
                            convert h_πColl using 2
                          rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                          simp at h_at_p
                        have h_πNotUnblk_i : ¬ π.IsUnblockableNonColliderAt i := by
                          intro h_πUnblk
                          rw [hπ_form_i] at h_πUnblk
                          have h_at_p :
                              (p_pre_i.append (Walk.cons (WalkStep.backward h_bw_πi)
                                (Walk.cons s_right_πi rest_πi))).IsUnblockableNonColliderAt
                                (p_pre_i.length + 1) := by
                            convert h_πUnblk using 2
                          rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                          apply h_left_sc
                          exact h_at_p.2.1 (by simp [WalkStep.IsBackward])
                        exact h_open.2 i ⟨h_πNC_i, h_πNotUnblk_i⟩
                    | bidir h_bd_πi =>
                      -- Bidir: (2) vacuous (IsBackward False), (3) holds.  Unblockable.
                      exfalso
                      have h_joint : (WalkStep.bidir h_bd_πi).IsUnblockableJoint s_app := by
                        refine ⟨?_, ?_, ?_⟩
                        · intro ⟨_, h_src⟩; exact h_no_src_app h_src
                        · intro h_back; simp at h_back
                        · intro _; exact h_w_app_sc
                      have h_at_p :
                          (p_pre_i.append (Walk.cons (WalkStep.bidir h_bd_πi)
                              (Walk.cons s_app rest_app))).IsUnblockableNonColliderAt
                            (p_pre_i.length + 1) :=
                        (Walk.isUnblockableNonColliderAt_append_cons_cons_one
                          p_pre_i (WalkStep.bidir h_bd_πi) s_app rest_app).mpr h_joint
                      have h_at_p_W : ((π.prefix i).append (σ.append (π.suffix j))).IsUnblockableNonColliderAt
                          (p_pre_i.length + 1) := by
                        rw [hW_form_zero]
                        exact h_at_p
                      apply h_blkNC.2
                      convert h_at_p_W using 1
                      omega
              · -- target ∉ Sc^G(vⱼ): joint blockable on W.  Transport from π at j.
                -- π's right edge at j is forward + target ∉ Sc.  π is blockable at j.
                -- Build π.IsBlockableNonColliderAt j and apply h_open.2 j.
                -- Need π's step at j-1.
                have h_pre_j_pos : 1 ≤ (π.prefix j).length := by
                  rw [Walk.length_prefix π hj]; omega
                obtain ⟨w_pre_j, p_pre_j, s_left_πj, h_pre_j_eq⟩ :=
                  Walk.walk_pos_eq_append_last (π.prefix j) h_pre_j_pos
                have h_p_pre_j_len : p_pre_j.length = j - 1 := by
                  have h1 : (π.prefix j).length = p_pre_j.length +
                      (Walk.cons s_left_πj (Walk.nil (π.nodeAt j))).length := by
                    rw [h_pre_j_eq, Walk.length_append]
                  rw [Walk.length_prefix π hj] at h1
                  simp [Walk.length_cons, Walk.length_nil] at h1
                  omega
                have h_pos_form_j : (p_pre_j.length + 1 : ℕ) = j := by omega
                have h_alt_eq_j :
                    (π.prefix j).append (π.suffix j) =
                      p_pre_j.append
                        (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj)) := by
                  rw [h_pre_j_eq, h_suf_j_eq, Walk.append_assoc,
                    Walk.cons_append, Walk.nil_append]
                have hπ_form_j : π = p_pre_j.append
                    (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj)) := by
                  rw [← h_alt_eq_j]
                  exact (Walk.prefix_append_suffix π hj).symm
                have h_πNC_j : π.IsNonColliderAt j := by
                  refine ⟨le_of_lt hj_lt_π, ?_⟩
                  intro h_πColl
                  rw [hπ_form_j] at h_πColl
                  have h_at_p :
                      (p_pre_j.append
                        (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj))).IsColliderAt
                        (p_pre_j.length + 1) := by
                    convert h_πColl using 2
                  rw [Walk.isColliderAt_append_cons_cons_one] at h_at_p
                  exact h_no_src_πj h_at_p.2
                have h_πNotUnblk_j : ¬ π.IsUnblockableNonColliderAt j := by
                  intro h_πUnblk
                  rw [hπ_form_j] at h_πUnblk
                  have h_at_p :
                      (p_pre_j.append
                        (Walk.cons s_left_πj (Walk.cons s_right_πj rest_πj))).IsUnblockableNonColliderAt
                        (p_pre_j.length + 1) := by
                    convert h_πUnblk using 2
                  rw [Walk.isUnblockableNonColliderAt_append_cons_cons_one] at h_at_p
                  apply h_target_sc
                  rw [← h_mid_eq]
                  exact h_at_p.2.2 h_s_right_πj_fwd
                exact h_open.2 j ⟨h_πNC_j, h_πNotUnblk_j⟩
          · -- k > i + σ.length: transport via splice_suf.
            have hWlen : ((π.prefix i).append (σ.append (π.suffix j))).length =
                i + σ.length + (π.length - j) := by
              rw [Walk.length_append, h_pre_len, Walk.length_append, h_suf_len, Nat.add_assoc]
            -- Bound k ≤ W.length:
            -- Position k must satisfy k ≤ W.length for blockable to be informative.
            -- (IsBlockableNonColliderAt requires k ≤ length via IsNonColliderAt.)
            have hk_le_Wlen : k ≤ ((π.prefix i).append (σ.append (π.suffix j))).length :=
              h_blkNC.1.1
            rw [hWlen] at hk_le_Wlen
            set k' := k - (i + σ.length) with hk'_def
            have h_k'_pos : 0 < k' := by omega
            have h_k'_le : k' ≤ π.length - j := by omega
            have h_eq : i + σ.length + k' = k := by omega
            have h_jk'_le : j + k' ≤ π.length := by omega
            have h_πNC : π.IsNonColliderAt (j + k') := by
              refine ⟨h_jk'_le, ?_⟩
              intro h_πColl
              apply h_blkNC.1.2
              rw [← h_eq]
              exact (Walk.isColliderAt_splice_suf π σ hi_le h_k'_pos).mpr h_πColl
            have h_πNotUnblk : ¬ π.IsUnblockableNonColliderAt (j + k') := by
              intro h_πUnblk
              apply h_blkNC.2
              rw [← h_eq]
              exact (Walk.isUnblockableNonColliderAt_splice_suf
                π σ hi_le h_k'_pos).mpr h_πUnblk
            rw [← h_eq, Walk.nodeAt_splice_suf π σ hi_le hj h_k'_le]
            exact h_open.2 (j + k') ⟨h_πNC, h_πNotUnblk⟩

-- REFACTOR-BLOCK-REPLACEMENT-END: replace_walk

end Walk

end Causality
